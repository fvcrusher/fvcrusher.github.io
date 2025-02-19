import Formula from "../Lib/formula.js";
import Parser from "../Lib/parser.js";

export class Solver
{
    #errors = null;

    get incorrect()
    {
        return this.#errors != null;
    }

    get errors()
    {
        return this.#errors;
    }

    #initial_formula = null;
    #current_replacement_idx = 0;

    get initial_formula()
    {
        return this.#initial_formula;
    }

    #solution_steps = [];

    get solution_steps()
    {
        return this.#solution_steps;
    }

    get cnf()
    {
        let cnf = this.#solution_steps[0].cnf_part;

        for (let step = 1; step < this.#solution_steps.length; step++)
            cnf = Formula.binary(Formula.Operator.AND, this.#solution_steps[step].cnf_part, cnf);

        cnf = Formula.binary(Formula.Operator.AND, this.#solution_steps[this.#solution_steps.length - 1].replacement, cnf);

        return cnf;
    }

    #get_atoms(clause)
    {
        let atoms = [];

        if (clause.opc == Formula.Operator.OR)
        {
            if (clause.lop != null)
                atoms = atoms.concat(this.#get_atoms(clause.lop));
            if (clause.rop != null)
                atoms = atoms.concat(this.#get_atoms(clause.rop));
        }

        else
            atoms.push(clause);

        return atoms;
    }

    #get_clauses(cnf)
    {
        let clauses = [];

        if (cnf.opc == Formula.Operator.AND)
        {
            if (cnf.lop != null)
                clauses = clauses.concat(this.#get_clauses(cnf.lop));
            if (cnf.rop != null)
                clauses = clauses.concat(this.#get_clauses(cnf.rop));
        }

        else
            clauses.push({clause: cnf, atoms_list: this.#get_atoms(cnf)});

        return clauses;
    }

    get cnf_parts()
    {
        return this.#get_clauses(this.cnf);
    }

    get cnf_latex()
    {
        return this.cnf_parts.map(clause => (clause.clause.opc == Formula.Operator.ATOM) ? `\$${clause.clause.cnf_latex}\$` : `\$(${clause.clause.cnf_latex})\$`).join(` \$${Formula.text_of(Formula.Operator.AND, true, false)}\$ `);
    }

    get cnf_parts_latex()
    {
        return "$\\{ \\hspace{0.07cm} " + this.cnf_parts.map(clause => clause.atoms_list.map(atom => atom.cnf_latex).join(" \\hspace{0.07cm} ")).join(", \\hspace{0.15cm} \$ \$") + " \\hspace{0.07cm} \\}$"
    }

    static #replacements = [
        "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", 
        "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", 
        "W", "X", "Y", "Z"
    ]

    get #current_replacement()
    {
        return Solver.#replacements[this.#current_replacement_idx++];
    }

    #fold_duplicated_not(formula)
    {
        if (formula != null && formula.opc == Formula.Operator.NOT &&
            formula.lop != null && formula.lop.opc == Formula.Operator.NOT)
        {
            formula.emplace(formula.lop.lop);
            this.#fold_duplicated_not(formula);
        }

        else
        {
            if (formula.lop != null)
                this.#fold_duplicated_not(formula.lop);
            if (formula.rop != null)
                this.#fold_duplicated_not(formula.rop);
        }
    }

    #get_cnf_part(opc, lop, rop, replacement)
    {
        let cnf_part = null;

        switch (opc)
        {
            case Formula.Operator.AND:
                cnf_part = Formula.binary(Formula.Operator.AND, 
                    Formula.binary(Formula.Operator.OR, 
                        Formula.binary(Formula.Operator.OR,
                            Formula.unary(Formula.Operator.NOT, lop),
                            Formula.unary(Formula.Operator.NOT, rop)
                        ),
                        replacement
                    ),
                    Formula.binary(Formula.Operator.AND,
                        Formula.binary(Formula.Operator.OR,
                            lop, Formula.unary(Formula.Operator.NOT, replacement),
                        ),
                        Formula.binary(Formula.Operator.OR,
                            rop, Formula.unary(Formula.Operator.NOT, replacement),
                        )
                    )
                );
                break;
            case Formula.Operator.OR:
                cnf_part = Formula.binary(Formula.Operator.AND, 
                    Formula.binary(Formula.Operator.OR, 
                        Formula.binary(Formula.Operator.OR,
                            lop, rop
                        ),
                        Formula.unary(Formula.Operator.NOT, replacement)
                    ),
                    Formula.binary(Formula.Operator.AND,
                        Formula.binary(Formula.Operator.OR,
                            Formula.unary(Formula.Operator.NOT, lop), replacement,
                        ),
                        Formula.binary(Formula.Operator.OR,
                            Formula.unary(Formula.Operator.NOT, rop), replacement,
                        )
                    )
                );
                break;
            case Formula.Operator.XOR:
                cnf_part = Formula.binary(Formula.Operator.AND, 
                    Formula.binary(Formula.Operator.OR, 
                        Formula.binary(Formula.Operator.OR,
                            Formula.unary(Formula.Operator.NOT, lop), 
                            Formula.unary(Formula.Operator.NOT, rop)
                        ),
                        Formula.unary(Formula.Operator.NOT, replacement)
                    ),
                    Formula.binary(Formula.Operator.AND,
                        Formula.binary(Formula.Operator.OR, 
                            Formula.binary(Formula.Operator.OR,
                                lop, rop
                            ),
                            Formula.unary(Formula.Operator.NOT, replacement)
                        ),
                        Formula.binary(Formula.Operator.AND,
                            Formula.binary(Formula.Operator.OR, 
                                Formula.binary(Formula.Operator.OR,
                                    lop, Formula.unary(Formula.Operator.NOT, rop)
                                ),
                                replacement
                            ),
                            Formula.binary(Formula.Operator.OR, 
                                Formula.binary(Formula.Operator.OR,
                                    Formula.unary(Formula.Operator.NOT, lop), rop
                                ),
                                replacement
                            )
                        )
                    )
                );
                break;
            case Formula.Operator.IMPL:
                cnf_part = Formula.binary(Formula.Operator.AND, 
                    Formula.binary(Formula.Operator.OR, 
                        Formula.binary(Formula.Operator.OR,
                            Formula.unary(Formula.Operator.NOT, lop), rop
                        ),
                        Formula.unary(Formula.Operator.NOT, replacement)
                    ),
                    Formula.binary(Formula.Operator.AND,
                        Formula.binary(Formula.Operator.OR,
                            lop, replacement,
                        ),
                        Formula.binary(Formula.Operator.OR,
                            Formula.unary(Formula.Operator.NOT, rop), replacement,
                        )
                    )
                );
                break;
        }

        this.#fold_duplicated_not(cnf_part);

        return cnf_part;
    }

    solve(formula)
    {
        let parser = new Parser();

        if (typeof formula === "string")
            this.#initial_formula = parser.parse(formula);
        else if (formula instanceof Formula)
            this.#initial_formula = Formula.copy(formula);
        else
            return;

        let errors_list = Solver.check_syntax(this.#initial_formula)
        if (errors_list.length != 0)
        {
            this.#errors = errors_list;
            return;
        }

        this.replace_binary_operation(Formula.copy(this.#initial_formula));
    }

    #is_atom_or_reversed_atom(formula)
    {
        return (
            formula.opc == Formula.Operator.ATOM ||
            (
                formula.opc == Formula.Operator.NOT &&
                formula.lop != null &&
                formula.lop.opc == Formula.Operator.ATOM
            )
        );
    }

    replace_binary_operation(formula)
    {
        if (formula.lop != null && !this.#is_atom_or_reversed_atom(formula.lop))
            this.replace_binary_operation(formula.lop);

        if (formula.rop != null && !this.#is_atom_or_reversed_atom(formula.rop))
            this.replace_binary_operation(formula.rop);

        if (
            formula.lop != null && formula.rop != null && 
            this.#is_atom_or_reversed_atom(formula.lop) &&
            this.#is_atom_or_reversed_atom(formula.rop)
        )
        {
            let binary_operation = Formula.copy(formula);

            formula.opc = Formula.Operator.ATOM;
            formula.lop = null;
            formula.rop = null;
            formula.name = this.#current_replacement;

            let cnf_part = this.#get_cnf_part(binary_operation.opc, binary_operation.lop, binary_operation.rop, formula);

            this.#solution_steps.push({replacement: formula, initial_operation: binary_operation, cnf_part: cnf_part});
        }
    }

    static check_syntax(ltl)
    {
        let parser = new Parser();
        let parsed_ltl = null;

        if (typeof ltl === "string")
            parsed_ltl = parser.parse(ltl);
        else if (ltl instanceof Formula)
            parsed_ltl = Formula.copy(ltl);

        let errors = parsed_ltl.errors;

        if (!parsed_ltl.contains_only(Formula.BooleanOperators))
            errors.push({string: ltl, index: -1, expected: "", found: "", message: "Formula must contain only classic boolean operators"})

        return errors;
    }
}

// let solver = new Solver();
// solver.solve("((x & y) + (x | y)) -> z");
// console.log(solver.solution_steps.map(step => { return `${step.replacement.string} = ${step.initial_operation.string}; ${(step.cnf_part == null) ? "N/I" : step.cnf_part.string}`; }));

// console.log(solver.cnf.latex);
// console.log(solver.cnf_parts.map(clause => clause.atoms_list.map(atom => atom.string).join()).join("\n"));
// console.log(solver.cnf_parts_latex);
