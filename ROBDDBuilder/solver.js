import Parser from "../Lib/parser.js";
import Formula from "../Lib/formula.js";
import TreeNode from "../Lib/tree.js";

export class Solver
{
    #initial_formula = null;
    #atoms_order = null;
    #known_branches = [];
    robdd = null;
    #solution_steps = [];
    #solution_line = 0;
    #suspicious_solution = false;

    get solution_steps()
    {
        return this.#solution_steps;
    }

    constructor()
    {}

    static #invert(formula)
    {
        switch (formula.opc)
        {
            case Formula.Operator.NOT:
                return formula.lop;
            default:
                return Formula.unary(Formula.Operator.NOT, formula);
        }
    }

    static #is_self_negation(f1, f2)
    {
        return (
            (f1.opc == Formula.Operator.NOT && f1.lop.equals(f2)) ||
            (f2.opc == Formula.Operator.NOT && f2.lop.equals(f1))
        );
    }

    #simplify(formula)
    {
        if (formula == null)
            return null;

        let rop = this.#simplify(formula.rop);
        let lop = this.#simplify(formula.lop);

        switch (formula.opc)
        {
            case Formula.Operator.ATOM:
                return new Formula(formula.name);

            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(formula.opc);

            case Formula.Operator.NOT:
                if (lop.opc == Formula.Operator.FALSE) 
                    return Formula.true();
                else if (lop.opc == Formula.Operator.TRUE) 
                    return Formula.false();
                else if (lop.opc == Formula.Operator.NOT) 
                    return lop.lop;
                return Formula.unary(formula.opc, lop);

            case Formula.Operator.AND:
                if (lop.equals(rop)) 
                    return lop;
                else if (Solver.#is_self_negation(lop, rop))
                    return Formula.false();
                else if (lop.opc == Formula.Operator.FALSE || rop.opc == Formula.Operator.FALSE)
                    return Formula.false();
                else if (lop.opc == Formula.Operator.TRUE)
                    return rop;
                else if (rop.opc == Formula.Operator.TRUE)
                    return lop;
                return Formula.binary(formula.opc, lop, rop);

            case Formula.Operator.OR:
                if (lop.equals(rop))
                    return lop;
                else if (Solver.#is_self_negation(lop, rop))
                    return Formula.true();
                else if (lop.opc == Formula.Operator.TRUE || rop.opc == Formula.Operator.TRUE)
                    return Formula.true();
                else if (lop.opc == Formula.Operator.FALSE)
                    return rop;
                else if (rop.opc == Formula.Operator.FALSE)
                    return lop;
                return Formula.binary(formula.opc, lop, rop);

            case Formula.Operator.XOR:
                if (lop.equals(rop))
                    return Formula.false();
                else if (Solver.#is_self_negation(lop, rop))
                    return Formula.true();
                else if (lop.opc == Formula.Operator.FALSE)
                    return rop;
                else if (rop.opc == Formula.Operator.FALSE)
                    return lop;
                else if (lop.opc == Formula.Operator.TRUE)
                    return Solver.#invert(rop);
                else if (rop.opc == Formula.Operator.TRUE)
                    return Solver.#invert(lop);
                return Formula.binary(formula.opc, lop, rop);

            case Formula.Operator.IMPL:
                if (lop.equals(rop))
                    return Formula.true();
                else if (Solver.#is_self_negation(lop, rop))
                    return rop;
                else if (lop.opc == Formula.Operator.FALSE)
                    return Formula.true();
                else if (lop.opc == Formula.Operator.TRUE)
                    return rop;
                else if (rop.opc == Formula.Operator.TRUE)
                    return Formula.true();
                else if (rop.opc == Formula.Operator.FALSE)
                    return Solver.#invert(lop);
                return Formula.binary(formula.opc, lop, rop);
        }
    }

    #propagate_variable(formula, variable, value)
    {
        if (formula == null)
            return null;

        let lop = this.#propagate_variable(formula.lop, variable, value);
        let rop = this.#propagate_variable(formula.rop, variable, value);

        switch (formula.opc)
        {
            case Formula.Operator.ATOM:
                if (formula.equals(variable))
                    return value ? Formula.true() : Formula.false();

                return new Formula(formula.name);

            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(formula.opc);

            case Formula.Operator.NOT:
                return Formula.unary(formula.opc, lop);

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.XOR:
            case Formula.Operator.IMPL:
                return Formula.binary(formula.opc, lop, rop);
            
            default:
                return null;
        }
    }

    #find_formula_mention(formula)
    {
        for (let i = 0; i < this.#known_branches.length; i++)
        {
            if (this.#known_branches[i].formula.equals(formula))
                return this.#known_branches[i].line;
        }

        return 0;
    }

    #solver_step(formula, variable_idx=0, depth = 0)
    {
        let current_line = this.#solution_line;

        for (let i = 0; i < this.#known_branches.length; i++)
        {
            if (this.#known_branches[i].formula.equals(formula))
                return this.#known_branches[i].robdd_node;
        }

        let current_node = null;

        if (formula.opc == Formula.Operator.TRUE || formula.opc == Formula.Operator.FALSE)
            current_node = new TreeNode((formula.opc == Formula.Operator.TRUE) ? "1" : "0");

        else
        {
            let idx = variable_idx;
            while (idx < this.#atoms_order.length)
            {
                if (formula.contains(this.#atoms_order[idx]))
                    break;
                idx++;
            }

            if (idx == this.#atoms_order.length) // Exiting, if there is no variables in formula
                throw new EvalError(`Formula is ${formula.string}, but there is no any variables left to propagate`);

            let current_variable = this.#atoms_order[idx];

            let true_branch_formula = this.#propagate_variable(formula, current_variable, true);
            true_branch_formula = this.#simplify(true_branch_formula);

            let false_branch_formula = this.#propagate_variable(formula, current_variable, false);
            false_branch_formula = this.#simplify(false_branch_formula);

            if (true_branch_formula.equals(false_branch_formula))
            {
                this.#suspicious_solution = true;
                current_node = this.#solver_step(true_branch_formula, idx + 1, depth);
            }

            else
            {
                current_node = new TreeNode(current_variable.string);

                let true_branch_mention = (this.#find_formula_mention(true_branch_formula) == 0) ? "" : ` (Already mentioned in line ${this.#find_formula_mention(true_branch_formula)})`;
                console.log(`${++this.#solution_line} ${Array(depth).fill("\t").join("")}${current_variable.string} = 1: ${true_branch_formula.string}${true_branch_mention}`);
                this.#solution_steps.push({depth: depth, step_no: this.#solution_line, step: `${current_variable.latex} = 1: ${true_branch_formula.latex}`, mention: this.#find_formula_mention(true_branch_formula)});
                let true_branch_node = this.#solver_step(true_branch_formula, idx + 1, depth + 1);

                let false_branch_mention = (this.#find_formula_mention(false_branch_formula) == 0) ? "" : ` (Already mentioned in line ${this.#find_formula_mention(false_branch_formula)})`;
                console.log(`${++this.#solution_line} ${Array(depth).fill("\t").join("")}${current_variable.string} = 0: ${false_branch_formula.string}${false_branch_mention}`);
                this.#solution_steps.push({depth: depth, step_no: this.#solution_line, step: `${current_variable.latex} = 0: ${false_branch_formula.latex}`, mention: this.#find_formula_mention(false_branch_formula)});
                let false_branch_node = this.#solver_step(false_branch_formula, idx + 1, depth + 1);
                
                current_node.true_branch = true_branch_node;
                current_node.false_branch = false_branch_node;
            }
        }

        this.#known_branches.push({formula: formula, robdd_node: current_node, line: current_line});
        return current_node;
    }

    solve(formula, atoms_order=null)
    {
        let parser = new Parser();

        if (atoms_order != null && atoms_order.length == Solver.get_atoms(formula).length)
        {
            for (let i = 0; i < atoms_order.length; i++)
            {
                if (typeof atoms_order[i] == "string")
                    atoms_order[i] = parser.parse(atoms_order[i]);
                else if (atoms_order[i] instanceof Formula);
                else
                    throw new EvalError("atoms in atoms order must be strings or Formula's");
            }

            this.#atoms_order = atoms_order;
        }

        else
            this.#atoms_order = Solver.get_atoms(formula);

        if (typeof formula === "string")
            this.#initial_formula = parser.parse(formula);
        else if (formula instanceof Formula)
            this.#initial_formula = Formula.copy(formula);
        else
            return;

        console.log(`Building ROBDD graph for ${this.#initial_formula.string}`);

        this.robdd = this.#solver_step(this.#initial_formula);
    }

    static get_atoms(formula)
    {
        let parser = new Parser();
        let parsed_formula = null;

        if (typeof formula === "string")
            parsed_formula = parser.parse(formula);
        else if (formula instanceof Formula)
            parsed_formula = Formula.copy(formula);

        if (parsed_formula != null)
            return parsed_formula.variables;
    }

    robdd_graph_dump(grouping = true, shuffle = false)
    {
        let result = `digraph G { rankdir=TB; ordering=\"${shuffle ? "in" : "out"}\"; bgcolor="transparent"\n`

        if (!grouping)
            result += `${this.#recursive_robdd_graph_dump_nodes(this.robdd).join("\n")}\n`;

        else
        {
            for (let i = 0; i < this.#atoms_order.length; i++)
                result += `\tsubgraph { rank=same\n${this.#recursive_robdd_graph_dump_nodes(this.robdd, true, this.#atoms_order[i]).join("\n")}\n\t}\n`

            result += `\tsubgraph { rank=same\n${this.#recursive_robdd_graph_dump_nodes(this.robdd, true).join("\n")}\n\t}\n`
        }

        result += `${this.#recursive_robdd_graph_dump_edges(this.robdd).join("\n")}\n`;

        result += "}"

        return result
    }

    #recursive_robdd_graph_dump_nodes(node, grouping = false, atom_to_dump = null, visited_nodes=[])
    {
        if (visited_nodes.indexOf(node) != -1)
            return [];
        visited_nodes.push(node);

        let result = [];

        if (
            !grouping || 
            (grouping && atom_to_dump != null && node.data == atom_to_dump.string) || 
            (grouping && atom_to_dump == null && (node.data == "1" || node.data == "0"))
        )
            result.push(`${grouping ? "\t\t" : "\t"}id${node.id} [label="${node.data}", shape=${(node.data == "1" || node.data == "0") ? "box" : "circle"}]`);

        if (node.false_branch)
            result = result.concat(this.#recursive_robdd_graph_dump_nodes(node.false_branch, grouping, atom_to_dump, visited_nodes));
    
        if (node.true_branch)
            result = result.concat(this.#recursive_robdd_graph_dump_nodes(node.true_branch, grouping, atom_to_dump, visited_nodes));

        return result;
    }

    #recursive_robdd_graph_dump_edges(node, visited_nodes=[])
    {
        if (visited_nodes.indexOf(node) != -1)
            return [];
        visited_nodes.push(node);

        let result = [];

        if (node.false_branch)
        {
            result.push(`\tid${node.id}->id${node.false_branch.id} [style=dashed]`);
            result = result.concat(this.#recursive_robdd_graph_dump_edges(node.false_branch, visited_nodes));
        }

        if (node.true_branch)
        {
            result.push(`\tid${node.id}->id${node.true_branch.id}`);
            result = result.concat(this.#recursive_robdd_graph_dump_edges(node.true_branch, visited_nodes));
        }

        return result;
    }
}

let solver = new Solver()
let vars = Solver.get_atoms("(x2 & !y2) | (!(x2 + y2) & ((x1 & !y1) | (!(x1 + y1) & (x0 & !y0))))");
console.log(vars.map((v) => v.string));
solver.solve("(x2 & !y2) | (!(x2 + y2) & ((x1 & !y1) | (!(x1 + y1) & (x0 & !y0))))", ["x0", "x1", "x2", "y0", "y1", "y2"]);
