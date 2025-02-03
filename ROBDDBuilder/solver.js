import Parser from "../Lib/parser.js";
import Formula from "../Lib/formula.js";
import TreeNode from "../Lib/tree.js";

export class Solver
{
    #initial_formula = null;

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

    #solver_step(formula, variables_order)
    {
        let idx = 0;
        while (idx < variables_order.length)
        {
            if (formula.contains(variables_order[idx]))
                break;
            idx++;
        }

        if (idx == variables_order.length) // Exiting, if there is no variables in formula
            return

        let current_variable = variables_order[idx];

        let true_branch_formula = this.#propagate_variable(formula, current_variable, true);
        true_branch_formula = this.#simplify(true_branch_formula);
        this.#solver_step(true_branch_formula, variables_order.slice(idx + 1));

        let false_branch_formula = this.#propagate_variable(formula, current_variable, false);
        false_branch_formula = this.#simplify(false_branch_formula);
        this.#solver_step(false_branch_formula, variables_order.slice(idx + 1));
    }

    solve(formula)
    {
        if (typeof formula === "string")
        {
            let parser = new Parser();
            this.#initial_formula = parser.parse(formula);
        }
        else
            return;

        console.log(this.#initial_formula.string);
        console.log("Simplifiing");
        console.log(this.#simplify(this.#initial_formula).string);
    }
}

let solver = new Solver()
solver.solve("(x2 & !y2) | (!(x2 + y2) & ((x1 & !y1) | (!(x1 + y1) & (x0 & !y0))))");
