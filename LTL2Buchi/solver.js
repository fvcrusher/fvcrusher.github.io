import Parser from "../Lib/parser.js";
import Formula from "../Lib/formula.js";

class Solver
{
    #initial_ltl = null;
    transformation_steps = [];

    get initial_ltl()
    {
        return this.#initial_ltl;
    }

    get ltl()
    {
        if (this.transformation_steps.length == 0)
            return this.#initial_ltl;
        return this.transformation_steps[this.transformation_steps.length - 1];
    }

    #variables = [];
    #subltls = [];

    get all_subltls()
    {
        return this.#variables.concat(this.#subltls);
    }

    constructor()
    {
        
    }

    #propagate_X(ltl, branch_X_count = 0)
    {
        switch (ltl.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(ltl.opc);

            case Formula.Operator.ATOM:
                let atom = new Formula(ltl.name);
                for (let i = 0; i < branch_X_count; i++)
                    atom = Formula.unary(Formula.Operator.X, atom);
                return atom;

            case Formula.Operator.X:
                return this.#propagate_X(ltl.lop, branch_X_count + 1);

            case Formula.Operator.NOT:
            case Formula.Operator.F:
            case Formula.Operator.G:
                return Formula.unary(ltl.opc, this.#propagate_X(ltl.lop, branch_X_count));

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                return Formula.binary(ltl.opc, this.#propagate_X(ltl.lop, branch_X_count), this.#propagate_X(ltl.rop, branch_X_count));
        }

        return null;
    }

    #substitute_R(ltl)
    {
        switch (ltl.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(ltl.opc);

            case Formula.Operator.ATOM:
                return new Formula(ltl.name);

            case Formula.Operator.R:
                return Formula.unary(
                    Formula.Operator.NOT,
                    Formula.binary(
                        Formula.Operator.U,
                        Formula.unary(Formula.Operator.NOT, this.#substitute_R(ltl.lop)),
                        Formula.unary(Formula.Operator.NOT, this.#substitute_R(ltl.rop))
                    )
                )

            case Formula.Operator.X:
            case Formula.Operator.NOT:
            case Formula.Operator.F:
            case Formula.Operator.G:
                return Formula.unary(ltl.opc, this.#substitute_R(ltl.lop));

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
                return Formula.binary(ltl.opc, this.#substitute_R(ltl.lop), this.#substitute_R(ltl.rop));
        }

        return null;
    }

    #substitute_W(ltl)
    {
        switch (ltl.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(ltl.opc);

            case Formula.Operator.ATOM:
                return new Formula(ltl.name);

            case Formula.Operator.W:
                return Formula.binary(
                    Formula.Operator.OR,
                    Formula.binary(
                        Formula.Operator.U, this.#substitute_W(ltl.lop), this.#substitute_W(ltl.rop)
                    ),
                    Formula.unary(
                        Formula.Operator.G, this.#substitute_W(ltl.lop)
                    )
                )

            case Formula.Operator.X:
            case Formula.Operator.NOT:
            case Formula.Operator.F:
            case Formula.Operator.G:
                return Formula.unary(ltl.opc, this.#substitute_W(ltl.lop));

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.R:
                return Formula.binary(ltl.opc, this.#substitute_W(ltl.lop), this.#substitute_W(ltl.rop));
        }

        return null;
    }

    #substitute_G(ltl)
    {
        switch (ltl.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(ltl.opc);

            case Formula.Operator.ATOM:
                return new Formula(ltl.name);

            case Formula.Operator.G:
                return Formula.unary(
                    Formula.Operator.NOT, 
                    Formula.unary(
                        Formula.Operator.F, 
                        Formula.unary(
                            Formula.Operator.NOT, this.#substitute_G(ltl.lop)
                        )
                    )
                )

            case Formula.Operator.X:
            case Formula.Operator.NOT:
            case Formula.Operator.F:
                return Formula.unary(ltl.opc, this.#substitute_G(ltl.lop));

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                return Formula.binary(ltl.opc, this.#substitute_G(ltl.lop), this.#substitute_G(ltl.rop));
        }

        return null;
    }

    #substitute_F(ltl)
    {
        switch (ltl.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(ltl.opc);

            case Formula.Operator.ATOM:
                return new Formula(ltl.name);

            case Formula.Operator.F:
                return Formula.binary(Formula.Operator.U, Formula.true(), this.#substitute_F(ltl.lop));

            case Formula.Operator.X:
            case Formula.Operator.NOT:
            case Formula.Operator.G:
                return Formula.unary(ltl.opc, this.#substitute_F(ltl.lop));

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                return Formula.binary(ltl.opc, this.#substitute_F(ltl.lop), this.#substitute_F(ltl.rop));
        }

        return null;
    }

    #transform()
    {
        this.transformation_steps = [];
        this.transformation_steps.push(this.ltl);
        this.transformation_steps.push(this.#propagate_X(this.ltl));
        this.transformation_steps.push(this.#substitute_R(this.ltl));
        this.transformation_steps.push(this.#substitute_W(this.ltl));
        this.transformation_steps.push(this.#substitute_G(this.ltl));
        this.transformation_steps.push(this.#substitute_F(this.ltl));

        let tmp = [];
        
        for (let step = 0; step < this.transformation_steps.length; step++)
        {
            let len = tmp.length
            if (len == 0 || !this.transformation_steps[step].equals(tmp[len - 1]))
                tmp.push(this.transformation_steps[step]);
        }

        this.transformation_steps = tmp;
    }

    #parse_subltls(ltl=null)
    {
        if (ltl == null)
            ltl = this.ltl;

        if (ltl.lop)
            this.#parse_subltls(ltl.lop);

        if (ltl.rop)
            this.#parse_subltls(ltl.rop);

        if (
            (ltl.opc == Formula.Operator.ATOM || ltl.opc == Formula.Operator.X) &&
            !this.#variables.some((variable) => variable.equals(ltl))
        )
            this.#variables.push(ltl);

        else if (
            (ltl.opc != Formula.Operator.ATOM && ltl.opc != Formula.Operator.X) &&
            !this.#subltls.some((variable) => variable.equals(ltl))
        )
            this.#subltls.push(ltl);
    }

    #clear_list(list)
    {
        while (list.pop());
    }

    #iterate_mask(mask)
    {
        if (mask.length != this.#variables.length)
        {
            this.#clear_list(mask);
            for (let i = 0; i < this.#variables.length; i++)
                mask.push(false);

            return true;
        }

        let last_false = mask.lastIndexOf(false)
        if (last_false == -1)
            return false;

        mask[last_false] = true;
        for (let i = last_false + 1; i < mask.length; i++)
            mask[i] = false;

        return true;
    }

    solve(ltl)
    {
        if (typeof ltl === "string")
        {
            let parser = new Parser();
            this.#initial_ltl = parser.parse(ltl);
        }
        else
            return;

        this.#transform();
        this.#parse_subltls();

        let variables_mask = [];
        while (this.#iterate_mask(variables_mask))
        {
            let all_mask = variables_mask.concat(Array(this.#subltls.length).fill(undefined));
            console.log(all_mask);
        }
    }
}

let solver = new Solver();
solver.solve("Fa U Gb & c -> d");
//solver.solve("x U (XFy & Fp) -> X(Gr | X(t & Xi & false) | s) & (o & p)");
for (let i = 0; i < solver.transformation_steps.length; i++)
    console.log(solver.transformation_steps[i].string);

console.log(`There is ${solver.all_subltls.length} subltls`);
for (let i = 0; i < solver.all_subltls.length; i++)
    console.log(solver.all_subltls[i].string);