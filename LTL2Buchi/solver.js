import Parser from "../Lib/parser.js";
import Formula from "../Lib/formula.js";
import TreeNode from "./tree.js";

export class Solver
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

    get variables()
    {
        return this.#variables;
    }

    get variables_count()
    {
        return this.#variables.length;
    }

    get all_subltls()
    {
        return this.#variables.concat(this.#subltls);
    }

    #states_trees = [];

    get states_count()
    {
        let sum = 0;
        for (let i = 0; i < this.#states_trees.length; i++)
            sum += this.#states_trees[i].leafs_count;

        return sum;
    }

    get states_trees_depth()
    {
        let max = 0;
        for (let i = 0; i < this.#states_trees.length; i++)
        {
            if (this.#states_trees[i].max_depth > max)
                max = this.#states_trees[i].max_depth;
        }

        return max;
    }

    get states()
    {
        let states = [];
        for (let i = 0; i < this.#states_trees.length; i++)
            states = states.concat(this.#states_trees[i].leafs);

        return states;
    }

    #definitions = [];

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

    #update_definitions(ltl=null)
    {
        let initial_ltl = (ltl == null);
        if (ltl == null)
            ltl = this.ltl;

        let found_in_childs = [];

        if (ltl.lop)
            found_in_childs = found_in_childs.concat(this.#update_definitions(ltl.lop));

        if (ltl.rop)
            found_in_childs = found_in_childs.concat(this.#update_definitions(ltl.rop));

        if (found_in_childs.length == 0 && ltl.opc == Formula.Operator.U && !this.#definitions.some((elem) => ltl.equals(elem[0])))
        {
            if (initial_ltl)
                this.#definitions.push([ltl, 0]);
            else
                this.#definitions.push([ltl, this.#definitions.length + 1]);

            found_in_childs.push(ltl);
        }

        return found_in_childs;
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

    #subltl_index(subltl)
    {
        return this.all_subltls.findIndex((elem, idx, array) => elem.equals(subltl));
    }

    #mask_repr(mask)
    {
        let mask_repr = "";
        for (let i = 0; i < mask.length; i++)
            mask_repr += mask[i] === undefined ? "\x1b[1;90m-\x1b[0m" : 
                         mask[i] ? "\x1b[1;32m1\x1b[0m" : "\x1b[1;31m0\x1b[0m";

        return mask_repr;
    }

    #calculate(all_mask, subltl=this.ltl)
    {
        let lvalue = (subltl.lop == null) ? undefined : this.#calculate(all_mask, subltl.lop);
        let rvalue = (subltl.rop == null) ? undefined : this.#calculate(all_mask, subltl.rop);

        let subltl_idx = this.#subltl_index(subltl);

        let result = all_mask[subltl_idx];

        switch (subltl.opc)
        {
            case Formula.Operator.TRUE:
                result = true;
                break;
            case Formula.Operator.FALSE:
                result = false;
                break;

            case Formula.Operator.ATOM:
            case Formula.Operator.X:
                result = all_mask[subltl_idx];
                break;

            case Formula.Operator.NOT:
                result = (lvalue == undefined) ? undefined : !lvalue;
                break;

            case Formula.Operator.AND:
                if (lvalue == true && rvalue == true)
                    result = true;
                else if (lvalue == false || rvalue == false)
                    result = false;
                break;

            case Formula.Operator.OR:
                if (lvalue == true || rvalue == true)
                    result = true;
                else if (lvalue == false && rvalue == false)
                    result = false;
                break;

            case Formula.Operator.XOR:
                if ((lvalue == true && rvalue == true) || (lvalue == false && rvalue == false))
                    result = false;
                else if ((lvalue == true && rvalue == false) || (lvalue == false && rvalue == true))
                    result = true;
                break;

            case Formula.Operator.IMPL:
                if (lvalue == false || rvalue == true)
                    result = true;
                else if (lvalue == true && rvalue == false)
                    result = false;
                break;

            case Formula.Operator.U:
                if (rvalue == true)
                    result = true;
                else if (lvalue == false && rvalue == false)
                    result = false;
                break;

            case Formula.Operator.F:
                if (lvalue == true)
                    result = true;
                break;

            case Formula.Operator.G:
                if (lvalue == false)
                    result = false;
                break;

            case Formula.Operator.W:
            case Formula.Operator.R:
            default:
                console.log(`Can not calculate operator ${subltl} directly`);
                break;
        }

        console.assert(all_mask[subltl_idx] == undefined || all_mask[subltl_idx] == result);

        all_mask[subltl_idx] = result;
        return result;
    }

    #build_state(all_mask, top_level=true)
    {
        let state = []
        for (let i = 0; i < all_mask.length; i++)
            state.push(all_mask[i]);

        this.#calculate(state);

        let node = new TreeNode(state);

        let undefined_state_idx = state.indexOf(undefined);

        if (undefined_state_idx != -1)
        {
            console.assert(this.all_subltls[undefined_state_idx].opc == Formula.Operator.U);

            state[undefined_state_idx] = false;
            node.false_branch = this.#build_state(state, false);
            state[undefined_state_idx] = true;
            node.true_branch = this.#build_state(state, false);
            state[undefined_state_idx] = undefined;
        }

        if (top_level)
            this.#states_trees.push(node);
        
        return node;
    }

    #is_initial_state(state_no)
    {
        let state = this.states[state_no - 1];

        return state[state.length - 1];
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
        let i = 0;
        for (i = 0; i < this.transformation_steps.length; i++)
            console.log(`Step ${i + 1}: ${this.transformation_steps[i].string}`);

        for (let announced = this.#update_definitions(); announced.length != 0; announced = this.#update_definitions())
            console.log(`Step ${++i}: ${this.ltl.def_string(this.#definitions)}`);

        this.#parse_subltls();
        console.log(`Found ${this.all_subltls.length} unique subltls: ${this.all_subltls.map((subltl) => subltl.def_string(this.#definitions)).join("; ")}`);

        let variables_mask = [];
        while (this.#iterate_mask(variables_mask))
        {
            let all_mask = variables_mask.concat(Array(this.#subltls.length).fill(undefined));
            this.#build_state(all_mask);
        }

        console.log(`Found ${this.states_count} states, max split depth is ${this.states_trees_depth}`);


    }
}

// let solver = new Solver();
// // solver.solve("Fa U Gb & c -> d");
// // solver.solve("x U (XFy & Fp) -> X(Gr | X(t & Xi & false) | s) & (o & p)");
// // solver.solve("(p -> Xq) U (!p & q)");
// // solver.solve("G(q -> (!p & X(!q U p)))");
// solver.solve("Fp U Fq");
