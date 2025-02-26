import Parser from "../Lib/parser.js";
import Formula from "../Lib/formula.js";
import TreeNode from "../Lib/tree.js";

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

    get states_trees()
    {
        return this.#states_trees;
    }

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

    raw_state_path(idx)
    {
        let internal_idx = idx;
        let tree_idx = 0;

        while (internal_idx >= this.states_trees[tree_idx].leafs_count)
        {
            internal_idx -= this.states_trees[tree_idx].leafs_count;
            tree_idx++;
        }

        let cur_tree_node = this.states_trees[tree_idx];

        let path = [cur_tree_node];

        while (cur_tree_node.false_branch != null && cur_tree_node.true_branch != null)
        {
            if (internal_idx < cur_tree_node.false_branch.leafs_count)
                cur_tree_node = cur_tree_node.false_branch;

            else
            {
                internal_idx -= cur_tree_node.false_branch.leafs_count;
                cur_tree_node = cur_tree_node.true_branch;
            }

            path.push(cur_tree_node);
        }

        return path;
    }

    raw_states_table()
    {
        let min = (a, b) => (a > b) ? a : b;

        let table = [];
        for (let i = 0; i < this.states_count; i++)
            table.push(this.raw_state_path(i));
        
        for (let i = table.length - 1; i > 0; i--)
        {
            for (let j = 0; j < min(table[i].length, table[i - 1].length); j++)
            {
                if (table[i][j] == table[i - 1][j])
                    table[i][j] = null;
                else
                    break;
            }
        }

        return table;
    }

    #definitions = [];

    get definitions()
    {
        return this.#definitions;
    }

    #inversed_mask = false;

    #initial_states = [];

    get initial_states()
    {
        return this.#initial_states;
    }

    #acceptable_states = [];

    get acceptable_states()
    {
        return this.#acceptable_states;
    }

    #edges = [];

    get edges()
    {
        return this.#edges;
    }

    get untils_list()
    {
        let found = [];

        for (let i = 0; i < this.all_subltls.length; i++)
        {
            if (this.all_subltls[i].opc == Formula.Operator.U)
                found.push(this.all_subltls[i]);
        }

        return found;
    }

    constructor(inversed_mask=false)
    {
        this.#inversed_mask = inversed_mask;
    }

    truth_list_for_mask(mask)
    {
        let truth_list = [];

        for (let i = 0; i < mask.length; i++)
        {
            if (mask[i] == true)
                truth_list.push(this.all_subltls[i]);
        }

        return truth_list;
    }

    atoms_truth_list_for_mask(mask)
    {
        let truth_list = [];

        for (let i = 0; i < mask.length; i++)
        {
            if (mask[i] == true && (this.all_subltls[i].opc == Formula.Operator.ATOM || this.all_subltls[i].opc == Formula.Operator.X))
                truth_list.push(this.all_subltls[i]);
        }

        return truth_list;
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
            case Formula.Operator.XOR:
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
            case Formula.Operator.XOR:
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
            case Formula.Operator.XOR:
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
            case Formula.Operator.XOR:
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
            case Formula.Operator.XOR:
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

    #collect_definitions(ltl=null)
    {
        let initial_ltl = (ltl == null);
        if (ltl == null)
            ltl = this.ltl;

        if (ltl.lop)
            this.#collect_definitions(ltl.lop);

        if (ltl.rop)
            this.#collect_definitions(ltl.rop);

        if (initial_ltl)
            this.#definitions.push([ltl, 0]);

        else if (ltl.opc == Formula.Operator.U && !this.#definitions.some((elem) => ltl.equals(elem[0])))
            this.#definitions.push([ltl, this.#definitions.length + 1]);
    }

    get_disjoint_definitions(known_definitions, ltl=null)
    {
        let definitions = []

        let initial_ltl = (ltl == null);
        if (ltl == null)
            ltl = this.ltl;

        if (ltl.lop)
        {
            let left_definitions = this.get_disjoint_definitions(known_definitions, ltl.lop);
            for (let i = 0; i < left_definitions.length; i++)
            {
                if (definitions.findIndex((elem) => elem[0].equals(left_definitions[i])) == -1)
                    definitions.push(left_definitions[i]);
            }
        }

        if (ltl.rop)
        {
            let right_definitions = this.get_disjoint_definitions(known_definitions, ltl.rop);
            for (let i = 0; i < right_definitions.length; i++)
            {
                if (definitions.findIndex((elem) => elem[0].equals(right_definitions[i])) == -1)
                    definitions.push(right_definitions[i]);
            }
        }

        if (definitions.length == 0 && (ltl.opc == Formula.Operator.U || initial_ltl))
        {
            for (let i = 0; i < known_definitions.length; i++)
            {
                if (known_definitions[i][0].equals(ltl))
                    return definitions;
            }

            for (let i = 0; i < this.#definitions.length; i++)
            {
                if (this.#definitions[i][0].equals(ltl))
                    return definitions.concat([this.#definitions[i]]);
            }
        }

        return definitions;
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

        let found_false = this.#inversed_mask ? mask.indexOf(false) : mask.lastIndexOf(false);
        if (found_false == -1)
            return false;

        mask[found_false] = true;
        for (let i = found_false + (this.#inversed_mask ? -1 : 1); this.#inversed_mask ? (i >= 0) : (i < mask.length); i += this.#inversed_mask ? -1 : 1)
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
        let state = this.states[state_no];

        return state[state.length - 1];
    }

    #build_initial_states()
    {
        this.#initial_states = [];

        for (let state_no = 0; state_no < this.states_count; state_no++)
        {
            if (this.#is_initial_state(state_no))
                this.#initial_states.push(state_no);
        }
    }

    #is_acceptable_state(state_no, until)
    {
        let state = this.states[state_no];

        for (let until_idx = 0; until_idx < this.all_subltls.length; until_idx++)
        {
            if (this.all_subltls[until_idx].equals(until))
            {
                for (let until_rhs_idx = 0; until_rhs_idx < this.all_subltls.length; until_rhs_idx++)
                {
                    if (this.all_subltls[until_rhs_idx].equals(until.rop))
                    {
                        if (state[until_idx] == state[until_rhs_idx])
                            return true;
                        else
                            return false;
                    }
                }
            }
        }
    }

    #build_acceptable_states()
    {
        this.#acceptable_states = [];

        for (let until_no = 0; until_no < this.untils_list.length; until_no++)
        {
            let acc = [];
            for (let state_no = 0; state_no < this.states_count; state_no++)
            {
                if (this.#is_acceptable_state(state_no, this.untils_list[until_no]))
                    acc.push(state_no);
            }
            this.#acceptable_states.push(acc);
        }
    }

    edge_resrictions(from)
    {
        let state = this.states[from]

        let restrictions = [];

        for (let i = 0; i < state.length; i++)
        {
            switch(this.all_subltls[i].opc)
            {
                case Formula.Operator.X:
                    restrictions.push(`${this.all_subltls[i].lop.def_latex(this.definitions)} ${state[i] ? "\\in" : "\\notin"} s'`);
                    break;

                case Formula.Operator.U:
                    let lhs_idx = this.all_subltls.findIndex((subltl) => subltl.equals(this.all_subltls[i].lop))
                    let rhs_idx = this.all_subltls.findIndex((subltl) => subltl.equals(this.all_subltls[i].rop))
                    if (state[lhs_idx] == true && state[rhs_idx] == false)
                        restrictions.push(`${this.all_subltls[i].def_latex(this.definitions)} ${state[i] ? "\\in" : "\\notin"} s'`);
                    break;
            }
        }

        return restrictions.join("\\hspace{0.1cm}\\mathbf{\\wedge}\\hspace{0.1cm}");
    }

    #check_edge_rules(from, to)
    {
        for (let i = 0; i < this.all_subltls.length; i++)
        {
            switch (this.all_subltls[i].opc)
            {
                case Formula.Operator.X:
                    let x_var_idx = this.all_subltls.findIndex((elem) => elem.equals(this.all_subltls[i].lop));
                    if (this.states[from][i] != this.states[to][x_var_idx])
                        return false;
                    break;

                case Formula.Operator.U:
                    let u_lhs_idx = this.all_subltls.findIndex((elem) => elem.equals(this.all_subltls[i].lop));
                    let u_rhs_idx = this.all_subltls.findIndex((elem) => elem.equals(this.all_subltls[i].rop));
                    if (!(
                        (this.states[from][i] == true && this.states[from][u_rhs_idx] == true) ||
                        (this.states[from][i] == false && this.states[from][u_lhs_idx] == false && this.states[from][u_rhs_idx] == false) ||
                        (this.states[from][u_lhs_idx] == true && this.states[from][u_rhs_idx] == false && this.states[from][i] == this.states[to][i])
                    ))
                        return false;
                    break;
            }
        }

        return true;
    }

    #build_edges()
    {
        this.#edges = [];

        for (let state_no = 0; state_no < this.states_count; state_no++)
        {
            let edg = [];

            for (let target_no = 0; target_no < this.states_count; target_no++)
            {
                if (this.#check_edge_rules(state_no, target_no))
                    edg.push(target_no);
            }

            this.#edges.push(edg);
        }
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

        if (!this.#initial_ltl.correct)
        {
            this.#errors = this.#initial_ltl.errors;
            return;
        }

        this.#transform();
        let i = 0;
        for (i = 0; i < this.transformation_steps.length; i++)
            console.log(`Step ${i + 1}: ${this.transformation_steps[i].string}`);

        this.#collect_definitions();

        this.#parse_subltls();
        console.log(`Found ${this.all_subltls.length} unique subltls: ${this.all_subltls.map((subltl) => subltl.def_string(this.#definitions)).join("; ")}`);

        let variables_mask = [];
        while (this.#iterate_mask(variables_mask))
        {
            let all_mask = variables_mask.concat(Array(this.#subltls.length).fill(undefined));
            this.#build_state(all_mask);
        }

        console.log(`Found ${this.states_count} states, max split depth is ${this.states_trees_depth}`);

        this.#build_initial_states();
        this.#build_acceptable_states();
        this.#build_edges();
    }

    static check_syntax(ltl)
    {
        let parser = new Parser();
        let parsed_ltl = null;

        if (typeof ltl === "string")
            parsed_ltl = parser.parse(ltl);
        else if (ltl instanceof Formula)
            parsed_ltl = Formula.copy(ltl);

        if (parsed_ltl == null)
            return [];

        return parsed_ltl.errors;
    }
}

// let solver = new Solver();
// solver.solve("Fa U Gb & c -> d");
// solver.solve("x U (XFy & Fp) -> X(Gr | X(t & Xi & false) | s) & (o & p)");
// solver.solve("(p -> Xq) U (!p & q)");
// solver.solve("G(q -> (!p & X(!q U p)))");
// solver.solve("p U t");
// solver.solve("Fp U Fq");
// console.log(solver.raw_states_table());
