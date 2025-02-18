class Formula 
{
    static opcode_of(str)
    {
        if (str.length != 1)
            throw new Error(`String must contains only one character, but string of ${str.length} given`);

        switch (str)
        {
            case "!": return Formula.Operator.NOT;
            case "X": return Formula.Operator.X;
            case "F": return Formula.Operator.F;
            case "G": return Formula.Operator.G;
            case "&": return Formula.Operator.AND;
            case "|": return Formula.Operator.OR;
            case "+": return Formula.Operator.XOR;
            case "U": return Formula.Operator.U;
            case "R": return Formula.Operator.R;
            case "W": return Formula.Operator.W;
            default: throw new Error(`Unknown symbol ${str}`);
        }
    }

    static text_of(opc, latex=false, compact=false)
    {
        switch (opc)
        {
            case Formula.Operator.TRUE: return compact ? "1" : (latex ? "\\mathtt{true}" : "true");
            case Formula.Operator.FALSE: return compact ? "0" : (latex ? "\\mathtt{false}" : "false");
            case Formula.Operator.NOT: return latex ? "\\mathbf{\\neg} " : "!";
            case Formula.Operator.X: return latex ? "\\mathbf{X} " : "X";
            case Formula.Operator.F: return latex ? "\\mathbf{F} " : "F";
            case Formula.Operator.G: return latex ? "\\mathbf{G} " : "G";
            case Formula.Operator.AND: return latex ? (compact ? " \\hspace{0.075cm} " : " \\hspace{0.1cm}\\mathbf{\\wedge}\\hspace{0.1cm} ") : (compact ? "" : " & ");
            case Formula.Operator.OR: return latex ? " \\hspace{0.1cm}\\mathbf{\\vee}\\hspace{0.1cm} " : " | ";
            case Formula.Operator.IMPL: return latex ? " \\hspace{0.1cm}\\mathbf{\\rightarrow}\\hspace{0.1cm} " : " -> ";
            case Formula.Operator.XOR: return latex ? " \\hspace{0.1cm}\\mathbf{\\oplus}\\hspace{0.1cm} " : " + ";
            case Formula.Operator.U: return latex ? " \\hspace{0.1cm}\\mathbf{U}\\hspace{0.1cm} " : " U ";
            case Formula.Operator.R: return latex ? " \\hspace{0.1cm}\\mathbf{W}\\hspace{0.1cm} " : " R ";
            case Formula.Operator.W: return latex ? " \\hspace{0.1cm}\\mathbf{R}\\hspace{0.1cm} " : " W ";
            default: return "?";
        }
    }

    static #definition_text(def_no, latex=false)
    {
        switch (def_no)
        {
            case 0: return latex ? "\\varphi" : "φ";
            case 1: return latex ? "\\alpha" : "α";
            case 2: return latex ? "\\beta" : "β";
            case 3: return latex ? "\\gamma" : "γ";
            case 4: return latex ? "\\delta" : "δ";
            case 5: return latex ? "\\varepsilon" : "ε";
            case 6: return latex ? "\\zeta" : "ζ";
            case 7: return latex ? "\\eta" : "η";
            case 8: return latex ? "\\vartheta" : "ϑ";
            case 9: return latex ? "\\mu" : "μ";
            case 10: return latex ? "\\nu" : "ν";
            case 11: return latex ? "\\xi" : "ξ";
            case 12: return latex ? "\\rho" : "ρ";
            case 13: return latex ? "\\sigma" : "σ";
            case 14: return latex ? "\\chi" : "χ";
            case 15: return latex ? "\\psi" : "ψ";
            case 16: return latex ? "\\omega" : "ω";
        }
    }

    static copy(other)
    {
        switch (other.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return new Formula(other.opc);

            case Formula.Operator.ATOM:
                return new Formula(other.name);

            case Formula.Operator.NOT:
            case Formula.Operator.X:
            case Formula.Operator.F:
            case Formula.Operator.G:
                return Formula.unary(other.opc, Formula.copy(other.lop));

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.XOR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                return Formula.binary(other.opc, Formula.copy(other.lop), Formula.copy(other.rop));

            case Formula.Operator.ERROR_NODE:
                return Formula.error(other.#error_info.string, other.#error_info.index, other.#error_info.expected, other.#error_info.found, other.#error_info.message);
        }

        return null;
    }

    static Operator = Object.freeze(
        {
            TRUE: 0,
            FALSE: 1,
            ATOM: 2,
            NOT: 3,
            X: 4,
            F: 5,
            G: 6,
            AND: 7,
            OR: 8,
            XOR: 9,
            IMPL: 10,
            U: 11,
            W: 12,
            R: 13,
            ERROR_NODE: -1
        }
    )

    lop = null;
    rop = null;
    opc = null;
    name = null;

    #error_info = null;

    constructor(operator)
    {
        if (typeof operator === "number")
            this.opc = operator;
        else if (typeof operator === "string")
        {
            this.opc = Formula.Operator.ATOM;
            this.name = String(operator);
        }
        else 
            throw new Error(`Parameter must be \"number\" or \"string\", but \"${typeof operator}\" given`);
    }

    static true()
    {
        return new Formula(Formula.Operator.TRUE);
    }

    static false()
    {
        return new Formula(Formula.Operator.FALSE);
    }

    static unary(opc, operand)
    {
        let node = new Formula(opc);
        node.lop = operand;
        return node;
    }

    static binary(opc, l_operand, r_operand)
    {
        let node = new Formula(opc);
        node.lop = l_operand;
        node.rop = r_operand;
        return node;
    }

    static error(formula_string, position, expected, found, message=null)
    {
        let node = new Formula(Formula.Operator.ERROR_NODE);
        node.#error_info = {string: formula_string, index: position, expected: expected, found: found, message: message};
        return node;
    }

    get correct()
    {
        let flag = this.opc != Formula.Operator.ERROR_NODE;

        if (this.lop != null)
            flag &= this.lop.correct;
        if (this.rop != null)
            flag &= this.rop.correct;

        return flag;
    }

    get errors()
    {
        let errors_list = [];
        if (this.opc == Formula.Operator.ERROR_NODE)
            errors_list.push(this.#error_info);

        if (this.lop != null)
            errors_list = errors_list.concat(this.lop.errors);

        if (this.rop != null)
            errors_list = errors_list.concat(this.rop.errors);

        return errors_list;
    }

    equals(other)
    {
        let node_equals = (this.opc == other.opc && this.name == other.name);
        let lop_equals = (this.lop == null && other.lop == null) || (this.lop != null && other.lop != null && this.lop.equals(other.lop));
        let rop_equals = (this.rop == null && other.rop == null) || (this.rop != null && other.rop != null && this.rop.equals(other.rop));
        return node_equals && lop_equals && rop_equals;
    }

    contains(other)
    {
        let contains = false;

        contains |= this.equals(other);
        
        if (this.lop != null)
            contains |= this.lop.contains(other);

        if (this.rop != null)
            contains |= this.rop.contains(other);

        return contains;
    }

    static #no_need_wrapping(opc, nested_opc, compact=false)
    {
        return (
            (opc === Formula.Operator.AND && nested_opc === Formula.Operator.AND) ||
            (opc === Formula.Operator.OR && nested_opc === Formula.Operator.OR) ||
            (opc === Formula.Operator.XOR && nested_opc === Formula.Operator.XOR) ||
            (compact && nested_opc === Formula.Operator.AND)
        )
    }

    #to_string_internal(wrap=false, latex=false, compact=false, compact_not=false, definitions=[], announce=[])
    {
        let str = "";

        let wrap_lop = (this.lop != null && Formula.#no_need_wrapping(this.opc, this.lop.opc, compact)) ? false : true;
        let wrap_rop = (this.rop != null && Formula.#no_need_wrapping(this.opc, this.rop.opc, compact)) ? false : true;

        let announce_definition = -1;

        for (let i = 0; i < definitions.length; i++)
        {
            if (this.equals(definitions[i][0]))
                return Formula.#definition_text(definitions[i][1]);
        }

        for (let i = 0; i < announce.length; i++)
        {
            if (this.equals(announce[i][0]))
            {
                announce_definition = announce[i][1];
                break;
            }
        }

        if (latex && announce_definition != -1)
            str += "\\overbrace{"

        switch (this.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                str += `${Formula.text_of(this.opc, latex, compact)}`;
                break;
            
            case Formula.Operator.ATOM:
                str += this.name;
                break;

            case Formula.Operator.NOT:
                if (compact_not || compact)
                {
                    str += `\\overline{${this.lop.#to_string_internal(wrap_lop, latex, compact, definitions, announce)}}`;
                    break;
                }
            case Formula.Operator.X:
            case Formula.Operator.F:
            case Formula.Operator.G:
                str += `${Formula.text_of(this.opc, latex, compact)}${this.lop.#to_string_internal(wrap_lop, latex, compact, definitions, announce)}`;
                break;

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.XOR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                let res = `${this.lop.#to_string_internal(wrap_lop, latex, compact, definitions, announce)}${Formula.text_of(this.opc, latex, compact)}${this.rop.#to_string_internal(wrap_rop, latex, compact, definitions, announce)}`;
                str += (wrap ? `(${res})` : res);
                break;

            case Formula.Operator.ERROR_NODE:
                str += "<error_node>";
                break;

            default:
                throw new Error(`Unexpected operator kind: opc=${this.opc}`);
        }

        if (latex && announce_definition != -1)
            str += `}^{${Formula.#definition_text(announce_definition)}}`

        return str;
    }

    get string()
    {
        return this.#to_string_internal(false, false, false, false);
    }

    def_string(definitions, announce=[])
    {
        return this.#to_string_internal(false, false, false, false, definitions, announce);
    }

    get latex()
    {
        return this.#to_string_internal(false, true, false, false);
    }

    def_latex(definitions, announce=[])
    {
        return this.#to_string_internal(false, true, false, false, definitions, announce);
    }

    get compact_latex()
    {
        return this.#to_string_internal(false, true, true, true);
    }

    get cnf_latex()
    {
        return this.#to_string_internal(false, true, false, true)
    }

    get variables()
    {
        let variables = [];

        if (this.lop != null)
            variables = this.lop.variables;

        if (this.rop != null)
        {
            let rop_variables = this.rop.variables;
            for (let i = 0; i < rop_variables.length; i++)
            {
                if (!variables.some((variable) => variable.equals(rop_variables[i])))
                    variables.push(rop_variables[i]);
            }
        }

        if (this.opc == Formula.Operator.ATOM && !variables.some((variable) => variable.equals(this)) && this.name != "")
            variables.push(Formula.copy(this))

        return variables;
    }
}

export default Formula;
