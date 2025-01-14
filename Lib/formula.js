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

    static text_of(opc, latex=false)
    {
        switch (opc)
        {
            case Formula.Operator.TRUE: return latex ? "\\mathtt{true}" : "true";
            case Formula.Operator.FALSE: return latex ? "\\mathtt{false}" : "false";
            case Formula.Operator.NOT: return latex ? "\\mathbf{\\neg}" : "!";
            case Formula.Operator.X: return latex ? "\\mathbf{X}" : "X";
            case Formula.Operator.F: return latex ? "\\mathbf{F}" : "F";
            case Formula.Operator.G: return latex ? "\\mathbf{G}" : "G";
            case Formula.Operator.AND: return latex ? "\\hspace{0.1cm}\\mathbf{\\wedge}\\hspace{0.1cm}" : "&";
            case Formula.Operator.OR: return latex ? "\\hspace{0.1cm}\\mathbf{\\vee}\\hspace{0.1cm}" : "|";
            case Formula.Operator.IMPL: return latex ? "\\hspace{0.1cm}\\mathbf{\\rightarrow}\\hspace{0.1cm}" : "->";
            case Formula.Operator.XOR: return latex ? "\\hspace{0.1cm}\\mathbf{\\oplus}\\hspace{0.1cm}" : "+";
            case Formula.Operator.U: return latex ? "\\hspace{0.1cm}\\mathbf{U}\\hspace{0.1cm}" : "U";
            case Formula.Operator.R: return latex ? "\\hspace{0.1cm}\\mathbf{W}\\hspace{0.1cm}" : "R";
            case Formula.Operator.W: return latex ? "\\hspace{0.1cm}\\mathbf{R}\\hspace{0.1cm}" : "W";
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
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                return Formula.binary(other.opc, Formula.copy(other.lop), Formula.copy(other.rop));
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
            R: 13
        }
    )

    lop = null;
    rop = null;
    opc = null;
    name = null;

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

    equals(other)
    {
        let node_equals = (this.opc == other.opc && this.name == other.name);
        let lop_equals = (this.lop == null && other.lop == null) || (this.lop != null && other.lop != null && this.lop.equals(other.lop));
        let rop_equals = (this.rop == null && other.rop == null) || (this.rop != null && other.rop != null && this.rop.equals(other.rop));
        return node_equals && lop_equals && rop_equals;
    }

    static #need_wrapping(opc, nested_opc)
    {
        return (
            (opc === Formula.Operator.AND && nested_opc === Formula.Operator.AND) ||
            (opc === Formula.Operator.OR && nested_opc === Formula.Operator.OR) ||
            (opc === Formula.Operator.XOR && nested_opc === Formula.Operator.XOR)
        )
    }

    #to_string_internal(wrap=false, latex=false, definitions=[])
    {
        let wrap_lop = (this.lop != null && Formula.#need_wrapping(this.opc, this.lop.opc)) ? false : true;
        let wrap_rop = (this.rop != null && Formula.#need_wrapping(this.opc, this.rop.opc)) ? false : true;

        for (let i = 0; i < definitions.length; i++)
        {
            if (this.equals(definitions[i][0]))
                return Formula.#definition_text(definitions[i][1]);
        }

        switch (this.opc)
        {
            case Formula.Operator.TRUE:
            case Formula.Operator.FALSE:
                return `${Formula.text_of(this.opc, latex)}`;
            
            case Formula.Operator.ATOM:
                return this.name;

            case Formula.Operator.NOT:
            case Formula.Operator.X:
            case Formula.Operator.F:
            case Formula.Operator.G:
                return `${Formula.text_of(this.opc, latex)}${this.lop.#to_string_internal(wrap_lop, latex, definitions)}`;

            case Formula.Operator.AND:
            case Formula.Operator.OR:
            case Formula.Operator.IMPL:
            case Formula.Operator.U:
            case Formula.Operator.W:
            case Formula.Operator.R:
                let res = `${this.lop.#to_string_internal(wrap_lop, latex, definitions)} ${Formula.text_of(this.opc, latex)} ${this.rop.#to_string_internal(wrap_rop, latex, definitions)}`;
                return wrap ? `(${res})` : res;

            default:
                throw new Error(`Unexpected operator kind: opc=${this.opc}`);
        }
    }

    get string()
    {
        return this.#to_string_internal(false, false);
    }

    def_string(definitions)
    {
        return this.#to_string_internal(false, false, definitions);
    }

    get latex()
    {
        return this.#to_string_internal(false, true);
    }

    def_latex(definitions)
    {
        return this.#to_string_internal(false, true, definitions);
    }
}

export default Formula;
