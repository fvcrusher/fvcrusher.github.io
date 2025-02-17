import Stream from "./stream.js";
import Formula from "./formula.js";

class OldParser
{
    static #isSpace(str)
    {
        return str.length === 1 && str.match(/\s/i);
    }

    static #isAtomNameSymbol(str)
    {
        return str.length === 1 && str.match(/[a-z0-9]/i);
    }

    #stream = null;
    #stack = [];

    parse(formula)
    {
        this.#stream = new Stream(formula);

        if (typeof formula != "string")
            throw new Error(`formula must be string, but ${typeof formula} given`);

        this.#parse_until(null);
        
        if (this.#stack.length != 1)
            throw new Error(`Something went wrong while parsing \'${formula}\'`);

        return this.#stack.pop();
    }

    #skip_empty()
    {
        while (!this.#stream.end && OldParser.#isSpace(this.#stream.current))
            this.#stream.next();
    }

    #parse_until(end_symbol)
    {
        while (!this.#stream.end && (end_symbol == null || this.#stream.current != end_symbol))
            this.#parse_term();

        if (!this.#stream.end && this.#stream.current == end_symbol)
            this.#stream.next();
    }

    #parse_atom()
    {
        let end = 0;
        while (!this.#stream.end_at(end) && OldParser.#isAtomNameSymbol(this.#stream.at(end)))
            end++;

        let name = this.#stream.slice(0, end);
        this.#stream.move(end);
        
        if (name === "true")
            return new Formula(Formula.Operator.TRUE);
        
        else if (name === "false")
            return new Formula(Formula.Operator.FALSE);

        return new Formula(name);
    }

    #parse_term()
    {
        this.#skip_empty();
        let c = this.#stream.current;

        switch (c)
        {
            default:
                this.#stack.push(this.#parse_atom());
                break;

            case "!":
            case "X":
            case "F":
            case "G":
                this.#stream.next();
                this.#parse1(Formula.opcode_of(c));
                break;
            
            case "&":
            case "|":
            case "+":
            case "U":
            case "R":
            case "W":
                this.#stream.next();
                this.#parse2(Formula.opcode_of(c));
                break;

            case "-":
                if (this.#stream.at(1) != ">")
                    throw new Error(`Unexpected token \'${this.#stream.slice(0, 2)}\'`);

                this.#stream.move(2);

                this.#parse2(Formula.Operator.IMPL);
                break;
            
            case "(":
                this.#stream.next();
                this.#parse_until(")");
                break;
            
            case ")":
                break;
        }
    }

    #parse1(opc)
    {
        this.#parse_term();
        let ltl = this.#stack.pop();
        this.#stack.push(Formula.unary(opc, ltl));
    }

    #parse2(opc)
    {
        this.#parse_term();
        let rop = this.#stack.pop();
        let lop = this.#stack.pop();
        this.#stack.push(Formula.binary(opc, lop, rop));
    }
}

class Parser
{
    static #isAtomSymbol(str)
    {
        return str.length === 1 && str.match(/[a-zA-EH-QSTVYZ\d_]/);
    }

    #stream = null;

    parse(formula)
    {
        this.#stream = new Stream(formula);
        this.#stream.remove_spaces();
        let result = this.GetImpl();
        if (!this.#stream.end)
            return Formula.error(this.#stream.initial_str, this.#stream.initial_counter, "EOL", this.#stream.current, `Expected end of line, but '${this.#stream.current}' found`)
        return result;
    }

    GetImpl()
    {
        let lop = this.GetXor();

        while (!this.#stream.end_at(2) && this.#stream.slice(0, 2) == "->")
        {
            this.#stream.move(2);
            let rop = this.GetXor();
            lop = Formula.binary(Formula.Operator.IMPL, lop, rop);
        }

        return lop;
    }

    GetXor()
    {
        let lop = this.GetOr();

        while (this.#stream.current == "+")
        {
            this.#stream.next();
            let rop = this.GetOr();
            lop = Formula.binary(Formula.Operator.XOR, lop, rop);
        }

        return lop;
    }

    GetOr()
    {
        let lop = this.GetAnd();

        while (this.#stream.current == "|")
        {
            this.#stream.next();
            let rop = this.GetAnd();
            lop = Formula.binary(Formula.Operator.OR, lop, rop);
        }

        return lop;
    }

    GetAnd()
    {
        let lop = this.GetBinaryLtlOps();

        while (this.#stream.current == "&")
        {
            this.#stream.next();
            let rop = this.GetBinaryLtlOps();
            lop = Formula.binary(Formula.Operator.AND, lop, rop);
        }

        return lop;
    }

    GetBinaryLtlOps()
    {
        let lop = this.GetNot();

        while (this.#stream.startswith("U", "W", "R"))
        {
            let op = this.#stream.current;
            this.#stream.next();
            let rop = this.GetNot();
            switch (op)
            {
                case "U":
                    lop = Formula.binary(Formula.Operator.U, lop, rop);
                    break;
                case "W":
                    lop = Formula.binary(Formula.Operator.W, lop, rop);
                    break;
                case "R":
                    lop = Formula.binary(Formula.Operator.R, lop, rop);
                    break;
            }
        }

        return lop;
    }

    GetNot()
    {
        if (this.#stream.startswith("!", "¬", "-"))
        {
            this.#stream.next();
            let lop = this.GetNot();
            return Formula.unary(Formula.Operator.NOT, lop);
        }
        
        return this.GetUnaryLtlOps();
    }

    GetUnaryLtlOps()
    {
        if (this.#stream.startswith("X", "F", "<>", "G", "[]"))
        {
            let op = this.#stream.slice(0, this.#stream.startswith("X", "F", "G") ? 1 : 2);
            this.#stream.move(this.#stream.startswith("X", "F", "G") ? 1 : 2);
            let lop = this.GetNot();
            switch (op)
            {
                case "X":
                    return Formula.unary(Formula.Operator.X, lop);
                case "F":
                case "<>":
                    return Formula.unary(Formula.Operator.F, lop);
                case "G":
                case "[]":
                    return Formula.unary(Formula.Operator.G, lop);                    
            }
        }

        return this.GetSubExpression();
    }

    static #getEnclosing(bracket)
    {
        switch (bracket)
        {
            case "(": return ")";
            case "[": return "]";
            case "{": return "}";
        }
    }

    GetSubExpression()
    {
        if (this.#stream.startswith("(", "[", "{"))
        {
            let opening_bracket = this.#stream.current;
            this.#stream.next();
            let expression = this.GetImpl();

            if (this.#stream.current != Parser.#getEnclosing(opening_bracket))
                return Formula.error(this.#stream.initial_str, this.#stream.initial_counter, Parser.#getEnclosing(opening_bracket), this.#stream.current == undefined ? "EOL" : this.#stream.current, `Expected enclosing bracket '${Parser.#getEnclosing(opening_bracket)}', but '${this.#stream.current == undefined ? "EOL" : this.#stream.current}' found`);

            this.#stream.next();
            return expression;
        }
        else 
            return this.GetAtom();
    }

    GetAtom()
    {
        let len = 0;
        while (!this.#stream.end_at(len) && Parser.#isAtomSymbol(this.#stream.at(len)))
            len++;

        if (len == 0)
            return Formula.error(this.#stream.initial_str, this.#stream.initial_counter, "variable name", this.#stream.current == undefined ? "EOL" : this.#stream.current, `Expected variable, but '${this.#stream.current == undefined ? "EOL" : this.#stream.current}' found`)

        let name = this.#stream.slice(0, len);
        this.#stream.move(len);

        switch (name)
        {
            case "true":
            case "1":
                return Formula.true();

            case "false":
            case "0":
                return Formula.false();

            default:
                return new Formula(name);
        }
    }
}

export default Parser;
