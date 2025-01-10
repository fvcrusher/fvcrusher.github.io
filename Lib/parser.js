import Stream from "./stream.js";
import Formula from "./formula.js";

class Parser
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
        while (!this.#stream.end && Parser.#isSpace(this.#stream.current))
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
        while (!this.#stream.end_at(end) && Parser.#isAtomNameSymbol(this.#stream.at(end)))
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

export default Parser;
