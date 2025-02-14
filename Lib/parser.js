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

class NewParser
{
    static #isAtomSymbol(str)
    {
        return str.length === 1 && str.match(/[\w\d]/i);
    }

    static #isSpace(str)
    {
        return str.length === 1 && str.match(/\s/i);
    }

    #skip_empty()
    {
        while (!this.#stream.end && NewParser.#isSpace(this.#stream.current))
            this.#stream.next();
    }

    #stream = null;

    parse(formula)
    {
        this.#stream = new Stream(formula);
        return this.GetImpl();
    }

    GetImpl()
    {
        this.#skip_empty();
        let lop = this.GetXor();
        this.#skip_empty();

        while (!this.#stream.end_at(2) && this.#stream.slice(0, 2) == "->")
        {
            this.#stream.move(2);
            this.#skip_empty();
            let rop = this.GetXor();
            this.#skip_empty();
            lop = Formula.binary(Formula.Operator.IMPL, lop, rop);
        }

        return lop;
    }

    GetXor()
    {
        this.#skip_empty();
        let lop = this.GetOr();
        this.#skip_empty();

        while (this.#stream.current == "+")
        {
            this.#stream.next();
            this.#skip_empty();
            let rop = this.GetOr();
            this.#skip_empty();
            lop = Formula.binary(Formula.Operator.XOR, lop, rop);
            this.#skip_empty();
        }

        return lop;
    }

    GetOr()
    {
        this.#skip_empty();
        let lop = this.GetAnd();
        this.#skip_empty();

        while (this.#stream.current == "|")
        {
            this.#stream.next();
            this.#skip_empty();
            let rop = this.GetAnd();
            this.#skip_empty();
            lop = Formula.binary(Formula.Operator.OR, lop, rop);
            this.#skip_empty();
        }

        return lop;
    }

    GetAnd()
    {
        this.#skip_empty();
        let lop = this.GetNot();
        this.#skip_empty();

        while (this.#stream.current == "&")
        {
            this.#stream.next();
            this.#skip_empty();
            let rop = this.GetNot();
            this.#skip_empty();
            lop = Formula.binary(Formula.Operator.AND, lop, rop);
            this.#skip_empty();
        }

        return lop;
    }

    GetNot()
    {
        this.#skip_empty();
        if (this.#stream.current == "!")
        {
            this.#stream.next();
            this.#skip_empty();
            let lop = this.GetNot();
            this.#skip_empty();
            return Formula.unary(Formula.Operator.NOT, lop);
        }
        
        return this.GetLtlOps();
    }

    GetLtlOps()
    {
        this.#skip_empty();

        return this.GetSubExpression();
    }

    GetSubExpression()
    {
        this.#skip_empty();
        if (this.#stream.current == "(")
        {
            this.#stream.next();
            this.#skip_empty();
            let expression = this.GetImpl();
            this.#skip_empty();
            this.#stream.next();
            this.#skip_empty();

            return expression;
        }
        else 
            return this.GetAtom();
    }

    GetAtom()
    {
        this.#skip_empty();
        let len = 0;
        while (!this.#stream.end_at(len) && NewParser.#isAtomSymbol(this.#stream.at(len)))
            len++;

        let name = this.#stream.slice(0, len);
        this.#stream.move(len);

        switch (name)
        {
            case "true":
            case "1":
                return new Formula.true();

            case "false":
            case "0":
                return new Formula.false();

            default:
                return new Formula(name);
        }
    }
}

export default Parser;
