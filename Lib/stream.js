class Stream
{
    #str = null;
    #counter = 0;

    get str()
    {
        return this.#str;
    }

    get rest_of_str()
    {
        return this.#str.slice(this.#counter, this.#str.length);
    }

    constructor(str)
    {
        if (!(typeof str === "string"))
            throw new Error(`string expected, but ${typeof str} given`);

        this.#str = str;
        this.#counter = 0;
    }

    get current_idx()
    {
        return this.#counter;
    }

    get current()
    {
        return this.#str[this.#counter];
    }

    at(idx)
    {
        return this.#str[this.#counter + idx];
    }

    slice(from, to)
    {
        return this.#str.slice(this.#counter + from, this.#counter + to);
    }

    next()
    {
        this.#counter++;
    }

    move(cnt)
    {
        this.#counter += cnt;
    }

    reset()
    {
        this.#counter = 0;
    }

    get end()
    {
        return this.#counter >= this.#str.length;
    }

    end_at(cnt)
    {
        return this.#counter + cnt >= this.#str.length;
    }

    remove_spaces()
    {
        this.#str = this.#str.replaceAll(/\s/gi, "");
    }

    startswith() 
    {
        for (let i = 0; i < arguments.length; i++)
        {
            if (arguments[i] == this.slice(0, arguments[i].length))
                return true;
        }

        return false;
    }
}

export default Stream;
