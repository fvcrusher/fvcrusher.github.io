class Stream
{
    #str = null;
    #counter = 0;

    constructor(str)
    {
        if (!(typeof str === "string"))
            throw new Error(`string expected, but ${typeof str} given`);

        this.#str = str;
        this.#counter = 0;
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

    get left_str()
    {
        return this.#str.slice(this.#counter, this.#str.length);
    }
}

export default Stream;
