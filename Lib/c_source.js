export class CSource
{
    #source_code = null;
    #clear_source_code = null;
    #function_name = null;

    static #remove_comments(source_code)
    {
        let resulting_code = "";
        for (let idx = 0; idx < source_code.length; idx++)
        {
            if (source_code.slice(idx).startsWith("//"))
            {
                while (idx < source_code.length && !(source_code[idx] == "\n"))
                    idx++;
            }

            else if (source_code.slice(idx).startsWith("/*"))
            {
                while (idx < source_code.length && !(source_code.slice(idx).startsWith("*/")))
                    idx++;
                idx += 2;
            }

            resulting_code += source_code[idx];
        }

        return resulting_code;
    }

    static #remove_voids(source_code)
    {
        let no_empty_lines = source_code.replace(/\n[\s]*\n/g, "\n").trim();
        return no_empty_lines;
    }

    static #format_source(source_code)
    {
        let without_comments = CSource.#remove_comments(source_code);
        let clear = CSource.#remove_voids(without_comments)
        return clear;
    }

    static #get_function_name(source_code)
    {
        let result = /(?:void|int|float|char|bool|signed|unsigned|short|long|double)(?: (?:void|int|float|char|bool|signed|unsigned|short|long|double))* (?<function_name>\w+?)\(/g.exec(source_code);
        if (result == null)
            return "";
        return result[1];
    }

    constructor(source_code)
    {
        this.#source_code = source_code;
        this.#clear_source_code = CSource.#format_source(source_code);
        this.#function_name = CSource.#get_function_name(this.clear_source_unformatted);
    }

    get source()
    {
        return this.#source_code;
    }

    get clear_source()
    {
        return this.#clear_source_code;
    }

    get clear_source_unformatted()
    {
        return this.#clear_source_code.replace(/\s+/g, " ").replace(/ ?([;,=+\-\{\}\[\]\(\)<>|&*!]) ?/g, "$1").trim();
    }

    get function_name()
    {
        return this.#function_name;
    }
}
