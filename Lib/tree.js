class TreeNode
{
    #data = null;
    false_branch = null;
    true_branch = null;
    #id = 0;
    static #counter = 0;

    get id()
    {
        return this.#id;
    }

    get data()
    {
        return this.#data;
    }

    constructor(data)
    {
        this.#id = TreeNode.#counter++;
        this.#data = data;
    }

    get leafs_count()
    {
        if (this.true_branch == null && this.false_branch == null)
            return 1;

        else
            return this.true_branch.leafs_count + this.false_branch.leafs_count;
    }

    static #max(a, b)
    {
        return (a > b) ? a : b;
    }

    get max_depth()
    {
        if (this.true_branch == null && this.false_branch == null)
            return 1;

        else
            return TreeNode.#max(this.true_branch.max_depth, this.false_branch.max_depth) + 1;
    }

    get leafs()
    {
        if (this.true_branch == null && this.false_branch == null)
            return [this.data];

        else
            return this.false_branch.leafs.concat(this.true_branch.leafs);
    }
}

export default TreeNode;
