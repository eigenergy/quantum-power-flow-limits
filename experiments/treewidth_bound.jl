using LinearAlgebra
using SparseArrays

if length(ARGS) != 3
    println(stderr, "usage: treewidth_bound.jl <n> <edge-list> <output>")
    exit(2)
end

n = parse(Int, ARGS[1])
edge_path = ARGS[2]
output_path = ARGS[3]

rows = Int[]
cols = Int[]
degree = zeros(Float64, n)

for line in eachline(edge_path)
    fields = split(line)
    length(fields) == 2 || error("invalid edge line: $line")
    u = parse(Int, fields[1]) + 1
    v = parse(Int, fields[2]) + 1
    1 <= u <= n || error("edge endpoint out of range")
    1 <= v <= n || error("edge endpoint out of range")
    u == v && continue
    push!(rows, u)
    push!(cols, v)
    push!(rows, v)
    push!(cols, u)
    degree[u] += 1.0
    degree[v] += 1.0
end

offdiag = sparse(rows, cols, fill(-1.0, length(rows)), n, n)
matrix = offdiag + spdiagm(0 => degree .+ 1.0)
factor = cholesky(Symmetric(matrix); check=true)
used_ordering = factor.p
lower = sparse(factor.L)
row_indices = rowvals(lower)

open(output_path, "w") do io
    println(io, "order ", join(used_ordering .- 1, " "))
    for column in 1:n
        bag = Int[]
        for pointer in nzrange(lower, column)
            push!(bag, used_ordering[row_indices[pointer]] - 1)
        end
        println(io, "bag ", join(bag, " "))
    end
end
