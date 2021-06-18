abstract type AbstractMTable{I,Tw} <: MultiplicativeStructure{Tw,I} end

Base.size(mt::AbstractMTable) = size(mt.table)

_check(mt::AbstractMTable) = check(mt.table, basis(mt), _istwisted(mt))

function _check(product_matrix, basis, twisted::Bool)
    idx = findfirst(iszero, product_matrix)
    if idx != nothing
        i, j = Tuple(idx)
        x = (twisted ? star(basis[i]) : basis[i])
        throw(ProductNotDefined(i, j, "$x · $(basis[j]) =
        $(_product(Val(twisted), x, basis[j]))"))
    end
    return true
end

_iscached(mt::AbstractMTable, i, j) = !iszero(mt.table[i, j])


## MTables

struct MTable{I,Twisted,M<:AbstractMatrix{I}} <: AbstractMTable{I,Twisted}
    table::M
end

MTable{Tw}(mt::AbstractMatrix{<:Integer}) where {Tw} = MTable{eltype(mt),Tw,typeof(mt)}(mt)

MTable(b::AbstractBasis; table_size) = MTable{false}(b; table_size = table_size)

function MTable{Tw}(basis::AbstractBasis; table_size) where {Tw}
    @assert length(table_size) == 2
    @assert 1 <= first(table_size) <= length(basis)
    @assert 1 <= last(table_size) <= length(basis)

    table = zeros(SparseArrays.indtype(basis), table_size)

    complete!(table, basis, Val(Tw))

    _check(table, basis, Tw)

    return MTable{Tw}(table)
end

function complete!(table, basis, ::Val{false})
    Threads.@threads for j in 1:size(table, 2)
        y = basis[j]
        for i in 1:size(table, 1)
            table[i, j] = basis[_product(Val(false), basis[i] ,y)]
        end
    end
    return table
end

function complete!(table, basis, ::Val{true})
    Threads.@threads for i in 1:size(table, 1)
        x = star(basis[i])
        for j in 1:size(table, 2)
            # star(x)*y
            table[i, j] = basis[_product(Val(false), x, basis[j])]
        end
    end
    return table
end

basis(mt::MTable) = throw("No basis is defined for a simple $(typeof(mt))")

Base.@propagate_inbounds function Base.getindex(m::MTable, i::Integer, j::Integer)
    @boundscheck checkbounds(m, i, j)
    @boundscheck iszero(m.table[i, j]) && throw(ProductNotDefined(i, j))
    return m.table[i, j]
end

