abstract type AbstractStarAlgebra end

struct StarAlgebra{O,T,M<:MultiplicativeStructure,B<:AbstractBasis{T}} <:
       AbstractStarAlgebra
    object::O
    mstructure::M
    basis::B

    function StarAlgebra(obj, basis::AbstractBasis, mstr::MultiplicativeStructure)
        O = typeof(obj)
        T = eltype(basis)
        M = typeof(mstr)
        B = typeof(basis)

        return new{O,T,M,B}(obj, mstr, basis)
    end

    function StarAlgebra(obj, mstr::MultiplicativeStructure)
        O = typeof(obj)
        T = Symbol
        M = typeof(mstr)
        B = Basis{T,Int}

        return new{O,T,M,B}(obj, mstr)
    end
end

# TrivialMStructure:
StarAlgebra(obj, basis::AbstractBasis) = StarAlgebra{false}(obj, basis)

function StarAlgebra{Tw}(obj, basis::AbstractBasis) where {Tw}
    mstr = TrivialMStructure{Tw}(basis)
    return StarAlgebra(obj, basis, mstr)
end

# CachedMStructure:
StarAlgebra(obj, basis::AbstractBasis, cache_size::Tuple{<:Integer,Integer}) =
    StarAlgebra{false}(obj, basis, cache_size)

function StarAlgebra{Tw}(
    obj,
    basis::AbstractBasis,
    cache_size::Tuple{<:Integer,Integer},
) where {Tw}
    mstr = CachedMTable{Tw}(basis, table_size = cache_size)
    return StarAlgebra(obj, basis, mstr)
end

hasbasis(A::StarAlgebra) = isdefined(A, :basis)

basis(A::StarAlgebra) = A.basis
object(A::StarAlgebra) = A.object
# Base.eltype(A::StarAlgebra{O,B}) where {O,B} = eltype(B)


struct AlgebraElement{A,T,V<:AbstractVector{T}}
    coeffs::V
    parent::A

    function AlgebraElement(coeffs::AbstractVector, A::AbstractStarAlgebra)
        if hasbasis(A)
            @assert length(coeffs) == length(basis(A))
        end
        return new{typeof(A),eltype(coeffs),typeof(coeffs)}(coeffs, A)
    end
end

coeffs(a::AlgebraElement) = a.coeffs
Base.parent(a::AlgebraElement) = a.parent
Base.eltype(a::AlgebraElement) = eltype(coeffs(a))


### constructing elements

function Base.zero(A::AbstractStarAlgebra, T = Int)
    if hasbasis(A)
        return AlgebraElement(spzeros(T, length(basis(A))), A)
    else
        return AlgebraElement(spzeros(T, maximum(A.mstructure)))
    end
end

Base.one(A::AbstractStarAlgebra, T = Int) = A(one(object(A)), T)

Base.zero(a::AlgebraElement) = zero(parent(a))
Base.one(a::AlgebraElement) = one(parent(a))

Base.iszero(a::AlgebraElement) = iszero(coeffs(a))

function Base.isone(a::AlgebraElement, T = Int)
    b = basis(parent(a))
    k = findfirst(!iszero, coeffs(a))
    k === nothing && return false
    isone(a[k]) || return false
    return isone(b[k])
end

function (A::AbstractStarAlgebra)(elt, T = Int)
    if hasbasis(A)
        b = basis(A)
        i = b[elt]
        return AlgebraElement(sparsevec([i], [one(T)], length(b)), A)
    else
        throw("Cannot coerce $elt to an algebra without defined basis")
    end
end

function (A::AbstractStarAlgebra)(x::Number)
    g = one(object(A))
    res = A(g, typeof(x))
    res = mul!(res, res, x)
    return res
end

Base.similar(X::AlgebraElement, ::Type{T} = eltype(X)) where {T} =
    AlgebraElement(similar(coeffs(X), T), parent(X))
