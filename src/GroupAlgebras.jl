module GroupAlgebras

using Nemo
import Nemo: Group, GroupElem, Ring

import Base: convert, show, isequal, ==
import Base: +, -, *, //
import Base: size, length, norm, rationalize


type GroupRing <: Ring
   group::Group
   pm::Array{Int,2}
   basis::Vector{GroupElem}
   basis_dict::Dict{GroupElem, Int}

   GroupRing(G::Group) = new(G)
end

type GroupRingElem{T<:Number}
   coeffs::AbstractVector{T}
   parent::GroupRing

   function GroupRingElem(coeffs::AbstractVector)
      return new(coeffs)
   end
end

export GroupRing, GroupRingElem


show{T}(io::IO, X::GroupAlgebraElement{T}) = print(io,
    "Element of Group Algebra over $T of length $(length(X)):\n $(X.coefficients)")


GroupRingElem{T}(c::AbstractVector{T}, A::GroupRing) = GroupRingElem{T}(c,A)

convert{T<:Number}(::Type{T}, X::GroupRingElem) =
   GroupRingElem(parent(X), convert(AbstractVector{T}, X.coeffs))

function GroupRing(G::Group, pm::Array{Int,2})
   size(pm,1) == size(pm,2) || throw("pm must be of size (n,n), got
      $(size(pm))")
   return GroupRing(Group, pm)
end

function GroupRing(G::Group, pm::Array{Int,2}, basis::Vector)
   size(pm,1) == size(pm,2) || throw("pm must be of size (n,n), got
      $(size(pm))")
   eltype(basis) == elem_type(G) || throw("basis must consist of elements of $G")
   basis_dict = Dict(g => i for (i,g) in enumerate(basis))
   return GroupRing(Group, pm, basis, basis_dict)
end

function GroupRing(G::Group; complete=false)
   A = GroupRing(Group)
   if complete
      complete(A)
   end
   return A
end
end

(==)(X::GroupAlgebraElement, Y::GroupAlgebraElement) = isequal(X,Y)

function add{T<:Number}(X::GroupAlgebraElement{T}, Y::GroupAlgebraElement{T})
    X.product_matrix == Y.product_matrix || throw(ArgumentError(
    "Elements don't seem to belong to the same Group Algebra!"))
    return GroupAlgebraElement(X.coefficients+Y.coefficients, X.product_matrix)
end

function add{T<:Number, S<:Number}(X::GroupAlgebraElement{T},
    Y::GroupAlgebraElement{S})
    warn("Adding elements with different base rings!")
    return GroupAlgebraElement(+(promote(X.coefficients, Y.coefficients)...),
    X.product_matrix)
end

(+)(X::GroupAlgebraElement, Y::GroupAlgebraElement) = add(X,Y)
(-)(X::GroupAlgebraElement) = GroupAlgebraElement(-X.coefficients, X.product_matrix)
(-)(X::GroupAlgebraElement, Y::GroupAlgebraElement) = add(X,-Y)

function algebra_multiplication{T<:Number}(X::AbstractVector{T}, Y::AbstractVector{T}, pm::Array{Int,2})
    result = zeros(X)
    for (j,y) in enumerate(Y)
        if y != zero(T)
            for (i, index) in enumerate(pm[:,j])
                if X[i] != zero(T)
                    index == 0 && throw(ArgumentError("The product don't seem to belong to the span of basis!"))
                    result[index] += X[i]*y
                end
            end
        end
    end
    return result
end

function group_star_multiplication{T<:Number}(X::GroupAlgebraElement{T},
    Y::GroupAlgebraElement{T})
    X.product_matrix == Y.product_matrix || ArgumentError(
    "Elements don't seem to belong to the same Group Algebra!")
    result = algebra_multiplication(X.coefficients, Y.coefficients, X.product_matrix)
    return GroupAlgebraElement(result, X.product_matrix)
end

function group_star_multiplication{T<:Number, S<:Number}(
    X::GroupAlgebraElement{T},
    Y::GroupAlgebraElement{S})
    S == T || warn("Multiplying elements with different base rings!")
    return group_star_multiplication(promote(X,Y)...)
end

(*){T<:Number, S<:Number}(X::GroupAlgebraElement{T},
    Y::GroupAlgebraElement{S}) = group_star_multiplication(X,Y);

(*){T<:Number}(a::T, X::GroupAlgebraElement{T}) = GroupAlgebraElement(
    a*X.coefficients, X.product_matrix)

function scalar_multiplication{T<:Number, S<:Number}(a::T,
    X::GroupAlgebraElement{S})
    promote_type(T,S) == S || warn("Scalar and coefficients are in different rings! Promoting result to $(promote_type(T,S))")
    return GroupAlgebraElement(a*X.coefficients, X.product_matrix)
end

(*){T<:Number}(a::T,X::GroupAlgebraElement) = scalar_multiplication(a, X)

//{T<:Rational, S<:Rational}(X::GroupAlgebraElement{T}, a::S) =
    GroupAlgebraElement(X.coefficients//a, X.product_matrix)

//{T<:Rational, S<:Integer}(X::GroupAlgebraElement{T}, a::S) =
    X//convert(T,a)

length(X::GroupAlgebraElement) = length(X.coefficients)
size(X::GroupAlgebraElement) = size(X.coefficients)

function norm(X::GroupAlgebraElement, p=2)
    if p == 1
        return sum(abs(X.coefficients))
    elseif p == Inf
        return max(abs(X.coefficients))
    else
        return norm(X.coefficients, p)
    end
end

ɛ(X::GroupAlgebraElement) = sum(X.coefficients)

function rationalize{T<:Integer, S<:Number}(
    ::Type{T}, X::GroupAlgebraElement{S}; tol=eps(S))
    v = rationalize(T, X.coefficients, tol=tol)
    return GroupAlgebraElement(v, X.product_matrix)
end

end
