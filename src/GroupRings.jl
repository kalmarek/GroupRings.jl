module GroupRings

using Nemo
import Nemo: Group, GroupElem, Ring, parent, elem_type, parent_type

import Base: convert, show, hash, ==, +, -, *, //, /, length, norm, rationalize, deepcopy_internal

###############################################################################
#
#   GroupRings / GroupRingsElem
#
###############################################################################

type GroupRing <: Ring
   group::Group
   pm::Array{Int,2}
   basis::Vector{GroupElem}
   basis_dict::Dict{GroupElem, Int}

   function GroupRing(G::Group; full=false)
      A = new(G)
      if full
         complete(A)
      end
      return A
   end
end

abstract AbstractGroupRingElem

type GroupRingElem{T<:Number} <: AbstractGroupRingElem
   coeffs::AbstractVector{T}
   parent::GroupRing

   function GroupRingElem(coeffs::AbstractVector)
      return new(coeffs)
   end
end

export GroupRing, GroupRingElem

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type(::GroupRing) = GroupRingElem

parent_type(::GroupRingElem) = GroupRing

parent(g::GroupRingElem) = g.parent

###############################################################################
#
#   GroupRing / GroupRingElem constructors
#
###############################################################################

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

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

function (A::GroupRing)(X::GroupRingElem)
   length(X) == length(A.basis) || throw("Can not coerce to $A: lengths differ")
   X.parent = A
   return X
end

function (A::GroupRing)(x::AbstractVector)
   length(x) == length(A.basis) || throw("Can not coerce to $A: lengths differ")
   return GroupRingElem(x, A)
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function deepcopy_internal(X::GroupRingElem, dict::ObjectIdDict)
   return GroupRingElem(deepcopy(X.coeffs), parent(X))
end

function hash(X::GroupRingElem, h::UInt)
   return hash(X.coeffs, hash(parent(X), h))
end

###############################################################################
#
#   String I/O
#
###############################################################################

function show(io::IO, A::GroupRing)
   print(io, "GroupRing of $(A.group)")
end

function show(io::IO, X::GroupRingElem)
   T = eltype(X.coeffs)
   print(io, "Element of Group Algebra of $(parent(X)) over $T:\n $(X.coeffs)")
end

###############################################################################
#
#   Comparison
#
###############################################################################

function (==)(X::GroupRingElem, Y::GroupRingElem)
   parent(X) == parent(Y) || return false
   if eltype(X.coeffs) != eltype(S.coeffs)
      warn("Comparing elements with different coeffs Rings!")
   end
   X.coeffs == Y.coeffs || return false
   return true
end

function (==)(A::GroupRing, B::GroupRing)
   return A.group == B.group
end

###############################################################################
#
#   Scalar operators
#
###############################################################################

(-)(X::GroupRingElem) = GroupRingElem(-X.coeffs, parent(X))

(*){T<:Number}(a::T, X::GroupRingElem{T}) = GroupRingElem(a*X.coeffs, parent(X))

function scalar_multiplication{T<:Number, S<:Number}(a::T,
   X::GroupRingElem{S})
   promote_type(T,S) == S || warn("Scalar and coeffs are in different rings! Promoting result to $(promote_type(T,S))")
      return GroupRingElem(a*X.coeffs, parent(X))
   end
end

(*){T<:Number}(a::T,X::GroupRingElem) = scalar_multiplication(a, X)

(/){T<:Number}(a::T, X::GroupRingElem) = scalar_multiplication(1/a, X)

(//){T<:Rational, S<:Rational}(X::GroupRingElem{T}, a::S) =
GroupRingElem(X.coeffs//a, parent(X))

(//){T<:Rational, S<:Integer}(X::GroupRingElem{T}, a::S) =
X//convert(T,a)

###############################################################################
#
#   Binary operators
#
###############################################################################

function add{T<:Number}(X::GroupRingElem{T}, Y::GroupRingElem{T})
   parent(X) == parent(Y) || throw(ArgumentError(
   "Elements don't seem to belong to the same Group Algebra!"))
   return GroupRingElem(X.coeffs+Y.coeffs, parent(X))
end

function add{T<:Number, S<:Number}(X::GroupRingElem{T},
   Y::GroupRingElem{S})
   parent(X) == parent(Y) || throw(ArgumentError(
   "Elements don't seem to belong to the same Group Algebra!"))
   warn("Adding elements with different base rings!")
   return GroupRingElem(+(promote(X.coeffs, Y.coeffs)...), parent(X))
end

(+)(X::GroupRingElem, Y::GroupRingElem) = add(X,Y)
(-)(X::GroupRingElem, Y::GroupRingElem) = add(X,-Y)

function algebra_multiplication{T<:Number}(X::AbstractVector{T},
   Y::AbstractVector{T}, pm::Array{Int,2})
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

function group_star_multiplication{T<:Number}(X::GroupRingElem{T},
   Y::GroupRingElem{T})
   parent(X) == parent(Y) || throw(ArgumentError(
   "Elements don't seem to belong to the same Group Algebra!"))
   result = algebra_multiplication(X.coeffs, Y.coeffs, X.pm)
   return GroupRingElem(result, parent(X))
end

function group_star_multiplication{T<:Number, S<:Number}(
   X::GroupRingElem{T}, Y::GroupRingElem{S})
   warn("Multiplying elements with different base rings!")
   return group_star_multiplication(promote(X,Y)...)
end

(*)(X::GroupRingElem, Y::GroupRingElem) = group_star_multiplication(X,Y)

###############################################################################
#
#   Misc
#
###############################################################################

length(X::GroupRingElem) = length(X.coeffs)

norm(X::GroupRingElem, p=2) = norm(X.coeffs, p)

augmentation(X::GroupRingElem) = sum(X.coeffs)

function rationalize{T<:Integer, S<:Number}(::Type{T}, X::GroupRingElem{S};
   tol=eps(S))
   v = rationalize(T, X.coeffs, tol=tol)
   return GroupRingElem(v, parent(X))
end

function reverse_dict(a::AbstractVector)
   return Dict{eltype(a), Int}(x => i for (i,x) in enumerate(a))
end

function create_pm{T<:GroupElem}(basis::Vector{T}, basis_dict::Dict{T, Int},
   limit; twisted=false)
   product_matrix = zeros(Int, (limit,limit))
   for i in 1:limit
      x = basis([i])
      if twisted
         x = inv(x)
      end
      for j in 1:limit
         w = x*basis[j]
         product_matrix[i,j] = basis_dict[w]
      end
   end
   return product_matrix
end

function complete(A::GroupRing)
   isdefined(A, :basis) || A.basis = collect(elements(A.group))
   isdefined(A, :basis_dict) || A.basis_dict = reverse_dict(A.basis)
   if !isdefined(A, :pm)
      A.pm = try
         create_pm(basis, basis_dict)
      catch err
         isa(err, KeyError) && throw("Product is not supported on basis!"))
         throw(err)
      end
   return A
end

function complete(X::GroupRingElem)
   isdefined(X, :parent) || throw("You have to define parent of X before!")
   complete(parent(X))
   return X
end

end # of module GroupRings
