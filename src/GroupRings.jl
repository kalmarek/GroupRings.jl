module GroupRings

using Nemo
import Nemo: Group, GroupElem, Ring, RingElem, parent, elem_type, parent_type

import Base: convert, show, hash, ==, +, -, *, //, /, length, norm, rationalize, deepcopy_internal, getindex, setindex!, eltype, one

###############################################################################
#
#   GroupRings / GroupRingsElem
#
###############################################################################

type GroupRing <: Ring
   group::Group
   basis::Vector{GroupElem}
   basis_dict::Dict{GroupElem, Int}
   pm::Array{Int,2}

   function GroupRing(G::Group; full=false)
      A = new(G)
      if full
         complete(A)
      end
      return A
   end

   function GroupRing(G::Group, basis, basis_dict, pm::Array{Int,2})
      return new(G, basis, basis_dict, pm)
   end
end

type GroupRingElem{T<:Number} <: RingElem
   coeffs::AbstractVector{T}
   parent::GroupRing

   function GroupRingElem(c::AbstractVector{T}, RG::GroupRing, check=true)
      if check
         isdefined(RG, :basis) || complete(RG)
         length(c) == length(RG.basis) || throw("Can't create GroupRingElem -- lengths differ: length(c) = $(length(c)) != $(length(RG.basis)) = length(RG.basis)")
      end
      return new(c, RG)
   end
end

export GroupRing, GroupRingElem, complete, create_pm

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type(::GroupRing) = GroupRingElem

parent_type{T}(::GroupRingElem{T}) = GroupRing

parent{T}(g::GroupRingElem{T}) = g.parent

###############################################################################
#
#   GroupRing / GroupRingElem constructors
#
###############################################################################

function GroupRingElem{T<:Number}(c::AbstractVector{T}, RG::GroupRing)
   return GroupRingElem{T}(c, RG)
end

function convert{T<:Number}(::Type{T}, X::GroupRingElem)
   return GroupRingElem(convert(AbstractVector{T}, X.coeffs), parent(X))
end

function GroupRing(G::Group, pm::Array{Int,2})
   size(pm,1) == size(pm,2) || throw("pm must be square, got $(size(pm))")
   return GroupRing(G, pm)
end

function GroupRing(G::Group, basis::Vector)
   basis_dict = reverse_dict(basis)
   pm = try
      create_pm(basis, basis_dict)
   catch err
      isa(err, KeyError) && throw("Products are not supported on basis")
      throw(err)
   end
   return GroupRing(G, basis, basis_dict, pm)
end

function GroupRing(G::Group, basis::Vector, pm::Array{Int,2})
   size(pm,1) == size(pm,2) || throw("pm must be of size (n,n), got
      $(size(pm))")
   eltype(basis) == elem_type(G) || throw("basis must consist of elements of $G")
   basis_dict = reverse_dict(basis)
   return GroupRing(G, basis, basis_dict, pm)
end

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

function (RG::GroupRing)(T::Type=Int)
   isdefined(RG, :basis) || throw("Complete the definition of GroupRing first")
   return GroupRingElem(spzeros(T,length(RG.basis)), RG)
end

function (RG::GroupRing)(g::GroupElem, T::Type=Int)
   typeof(g) == elem_type(RG.group) || throw("$g does not belong to $(RG.group), the underlying group of $RG")
   g = try
      RG.group(g)
   catch
      throw("Can't coerce $g to the underlying group of $RG")
   end
   result = RG(T)
   result[g] = one(T)
   return result
end

function (RG::GroupRing)(x::AbstractVector)
   length(x) == length(RG.basis) || throw("Can not coerce to $RG: lengths differ")
   result = RG(eltype(x))
   result.coeffs = x
   return result
end

(RG::GroupRing)(X::GroupRingElem) = RG(X.coeffs)

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

function getindex(X::GroupRingElem, n::Int)
   return X.coeffs[n]
end

function getindex(X::GroupRingElem, g::GroupElem)
   return X.coeffs[parent(X).basis_dict[g]]
end

function setindex!(X::GroupRingElem, value, n::Int)
   X.coeffs[n] = value
end

function setindex!(X::GroupRingElem, value, g::GroupElem)
   RG = parent(X)
   typeof(g) == elem_type(RG.group) || throw("$g is not an element of $(RG.group)")
   g = (RG.group)(g)
   X.coeffs[RG.basis_dict[g]] = value
end

eltype(X::GroupRingElem) = eltype(X.coeffs)

one(RG::GroupRing) = RG(RG.group())

function generators(RG::GroupRing)
   S = generators(RG.group)
   S = unique([S..., [inv(s) for s in S]...])
   return [RG(s) for s in S]
end

###############################################################################
#
#   String I/O
#
###############################################################################

function show(io::IO, A::GroupRing)
   print(io, "Group Ring of [$(A.group)]")
end

function show(io::IO, X::GroupRingElem)
   T = eltype(X.coeffs)
   RG = parent(X)
   if X == RG(T)
      print(io, "$(zero(T))*$((RG.group)())")
   else
      elts = ("$(X[i])*$(RG.basis[i])" for i in 1:length(RG.basis) if X[i] != zero(T))
      join(io, elts, " + ")
   end
end

###############################################################################
#
#   Comparison
#
###############################################################################

function (==)(X::GroupRingElem, Y::GroupRingElem)
   parent(X) == parent(Y) || return false
   if eltype(X.coeffs) != eltype(Y.coeffs)
      warn("Comparing elements with different coeffs Rings!")
   end
   all(X.coeffs .== Y.coeffs) || return false
   return true
end

function (==)(A::GroupRing, B::GroupRing)
   A.group == B.group || return false
   A.basis == B.basis || return false
   return true
end

###############################################################################
#
#   Scalar operators
#
###############################################################################

(-)(X::GroupRingElem) = GroupRingElem(-X.coeffs, parent(X))

(*){T<:Number}(a::T, X::GroupRingElem{T}) = GroupRingElem(a*X.coeffs, parent(X))

function scalar_mult{T<:Number, S<:Number}(a::T, X::GroupRingElem{S})
   promote_type(T,S) == S || warn("Scalar and coeffs are in different rings! Promoting result to $(promote_type(T,S))")
   return GroupRingElem(a*X.coeffs, parent(X))
end

(*)(a, X::GroupRingElem) = scalar_mult(a, X)
(*)(X::GroupRingElem, a) = a*X

# disallow Nemo.Rings to hijack *(::Integer, ::RingElem)
(*){T<:Integer}(a::T, X::GroupRingElem) = scalar_mult(a, X)

(/)(X::GroupRingElem, a) = scalar_mult(1/a, X)

function (//){T<:Integer, S<:Integer}(X::GroupRingElem{T}, a::S)
   U = typeof(X[1]//a)
   warn("Rational division: promoting result to $U")
   return convert(U, X)//a
end

(//){T<:Rational, S<:Rational}(X::GroupRingElem{T}, a::S) =
   GroupRingElem(X.coeffs//a, parent(X))

(//){T<:Rational, S<:Integer}(X::GroupRingElem{T}, a::S) = X//convert(T,a)

###############################################################################
#
#   Binary operators
#
###############################################################################

function add{T<:Number}(X::GroupRingElem{T}, Y::GroupRingElem{T})
   parent(X) == parent(Y) || throw(ArgumentError(
   "Elements don't seem to belong to the same Group Ring!"))
   return GroupRingElem(X.coeffs+Y.coeffs, parent(X))
end

function add{T<:Number, S<:Number}(X::GroupRingElem{T},
   Y::GroupRingElem{S})
   parent(X) == parent(Y) || throw(ArgumentError(
   "Elements don't seem to belong to the same Group Ring!"))
   warn("Adding elements with different base rings!")
   return GroupRingElem(+(promote(X.coeffs, Y.coeffs)...), parent(X))
end

(+)(X::GroupRingElem, Y::GroupRingElem) = add(X,Y)
(-)(X::GroupRingElem, Y::GroupRingElem) = add(X,-Y)

function groupring_mult!(X,Y,pm,result)
   for (j,y) in enumerate(Y)
      if y != zero(eltype(Y))
         for (i, index) in enumerate(pm[:,j])
            if X[i] != zero(eltype(X))
               index == 0 && throw(ArgumentError("The product don't seem to belong to the span of basis!"))
               result[index] += X[i]*y
            end
         end
      end
   end
end

function groupring_mult{T<:Number}(X::AbstractVector{T}, Y::AbstractVector{T},
   pm::Array{Int,2})
   result = zeros(X)
   groupring_mult!(X,Y,pm,result)
   return result
end

function groupring_mult(X::AbstractVector, Y::AbstractVector, pm::Array{Int,2})
   T = promote_type(eltype(X), eltype(Y))
   result = zeros(T, deepcopy(X))
   groupring_mult!(X, Y, pm, result)
   return result
end

function groupring_mult{T<:Number}(X::GroupRingElem{T}, Y::GroupRingElem{T})
   parent(X) == parent(Y) || throw(ArgumentError(
   "Elements don't seem to belong to the same Group Ring!"))
   RG = parent(X)
   isdefined(RG, :pm) || complete(RG)
   result = groupring_mult(X.coeffs, Y.coeffs, RG.pm)
   return GroupRingElem(result, RG)
end

function groupring_mult{T<:Number, S<:Number}(X::GroupRingElem{T},
      Y::GroupRingElem{S})
   parent(X) == parent(Y) || throw("Elements don't seem to belong to the same
   Group Ring!")
   warn("Multiplying elements with different base rings!")
   RG = parent(X)
   isdefined(RG, :pm) || complete(RG)
   result = groupring_mult(X.coeffs, Y.coeffs, RG.pm)
   return GroupRingElem(result, RG)
end

(*)(X::GroupRingElem, Y::GroupRingElem) = groupring_mult(X,Y)

###############################################################################
#
#   *-involution
#
###############################################################################

function star{T}(X::GroupRingElem{T})
   RG = parent(X)
   isdefined(RG, :basis) || complete(RG)
   result = RG(T)
   for (i,c) in enumerate(X.coeffs)
      if c != zero(T)
         g = inv(RG.basis[i])
         result[g] = c
      end
   end
   return result
end

###############################################################################
#
#   Misc
#
###############################################################################

length(X::GroupRingElem) = countnz(X.coeffs)

norm(X::GroupRingElem, p=2) = norm(X.coeffs, p)

augmentation(X::GroupRingElem) = sum(X.coeffs)

function rationalize{T<:Integer, S<:Number}(::Type{T}, X::GroupRingElem{S};
   tol=eps(S))
   v = rationalize(T, X.coeffs, tol=tol)
   return GroupRingElem(v, parent(X))
end

function reverse_dict(iter)
   T = eltype(iter)
   return Dict{T, Int}(x => i for (i,x) in enumerate(iter))
end

function create_pm{T<:GroupElem}(basis::Vector{T}, basis_dict::Dict{T, Int},
   limit=length(basis); twisted=false)
   product_matrix = zeros(Int, (limit,limit))
   for i in 1:limit
      x = basis[i]
      if twisted
         x = inv(x)
      end
      for j in 1:limit
         w = x*(basis[j])
         product_matrix[i,j] = basis_dict[w]
      end
   end
   return product_matrix
end

create_pm{T<:GroupElem}(b::Vector{T}) = create_pm(b, reverse_dict(b))

function complete(A::GroupRing)
   if !isdefined(A, :basis)
      A.basis = collect(elements(A.group))
   end
   if !isdefined(A, :basis_dict)
      A.basis_dict = reverse_dict(A.basis)
   end
   if !isdefined(A, :pm)
      A.pm = try
         create_pm(A.basis, A.basis_dict)
      catch err
         isa(err, KeyError) && throw("Product is not supported on basis")
         throw(err)
      end
   end
   return A
end

end # of module GroupRings
