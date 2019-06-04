__precompile__()
module GroupRings

using AbstractAlgebra
import AbstractAlgebra: Group, GroupElem, Ring, RingElem, parent, elem_type, parent_type, addeq!, mul!

using SparseArrays
using LinearAlgebra
using Markdown

import Base: convert, show, hash, ==, +, -, *, ^, //, /, length, getindex, setindex!, eltype, one, zero

export GroupRing, GroupRingElem, complete!, create_pm, star, aug, supp

###############################################################################
#
#   Basic manipulation && Array protocol
#
###############################################################################

function hash(X::GroupRingElem, h::UInt)
   return hash(X.coeffs, hash(parent(X), hash(GroupRingElem, h)))
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
   if !(g in keys(RG.basis_dict))
      g = (RG.group)(g)
   end
   X.coeffs[RG.basis_dict[g]] = value
end

Base.size(X::GroupRingElem) = size(X.coeffs)
Base.IndexStyle(::Type{GroupRingElem}) = Base.LinearFast()

dense(X::GroupRingElem{T, A}) where {T, A<:DenseVector} = X

function dense(X::GroupRingElem{T, Sp}) where {T, Sp<:SparseVector}
   return parent(X)(Vector(X.coeffs))
end

SparseArrays.sparse(X::GroupRingElem{T, Sp}) where {T, Sp<:SparseVector} = X

function SparseArrays.sparse(X::GroupRingElem{T, A}) where {T, A<:Vector}
   return parent(X)(sparse(X.coeffs))
end

###############################################################################
#
#   String I/O
#
###############################################################################

function show(io::IO, A::GroupRing)
   print(io, "Group Ring of $(A.group)")
end

function show(io::IO, X::GroupRingElem)
   RG = parent(X)
   T = eltype(X.coeffs)
   if X.coeffs == zero(X.coeffs)
      print(io, "$(zero(T))*$((RG.group)())")
   elseif isdefined(RG, :basis)
      non_zeros = ((X.coeffs[i], RG.basis[i]) for i in findall(!iszero, X.coeffs))
      elts = String[]
      for (c,g) in non_zeros
      	  sgn = (sign(c)>=0 ? " + " : " - ")
	  if c == T(1)
	      coeff = ""
	  else
	      coeff = "$(abs(c))"
	  end
	  push!(elts, sgn*coeff*"$(g)")
      end
      str = join(elts, "")
      if sign(first(non_zeros)[1]) > 0
         str = str[4:end]
      end
      print(io, str)
   else
      @warn("Basis of the parent Group is not defined, showing coeffs")
      show(io, MIME("text/plain"), X.coeffs)
   end
end

###############################################################################
#
#   Comparison
#
###############################################################################

function (==)(X::GroupRingElem, Y::GroupRingElem)
   if eltype(X.coeffs) != eltype(Y.coeffs)
      @warn("Comparing elements with different coeffs Rings!")
   end
   suppX = supp(X)
   suppX == supp(Y) || return false

   for g in suppX
      X[g] == Y[g] || return false
   end

   return true
end

function (==)(A::GroupRing, B::GroupRing)
   A.group == B.group || return false
   if isdefined(A, :basis) && isdefined(B, :basis)
      A.basis == B.basis || return false
   elseif isdefined(A, :pm) && isdefined(B, :pm)
      A.pm == B.pm || return false
   end
   return true
end


###############################################################################
#
#   *-involution
#
###############################################################################

function star(X::GroupRingElem{T}) where T
   RG = parent(X)
   isdefined(RG, :basis) || throw("*-involution without basis is not possible")
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

length(X::GroupRingElem) = count(!iszero, X.coeffs)

LinearAlgebra.norm(X::GroupRingElem, p::Int=2) = norm(X.coeffs, p)

aug(X::GroupRingElem) = sum(X.coeffs)

supp(X::GroupRingElem) = parent(X).basis[findall(!iszero, X.coeffs)]

function reverse_dict(::Type{I}, iter) where I<:Integer
   length(iter) > typemax(I) && error("Can not produce reverse dict: $(length(iter)) is too large for $T")
   return Dict{eltype(iter), I}(x => i for (i,x) in enumerate(iter))
end

reverse_dict(iter) = reverse_dict(Int, iter)

function create_pm(basis::Vector{T}, basis_dict::Dict{T, Int},
   limit::Int=length(basis); twisted::Bool=false, check=true) where {T<:GroupElem}
   product_matrix = zeros(Int, (limit,limit))
   Threads.@threads for i in 1:limit
      x = basis[i]
      if twisted
         x = inv(x)
      end
      for j in 1:limit
         product_matrix[i,j] = basis_dict[x*basis[j]]
      end
   end

   check && check_pm(product_matrix, basis, twisted)

   return product_matrix
end

create_pm(b::Vector{T}) where {T<:GroupElem} = create_pm(b, reverse_dict(b))

function check_pm(product_matrix, basis, twisted=false)
   idx = findfirst(product_matrix' .== 0)
   if idx != nothing
      @warn("Product is not supported on basis")
      i,j = Tuple(idx)
      x = basis[i]
      if twisted
         x = inv(x)
      end
      throw(KeyError(x*basis[j]))
   end
   return true
end

function complete!(RG::GroupRing)
   isdefined(RG, :basis) || throw(ArgumentError("Provide basis for completion first!"))
   if !isdefined(RG, :pm) 
      initializepm!(RG, fill=false)
      return RG
   end

   warning = false
   for idx in findall(RG.pm .== 0)
      i,j = Tuple(idx)
      g = RG.basis[i]*RG.basis[j]
      if haskey(RG.basis_dict, g)
          RG.pm[i,j] = RG.basis_dict[g]
      else
         if !warning
            warning = true
         end
      end
   end
   warning && @warn("Some products were not supported on basis")
   return RG
end

function initializepm!(RG::GroupRing; fill::Bool=false)
   isdefined(RG, :basis) || throw("For baseless Group Rings You need to provide pm.")
   isdefined(RG, :pm) && return RG
   if fill
      RG.pm = try
         create_pm(RG.basis, RG.basis_dict)
      catch err
         isa(err, KeyError) && throw("Product is not supported on basis, $err.")
         throw(err)
      end
   else
      RG.pm = zeros(Int, length(RG.basis), length(RG.basis))
   end
   return RG
end

end # of module GroupRings
