module GroupRings

using AbstractAlgebra
import AbstractAlgebra: Group, NCRing, NCRingElem, parent, elem_type, parent_type, addeq!, mul!

using SparseArrays
import LinearAlgebra

import Base: convert, show, hash, ==, +, -, *, ^, //, /, length, getindex, setindex!, eltype, one, zero

GroupOrNCRing = Union{AbstractAlgebra.Group, AbstractAlgebra.NCRing}
GroupOrNCRingElem = Union{AbstractAlgebra.GroupElem, AbstractAlgebra.NCRingElem}

###############################################################################
#
#   GroupRings / GroupRingsElem
#
###############################################################################

mutable struct GroupRing{Gr<:GroupOrNCRing, T<:GroupOrNCRingElem} <: NCRing
   group::Gr
   basis::Vector{T}
   basis_dict::Dict{T, Int}
   pm::Matrix{Int}

   function GroupRing(G::Gr, basis::Vector{T};
         cachedmul::Bool=false) where {Gr, T}
      RG = new{Gr, T}(G, basis, reverse_dict(basis))
      cachedmul && initializepm!(RG)
      return RG
   end

   function GroupRing(G::Gr, b::Vector{T}, b_d::Dict{T, Int}, pm::Array{Int,2}) where {Gr,T}
      return new{Gr, T}(G, b, b_d, pm)
   end

   function GroupRing(G::Gr, pm::Array{Int,2}) where {Gr}
      RG = new{Gr, elem_type(G)}(G)
      RG.pm = pm
      return RG
   end
end

mutable struct GroupRingElem{T, A<:AbstractVector, GR<:GroupRing} <: NCRingElem
   coeffs::A
   parent::GR

   function GroupRingElem{T, A, GR}(c::AbstractVector{T}, RG::GR, check=true) where {T, A, GR}
      if check
         if hasbasis(RG)
            length(c) == length(RG.basis) || throw(
            "Can't create GroupRingElem -- lengths differ: length(c) =
            $(length(c)) != $(length(RG.basis)) = length(RG.basis)")
         else
            # @warn("Basis of the GroupRing is not defined.")
         end
      end
      return new{T, A, GR}(c, RG)
   end
end

export GroupRing, GroupRingElem, complete!, create_pm, star, aug, supp

###############################################################################
#
#   GroupRing / GroupRingElem constructors
#
###############################################################################

function GroupRingElem(c::AbstractVector, RG::GroupRing)
   return GroupRingElem{eltype(c), typeof(c), typeof(RG)}(c, RG)
end

function GroupRing(G::Generic.SymmetricGroup; cachedmul::Bool=false)
   return GroupRing(G, vec(collect(G)), cachedmul=cachedmul)
end

function GroupRing(G::Group, basis::AbstractVector, pm::AbstractMatrix{<:Integer})
   size(pm,1) == size(pm,2) || throw("pm must be square, got $(size(pm))")
   eltype(basis) == elem_type(G) || throw("Basis must consist of elements of $G")
   return GroupRing(G, basis, reverse_dict(basis), pm)
end

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type(::Type{GroupRing}) = GroupRingElem

eltype(::Type{GroupRingElem{T, A, Gr}}) where {T, A, Gr} = T

parent(g::GroupRingElem) = g.parent

parent_type(X::GroupRingElem) = typeof(parent(X))

Base.promote_rule(::Type{GroupRingElem{T}}, ::Type{GroupRingElem{S}}) where {T,S} =
   GroupRingElem{promote_type(T,S)}

function convert(::Type{T}, X::GroupRingElem) where T<:Number
   return GroupRingElem(Vector{T}(X.coeffs), parent(X))
end

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

# sparse storage:

zero(RG::GroupRing, T::Type=Int) = RG(T)
one(RG::GroupRing, T::Type=Int) = RG(one(RG.group), T)
one(RG::GroupRing{<:AbstractAlgebra.NCRing}, T::Type=Int) = RG(one(RG.group), T)

function (RG::GroupRing)(T::Type=Int)
   hasbasis(RG) || throw("Can not coerce without basis of GroupRing")
   return GroupRingElem(spzeros(T,length(RG.basis)), RG)
end

function (RG::GroupRing)(i::Int, T::Type=Int)
   elt = RG(T)
   elt[one(RG.group)] = i
   return elt
end

function (RG::GroupRing{<:AbstractAlgebra.NCRing})(i::Int, T::Type=Int)
   elt = RG(T)
   elt[one(RG.group)] = i
   return elt
end

function (RG::GroupRing)(g::GroupOrNCRingElem, T::Type=Int)
   result = RG(T)
   result[RG.group(g)] = one(T)
   return result
end

function (RG::GroupRing{Gr,T})(V::Vector{T}, S::Type=Int) where {Gr, T}
   res = RG(S)
   for g in V
      res[g] += one(S)
    end
    return res
end

function (RG::GroupRing)(f::Function, X::GroupRingElem{T}) where T
   hasbasis(RG) || throw("Can not coerce without basis of GroupRing")
   res = RG(T)
   for g in supp(X)
      res[f(g)] = X[g]
   end
   return res
end

# keep storage type

function (RG::GroupRing)(x::AbstractVector{T}) where T
   hasbasis(RG) || throw("Basis of GroupRing not defined. For advanced use the direct constructor of GroupRingElem is provided.")
   length(x) == length(RG.basis) || throw("Can not coerce to $RG: lengths differ")
   return GroupRingElem(x, RG)
end

function (RG::GroupRing)(X::GroupRingElem)
   RG == parent(X) || throw("Can not coerce!")
   return RG(X.coeffs)
end

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

function getindex(X::GroupRingElem, g::GroupOrNCRingElem)
   return X.coeffs[parent(X).basis_dict[g]]
end

function setindex!(X::GroupRingElem, value, n::Int)
   X.coeffs[n] = value
end

function setindex!(X::GroupRingElem, value, g::GroupOrNCRingElem)
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
   return GroupRingElem(Vector(X.coeffs), parent(X))
end

SparseArrays.sparse(X::GroupRingElem{T, Sp}) where {T, Sp<:SparseVector} = X

function SparseArrays.sparse(X::GroupRingElem{T, A}) where {T, A<:Vector}
   return GroupRingElem(sparse(X.coeffs), parent(X))
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
      print(io, "$(zero(T))*$(one(RG.group))")
   elseif hasbasis(RG)
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
   suppX = supp(X)
   suppX == supp(Y) || return false

   for g in suppX
      X[g] == Y[g] || return false
   end

   return true
end

function (==)(A::GroupRing, B::GroupRing)
   A.group == B.group || return false
   if hasbasis(A) && hasbasis(B)
      A.basis == B.basis || return false
   elseif isdefined(A, :pm) && isdefined(B, :pm)
      A.pm == B.pm || return false
   end
   return true
end

hasbasis(A::GroupRing) = isdefined(A, :basis)

Base.deepcopy_internal(x::GroupRingElem, dict::IdDict) =
   GroupRingElem(deepcopy(x.coeffs), parent(x))

###############################################################################
#
#   Scalar operators
#
###############################################################################

(-)(X::GroupRingElem) = GroupRingElem(-X.coeffs, parent(X))

function mul!(a::T, X::GroupRingElem{T}) where T
   X.coeffs .*= a
   return X
end

_mul(a::Number, X::GroupRingElem) = GroupRingElem(a.*X.coeffs, parent(X))

Base.:*(a::Number, X::GroupRingElem) = _mul(a, X)
Base.:*(X::GroupRingElem, a::Number) = _mul(a, X)

# disallow Rings to hijack *(::, ::GroupRingElem)
*(a::Union{AbstractFloat, Integer, RingElem, Rational}, X::GroupRingElem) = _mul(a, X)

(/)(X::GroupRingElem, a) = 1/a*X
(//)(X::GroupRingElem, a::Union{Integer, Rational}) = 1//a*X

(^)(X::GroupRingElem, n::Integer) = Base.power_by_squaring(X, n)

###############################################################################
#
#   Binary operators
#
###############################################################################

function addeq!(X::GroupRingElem, Y::GroupRingElem)
   X.coeffs += Y.coeffs
   return X
end

Base.:+(X::GroupRingElem, Y::GroupRingElem) = addeq!(deepcopy(X), Y)
-(X::GroupRingElem, Y::GroupRingElem) where T = addeq!((-Y), X)

"""
    fmac!(result::AbstractVector{T},
              X::AbstractVector,
              Y::AbstractVector,
             pm::Array{Int,2}) where T
> Fused multiply-add for group ring coeffs using multiplication table `pm`.
> The result of X*Y in GroupRing is added in-place to `result`.
> Notes:
> * this method will silently produce false results if `X[k]` is non-zero for
> `k > size(pm,1)`.
> * This method will fail if any zeros (i.e. uninitialised entries) are present
> in `pm`.
> Use with extreme care!
"""

function fmac!(result::AbstractVector{T},
                   X::AbstractVector,
                   Y::AbstractVector,
                  pm::Array{Int,2}) where T
   z = zero(T)
   s1 = size(pm,1)
   s2 = size(pm,2)

   @inbounds for j in 1:s2
      if Y[j] != z
         for i in 1:s1
            if X[i] != z
               result[pm[i,j]] += X[i]*Y[j]
            end
         end
      end
   end
   return result
end

"""
    GRmul!(result::AbstractVector{T}, X::AbstractVector, Y::AbstractVector,
           pm::Matrix{<:Integer}) where T
> The most specialised multiplication for `X` and `Y` (intended for `coeffs` of
> `GroupRingElems`), using multiplication table `pm`.
> Notes:
> * this method will silently produce false results if `X[k]` is non-zero for
> `k > size(pm,1)`.
> * This method will fail if any zeros (i.e. uninitialised entries) are present
> in `pm`.
> Use with extreme care!
"""
function GRmul!(result::AbstractVector{T},
                   X::AbstractVector,
                   Y::AbstractVector,
                  pm::AbstractMatrix{<:Integer}) where T
   z = zero(T)
   result .= z

   return fmac!(result, X, Y, pm)
end

"""
    mul!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)
> In-place multiplication for `GroupRingElem`s `X` and `Y`.
> `mul!` will make use the initialised entries of `pm` attribute of
> `parent(X)::GroupRing` (if available), and will compute and store in `pm` the
> remaining products necessary to perform the multiplication.
> The method will fail with `KeyError` if product `X*Y` is not supported on
> `parent(X).basis`.
"""
function mul!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)
   if result === X
      result = deepcopy(result)
   end
   T = eltype(result.coeffs)
   z = zero(T)
   result.coeffs .= z

   RG = parent(X)

   lX = length(X.coeffs)
   lY = length(Y.coeffs)

   if isdefined(RG, :pm)
      s = size(RG.pm)
      k = findprev(!iszero, X.coeffs, lX)
      (k == nothing ? 0 : k) <= s[1] || throw("Element in X outside of support of parents product: $k $(RG.basis[k])")
      k = findprev(!iszero, Y.coeffs, lY)
      (k == nothing ? 0 : k) <= s[2] || throw("Element in Y outside of support of parents product")

      for j in 1:lY
         if Y.coeffs[j] != z
            for i in 1:lX
               if X.coeffs[i] != z
                  if RG.pm[i,j] == 0
                     RG.pm[i,j] = RG.basis_dict[RG.basis[i]*RG.basis[j]]
                  end
                  result.coeffs[RG.pm[i,j]] += X[i]*Y[j]
               end
            end
         end
      end
   else
      for j in 1:lY
         if Y.coeffs[j] != z
            for i in 1:lX
               if X.coeffs[i] != z
                  result[RG.basis[i]*RG.basis[j]] += X[i]*Y[j]
               end
            end
         end
      end
   end
   return result
end

function *(X::GroupRingElem{T}, Y::GroupRingElem{S}, check::Bool=true) where {T,S}
   if check
      parent(X) === parent(Y) || throw("Elements don't seem to belong to the same Group Ring!")
   end

   TT = promote_type(T,S)

   if hasbasis(parent(X))
      result = parent(X)(similar(X.coeffs, TT))
      result = mul!(result, X, Y)
   else
      result = similar(X.coeffs, TT)
      result = GRmul!(result, X.coeffs, Y.coeffs, parent(X).pm)
      result = GroupRingElem(result, parent(X))
   end
   return result
end

###############################################################################
#
#   *-involution
#
###############################################################################

function star(X::GroupRingElem{T}) where T
   RG = parent(X)
   hasbasis(RG) || throw("*-involution without basis is not possible")
   result = RG(T)
   for (i,c) in enumerate(X.coeffs)
      if c != zero(T)
         g = star(RG.basis[i])
         result[g] = c
      end
   end
   return result
end

star(g::GroupElem) = inv(g)
star(r::NCRingElem) = inv(r)

###############################################################################
#
#   Misc
#
###############################################################################

length(X::GroupRingElem) = count(!iszero, X.coeffs)

LinearAlgebra.norm(X::GroupRingElem, p::Int=2) = LinearAlgebra.norm(X.coeffs, p)

aug(X::GroupRingElem) = sum(X.coeffs)

supp(X::GroupRingElem) = parent(X).basis[findall(!iszero, X.coeffs)]

function reverse_dict(::Type{I}, iter) where I<:Integer
   length(iter) > typemax(I) && error("Can not produce reverse dict: $(length(iter)) is too large for $T")
   return Dict{eltype(iter), I}(x => i for (i,x) in enumerate(iter))
end

reverse_dict(iter) = reverse_dict(Int, iter)

function create_pm(basis::AbstractVector{T}, basis_dict::Dict{T, Int},
   limit::Int=length(basis); twisted::Bool=false, check=true) where T
   product_matrix = zeros(Int, (limit,limit))
   Threads.@threads for i in 1:limit
      x = basis[i]
      if twisted
         x = star(x)
      end
      for j in 1:limit
         product_matrix[i,j] = get(basis_dict, x*basis[j], 0)
      end
   end

   check && check_pm(product_matrix, basis, twisted)

   return product_matrix
end

create_pm(b::AbstractVector{<:GroupOrNCRingElem}) = create_pm(b, reverse_dict(b))

function check_pm(product_matrix, basis, twisted=false)
   idx = findfirst(product_matrix' .== 0)
   if idx != nothing
      @warn("Product is not supported on basis")
      i,j = Tuple(idx)
      x = (twisted ? star(basis[i]) : basis[i])
      throw(KeyError(x*basis[j]))
   end
   return true
end

function complete!(RG::GroupRing, twisted::Bool=false)
   hasbasis(RG) || throw(ArgumentError("Provide basis for completion first!"))
   if !isdefined(RG, :pm)
      initializepm!(RG, fill=false)
      return RG
   end

   warning = false
   for idx in findall(iszero, RG.pm)
      i,j = Tuple(idx)
      g = (twisted ? star(RG.basis[i]) : RG.basis[i])*RG.basis[j]
      if haskey(RG.basis_dict, g)
          RG.pm[i,j] = RG.basis_dict[g]
      else
         warning = true
      end
   end
   warning && @warn("Some products were not supported on basis")
   return RG
end

function initializepm!(RG::GroupRing; fill::Bool=false)
   hasbasis(RG) || throw("For baseless Group Rings You need to provide pm.")
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
