__precompile__()
module GroupRings

using Nemo
import Nemo: Group, GroupElem, Ring, RingElem, parent, elem_type, parent_type, mul!, addeq!, divexact

import Base: convert, show, hash, ==, +, -, *, //, /, length, norm, rationalize, deepcopy_internal, getindex, setindex!, eltype, one, zero

###############################################################################
#
#   GroupRings / GroupRingsElem
#
###############################################################################

baseless_warn = false

type GroupRing{Gr<:Group, T<:GroupElem} <: Ring
   group::Gr
   basis::Vector{T}
   basis_dict::Dict{T, Int}
   pm::Array{Int,2}

   function GroupRing(G::Group, basis::Vector{T}; fastm::Bool=false)
      RG = new(G, basis, reverse_dict(basis))
      fastm && fastm!(RG)
      return RG
   end

   function GroupRing(G::Gr, basis::Vector{T}, basis_dict::Dict{T,Int}, pm::Array{Int,2})
      return new(G, basis, basis_dict, pm)
   end

   function GroupRing(G::Gr, pm::Array{Int,2})
      RG = new(G)
      RG.pm = pm
      return RG
   end
end

GroupRing{Gr<:Group, T<:GroupElem}(G::Gr, basis::Vector{T}; fastm::Bool=true) =
   GroupRing{Gr, T}(G, basis, fastm=fastm)

GroupRing{Gr<:Group, T<:GroupElem}(G::Gr, b::Vector{T}, b_d::Dict{T,Int}, pm::Array{Int,2}) = GroupRing{Gr, T}(G, b, b_d, pm)

GroupRing{Gr<:Group}(G::Gr, pm::Array{Int,2}) =
   GroupRing{Gr, elem_type(G)}(G, pm)

type GroupRingElem{T<:Number} <: RingElem
   coeffs::AbstractVector{T}
   parent::GroupRing

   function GroupRingElem(c::AbstractVector{T}, RG::GroupRing, check=true)
      if check
         if isdefined(RG, :basis)
            length(c) == length(RG.basis) || throw(
            "Can't create GroupRingElem -- lengths differ: length(c) =
            $(length(c)) != $(length(RG.basis)) = length(RG.basis)")
         else
            warn("Basis of the GroupRing is not defined.")
         end
      end
      return new(c, RG)
   end
end

export GroupRing, GroupRingElem, complete!, create_pm, star

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type{T,S}(::Type{GroupRing{T,S}}) = GroupRingElem

parent_type(::Type{GroupRingElem}) = GroupRing

eltype(X::GroupRingElem) = eltype(X.coeffs)

parent(g::GroupRingElem) = g.parent

Base.promote_rule{T<:Number,S<:Number}(::Type{GroupRingElem{T}}, ::Type{GroupRingElem{S}}) = GroupRingElem{promote_type(T,S)}

function convert{T<:Number}(::Type{T}, X::GroupRingElem)
   return GroupRingElem(convert(AbstractVector{T}, X.coeffs), parent(X))
end

###############################################################################
#
#   GroupRing / GroupRingElem constructors
#
###############################################################################

function GroupRingElem{T<:Number}(c::AbstractVector{T}, RG::GroupRing)
   return GroupRingElem{T}(c, RG)
end

function GroupRing(G::Group; fastm::Bool=false)
   return GroupRing(G, [elements(G)...], fastm=fastm)
end

function GroupRing(G::Group, basis::Vector, pm::Array{Int,2})
   size(pm,1) == size(pm,2) || throw("pm must be square, got $(size(pm))")
   eltype(basis) == elem_type(G) || throw("Basis must consist of elements of $G")
   return GroupRing(G, basis, reverse_dict(basis), pm)
end

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

zero(RG::GroupRing, T::Type=Int) = RG(T)
one(RG::GroupRing, T::Type=Int) = RG(RG.group(), T)
one{R<:Nemo.Ring, S<:Nemo.RingElem}(RG::GroupRing{R,S}) = RG(eye(RG.group()))

function (RG::GroupRing)(i::Int, T::Type=Int)
   elt = RG(T)
   elt[RG.group()] = i
   return elt
end

function (RG::GroupRing{R,S}){R<:Ring, S}(i::Int, T::Type=Int)
   elt = RG(T)
   elt[eye(RG.group())] = i
   return elt
end

function (RG::GroupRing)(T::Type=Int)
   isdefined(RG, :basis) || throw("Can not coerce without basis of GroupRing")
   return GroupRingElem(spzeros(T,length(RG.basis)), RG)
end

function (RG::GroupRing)(g::GroupElem, T::Type=Int)
   g = RG.group(g)
   result = RG(T)
   result[g] = one(T)
   return result
end

function (RG::GroupRing){T<:Number}(x::AbstractVector{T})
   isdefined(RG, :basis) || throw("Can not coerce without basis of GroupRing")
   length(x) == length(RG.basis) || throw("Can not coerce to $RG: lengths differ")
   result = RG(eltype(x))
   result.coeffs = x
   return result
end

function (RG::GroupRing{Gr,T}){Gr<:Nemo.Group, T<:Nemo.GroupElem}(V::Vector{T},
   S::Type=Rational{Int}; alt=false)
    res = RG(S)
    for g in V
        c = (alt ? sign(g)*one(S) : one(S))
        res[g] += c/length(V)
    end
    return res
end

function (RG::GroupRing)(X::GroupRingElem)
   RG == parent(X) || throw("Can not coerce!")
   return RG(X.coeffs)
end

function (RG::GroupRing)(X::GroupRingElem, emb::Function)
   isdefined(RG, :basis) || throw("Can not coerce without basis of GroupRing")
   result = RG(eltype(X.coeffs))
   T = typeof(X.coeffs)
   result.coeffs = T(result.coeffs)
   for g in parent(X).basis
      result[emb(g)] = X[g]
   end
   return result
end

###############################################################################
#
#   Basic manipulation && Array protocol
#
###############################################################################

function deepcopy_internal(X::GroupRingElem, dict::ObjectIdDict)
   return GroupRingElem(deepcopy(X.coeffs), parent(X))
end

function hash(X::GroupRingElem, h::UInt)
   return hash(full(X.coeffs), hash(parent(X), hash(GroupRingElem, h)))
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
   if !(g in keys(RG.basis_dict))
      g = (RG.group)(g)
   end
   X.coeffs[RG.basis_dict[g]] = value
end

Base.size(X::GroupRingElem) = size(X.coeffs)
Base.linearindexing{T<:GroupRingElem}(::Type{T}) = Base.LinearFast()

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
   if X.coeffs == zero(X.coeffs)
      T = eltype(X.coeffs)
      print(io, "$(zero(T))*$((RG.group)())")
   elseif isdefined(RG, :basis)
      non_zeros = ((X.coeffs[i], RG.basis[i]) for i in findn(X.coeffs))
      elts = ("$(sign(c)> 0? " + ": " - ")$(abs(c))*$g" for (c,g) in non_zeros)
      str = join(elts, "")[2:end]
      if sign(first(non_zeros)[1]) > 0
         str = str[3:end]
      end
      print(io, str)
   else
      baseless_warn && warn("Basis of the parent Group is not defined, showing coeffs")
      show(io, MIME("text/plain"), X.coeffs)
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
   if isdefined(A, :basis) && isdefined(B, :basis)
      A.basis == B.basis || return false
   else
      baseless_warn && warn("Bases of GroupRings are not defined, comparing products mats.")
      A.pm == B.pm || return false
   end
   return true
end

###############################################################################
#
#   Scalar operators
#
###############################################################################

(-)(X::GroupRingElem) = GroupRingElem(-X.coeffs, parent(X))

function mul!{T<:Number}(a::T, X::GroupRingElem{T})
   X.coeffs .*= a
   return X
end

mul{T<:Number}(a::T, X::GroupRingElem{T}) = GroupRingElem(a*X.coeffs, parent(X))

function mul{T<:Number, S<:Number}(a::T, X::GroupRingElem{S})
   promote_type(T,S) == S || warn("Scalar and coeffs are in different rings! Promoting result to $(promote_type(T,S))")
   return GroupRingElem(a*X.coeffs, parent(X))
end

(*)(a, X::GroupRingElem) = mul(a,X)
(*)(X::GroupRingElem, a) = mul(a,X)

# disallow Nemo.Rings to hijack *(::Integer, ::RingElem)
(*){T<:Integer}(a::T, X::GroupRingElem) = mul(a,X)

(/)(X::GroupRingElem, a) = 1/a*X

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

function addeq!{T}(X::GroupRingElem{T}, Y::GroupRingElem{T})
   X.coeffs .+= Y.coeffs
   return X
end

function add{T<:Number}(X::GroupRingElem{T}, Y::GroupRingElem{T}, check::Bool=true)
   if check
      parent(X) == parent(Y) || throw("Elements don't seem to belong to the same Group Ring!")
   end
   return GroupRingElem(X.coeffs+Y.coeffs, parent(X))
end

function add{T<:Number, S<:Number}(X::GroupRingElem{T},
   Y::GroupRingElem{S}, check::Bool=true)
   if check
      parent(X) == parent(Y) || throw("Elements don't seem to belong to the same Group Ring!")
   end
   warn("Adding elements with different base rings!")
   return GroupRingElem(+(promote(X.coeffs, Y.coeffs)...), parent(X))
end

(+)(X::GroupRingElem, Y::GroupRingElem) = add(X,Y)
(-)(X::GroupRingElem, Y::GroupRingElem) = add(X,-Y)

doc"""
    mul!{T}(result::AbstractArray{T},
                 X::AbstractVector,
                 Y::AbstractVector,
                pm::Array{Int,2})
> The most specialised multiplication for `X` and `Y` (intended for `coeffs` of
> `GroupRingElems`), using multiplication table `pm`.
> Notes:
> * this method will silently produce false results if `X[k]` is non-zero for
> `k > size(pm,1)`.
> * This method will fail if any zeros (i.e. uninitialised entries) are present
> in `pm`.
> * Use with extreme care!
"""
function mul!{T}(result::AbstractVector{T},
                      X::AbstractVector,
                      Y::AbstractVector,
                     pm::Array{Int,2})
   z = zero(T)
   result .= z
   lY = length(Y)
   s = size(pm,1)

   @inbounds for j in 1:lY
      if Y[j] != z
         for i in 1:s
            if X[i] != z
               pm[i,j] == 0 && throw(ArgumentError("The product don't seem to be supported on basis!"))
               result[pm[i,j]] += X[i]*Y[j]
            end
         end
      end
   end
   return result
end

doc"""
    mul!{T}(result::GroupRingElem{T},
                 X::GroupRingElem,
                 Y::GroupRingElem)
> In-place multiplication for `GroupRingElem`s `X` and `Y`.
> `mul!` will make use the initialised entries of `pm` attribute of
> `parent(X)::GroupRing` (if available), and will compute and store in `pm` the
> remaining products necessary to perform the multiplication.
> The method will fail with `KeyError` if product `X*Y` is not supported on
> `parent(X).basis`.
"""
function mul!{T}(result::GroupRingElem{T}, X::GroupRingElem, Y::GroupRingElem)
   if result === X
      result = deepcopy(result)
   end

   z = zero(T)
   result.coeffs .= z

   RG = parent(X)

   lX = length(X.coeffs)
   lY = length(Y.coeffs)

   if isdefined(RG, :pm)
      s = size(RG.pm)
      findlast(X.coeffs) <= s[1] || throw("Element in X outside of support of RG.pm")
      findlast(Y.coeffs) <= s[2] || throw("Element in Y outside of support of RG.pm")

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

function *{T<:Number}(X::GroupRingElem{T}, Y::GroupRingElem{T}, check::Bool=true)
   if check
      parent(X) == parent(Y) || throw("Elements don't seem to belong to the same Group Ring!")
   end
   if isdefined(parent(X), :basis)
      result = parent(X)(similar(X.coeffs))
      result = mul!(result, X, Y)
   else
      result = mul!(similar(X.coeffs), X.coeffs, Y.coeffs, parent(X).pm)
      result = GroupRingElem(result, parent(X))
   end
   return result
end

function *{T<:Number, S<:Number}(X::GroupRingElem{T}, Y::GroupRingElem{S}, check::Bool=true)
   if true
      parent(X) == parent(Y) || throw("Elements don't seem to belong to the same Group Ring!")
   end

   TT = typeof(first(X.coeffs)*first(Y.coeffs))
   warn("Multiplying elements with different base rings! Promoting the result to $TT.")

   if isdefined(parent(X), :basis)
      result = parent(X)(similar(X.coeffs))
      result = convert(TT, result)
      result = mul!(result, X, Y)
   else
      result = convert(TT, similar(X.coeffs))
      result = mul!(result, X.coeffs, Y.coeffs, parent(X).pm)
      result = GroupRingElem(result, parent(X))
   end
   return result
end



function divexact{T}(X::GroupRingElem{T}, Y::GroupRingElem{T})
   if length(Y) != 1
      throw("Can not divide by a non-primitive element: $(Y)!")
   else
      idx = findfirst(Y)
      c = Y[idx]
      c != 0 || throw("Can not invert: $c not found in $Y")
      g = parent(Y).basis[idx]
      return X*1//c*parent(Y)(inv(g))
   end
end

###############################################################################
#
#   *-involution
#
###############################################################################

function star{T}(X::GroupRingElem{T})
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

length(X::GroupRingElem) = countnz(X.coeffs)

norm(X::GroupRingElem, p=2) = norm(X.coeffs, p)

augmentation(X::GroupRingElem) = sum(X.coeffs)

function rationalize{T<:Integer, S<:Integer}(::Type{T}, X::GroupRingElem{S})
   return convert(Rational{T}, X)
end

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
   limit::Int=length(basis); twisted::Bool=false, check=true)
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

function check_pm(product_matrix, basis, twisted)
   idx = findfirst(product_matrix' .== 0)
   if idx != 0
      warn("Product is not supported on basis")
      i,j = ind2sub(product_matrix, idx)
      x = basis[i]
      if twisted
         x = inv(x)
      end
      throw(KeyError(x*basis[j]))
   end
   return true
end

create_pm{T<:GroupElem}(b::Vector{T}) = create_pm(b, reverse_dict(b))

function complete!(RG::GroupRing)
   if !isdefined(RG, :basis)
      RG.basis = [elements(RG.group)...]
   end

   fastm!(RG, fill=false)

   warning = false
   for linidx in find(RG.pm .== 0)
      i,j = ind2sub(size(RG.pm), linidx)
      g = RG.basis[i]*RG.basis[j]
      if haskey(RG.basis_dict, g)
          RG.pm[i,j] = RG.basis_dict[g]
      else
         if !warning
            warning = true
         end
      end
   end
   warning && warn("Some products were not supported on basis")
   return RG
end

function fastm!(RG::GroupRing; fill::Bool=false)
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
