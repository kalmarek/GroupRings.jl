module GroupRings

using Nemo
import Nemo: Group, GroupElem, Ring, RingElem, parent, elem_type, parent_type, mul!, addeq!, divexact

import Base: convert, show, hash, ==, +, -, *, //, /, length, norm, rationalize, deepcopy_internal, getindex, setindex!, eltype, one, zero

###############################################################################
#
#   GroupRings / GroupRingsElem
#
###############################################################################

type GroupRing{Gr<:Group, T<:GroupElem} <: Ring
   group::Gr
   basis::Vector{T}
   basis_dict::Dict{T, Int}
   pm::Array{Int,2}

   function GroupRing(G::Group, basis::Vector{T}; init::Bool=false)
      RG = new(G, basis, reverse_dict(basis))
      if init
         RG.pm = try
            create_pm(RG.basis, RG.basis_dict)
         catch err
            isa(err, KeyError) && throw("Product is not supported on basis")
            throw(err)
         end
      else
         RG.pm = zeros(Int, length(basis), length(basis))
      end
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

GroupRing{Gr<:Group, T<:GroupElem}(G::Gr, basis::Vector{T}; init=false) =
   GroupRing{Gr, T}(G, basis, init=init)

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

export GroupRing, GroupRingElem, complete, create_pm

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type(::GroupRing) = GroupRingElem

parent_type(::GroupRingElem) = GroupRing
parent_type(::Type{GroupRingElem}) = GroupRing

eltype(X::GroupRingElem) = eltype(X.coeffs)

parent{T}(g::GroupRingElem{T}) = g.parent

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

function GroupRing(G::Group; init::Bool=false)
   return GroupRing(G, collect(elements(G)), init=init)
end

function GroupRing(G::Group, basis::Vector, pm::Array{Int,2})
   size(pm,1) == size(pm,2) || throw("pm must be square, got $(size(pm))")
   eltype(basis) == elem_type(G) || throw("Basis must consist of elements of $G")
   basis_dict = reverse_dict(basis)
   return GroupRing(G, basis, basis_dict, pm)
end

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

zero(RG::GroupRing, T::Type=Int) = RG(T)
one(RG::GroupRing, T::Type=Int) = RG(RG.group(), T)

function (RG::GroupRing)(i::Int, T::Type=Int)
   elt = RG(T)
   elt[RG.group()] = i
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

function (RG::GroupRing)(x::AbstractVector)
   isdefined(RG, :basis) || throw("Can not coerce without basis of GroupRing")
   length(x) == length(RG.basis) || throw("Can not coerce to $RG: lengths differ")
   result = RG(eltype(x))
   result.coeffs = x
   return result
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
      warn("Basis of the parent Group is not defined, showing coeffs")
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
      warn("Bases of GroupRings are not defined, comparing products mats.")
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

function mul!{T}(result::AbstractVector{T},
                      X::AbstractVector,
                      Y::AbstractVector,
                     pm::Array{Int,2})
   z = zero(T)
   result .= z
   for j in eachindex(Y)
      if Y[j] != z
         for i in 1:size(pm,1)
            if X[i] != z
               pm[i,j] == 0 && throw(ArgumentError("The product don't seem to be supported on basis!"))
               result[pm[i,j]] += X[i]*Y[j]
            end
         end
      end
   end
end

function mul!{T}(result::GroupRingElem{T}, X::GroupRingElem, Y::GroupRingElem)
   if result === X
      result = deepcopy(result)
   end

   z = zero(T)
   result.coeffs .= z

   for j in eachindex(Y.coeffs)
      if Y.coeffs[j] != z
         for i in eachindex(X.coeffs)
            if X.coeffs[i] != z
               if parent(X).pm[i,j] == 0
                  g = parent(X).basis[i]*parent(Y).basis[j]
                  parent(X).pm[i,j] = parent(X).basis_dict[g]
               end
               result.coeffs[parent(X).pm[i,j]] += X[i]*Y[j]
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
      result = similar(X.coeffs)
      result = mul!(result, X.coeffs, Y.coeffs, parent(X).pm)
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

   result = mul!(result, X, Y)
   return result

   if isdefined(parent(X), :basis)
      result = parent(X)(similar(X.coeffs))
      result = convert(TT, result)
      result = mul!(result, X, Y)
   else
      result = similar(X.coeffs)
      result = convert(TT, result)
      result = mul!(result, X.coeffs, Y.coeffs, parent(X).pm)
      result = GroupRingElem(result, parent(X))
   end
   return result
end



function divexact{T}(X::GroupRingElem{T}, Y::GroupRingElem{T})
   if length(Y) != 1
      throw("Can not divide by a non-primitive element $(Y)!")
   else
      idx = findfirst(Y)
      c = Y[idx]
      c == 0 || throw("Can not invert")
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

function complete!(RG::GroupRing)
   if !isdefined(RG, :basis)
      RG.basis = [elements(RG.group)...]
   end
   if !isdefined(RG, :basis_dict)
      RG.basis_dict = reverse_dict(RG.basis)
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
