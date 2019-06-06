###############################################################################
#
#   NCRing Interface
#
###############################################################################

AbstractAlgebra.parent_type(::Type{GroupRingElem{T, GR}}) where {T, GR} = GR

function AbstractAlgebra.elem_type(::Type{<:GroupRing{R,G,El}}) where {R,G,El}
	return GroupRingElem{elem_type(R), GroupRing{R,G,El}}
end

AbstractAlgebra.base_ring(RG::GroupRing) = RG.base_ring

AbstractAlgebra.parent(X::GroupRingElem) = X.parent

AbstractAlgebra.isexact_type(::Type{<:GroupRingElem{T}}) where T = isexact_type(T)

# hash(GroupRingElem) = 0x839279ac6f12f62a
function Base.hash(X::GroupRingElem, h::UInt)
   return ⊻(hash(X.coeffs, h), hash(parent(X), h), 0x839279ac6f12f62a)
end

function Base.deepcopy_internal(X::GroupRingElem, dict::IdDict)
   return parent(X)(deepcopy(X.coeffs))
end

Base.zero(RG::GroupRing) = RG(0)
Base.one(RG::GroupRing) = RG(1)
Base.iszero(X::GroupRingElem{T}) where T = all(x == zero(T) for x in X.coeffs.nzval)

function Base.isone(X::GroupRingElem{T}) where T
	idx = _identity_idx(parent(X))
    X[idx] == one(T) || return false
    all(X[i] == zero(T) for i in eachindex(X.coeffs) if i != idx) || return false
    return true
end

###############################################################################
#
#   String I/O
#
###############################################################################

Base.show(io::IO, RG::GroupRing) =
   print(io, "Group ring of $(RG.group) with coefficients in $(base_ring(RG))")

function Base.show(io::IO, X::GroupRingElem{T}) where T
   RG = parent(X)
   if iszero(X)
      print(io, "$(zero(T))*$(multiplicative_id(RG.group))")
   elseif hasbasis(RG)
      suppX = supp(X)
      elts = String[]

      elts = String[]
      sgn = ""
      for g in suppX
         coeff = X[g]
         if X[g] < 0
            sgn = " - "
            coeff = -coeff
         end
	      push!(elts, sgn*string(coeff)*string(g))
         sgn = " + "
      end
      str = join(elts, "")
      print(io, str)
   else
      @warn("Basis of the parent group ring is not defined, showing coeffs")
      show(io, MIME("text/plain"), X.coeffs)
   end
end

AbstractAlgebra.needs_parentheses(X::GroupRingElem) = true
AbstractAlgebra.displayed_with_minus_in_front(X::GroupRingElem) = false
AbstractAlgebra.show_minus_one(::Type{<:GroupRingElem}) = true

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(X::GroupRingElem{T}, Y::GroupRingElem{S}) where {T,S}
   if promote_type(T,S) ≠ T || promote_type(T,S) ≠ S
      @warn "Comparing elements with incompatible coeffs Rings: $T and $S can be only compared as $(promote_type(T,S))"
   end
   length(X.coeffs) == length(Y.coeffs) || return false
   parent(X).group == parent(Y).group || return false
   return all(x == y for (x,y) in zip(X.coeffs, Y.coeffs))
end

Base.isequal(X::GroupRingElem, Y::GroupRingElem) = X == Y

_equalorzero(x,y) = x == y || x == 0 || y == 0

function ==(A::GroupRing, B::GroupRing)
   A.group == B.group || return false
   # base_ring(A) == base_ring(B) || return false

   bases = hasbasis(A) && hasbasis(B)
   caches = cachesmultiplication(A) && cachesmultiplication(B)

   if bases && caches
      length(A) == length(B) || return false
      size(A.pm) == size(B.pm) || return false
      all(A.basis[i] == B.basis[i] for i in eachindex(A.basis)) || return false
      all(_equalorzero(A.pm[i], B.pm[i]) for i in eachindex(A.pm)) || return false
      return true
   elseif bases # && !caches
      length(A) == length(B) || return false
      all(A.basis[i] == B.basis[i] for i in eachindex(A.basis)) || return false
      return true
   elseif caches # && !bases
      size(A.pm) == size(B.pm) || return false
      all(A.pm[i] == B.pm[i] for i in eachindex(A.pm)) || return false
      return true
   else
      return false
   end
end

###############################################################################
#
#   Exact Division (TODO)
#
###############################################################################

function AbstractAlgebra.divexact_left(X::GroupRingElem, Y::GroupRingElem)
   isunit(Y) || throw(DivideError())
   return inv(Y)*X
end

function AbstractAlgebra.divexact_right(X::GroupRingElem, Y::GroupRingElem)
   isunit(Y) || throw(DivideError())
   return X*inv(Y)
end

###############################################################################
#
#   promotion, rand, isapprox
#
###############################################################################

AbstractAlgebra.promote_rule(::Type{GREl}, ::Type{T}) where {T<:RingElement, GREl<:GroupRingElem{T}} = GREl

function AbstractAlgebra.promote_rule(
    ::Type{<:GroupRingElem{T, GR}},
    ::Type{<:GroupRingElem{S, GR}}) where {T<:RingElement, S<:RingElement, GR}
    R = AbstractAlgebra.promote_rule(T, S)
    return (R == Union{} ? Union{} : GroupRingElem{R, GR})
end

function AbstractAlgebra.promote_rule(::Type{<:GroupRingElem{T, GR}}, ::Type{S}) where {T, GR, S<:RingElement}
    R = AbstractAlgebra.promote_rule(T, S)
    return (R == Union{} ? Union{} : GroupRingElem{R, GR})
end

function AbstractAlgebra.promote_rule(u::Type{U}, x::Type{GREl}) where {T, GREl<:GroupRingElem{T}, U<:RingElement}
    return AbstractAlgebra.promote_rule(x, u)
end

function Base.rand(RG::GroupRing, density=0.05, args...)
	l = length(RG)

	if cachesmultiplication(RG)
		nzind = rand(1:size(RG.pm, 1), floor(Int, density*l))
	else
		nzind = rand(1:l, floor(Int, density*l))
	end

   nzval = [rand(base_ring(RG), args...) for _ in nzind]

	return GroupRingElem(sparsevec(nzind, nzval, l), RG)
end

function Base.isapprox(X::GroupRingElem{T}, Y::GroupRingElem{S};
	atol::Real=sqrt(eps())) where {T,S}
   parent(X) == parent(Y) || return false
   return isapprox(X.coeffs, Y.coeffs, atol=atol)
end

Base.isapprox(X::GroupRingElem{T}, a::T; atol::Real=sqrt(eps())) where T = isapprox(X, RG(a))

Base.isapprox(a::T, X::GroupRingElem{T}; atol::Real=sqrt(eps())) where T = isapprox(X,a)

###############################################################################
#
#   Additional functionality
#
###############################################################################

function AbstractAlgebra.isunit(X::GroupRingElem)
   count(!iszero, X.coeffs) == 1 || return false
   return isunit(X[supp(X)[1]])
end
