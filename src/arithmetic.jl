###############################################################################
#
#   Unsafe operators (NCRing interface)
#
###############################################################################

@doc doc"""
    zero!(X::GroupRingElem)
In-place set coefficients of `X` to `0`. The sparsity pattern of `X` will be preserved.
"""
zero!(X::GroupRingElem{T}) where T = ( fill!(X.coeffs, zero(T)); X )

@doc doc"""
    mul!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)
Perform the multiplication `X * Y` and store the result in `result`.

`mul!` will make use the initialised entries of `pm` attribute of `parent(X)` (if available), and will compute (and cache in `parent(X).pm`) the remaining products as necessary.

# Notes:
* `result` is zeroed before use
* aliasing of `result` and `X` or `Y` is allowed (in the case a `similar` copy is created)
* `mul!` will throw `BoundsError` if `X * Y` is not supported on `parent(X).basis`
* no checks on arguments parents (i.e. mathematical correctns) are performed
"""
function mul!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)

    result = zero!(_dealias(result, X, Y))
    X_nzeros_idx = findall(!iszero, X.coeffs)
    Y_nzeros_idx = findall(!iszero, Y.coeffs)

    RG = parent(X)

    if cachesmultiplication(RG)
        complete!(RG, X_nzeros_idx, Y_nzeros_idx)
        for j in Y_nzeros_idx
            for i in X_nzeros_idx
                result.coeffs[RG.pm[i,j]] += X[i]*Y[j]
            end
        end
    else
        for j in Y_nzeros_idx
            for i in X_nzeros_idx
                result[RG[i]*RG[j]] += X[i]*Y[j]
            end
        end
    end
    return result
end
@doc doc"""
    add!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)
Perform te the addition `X + Y` and store the result in `result`.

# Notes:
* `result` is zeroed before use
* aliasing of `result` and `X` or `Y` is allowed (in the case a `similar` copy is created)
* no checks on arguments parents (i.e. mathematical correctns) are performed
"""
function add!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)
    result = _dealias(result, X, Y)
    @inbounds for i in eachindex(result.coeffs)
        result.coeffs[i] = X.coeffs[i] + Y.coeffs[i]
    end
    return result
end

@doc doc"""
    addeq!(X::GroupRingElem, Y::GroupRingElem)
Add `Y` to `X` in-place (the result is stored in `X`).

# Notes:
* no checks on arguments parents (i.e. mathematical correctns) are performed
"""

function addeq!(X::GroupRingElem, Y::GroupRingElem)
    X.coeffs .+= Y.coeffs
    return X
end

function addmul!(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem,
    tmp::GroupRingElem=similar(result))
    tmp = mul!(tmp, X, Y)
    result = addeq!(result, tmp)
    return result
end

###############################################################################
#
#   Arithmetic operations (NCRing interface)
#
###############################################################################

-(X::GroupRingElem{T}) where T = GroupRingElem(-X.coeffs, parent(X))
^(X::GroupRingElem, n::Integer) = Base.power_by_squaring(X, n)

function Base.inv(X::GroupRingElem)
    if isunit(X)
        g = supp(X)[1]
        i_g = eltype(X)(inv(X[g]))
        return scalarmul!(base_ring(parent(X))(i_g), parent(X)(inv(g)))
    end
    throw(DivideError())
end

### Addition/Subtraction:

function +(X::GroupRingElem{T, GR}, Y::GroupRingElem{T, GR}) where {T, GR<:GroupRing}
    # @assert parent(X) == parent(Y)
    return add!(X, X, Y)
end

function +(X::GroupRingElem{S}, Y::GroupRingElem{T}) where {S,T}
    # @assert parent(X) == parent(Y)
    result = _promote(X, Y)
    return add!(result, X, Y)
end

# -Y creates a copy
-(X::GroupRingElem{T,GR}, Y::GroupRingElem{T,GR}) where {T,GR<:GroupRing} = addeq!(-Y, X)

# X - Y => X + (-Y) for other parameters TODO: this allocates two elements instead of one

### Multiplication:

function _mul(result::GroupRingElem, X::GroupRingElem, Y::GroupRingElem)
    RG = parent(X)
    if hasbasis(RG)
        result = mul!(result, X, Y)
    else
        result.coeffs = _mul!(result.coeffs, X.coeffs, Y.coeffs, RG.pm)
    end
    return result
end

function *(X::GroupRingElem{T,GR}, Y::GroupRingElem{T,GR}) where {T, GR<:GroupRing}
    # @assert parent(X) == parent(Y)
    return _mul(X, X, Y)
end

function *(X::GroupRingElem{S}, Y::GroupRingElem{T}) where {S,T}
    # @assert parent(X) == parent(Y)
    result = _promote(X, Y)
    return _mul(result, X, Y)
end

###############################################################################
#
#   Scalar and Ad-hoc operators
#
###############################################################################

### Addition/subtraction

function addeq!(X::GroupRingElem{T}, a::T) where T
    X[_identity_idx(parent(X))] += a
    return X
end

function addeq!(X::GroupRingElem{T, GroupRing{R,G,El}}, g::El, v=one(T)) where {T,R,G,El}
    @assert hasbasis(parent(X))
    X[g] += T(v)
    return X
end

+(X::GroupRingElem{T}, a::T) where T<:RingElement = addeq!(deepcopy(X), a)
+(a::T, X::GroupRingElem{T}) where T<:RingElement = addeq!(deepcopy(X), a)
+(X::GroupRingElem{T, GroupRing{R, G, El}}, g::El) where {T, R, G, El} = addeq!(deepcopy(X), g)
+(g::El, X::GroupRingElem{T, GroupRing{R, G, El}}) where {T, R, G, El} = addeq!(deepcopy(X), g)
# +(X::GroupRingElem{T}, a::S) where {S,T} = addeq!(deepcopy(X), base_ring(X)(a))
# +(a::S, X::GroupRingElem{T}) where {S,T} = addeq!(deepcopy(X), base_ring(X)(a))

-(X::GroupRingElem{T}, a::T) where T<:RingElement = addeq!(deepcopy(X), -a)
-(a::T, X::GroupRingElem{T}) where T<:RingElement = addeq!(-X, a)
-(X::GroupRingElem{T, GroupRing{R, G, El}}, g::El) where {T, R, G, El} = addeq!(deepcopy(X), g, -1)
-(g::El, X::GroupRingElem{T, GroupRing{R, G, El}}) where {T, R, G, El} = addeq!(-X, g)
# -(X::GroupRingElem{T}, a::S) where {S,T} = addeq!(deepcopy(X), -base_ring(X)(a))
# -(a::S, X::GroupRingElem{T}) where {S,T} = addeq!(-X, base_ring(X)(a))

### Scalar multiplication/scalar division

scalarmul!(a::T, X::GroupRingElem{T}) where T = (X.coeffs .*= a; return X)

function scalarmul(a::S, X::GroupRingElem{T}) where {S,T}
    if promote_type(S, T) == T
        return scalarmul!(base_ring(parent(X))(a), deepcopy(X))
    else
        RG = change_base_ring(parent(X), parent(a))
        @warn "Coefficient ring does not contain scalar $a;\nThe resulting GroupRingElem has coefficients in $(parent(a)) of type $(elem_type(parent(a)))."
        return scalarmul!(a, GroupRingElem(base_ring(RG).(X.coeffs), RG))
    end
end

*(a::T, X::GroupRingElem{T}) where T = scalarmul!(a, deepcopy(X))
# assuming commutativity of base_ring
*(X::GroupRingElem{T}, a::T) where T = scalarmul!(a, deepcopy(X))
*(a::T, X::GroupRingElem{S}) where {T, S} = scalarmul(a, X)
*(X::GroupRingElem{S}, a::T) where {T, S} = scalarmul(a, X)

# deambiguations:
*(a::Union{AbstractFloat, Integer, RingElem, Rational}, X::GroupRingElem) = scalarmul(a, X)
*(X::GroupRingElem, a::Union{AbstractFloat, Integer, RingElem, Rational}) = scalarmul(a, X)

# divisions
(/)(X::GroupRingElem, a) = inv(a)*X
(//)(X::GroupRingElem, a::Union{Integer, Rational}) = 1//a*X

###############################################################################
#
#   Unsafe operators on coefficients
#
###############################################################################

@doc doc"""
    _mul!(result::AbstractVector, X::AbstractVector, Y::AbstractVector, pm::AbstracctMatrix{<:Integer})
Unsafe multiplication for group ring elements (represented by coefficient vectors `result`, `X` and `Y`) using the provided multiplication table `pm`.
Performs the multiplication `X * Y` and stores the result in `result`.

# Notes:
* aliasing of `result` and `X` or `Y` is allowed (in the case a `similar` copy is created)
* `result` is zeroed before use
* `BoundsError` is thrown if `X * Y` is not determined by `pm`
* this method will silently produce false results if either `X[k]` or `Y[k]`
is non-zero for `k > size(pm,1)`
* use only if You know what you're doing!
"""
function _mul!(result::AbstractVector, X::AbstractVector, Y::AbstractVector,
    pm::AbstractMatrix{<:Integer})
    # this mul! is used for base-less multiplication
    if result === X || result === Y
        result = zero(result)
    else
        result .= zero(eltype(result))
    end
    return _addmul!(result, X, Y, pm)
end

@doc doc"""
    _addmul!(result::AbstractVector, X::AbstractVector, Y::AbstractVector, pm::AbstractMatrix{<:Integer})
Unsafe fused multiply-add for group ring elements (represented by coefficient vectors `X` and `Y`) using the provided multiplication table `pm`.
Performs the multiplication `X * Y` and adds the result to `result` in-place.

# Notes:
* aliasing of `result` and `X` or `Y` is NOT checked
* `BoundsError` is thrown if `X * Y` is not determined by `pm`
* this method will silently produce false results if either `X[k]` or `Y[k]`
is non-zero for `k > size(pm,1)`
* use only if You know what you're doing!
"""

function _addmul!(result::AbstractVector, X::AbstractVector, Y::AbstractVector,
    pm::AbstractMatrix{<:Integer})
    zX = zero(eltype(X))
    zY = zero(eltype(Y))
    @inbounds for j in 1:size(pm,2)
        if Y[j] != zY
            for i in 1:size(pm,1)
                if X[i] != zX
                    result[pm[i,j]] += X[i]*Y[j]
                end
            end
        end
    end
    return result
end
