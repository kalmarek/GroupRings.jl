###############################################################################
#
#   Array protocol
#
###############################################################################

### getindex for GroupRing

function Base.getindex(RG::GroupRing, i::Integer)
    @assert hasbasis(RG)
    return RG.basis[i]
end

function Base.getindex(RG::GroupRing{R,G,El}, g::El) where {R,G,El<:GroupElem}
    @assert hasbasis(RG)
    return RG.basis_dict[g]
end

Base.length(RG::GroupRing) = hasbasis(RG) ? length(RG.basis) : maximum(RG)

### Array protocol for GroupRingElem

Base.eltype(::Type{<:GroupRingElem{T}}) where T = T
Base.size(X::GroupRingElem) = size(X.coeffs)
Base.IndexStyle(::Type{GroupRingElem}) = Base.LinearFast()

Base.@propagate_inbounds function Base.getindex(X::GroupRingElem, i::Integer)
    return X.coeffs[i]
end

Base.@propagate_inbounds function Base.setindex!(X::GroupRingElem, val, i::Integer)
    return X.coeffs[i] = val
end

Base.similar(X::GroupRingElem) = GroupRingElem(similar(X.coeffs), parent(X), check=false)

function Base.similar(X::GroupRingElem, ::Type{T}) where T
    RG = change_base_ring(parent(X), parent(T()))
    return GroupRingElem(similar(X.coeffs, T), RG)
end

### indexing via group elements

Base.@propagate_inbounds function Base.getindex(X::GroupRingElem, g::GroupElem)
    RG = parent(X)
    @assert hasbasis(RG)
    return X.coeffs[RG[g]]
end

Base.@propagate_inbounds function Base.setindex!(X::GroupRingElem, val,  g::GroupElem)
    RG = parent(X)
    @assert hasbasis(RG)
    return X.coeffs[RG[g]] = val
end

###############################################################################
#
#   GroupRing specifics: augmentation, support, *-involution
#
###############################################################################

aug(X::GroupRingElem) = sum(X.coeffs)

function supp(X::GroupRingElem)
    @assert hasbasis(parent(X))
    dropzeros!(X.coeffs)
    return parent(X).basis[X.coeffs.nzind]
end

function star(X::GroupRingElem{T}) where T
    RG = parent(X)
    hasbasis(RG) || throw(ArgumentError("*-involution without basis is not possible"))
    nzind = [RG.basis_dict[inv(RG.basis[i])] for i in X.coeffs.nzind]
    return GroupRingElem(sparsevec(nzind, X.coeffs.nzval, X.coeffs.n), RG)
end


###############################################################################
#
#   Utilities
#
###############################################################################

LinearAlgebra.norm(X::GroupRingElem, p::Int=2) = norm(X.coeffs, p)

function _dealias(res::GroupRingElem, x::GroupRingElem, y::GroupRingElem)
    @assert size(res) == size(x) == size(y)
    if res.coeffs === x.coeffs || res.coeffs === y.coeffs
        res = similar(res)
    end
    return res
end

function _promote(X::GroupRingElem{S}, Y::GroupRingElem{T}) where {S,T}
    # TT = Core.Compiler.returntype(+, (T, S))
    TT = AbstractAlgebra.promote_type(S,T)
    # we do if else on TT to decide the parent of the result
    if TT == S
        result = similar(X)
    elseif TT == T
        result = similar(Y)
    else
        # we try to come up with parent; this will work for Julia numeric types
        R = parent(first(X)+first(Y))
        RG = change_base_ring(parent(X), R)
        result = GroupRingElem(similar(X.coeffs, TT), RG)
        @warn "Promoting group ring elements with different base rings!\nThe result has coefficients in $(R) of type $(eltype(result))."
    end
    return result
end

multiplicative_id(G::Group) = G()
multiplicative_id(R::NCRing) = one(R)

function _identity_idx(RG::GroupRing)
    hasbasis(RG) && return RG[multiplicative_id(RG.group)]
    @warn "Group ring has no basis attached. Assuming identity is at index 1"
    return 1
end

function _coerce_scalar(RG::GroupRing, c)
    val = base_ring(RG)(c)
    return GroupRingElem(sparsevec([_identity_idx(RG)], [val], length(RG)), RG, check=false)
end
