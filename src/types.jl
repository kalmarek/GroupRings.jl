###############################################################################
#
#   GroupRing & GroupRingElem structs
#
###############################################################################

mutable struct GroupRing{R<:Ring, Gr<:Group, El<:GroupElem} <: NCRing
    base_ring::R
    group::Gr
    basis::Vector{El}
    basis_dict::Dict{El, Int32}
    pm::Matrix{Int32}

    function GroupRing(coeffring::Ring, group::Group, basis::Vector{<:GroupElem};
        halfradius_length::Integer=0)

        elem_type(group) == eltype(basis) ||
        throw(ArgumentError("Basis must consist of elements of $G"))

        RG = new{typeof(coeffring), typeof(group), eltype(basis)}(
        coeffring, group, basis, reverse_dict(basis))

        if halfradius_length > 0
            pm = zeros(Int32, halfradius_length, halfradius_length)
            setcache!(RG, pm)
        end

        return RG
    end

    function GroupRing(coeffring::Ring, group::Group, basis::Vector{<:GroupElem},
        basis_dict::Dict{<:GroupElem,<:Integer}, pm::Matrix{<:Integer})
        size(pm,1) == size(pm,2) ||
        throw(ArgumentError("Multiplication table must be square, got one of size $(size(pm))"))
        elem_type(group) == eltype(basis) ||
        throw(ArgumentError("Basis must consist of elements of $G"))

        RG = new{typeof(coeffring), typeof(group), eltype(basis)}(
        coeffring, group, basis, basis_dict, pm)

        return RG
    end

    function GroupRing(coeffring::Ring, group::Group, pm::Matrix{<:Integer})
        size(pm,1) == size(pm,2) || throw(ArgumentError("Multiplication table must be square, got one of size $(size(pm))"))

        RG = new{typeof(coeffring), typeof(group), elem_type(group)}(coeffring, group)
        setcache!(RG, pm)
        return RG
    end
end

mutable struct GroupRingElem{T, GR<:GroupRing} <: NCRingElem
    coeffs::SparseVector{T, Int}
    parent::GR

    function GroupRingElem(c::AbstractVector{T}, RG::GR; check::Bool=true) where {T, GR}
        if check
            T == elem_type(base_ring(RG)) || throw(DomainError(c, "Call parent group ring on the vector to coerce the coefficients.s"))
            length(c) == length(RG) || throw(DomainError(c, "Can not coerce vector to $RG -- lengths differ:\n $(length(c)) ≠ $(length(RG))"))
        end
        return new{eltype(c), GR}(sparse(c), RG)
    end
end

###############################################################################
#
#   Constructors & parent object call overloads (NCRing interface)
#
###############################################################################

(RG::GroupRing)(i::Integer=0)= _coerce_scalar(RG, i)
(RG::GroupRing)(x::RingElem) = _coerce_scalar(RG, x)

function (RG::GroupRing)(X::GroupRingElem{T}) where {T}
    if RG == parent(X) && elem_type(base_ring(RG)) == T
        return X
    end
    if RG.group == parent(X).group
        return GroupRingElem(base_ring(RG).(X.coeffs), RG) # we do checks here
    end
    throw(ArgumentError("Can not coerce to $RG."))
end

###############################################################################
#
#   Additional Constructors / parent call overloads
#
###############################################################################

function GroupRing(coeffring::Ring, group::Group, basis::Vector{<:GroupElem},
    pm::Matrix{<:Integer})
    return GroupRing(coeffring, group, basis, reverse_dict(basis), pm)
end

function (RG::GroupRing)(g::GroupElem, val=one(base_ring(RG)))
    v = sparsevec([RG[g]], [base_ring(RG)(val)], length(RG))
    return GroupRingElem(v, RG, check=false)
end

function (RG::GroupRing{R, G, El})(V::AbstractVector{El},
    vals=[one(base_ring(RG)) for _ in V]) where {R, G, El}
    hasbasis(RG) || throw(ArgumentError("Can not embedd without basis of $RG"))
    l = length(RG)
    nzind = [RG[g] for g in V]
    return GroupRingElem(sparsevec(nzind, base_ring(RG).(vals), l), RG, check=false)
end

function (RG::GroupRing)(f, X::GroupRingElem)
    hasbasis(RG) || throw(ArgumentError("Can not embedd without basis of $RG"))
    suppX = supp(X)
    return RG([f(g) for g in suppX], [X[g] for g in suppX])
end

function (RG::GroupRing)(v::AbstractVector;
    adjust_length::Bool=false, widen_coefficients::Bool=false)

    if adjust_length
        l = length(RG)
        if length(v) < l
            @warn "Coefficients vector is length-defficient; adjusting."
            v = sparse(v)
            v = sparse(v.nzind, v.nzval, l)
        elseif length(c) > l
            throw(DomainError(v, "Can not coerce vector to $RG -- lengths differ:\n $(length(v)) ≠ $(length(RG))"))
        end
    end

    if widen_coefficients
        parent(first(v)) != base_ring(RG)
        RG = change_base_ring(RG, parent(first(v)))
        return GroupRingElem(v, RG)
    else
        R = base_ring(RG)
        return GroupRingElem(R.(v), RG)
    end
end

function AbstractAlgebra.change_base_ring(RG::GroupRing, R::Ring)
    if base_ring(RG) == R
        return RG
    end
    if hasbasis(RG) && cachesmultiplication(RG)
        return GroupRing(R, RG.group, RG.basis, RG.basis_dict, RG.pm)
    elseif hasbasis(RG)
        return GroupRing(R, RG.group, RG.basis, RG.basis_dict)
    elseif cachesmultiplication(RG)
        return GroupRing(R, RG.group, RG.pm)
    end
    throw(ArgumentError("Could not change the base ring of $RG to $R"))
end

function AbstractAlgebra.change_base_ring(X::GroupRingElem, R::Ring)
    if base_ring(parent(X)) == R
        return X
    else
        RG = change_base_ring(parent(X), R)
        return RG(X.coeffs)
    end
end

