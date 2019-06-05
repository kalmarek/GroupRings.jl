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

###############################################################################
#
#   Cache Manipulation
#
###############################################################################

hasbasis(RG::GroupRing) = isdefined(RG, :basis)
cachesmultiplication(RG::GroupRing) = isdefined(RG, :pm)

reverse_dict(iter) = reverse_dict(Int32, iter)

function reverse_dict(::Type{I}, iter) where I<:Integer
    length(iter) > typemax(I) && error("Can not produce reverse dict: $(length(iter)) is too large for $I")
    return Dict{eltype(iter), I}(x => i for (i,x) in enumerate(iter))
end

setcache!(RG::GroupRing, pm::Matrix{<:Integer}) = (RG.pm = pm; return RG)

function complete!(RG::GroupRing,
    indX=1:size(RG.pm, 1),
    indY=1:size(RG.pm, 2);
    twisted::Bool=false)

    @assert hasbasis(RG)

    # preallocate elements:
    res = RG.group()
    x = RG.group()
    i_old = 0

    for (j,i) in Iterators.ProductIterator((indY, indX))
        if iszero(RG.pm[i,j])
            if i != i_old
                x = (twisted ? inv(RG[i]) : RG[i])
                i_old = i
            end
            RG.pm[i,j] = RG[AbstractAlgebra.mul!(res, x, RG[j])]
        end
    end

    return RG
end

function complete!(RG::GroupRing, limit::Integer; twisted::Bool=false, check::Bool=true)
    hasbasis(RG) || throw(ArgumentError("Provide basis for completion first!"))

    if !cachesmultiplication(RG)
        setcache!(RG, create_pm(RG.basis, RG.basis_dict, limit, twisted=twisted, check=false))
        # we check correctness below
    else
        complete!(RG, 1:limit, 1:limit; twisted=twisted)
    end

    check && @assert check_pm(RG.pm, RG.basis; twisted=twisted)

    return RG
end

function create_pm(basis::AbstractVector{T}, basis_dict::Dict{T, <:Integer},
    limit::Integer=length(basis); twisted::Bool=false, check::Bool=true) where T

    product_matrix = zeros(Int32, limit, limit)

    Threads.@threads for i in 1:size(product_matrix, 1)
        x = (twisted ? inv(basis[i]) : basis[i])
        res = parent(x)()
        for j in 1:size(product_matrix, 2)
            res = AbstractAlgebra.mul!(res, x, basis[j])
            product_matrix[i,j] = basis_dict[res]
        end
    end

    # exceptions in threaded code are not critical so we need to
    check && @assert check_pm(product_matrix, basis, twisted=twisted)

    return product_matrix
end

function check_pm(pm::Matrix{<:Integer}, basis::Vector; twisted::Bool=false)

    idx = (0,0)
    for i in 1:size(pm, 1), j in 1:size(pm,2)
        # @info "" i j
        if iszero(pm[i,j])
            idx = (i,j)
            break
        end
    end

    if idx == (0,0)
        return true
    else
        i,j = Tuple(idx)
        x = ifelse(twisted, inv(basis[i]), basis[i])
        @error "Product x*y is not supported on basis:" x y=basis[j]
        throw(KeyError(x*basis[j]))
    end
end
