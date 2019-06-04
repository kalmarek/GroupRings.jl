using Test

using AbstractAlgebra
using GroupRings
using SparseArrays


@testset "Constructors: PermutationGroup" begin
    G = PermutationGroup(3)

    @test GroupRing(zz, G, collect(G)) isa AbstractAlgebra.NCRing
    @test GroupRing(zz, G, collect(G)) isa GroupRing

    RG = GroupRing(zz, G, collect(G))
    @test isdefined(RG, :basis)
    @test length(RG.basis) == 6
    @test length(RG) == 6
    @test isdefined(RG, :basis_dict)
    @test isdefined(RG, :pm) == false

    @test RG.basis_dict == GroupRings.reverse_dict(collect(G))

    @test GroupRing(zz, PermutationGroup(6), rand(1:6, 6,6)) isa GroupRing

    RG = GroupRing(zz, G, collect(G), halfradius_length=order(G))

    @test isdefined(RG, :pm)
    @test RG.pm == zeros(Int32, (6,6))

    @test GroupRings.complete!(RG) isa GroupRing
    @test all(RG.pm .> 0)
    S = collect(G)
    @test RG.pm == GroupRings.create_pm(S, GroupRings.reverse_dict(S))
    pm = GroupRings.create_pm(S, GroupRings.reverse_dict(S))
    @test GroupRing(zz, G, S) isa GroupRing
    @test GroupRing(zz, G, S, pm) isa GroupRing

    A = GroupRing(zz, G, S)
    B = GroupRing(zz, G, S, pm)
    C = GroupRing(zz, G, pm)

    @test RG == A
    @test RG == B
    @test RG == C

    A = GroupRing(qq, G, S)
    B = GroupRing(qq, G, S, pm)
    C = GroupRing(qq, G, pm)

    @test RG == A
    @test RG == B
    @test RG == C
end

@testset "Constructors FreeGroup" begin
    using Groups
    F = FreeGroup(3)
    S = gens(F)
    append!(S, [inv(s) for s in S])

    basis, sizes = Groups.generate_balls(S, F(), radius=4)
    d = GroupRings.reverse_dict(basis)
    @test_throws KeyError GroupRings.create_pm(basis, d)
    pm = GroupRings.create_pm(basis, d, sizes[2], check=false)
    @test findfirst(iszero, pm) == nothing

    @test GroupRing(zz, F, pm) isa GroupRing
    @test GroupRing(zz, F, basis, d, pm) isa GroupRing

    A = GroupRing(zz, F, pm)
    B = GroupRing(zz, F, basis, d, pm)
    @test A == B

    RF = GroupRing(zz, F, basis, d, GroupRings.create_pm(basis, d, check=false))
    nz1 = count(!iszero, RF.pm)
    @test nz1 > 1000

    GroupRings.complete!(RF, sizes[2], check=false)

    @test_throws KeyError GroupRings.check_pm(RF.pm, RF.basis)
    err = try
        GroupRings.check_pm(RF.pm, RF.basis)
    catch err
        err
    end
    err.key
    @test err.key == RF[2]^5

    @test findfirst(iszero, RF.pm[1:sizes[2], 1:sizes[2]]) == nothing
    nz2 = count(!iszero, RF.pm)
    @test nz2 > nz1
    @test nz2 == 2420


    g = B()
    s = S[2]
    g[s] = 1
    @test g == B(s)
    @test g[s^2] == 0
    @test_throws KeyError g[s^10]
end

@testset "GroupRingElems constructors/basic manipulation" begin
    G = PermutationGroup(3)
    RG = GroupRing(zz, G, collect(G), halfradius_length=order(G))
    a = rand(-10:10, 6)

    @test isa(GroupRingElem(a, RG), GroupRingElem)
    @test isa(RG(a), GroupRingElem)

    @test all(isa(RG(g), GroupRingElem) for g in G)

    @test_throws DomainError GroupRingElem([1,2,3], RG)
    @test isa(RG(G([2,3,1])), GroupRingElem)
    p = G([2,3,1])
    a = RG(p)
    @test length(a.coeffs) == 6
    @test isa(a.coeffs, SparseVector)
    @test supp(a) == [p]

    @test a.coeffs[5] == 1
    @test a[5] == 1
    @test a[p] == 1

    @test string(a) == "1(1,2,3)"
    @test string(-a) == " - 1(1,2,3)"

    @test RG([0,0,0,0,1,0]) == a

    s = G([1,2,3])
    @test a[s] == 0
    a[s] = -2

    @test a.coeffs[1] == -2
    @test a[1] == -2
    @test a[s] == -2

    @test string(a) == " - 2() + 1(1,2,3)"
    @test string(-a) == "2() - 1(1,2,3)"

    @test length(supp(a)) == 2
    @test supp(a) == [G(), G([2,3,1])]
end

@testset "Arithmetic" begin
    G = PermutationGroup(3)
    RG = GroupRing(zz, G, collect(G), halfradius_length=order(G))
    a = RG(ones(Int, order(G)))

    @testset "scalar operators" begin

        @test -a isa GroupRingElem
        @test (-a).coeffs == -(a.coeffs)

        @test 2*a isa GroupRingElem
        @test eltype(2*a) == typeof(2)
        @test (2*a).coeffs == 2 .*(a.coeffs)

        wt(c) = "Coefficient ring does not contain scalar $c.\nThe result has coefficients in $(parent(c)) of type $(elem_type(parent(c)))."

        @test 2.0*a isa GroupRingElem
        @test_logs (:warn, wt(2.0)) eltype(2.0*a) == typeof(2.0)
        @test_logs (:warn, wt(2.0)) (2.0*a).coeffs == 2.0.*(a.coeffs)

        @test_logs (:warn, wt(0.5)) (a/2).coeffs == a.coeffs./2
        b = a/2
        @test b isa GroupRingElem
        @test eltype(b) == typeof(1/2)
        @test (b/2).coeffs == 0.25*(a.coeffs)

        @test parent(b) == parent(a)
        @test base_ring(parent(b)) == AbstractAlgebra.RDF

        @test change_base_ring(parent(a), qq) isa GroupRing
        QG = change_base_ring(parent(a), qq)
        @test QG(a) == change_base_ring(a, qq)
        aq = change_base_ring(a, qq)
        @test eltype(aq) == elem_type(qq)
        @test aq.coeffs == convert(Vector{elem_type(qq)}, a.coeffs)

        @test aq//4 isa GroupRingElem
        @test eltype(aq//4) == elem_type(qq)

        @test_logs (:warn, wt(big(1//4))) aq//big(4) isa GroupRingElem

        @test_logs (:warn, wt(big(1//4))) eltype(b//(big(4)//1)) == Rational{BigInt}

        @test_logs (:warn, wt(1//1)) a//1 isa GroupRingElem

        @test_logs (:warn, wt(1//1)) eltype(a//1) == Rational{Int}
        af = change_base_ring(a, AbstractAlgebra.RDF)
        @test aq == af
    end

    @testset "Additive structure" begin
        @test RG(ones(Int, order(G))) == sum(RG(g) for g in G)
        a = RG(ones(Int, order(G)))
        b = sum((-1)^parity(g)*RG(g) for g in G)
        @test 1/2*(a+b).coeffs == [1.0, 0.0, 1.0, 0.0, 1.0, 0.0]

        a = RG(1) + RG(perm"(2,3)") + RG(perm"(1,2,3)")
        @test a == RG(1) + perm"(2,3)" + perm"(1,2,3)"
        @test a == perm"(2,3)" + (perm"(1,2,3)" + RG(1))

        b = RG(1) - RG(perm"(1,2)(3)") - RG(perm"(1,2,3)")
        @test b == RG(1) - perm"(1,2)(3)" - perm"(1,2,3)"
        @test b == -(perm"(1,2)(3)" - RG(1)) - perm"(1,2,3)"

        @test a - b == RG() + perm"(2,3)" + perm"(1,2)(3)" + 2RG(perm"(1,2,3)")

        @test 1//2*2a == a
        @test a + 2a == (3//1)*a
        @test 2a - (1//1)*a == a
    end

    @testset "Multiplicative structure" begin
        for g in G, h in G
            a = RG(g)
            b = RG(h)
            @test a*b == RG(g*h)
            @test (a+b)*(a+b) == a*a + a*b + b*a + b*b
        end

        for g in G
            @test star(RG(g)) == RG(inv(g))
            @test (RG(1) - g) * star(RG(1) - g) == RG(2) - g - inv(g)
            @test aug(RG(1) - g) == 0
        end

        a = RG(1) + perm"(2,3)" + perm"(1,2,3)"
        b = RG(1) - perm"(1,2)(3)" - perm"(1,2,3)"

        @test a*b == AbstractAlgebra.mul!(a,a,b)

        @test aug(a) == 3
        @test aug(b) == -1
        @test aug(a)*aug(b) == aug(a*b) == aug(b*a)

        z = sum((one(RG) - g)*star(one(RG) - g) for g in G)
        @test aug(z) == 0

        @test supp(z) == parent(z).basis
        @test supp(RG(1) + RG(perm"(2,3)")) == [G(), perm"(2,3)"]
        @test supp(a) == [perm"(3)", perm"(2,3)", perm"(1,2,3)"]
    end

    @testset "HPC multiplicative operations" begin

        G = PermutationGroup(6)
        RG = GroupRing(zz, G, collect(G), halfradius_length=order(G))
        RG2 = GroupRing(zz, G, collect(G), halfradius_length=order(G))

        Z = RG()
        W = RG()

        for g in [rand(G) for _ in 1:30]
            X = RG(g)
            Y = -RG(inv(g))
            for i in 1:10
                X[rand(G)] += rand(1:3)
                Y[rand(G)] -= rand(1:3)
            end

            @test X*Y ==
            RG2(X)*RG2(Y) ==
            GroupRings.mul!(Z, X, Y)

            @test Z.coeffs ==
                GroupRings._mul!(W.coeffs, X.coeffs, Y.coeffs, RG.pm) ==
                W.coeffs
            @test (2*X*Y).coeffs ==
                GroupRings._addmul!(W.coeffs, X.coeffs, Y.coeffs, RG.pm) ==
                GroupRings.scalarmul!(2, X*Y).coeffs
        end
    end
end

@testset "SumOfSquares in group rings" begin
    ∗ = star
    GroupRings.star(g::GroupElem) = inv(g)

    G = FreeGroup(["g", "h", "k", "l"])
    S = G.(G.gens)
    S = [S; inv.(S)]

    ID = G()
    RADIUS=3
    @time E_R, sizes = Groups.generate_balls(S, ID, radius=2*RADIUS);
    @test sizes == [9, 65, 457, 3201, 22409, 156865]
    E_rdict = GroupRings.reverse_dict(E_R)
    pm = GroupRings.create_pm(E_R, E_rdict, sizes[RADIUS]; twisted=true);
    RG = GroupRing(zz, G, E_R, E_rdict, pm)

    g, h, k, l = [RG[i] for i in 2:5]
    G = (RG(1)- g)
    @test G^2 == RG(2) - g - ∗(g)

    G, H, K, L = [RG(1) - elt for elt in (g,h,k,l)]
    GH = RG(1) - g*h
    KL = RG(1) - k*l

    X = RG(2) - ∗(g) - h
    Y = RG(2) - ∗(g*h) - k

    @test -(RG(2) - g*h - ∗(g*h)) + 2G^2 + 2H^2 == X^2
    @test RG(2) - g*h - ∗(g*h) == GH^2
    @test -(RG(2) - g*h*k - ∗(g*h*k)) + 2GH^2 + 2K^2 == Y^2
    @test -(RG(2) - g*h*k - ∗(g*h*k)) +
    2(GH^2 - 2G^2 - 2H^2) +
    4G^2 + 4H^2 + 2K^2 ==
    Y^2

    @test GH^2 - 2G^2 - 2H^2 == - X^2
    @test -(RG(2) - g*h*k - ∗(g*h*k)) + 4G^2 + 4H^2 + 2K^2 == 2X^2 + Y^2

    @test GH^2 == 2G^2 + 2H^2 - (RG(2) - ∗(g) - h)^2
    @test KL^2 == 2K^2 + 2L^2 - (RG(2) - ∗(k) - l)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2*GH^2 +
    2*KL^2 ==
    (RG(2) - ∗(g*h) - k*l)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2(2G^2 + 2H^2 - (RG(2) - ∗(g) - h)^2) +
    2(2K^2 + 2L^2 - (RG(2) - ∗(k) - l)^2) ==
    (RG(2) - ∗(g*h) - k*l)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2(2G^2 + 2H^2) +
    2(2K^2 + 2L^2) ==
    (RG(2) - ∗(g*h) - k*l)^2 +
    2(RG(2) - ∗(g)   - h  )^2 +
    2(RG(2) - ∗(k)   - l  )^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2(RG(2) - ∗(g*h*k) - g*h*k) +
    2L^2 ==
    (RG(2) - ∗(g*h*k) - l)^2

    @test RG(2) - ∗(g*h*k) - g*h*k ==
    2GH^2 + 2K^2 - (RG(2) - ∗(g*h) - k)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2(2GH^2 + 2K^2 - (RG(2) - ∗(g*h) - k)^2) + 2L^2 ==
    (RG(2) - ∗(g*h*k) - l)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2(2GH^2 + 2K^2) +  2L^2 ==
    (RG(2) - ∗(g*h*k) - l)^2 +
    2(RG(2) - ∗(g*h)   - k)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    8G^2 + 8H^2 + 4K^2 + 2L^2 ==
    (RG(2) - ∗(g*h*k) - l)^2 +
    2(RG(2) - ∗(g*h)   - k)^2 +
    4(RG(2) - ∗(g)     - h)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2GH^2 +
    2KL^2 ==
    (RG(2) - ∗(g*h) - k*l)^2

    @test -(RG(2) - ∗(g*h*k*l) - g*h*k*l) +
    2(2G^2 + 2H^2) + 2(2K^2 + 2L^2) ==
    (RG(2) - ∗(g*h) - k*l)^2 +
    2(RG(2) - ∗(k) - l)^2 + 2(RG(2) - ∗(g) - h)^2
end
