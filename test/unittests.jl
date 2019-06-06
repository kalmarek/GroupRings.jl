using LinearAlgebra

@testset "Unit tests" begin
    R = AbstractAlgebra.zz
    G = PermGroup(4)

    RG = GroupRing(R, G, collect(G), halfradius_length=order(G))

    X = rand(RG, 0.2, -3:3)
    Y = rand(RG, 0.4, -1:1)
    g = rand(G)

    @testset "misc" begin
        @test RG[5] isa elem_type(G)
        @test RG[g] isa Integer

        @test length(RG) == order(G)

        @test eltype(X) == elem_type(base_ring(RG))
        @test size(X) == (order(G),)
        @test X[5] isa eltype(X)
        @test X[g] isa eltype(X)

        @test similar(X) isa GroupRingElem

        X[5] = 10
        @test X[5] == 10
        @test X[RG[5]] == 10

        @test !(GroupRings._dealias(X,X,Y) === X)
        @test !(GroupRings._dealias(Y,X,Y) === Y)
        @test GroupRings._dealias(X,Y,Y) === X

        X[5] = 0

        k = length(X.coeffs.nzind)
        dropzeros!(X)
        @test length(X.coeffs.nzind) < k
        @test norm(X, 4) isa Float64

        @test aug(X) isa Int
        @test supp(X) isa Vector{elem_type(G)}
        @test [RG[g] for g in supp(X)] == X.coeffs.nzind

        @test star(X) isa GroupRingElem

        X_star = star(X)
        for g in supp(X_star)
            @test X_star[g] == X[inv(g)]
        end
    end

    @testset "types & utilities" begin
        @test GroupRings.multiplicative_id(PermGroup(3)) == PermGroup(3)()
        M = MatrixAlgebra(AbstractAlgebra.zz, 3)
        @test GroupRings.multiplicative_id(M) == one(M)

        let RG = RG
            @test GroupRings._identity_idx(RG) == 1
            v = GroupRings._coerce_scalar(RG, big(5))
            @test v == RG(5)
            @test v[1] == 5
            @test v[2] == 0

            RG.basis[1], RG.basis[2] = RG.basis[2], RG.basis[1]
            RG.basis_dict = GroupRings.reverse_dict(RG.basis)

            @test GroupRings._identity_idx(RG) == 2
            v = GroupRings._coerce_scalar(RG, big(5))
            @test v == RG(5)
            @test v[1] == 0
            @test v[2] == 5

            @test change_base_ring(RG, AbstractAlgebra.RDF) isa GroupRing
            RRG = change_base_ring(RG, AbstractAlgebra.RDF)
            @test base_ring(RRG) == AbstractAlgebra.RDF
            @test change_base_ring(v, AbstractAlgebra.RDF) == RRG(5)

            @test GroupRings._identity_idx(RRG) == 2
        end

    end

    @testset "in-place arithmetic" begin
        let X = deepcopy(X)
            @test zero!(X) == zero(RG)
            @test X == zero(RG)
        end

        for (inplace_op, op) in [(AbstractAlgebra.mul!, *),
                               (AbstractAlgebra.add!, +)]
            let X = X, Y = Y
                @test inplace_op(X, X, Y) == op(X, Y)
                @test inplace_op(X, Y, X) == op(Y, X)

                Z = inplace_op(X, X, Y)
                @test Z == op(X, Y)

                Z = inplace_op(Z, Y, X)
                @test Z == op(Y, X)
            end
        end

        let X = X, Y = Y
            Z = deepcopy(X)
            Z = AbstractAlgebra.addeq!(Z,Y)
            @test Z == X+Y

            Z = deepcopy(X)
            Z = AbstractAlgebra.addmul!(Z, X, Y, similar(Z))
            @test Z == X + X*Y
        end
    end

    @testset "ad-hoc operators" begin
        @test GroupRings.scalarmul!(3, RG(1)) == RG(3)
        @test RG(3) == 3RG(1) == RG(1)*3

        @test addeq!(RG(1), 1) == RG(2)
        @test RG(1) + 3 == 3 + RG(1) == RG(4)

        @test addeq!(RG(1), g, 2.0) == 2RG(g) + RG(1)
        @test RG(2) + g == g + RG(2) == RG([G(), g], [2, 1])

        @test RG(g) - 1 == RG(g) + (-1)
        @test 1 - RG(g) == -RG(g) + 1

        let RG = change_base_ring(RG, AbstractAlgebra.qq)
            @test (RG(g)//3)[g] == 1//3
            @test base_ring(RG) == AbstractAlgebra.qq

            t = RG(g)/3
            @test t isa GroupRingElem
            @test t[g] == 1/3

            @test base_ring(RG) == AbstractAlgebra.qq
            @test base_ring(parent(t)) == AbstractAlgebra.RDF
            @test isapprox(RG(g)//3, t)
            @test RG(g) + t == 4t
        end
    end

    @testset "unsafe arithmetic on vectors" begin
        Z = X*Y
        @test AbstractAlgebra.mul!(X, X, Y).coeffs == GroupRings._mul!(X.coeffs, X.coeffs, Y.coeffs, RG.pm) == (X*Y).coeffs

        @test AbstractAlgebra.addmul!(deepcopy(X), X, Y).coeffs == GroupRings._addmul!(deepcopy(X).coeffs, X.coeffs, Y.coeffs, RG.pm) == (X + X*Y).coeffs
    end
end
