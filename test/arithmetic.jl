@testset "Arithmetic" begin
    G = SymmetricGroup(3)
    b = New.Basis{UInt8}(collect(G))
    l = length(b)
    RG = New.StarAlgebra(G, b, (l,l))

    @testset "Module structure" begin
        a = New.AlgebraElement(ones(Int, order(G)), RG)

        @test -a isa New.AlgebraElement
        @test New.coeffs(-a) == -New.coeffs(a)

        @test 2*a isa New.AlgebraElement
        @test eltype(2*a) == typeof(2)
        @test New.coeffs(2*a) == 2New.coeffs(a)

        @test 2.0*a isa New.AlgebraElement
        @test eltype(2.0*a) == typeof(2.0)
        @test New.coeffs(2.0*a) == 2.0*New.coeffs(a)

        @test New.coeffs(a/2) == New.coeffs(a)/2
        b = a/2
        @test b isa New.AlgebraElement
        @test eltype(b) == typeof(1/2)
        @test New.coeffs(b/2) == 0.25*New.coeffs(a)

        c = a//1

        @test eltype(c) == Rational{Int}
        @test c//4 isa New.AlgebraElement
        @test c//big(4) isa New.AlgebraElement
        @test eltype(c//(big(4)//1)) == Rational{BigInt}

        @test (1.0a)*1//2 == (0.5a) == c//2
    end

    @testset "Additive structure" begin
        a = New.AlgebraElement(ones(Int, order(G)), RG)
        b = sum(sign(g)*RG(g) for g in G)

        @test a == New.AlgebraElement(ones(Int, order(G)), RG) == sum(RG(g) for g in G)

        @test 1/2*(a+b).coeffs == [1.0, 0.0, 1.0, 0.0, 1.0, 0.0]

        a = RG(1) + RG(perm"(2,3)") + RG(perm"(1,2,3)")
        b = RG(1) - RG(perm"(1,2)(3)") - RG(perm"(1,2,3)")

        @test a - b == RG(perm"(2,3)") + RG(perm"(1,2)(3)") + 2RG(perm"(1,2,3)")

        @test a + b - 2a == b - a

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
            @test New.star(RG(g)) == RG(inv(g))
            @test (one(RG)-RG(g))*New.star(one(RG)-RG(g)) ==
            2*one(RG) - RG(g) - RG(inv(g))
            @test New.aug(one(RG) - RG(g)) == 0
        end

        a = RG(1) + RG(perm"(2,3)") + RG(perm"(1,2,3)")
        b = RG(1) - RG(perm"(1,2)(3)") - RG(perm"(1,2,3)")

        @test a*b == New.mul!(a,a,b)

        @test New.aug(a) == 3
        @test New.aug(b) == -1
        @test New.aug(a)*New.aug(b) == New.aug(a*b) == New.aug(b*a)

        z = sum((one(RG)-RG(g))*New.star(one(RG)-RG(g)) for g in G)
        @test New.aug(z) == 0

        @test New.supp(z) == New.basis(parent(z))
        @test New.supp(RG(1) + RG(perm"(2,3)")) == [one(G), perm"(2,3)"]
        @test New.supp(a) == [perm"(3)", perm"(2,3)", perm"(1,2,3)"]

        @testset "Projections in Symm(3)" begin
            G = SymmetricGroup(3)
            b = New.Basis{UInt8}(collect(G))
            l = length(b)

            RG = New.StarAlgebra(G, b)
            @test RG isa New.StarAlgebra

            P = sum(RG(g) for g in b) // l
            @test P * P == P

            P3 = 2 * sum(RG(g) for g in b if sign(g) > 0) // l
            @test P3 * P3 == P3

            PAlt = sum(sign(g) * RG(g) for g in b) // l
            @test PAlt * PAlt == PAlt

            @test P3 * PAlt == PAlt * P3

            P2 = (RG(1) + RG(b[2])) // 2
            @test P2 * P2 == P2

            @test P2 * P3 == P3 * P2 == P

            P2m = (RG(1) - RG(b[2])) // 2
            @test P2m * P2m == P2m

            @test P2m * P3 == P3 * P2m == PAlt
            @test iszero(P2m * P2)
        end
    end

    @testset "Mutable API and trivial mstructure" begin

        G = SymmetricGroup(5)
        b = New.Basis{UInt8}(collect(G))

        RG = New.StarAlgebra(G, b)
        l = order(Int, G)
        RGc = New.StarAlgebra(G, b, (l, l))

        @test all(RG.mstructure .== RGc.mstructure)

        Z = zero(RGc)
        W = zero(RGc)

        for g in [rand(G) for _ in 1:30]
            X = RG(g)
            Y = -RG(inv(g))
            for i in 1:10
                X[rand(G)] += rand(1:3)
                Y[rand(G)] -= rand(1:3)
            end

            Xc = New.AlgebraElement(New.coeffs(X), RGc)
            Yc = New.AlgebraElement(New.coeffs(Y), RGc)

            @test New.coeffs(X*Y) ==
            New.coeffs(Xc*Yc) == New.coeffs(New.mul!(Z, X, Y))

            @test Z.coeffs == New.mul!(W.coeffs, X.coeffs, Y.coeffs, RG.mstructure)
            @test Z.coeffs == W.coeffs
            @test Z.coeffs == New.mul!(W.coeffs, X.coeffs, Y.coeffs, RGc.mstructure)
            @test Z.coeffs == W.coeffs

            New.zero!(W)

            @test New.coeffs((2*X*Y)) ==
            (New.fmac!(W.coeffs, X.coeffs, Y.coeffs, RG.mstructure); New.coeffs(New.mul!(W, W, 2)))
        end
    end
end
