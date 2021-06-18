using Groups

@testset "FreeGroup algebra" begin
    New.star(g::Groups.New.GroupElement) = inv(g)
    F = Groups.New.FreeGroup(4)
    S = [gens(F); inv.(gens(F))]

    ID = one(F)
    RADIUS=3
    @time E_R, sizes = Groups.wlmetric_ball(S, ID, radius=2*RADIUS);
    @test sizes == [9, 65, 457, 3201, 22409, 156865]

    b = New.Basis{UInt32}(E_R)

    @testset "MTables" begin
        mstr = New.MTable{false}(b, table_size=(sizes[RADIUS], sizes[RADIUS]))

        @test mstr isa New.MTable{UInt32, false}
        @test all(mstr[i,i]≠1 for i in 2:size(mstr, 1))
        @test all(mstr[1,i]==i for i in 1:size(mstr, 2))
        @test all(mstr[i,1]==i for i in 1:size(mstr, 1))

        tmstr = New.MTable{true}(b, table_size=(sizes[RADIUS], sizes[RADIUS]))

        @test tmstr isa New.MTable{UInt32, true}
        @test all(tmstr[i,i]==1 for i in 1:size(tmstr, 1))
        @test all(tmstr[1,i]==i for i in 1:size(tmstr, 2))
        @test all(tmstr[i,1]≠ i for i in 2:size(tmstr, 1))
    end

    tmstr = New.MTable{true}(b, table_size=(sizes[RADIUS], sizes[RADIUS]))

    RG = New.StarAlgebra(F, b, tmstr)

    g, h, k, l = S[1:4]

    length(b)

    G = (one(RG)-RG(g))
    G
    @test G^2 == New.mul!(zero(G), G, G) == 2one(RG) - RG(g) - New.star(RG(g))
    @test New.star(G*G) == G*G

    @testset "Sums of hermitian squares" begin
        ∗ = New.star

        𝕀 = one(RG)

        G  = (𝕀 - RG(g))
        H  = (𝕀 - RG(h))
        K  = (𝕀 - RG(k))
        L  = (𝕀 - RG(l))
        GH = (𝕀 - RG(g*h))
        KL = (𝕀 - RG(k*l))

        X = (2𝕀 - ∗(RG(g)) - RG(h))
        Y = (2𝕀 - ∗(RG(g*h)) - RG(k))



        @test -(2𝕀 - RG(g*h) - ∗(RG(g*h))) + 2G^2 + 2H^2 == X^2
        @test  (2𝕀 - RG(g*h) - ∗(RG(g*h))) == GH^2
        @test -(2𝕀 - RG(g*h*k) - ∗(RG(g*h*k))) + 2GH^2 + 2K^2 == Y^2
        @test -(2𝕀 - RG(g*h*k) - ∗(RG(g*h*k))) +
           2(GH^2 - 2G^2 - 2H^2) +
           4G^2 + 4H^2 + 2K^2 ==
              Y^2

        @test GH^2 - 2G^2 - 2H^2 == - X^2
        @test -(2𝕀 - RG(g*h*k) - ∗(RG(g*h*k))) + 4G^2 + 4H^2 + 2K^2 == 2X^2 + Y^2

        @test GH^2 == 2G^2 + 2H^2 - (2𝕀 - ∗(RG(g)) - RG(h))^2
        @test KL^2 == 2K^2 + 2L^2 - (2𝕀 - ∗(RG(k)) - RG(l))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) + 2*GH^2 + 2*KL^2 ==
           (2𝕀 - ∗(RG(g*h)) - RG(k*l))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           2(2G^2 + 2H^2 - (2𝕀 - ∗(RG(g)) - RG(h))^2) +
           2(2K^2 + 2L^2 - (2𝕀 - ∗(RG(k)) - RG(l))^2) ==
              (2𝕀 - ∗(RG(g*h)) - RG(k*l))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           2(2G^2 + 2H^2) +
           2(2K^2 + 2L^2) ==
              (2𝕀 - ∗(RG(g*h)) - RG(k*l))^2 +
              2(2𝕀 - ∗(RG(g)) - RG(h))^2 +
              2(2𝕀 - ∗(RG(k)) - RG(l))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           2(2𝕀 - ∗(RG(g*h*k)) - RG(g*h*k)) + 2L^2 ==
              (2𝕀 - ∗(RG(g*h*k)) - RG(l))^2

        @test 2𝕀 - ∗(RG(g*h*k)) - RG(g*h*k) ==
           2GH^2 + 2K^2 - (2𝕀 - ∗(RG(g*h)) - RG(k))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           2(2GH^2 + 2K^2 - (2𝕀 - ∗(RG(g*h)) - RG(k))^2) + 2L^2 ==
              (2𝕀 - ∗(RG(g*h*k)) - RG(l))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           2(2GH^2 + 2K^2) +  2L^2 ==
              (2𝕀 - ∗(RG(g*h*k)) - RG(l))^2 +
              2(2𝕀 - ∗(RG(g*h)) - RG(k))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           8G^2 + 8H^2 + 4K^2 + 2L^2 ==
              (2𝕀 - ∗(RG(g*h*k)) - RG(l))^2 + 2(2𝕀 - ∗(RG(g*h)) - RG(k))^2 + 4(2𝕀 - ∗(RG(g)) - RG(h))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
           2GH^2 + 2KL^2 == (2𝕀 - ∗(RG(g*h)) - RG(k*l))^2

        @test -(2𝕀 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) + 2(2G^2 + 2H^2) + 2(2K^2 + 2L^2) ==
           (2𝕀 - ∗(RG(g*h)) - RG(k*l))^2 + 2(2𝕀 - ∗(RG(k)) - RG(l))^2 + 2(2𝕀 - ∗(RG(g)) - RG(h))^2

    end
end
