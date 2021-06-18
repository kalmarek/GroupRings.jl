@testset "CachedMTable" begin
    elts = collect(SymmetricGroup(3))
    b = New.Basis{UInt8}(elts)

    mstr = New.CachedMTable{false}(b)
    @test all(iszero, mstr.table)
    New.cache!(mstr, 1, 2)
    @test mstr.table[1, 2] == 2
    @test mstr.table[1, 1] == 0

    @test mstr.table[2, 3] == 0
    @test mstr[2, 3] == 4
    @test mstr.table[2, 3] == 4

    @test b[b[2]*b[3]] == 4


    @test mstr.table[1, 3] == 0
    @test mstr.table[1, 4] == 0
    New.cache!(mstr, [1], [3, 4])
    @test mstr.table[1, 3] != 0
    @test mstr.table[1, 4] != 0


    tmstr = New.CachedMTable{true}(b)

    @test all(iszero, tmstr.table)
    @test tmstr[1, 2] == 2
    @test tmstr[2, 3] == 4
    @test tmstr[3, 2] == b[inv(b[3])*b[2]]
end

@testset "Group Algebra caching" begin
    G = SymmetricGroup(3)
    b = New.Basis{UInt8}(collect(G))
    l = length(b)

    RG = New.StarAlgebra(G, b, (l, l))
    @test RG isa New.StarAlgebra

    D = ((l + 1) * one(RG) - sum(RG(g) for g in b)) // 6
    @test D isa New.AlgebraElement
    g = RG(b[1])
    @test isone(g)
    @test one(RG) == g
    @test iszero(zero(RG))
    @test 0 * g == zero(RG)
    @test iszero(0 * g)

    h = RG(b[3])

    @test D * one(RG) == D

    @test all(New.supp(D) .== b)

    @test one(RG) * D == D
    @test any(iszero, RG.mstructure.table)

    @test D * D isa New.AlgebraElement

    @test all(!iszero, RG.mstructure.table)
end
