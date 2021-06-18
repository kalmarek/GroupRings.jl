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

