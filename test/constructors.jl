@testset "Algebra and Elements Constructors" begin
    G = SymmetricGroup(3)
    b = New.Basis{UInt8}(collect(G))
    l = length(b)

    RG = New.StarAlgebra(G, b, (l, l))

    a = rand(6)

    @test New.AlgebraElement(a, RG) isa New.AlgebraElement
    @test all(RG(g) isa New.AlgebraElement{typeof(RG)} for g in G)

    @test_throws AssertionError New.AlgebraElement([1,2,3], RG)
    @test New.AlgebraElement([1,2,3,0,0,0], RG) isa New.AlgebraElement

    p = G([2,3,1])
    a = RG(p)
    @test New.coeffs(a) isa SparseVector
    @test New.coeffs(a)[5] == 1
    @test all(New.coeffs(a)[i] == 0 for i in 1:6 if i ≠ 5)
    @test a(p) == 1
    @test all(a(g) == 0 for g in G if g != p)

    @test sprint(show, a) == "1·(1,2,3)"
    @test sprint(show, -a) == "-1·(1,2,3)"

    @test New.AlgebraElement([0,0,0,0,1,0], RG) == a

    @test New.supp(a) == [p]
    @test New.supp_ind(a) == [5]

    s = one(G)
    @test a(s) == 0

    a[s] = 2

    @test New.coeffs(a)[1] == 2
    @test a[1] == 2
    @test a(s) == 2

    @test New.supp(a) == [s, p]
    @test New.supp_ind(a) == [1, 5]

    @test sprint(show, a) == "2·() +1·(1,2,3)"
    @test sprint(show, -a) == "-2·() -1·(1,2,3)"
    @test sprint(show, New.AlgebraElement([2,0,0,0,-1,0], RG)) == "2·() -1·(1,2,3)"
end
