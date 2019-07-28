using Test

using AbstractAlgebra
using GroupRings
using SparseArrays


@testset "GroupRings" begin
   @testset "Constructors: PermutationGroup" begin
      G = PermutationGroup(3)

      @test isa(GroupRing(G), AbstractAlgebra.NCRing)
      @test isa(GroupRing(G), GroupRing)

      RG = GroupRing(G)
      @test isdefined(RG, :basis) == true
      @test length(RG.basis) == 6
      @test isdefined(RG, :basis_dict) == true
      @test isdefined(RG, :pm) == false

      @test isa(GroupRing(PermutationGroup(6), rand(1:6, 6,6)), GroupRing)

      RG = GroupRing(G, cachedmul=true)
      @test isdefined(RG, :pm) == true
      @test RG.pm == zeros(Int, (6,6))

      @test isa(complete!(RG), GroupRing)
      @test all(RG.pm .> 0)
      @test RG.pm == GroupRings.initializepm!(GroupRing(G, cachedmul=false), fill=true).pm

      @test RG.basis_dict == GroupRings.reverse_dict(collect(G))

      @test isa(GroupRing(G, collect(G)), GroupRing)
      S = collect(G)
      pm = create_pm(S)
      @test isa(GroupRing(G, S), GroupRing)
      @test isa(GroupRing(G, S, pm), GroupRing)

      A = GroupRing(G, S)
      B = GroupRing(G, S, pm)

      @test RG == A
      @test RG == B
   end

   @testset "GroupRing constructors FreeGroup" begin
      using Groups
      F = FreeGroup(3)
      S = gens(F)
      append!(S, [inv(s) for s in S])

      basis, sizes = Groups.generate_balls(S, F(), radius=4)
      d = GroupRings.reverse_dict(basis)
      @test_throws KeyError create_pm(basis)
      pm = create_pm(basis, d, sizes[2])

      @test isa(GroupRing(F, basis, pm), GroupRing)
      @test isa(GroupRing(F, basis, d, pm), GroupRing)

      A = GroupRing(F, basis, pm)
      B = GroupRing(F, basis, d, pm)
      @test A == B

      RF = GroupRing(F, basis, d, create_pm(basis, d, check=false))
      nz1 = count(!iszero, RF.pm)
      @test nz1 > 1000

      GroupRings.complete!(RF)
      nz2 = count(!iszero, RF.pm)
      @test nz2 > nz1
      @test nz2 == 45469

      g = B()
      s = S[2]
      g[s] = 1
      @test g == B(s)
      @test g[s^2] == 0
      @test_throws KeyError g[s^10]
   end

   @testset "GroupRingElems constructors/basic manipulation" begin
      G = PermutationGroup(3)
      RG = GroupRing(G, cachedmul=true)
      a = rand(6)
      @test isa(GroupRingElem(a, RG), GroupRingElem)
      @test isa(RG(a), GroupRingElem)

      @test all(isa(RG(g), GroupRingElem) for g in G)

      @test_throws String GroupRingElem([1,2,3], RG)
      @test isa(RG(G([2,3,1])), GroupRingElem)
      p = G([2,3,1])
      a = RG(p)
      @test length(a) == 1
      @test isa(a.coeffs, SparseVector)

      @test a.coeffs[5] == 1
      @test a[5] == 1
      @test a[p] == 1

      @test string(a) == "(1,2,3)"
      @test string(-a) == " - 1(1,2,3)"

      @test RG([0,0,0,0,1,0]) == a

      s = G([1,2,3])
      @test a[s] == 0
      a[s] = 2

      @test a.coeffs[1] == 2
      @test a[1] == 2
      @test a[s] == 2

      @test string(a) == "2() + (1,2,3)"
      @test string(-a) == " - 2() - 1(1,2,3)"

      @test length(a) == 2

      @testset "RSL(3,Z)" begin
         N = 3
         halfradius = 2
         M = MatrixAlgebra(zz, N)
         E(M, i,j) = (e_ij = one(M); e_ij[i,j] = 1; e_ij)
         S = [E(M, i,j) for i in 1:N for j in 1:N if i≠j]
         S = unique([S; inv.(S)])
         E_R, sizes = Groups.generate_balls(S, radius=2*halfradius)
         E_rdict = GroupRings.reverse_dict(E_R)
         pm = GroupRings.create_pm(E_R, E_rdict, sizes[halfradius]; twisted=true);

         @test GroupRing(M, E_R, E_rdict, pm) isa GroupRing
      end
   end

   @testset "Arithmetic" begin
      G = PermutationGroup(3)
      RG = GroupRing(G, cachedmul=true)
      a = RG(ones(Int, order(G)))

      @testset "scalar operators" begin

         @test isa(-a, GroupRingElem)
         @test (-a).coeffs == -(a.coeffs)

         @test isa(2*a, GroupRingElem)
         @test eltype(2*a) == typeof(2)
         @test (2*a).coeffs == 2 .*(a.coeffs)

         ww = "Scalar and coeffs are in different rings! Promoting result to Float64"

         @test isa(2.0*a, GroupRingElem)
         @test_logs (:warn, ww) eltype(2.0*a) == typeof(2.0)
         @test_logs (:warn, ww) (2.0*a).coeffs == 2.0.*(a.coeffs)

         @test_logs (:warn, ww) (a/2).coeffs == a.coeffs./2
         b = a/2
         @test isa(b, GroupRingElem)
         @test eltype(b) == typeof(1/2)
         @test (b/2).coeffs == 0.25*(a.coeffs)

         @test isa(convert(Rational{Int}, a), GroupRingElem)
         @test eltype(convert(Rational{Int}, a)) == Rational{Int}
         @test convert(Rational{Int}, a).coeffs ==
            convert(Vector{Rational{Int}}, a.coeffs)

         b = convert(Rational{Int}, a)

         @test isa(b//4, GroupRingElem)
         @test eltype(b//4) == Rational{Int}

         @test isa(b//big(4), NCRingElem)
         @test eltype(b//(big(4)//1)) == Rational{BigInt}

         @test isa(a//1, GroupRingElem)
         @test eltype(a//1) == Rational{Int}
         @test (1.0a)//1 == (1.0a)

      end

      @testset "Additive structure" begin
         @test RG(ones(Int, order(G))) == sum(RG(g) for g in G)
         a = RG(ones(Int, order(G)))
         b = sum((-1)^parity(g)*RG(g) for g in G)
         @test 1/2*(a+b).coeffs == [1.0, 0.0, 1.0, 0.0, 1.0, 0.0]

         a = RG(1) + RG(perm"(2,3)") + RG(perm"(1,2,3)")
         b = RG(1) - RG(perm"(1,2)(3)") - RG(perm"(1,2,3)")

         @test a - b == RG(perm"(2,3)") + RG(perm"(1,2)(3)") + 2RG(perm"(1,2,3)")

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
            @test (one(RG)-RG(g))*star(one(RG)-RG(g)) ==
               2*one(RG) - RG(g) - RG(inv(g))
            @test aug((one(RG)-RG(g))) == 0
         end

         a = RG(1) + RG(perm"(2,3)") + RG(perm"(1,2,3)")
         b = RG(1) - RG(perm"(1,2)(3)") - RG(perm"(1,2,3)")

         @test a*b == mul!(a,a,b)

         @test aug(a) == 3
         @test aug(b) == -1
         @test aug(a)*aug(b) == aug(a*b) == aug(b*a)

         z = sum((one(RG)-RG(g))*star(one(RG)-RG(g)) for g in G)
         @test aug(z) == 0

         @test supp(z) == parent(z).basis
         @test supp(RG(1) + RG(perm"(2,3)")) == [G(), perm"(2,3)"]
         @test supp(a) == [perm"(3)", perm"(2,3)", perm"(1,2,3)"]

      end

      @testset "HPC multiplicative operations" begin

         G = PermutationGroup(5)
         RG = GroupRing(G, cachedmul=true)
         RG2 = GroupRing(G, cachedmul=false)

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

            @test Z.coeffs == GroupRings.GRmul!(W.coeffs, X.coeffs, Y.coeffs, RG.pm) == W.coeffs
            @test (2*X*Y).coeffs ==
               GroupRings.fmac!(W.coeffs, X.coeffs, Y.coeffs, RG.pm) ==
               GroupRings.mul!(2, X*Y).coeffs
         end
      end
   end

   @testset "SumOfSquares in group rings" begin
      ∗ = star

      G = FreeGroup(["g", "h", "k", "l"])
      S = G.(G.gens)
      S = [S; inv.(S)]

      ID = G()
      RADIUS=3
      @time E_R, sizes = Groups.generate_balls(S, ID, radius=2*RADIUS);
      @test sizes == [9, 65, 457, 3201, 22409, 156865]
      E_rdict = GroupRings.reverse_dict(E_R)
      pm = GroupRings.create_pm(E_R, E_rdict, sizes[RADIUS]; twisted=true);
      RG = GroupRing(G, E_R, E_rdict, pm)

      g = RG.basis[2]
      h = RG.basis[3]
      k = RG.basis[4]
      l = RG.basis[5]
      G = (1-RG(g))
      @test G^2 == 2 - RG(g) - ∗(RG(g))

      G = (1-RG(g))
      H = (1-RG(h))
      K = (1-RG(k))
      L = (1-RG(l))
      GH = (1-RG(g*h))
      KL = (1-RG(k*l))

      X = (2 - ∗(RG(g)) - RG(h))
      Y = (2 - ∗(RG(g*h)) - RG(k))

      @test -(2 - RG(g*h) - ∗(RG(g*h))) + 2G^2 + 2H^2 == X^2
      @test (2 - RG(g*h) - ∗(RG(g*h))) == GH^2
      @test -(2 - RG(g*h*k) - ∗(RG(g*h*k))) + 2GH^2 + 2K^2 == Y^2
      @test -(2 - RG(g*h*k) - ∗(RG(g*h*k))) +
         2(GH^2 - 2G^2 - 2H^2) +
         4G^2 + 4H^2 + 2K^2 ==
            Y^2

      @test GH^2 - 2G^2 - 2H^2 == - X^2
      @test -(2 - RG(g*h*k) - ∗(RG(g*h*k))) + 4G^2 + 4H^2 + 2K^2 == 2X^2 + Y^2

      @test GH^2 == 2G^2 + 2H^2 - (2 - ∗(RG(g)) - RG(h))^2
      @test KL^2 == 2K^2 + 2L^2 - (2 - ∗(RG(k)) - RG(l))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) + 2*GH^2 + 2*KL^2 ==
         (2 - ∗(RG(g*h)) - RG(k*l))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         2(2G^2 + 2H^2 - (2 - ∗(RG(g)) - RG(h))^2) +
         2(2K^2 + 2L^2 - (2 - ∗(RG(k)) - RG(l))^2) ==
            (2 - ∗(RG(g*h)) - RG(k*l))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         2(2G^2 + 2H^2) +
         2(2K^2 + 2L^2) ==
            (2 - ∗(RG(g*h)) - RG(k*l))^2 +
            2(2 - ∗(RG(g)) - RG(h))^2 +
            2(2 - ∗(RG(k)) - RG(l))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         2(2 - ∗(RG(g*h*k)) - RG(g*h*k)) + 2L^2 ==
            (2 - ∗(RG(g*h*k)) - RG(l))^2

      @test 2 - ∗(RG(g*h*k)) - RG(g*h*k) ==
         2GH^2 + 2K^2 - (2 - ∗(RG(g*h)) - RG(k))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         2(2GH^2 + 2K^2 - (2 - ∗(RG(g*h)) - RG(k))^2) + 2L^2 ==
            (2 - ∗(RG(g*h*k)) - RG(l))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         2(2GH^2 + 2K^2) +  2L^2 ==
            (2 - ∗(RG(g*h*k)) - RG(l))^2 +
            2(2 - ∗(RG(g*h)) - RG(k))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         8G^2 + 8H^2 + 4K^2 + 2L^2 ==
            (2 - ∗(RG(g*h*k)) - RG(l))^2 + 2(2 - ∗(RG(g*h)) - RG(k))^2 + 4(2 - ∗(RG(g)) - RG(h))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) +
         2GH^2 + 2KL^2 == (2 - ∗(RG(g*h)) - RG(k*l))^2

      @test -(2 - ∗(RG(g*h*k*l)) - RG(g*h*k*l)) + 2(2G^2 + 2H^2) + 2(2K^2 + 2L^2) ==
         (2 - ∗(RG(g*h)) - RG(k*l))^2 + 2(2 - ∗(RG(k)) - RG(l))^2 + 2(2 - ∗(RG(g)) - RG(h))^2
   end
end
