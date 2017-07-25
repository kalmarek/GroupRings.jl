using GroupRings
using Base.Test

using Nemo

@testset "GroupRings" begin
   @testset "Constructors: PermutationGroup" begin
      G = PermutationGroup(3)

      @test isa(GroupRing(G), Nemo.Ring)
      @test isa(GroupRing(G), GroupRing)

      RG = GroupRing(G)
      @test isdefined(RG, :basis) == true
      @test length(RG.basis) == 6
      @test isdefined(RG, :basis_dict) == true
      @test isdefined(RG, :pm) == false

      RG = GroupRing(G, fastm=true)
      @test isdefined(RG, :pm) == true
      @test RG.pm == zeros(Int, (6,6))

      @test isa(complete!(RG), GroupRing)
      @test all(RG.pm .> 0)
      @test RG.pm == GroupRings.fastm!(GroupRing(G, fastm=false), fill=true).pm

      @test RG.basis_dict == GroupRings.reverse_dict(elements(G))

      @test isa(GroupRing(G, collect(elements(G))), GroupRing)
      S = collect(elements(G))
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
      S = unique(S)

      basis, sizes = Groups.generate_balls(S, F(), radius=4)
      d = GroupRings.reverse_dict(basis)
      @test_throws KeyError create_pm(basis)
      pm = create_pm(basis, d, sizes[2])

      @test isa(GroupRing(F, basis, pm), GroupRing)
      @test isa(GroupRing(F, basis, d, pm), GroupRing)

      A = GroupRing(F, basis, pm)
      B = GroupRing(F, basis, d, pm)
      @test A == B

      g = B()
      s = S[2]
      g[s] = 1
      @test g == B(s)
      @test g[s^2] == 0
      @test_throws KeyError g[s^10]
   end

   @testset "GroupRingElems constructors/basic manipulation" begin
      G = PermutationGroup(3)
      RG = GroupRing(G, fastm=true)
      a = rand(6)
      @test isa(GroupRingElem(a, RG), GroupRingElem)
      @test isa(RG(a), GroupRingElem)

      for g in elements(G)
         @test isa(RG(g), GroupRingElem)
      end

      @test_throws String GroupRingElem([1,2,3], RG)
      @test isa(RG(G([2,3,1])), GroupRingElem)
      p = G([2,3,1])
      a = RG(p)
      @test length(a) == 1
      @test isa(a.coeffs, SparseVector)

      @test a.coeffs[5] == 1
      @test a[5] == 1
      @test a[p] == 1

      @test string(a) == "1*[2, 3, 1]"
      @test string(-a) == "- 1*[2, 3, 1]"

      @test RG([0,0,0,0,1,0]) == a

      s = G([1,2,3])
      @test a[s] == 0
      a[s] = 2

      @test a.coeffs[1] == 2
      @test a[1] == 2
      @test a[s] == 2

      @test string(a) == "2*[1, 2, 3] + 1*[2, 3, 1]"
      @test string(-a) == "- 2*[1, 2, 3] - 1*[2, 3, 1]"

      @test length(a) == 2
   end

   @testset "Arithmetic" begin
      G = PermutationGroup(3)
      RG = GroupRing(G, fastm=true)
      a = RG(ones(Int, order(G)))

      @testset "scalar operators" begin

         @test isa(-a, GroupRingElem)
         @test (-a).coeffs == -(a.coeffs)

         @test isa(2*a, GroupRingElem)
         @test eltype(2*a) == typeof(2)
         @test (2*a).coeffs == 2.*(a.coeffs)

         @test isa(2.0*a, GroupRingElem)
         @test eltype(2.0*a) == typeof(2.0)
         @test (2.0*a).coeffs == 2.0.*(a.coeffs)

         b = RG(1) + GroupRings.star(a)
         @test a*b == mul!(a,a,b)

         @test isa(a/2, GroupRingElem)
         @test eltype(a/2) == typeof(1/2)
         @test (a/2).coeffs == 0.5*(a.coeffs)

         @test isa(convert(Rational{Int}, a), GroupRingElem)
         @test eltype(convert(Rational{Int}, a)) == Rational{Int}
         @test convert(Rational{Int}, a).coeffs ==
            convert(Vector{Rational{Int}}, a.coeffs)

         b = convert(Rational{Int}, a)

         @test isa(b//4, GroupRingElem)
         @test eltype(b//4) == Rational{Int}

         @test isa(b//big(4), GroupElem)
         @test eltype(b//(big(4)//1)) == Rational{BigInt}

         @test isa(a//1, GroupRingElem)
         @test eltype(a//1) == Rational{Int}
         @test_throws MethodError (1.0*a)//1

      end

      @testset "Additive structure" begin
         @test RG(ones(Int, order(G))) == sum(RG(g) for g in elements(G))
         a = RG(ones(Int, order(G)))
         b = sum((-1)^parity(g)*RG(g) for g in elements(G))
         @test 1/2*(a+b).coeffs == [1.0, 0.0, 1.0, 0.0, 1.0, 0.0]
      end

      @testset "Multiplicative structure" begin
         for g in elements(G), h in elements(G)
            a = RG(g)
            b = RG(h)
            @test a*b == RG(g*h)
            @test (a+b)*(a+b) == a*a + a*b + b*a + b*b
         end

         for g in elements(G)
            @test GroupRings.star(RG(g)) == RG(inv(g))
            @test (one(RG)-RG(g))*GroupRings.star(one(RG)-RG(g)) ==
               2*one(RG) - RG(g) - RG(inv(g))
            @test GroupRings.augmentation((one(RG)-RG(g))) == 0
         end

         z = sum((one(RG)-RG(g))*GroupRings.star(one(RG)-RG(g)) for g in elements(G))

         @test GroupRings.augmentation(z) == 0

         @test rationalize(Int, z) == convert(Rational{Int}, z)
      end

   end
end
