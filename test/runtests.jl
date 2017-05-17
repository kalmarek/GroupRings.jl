using GroupRings
using Base.Test

using Nemo

# write your own tests here
@testset "GroupRing constructors: PermutationGroup" begin
   G = PermutationGroup(3)

   @test isa(GroupRing(G), Nemo.Ring)
   @test isa(GroupRing(G), GroupRing)

   RG = GroupRing(G)
   @test isdefined(RG, :pm) == false
   @test isdefined(RG, :basis) == false
   @test isdefined(RG, :basis_dict) == false

   @test isa(complete(RG), GroupRing)
   @test size(RG.pm) == (6,6)
   @test length(RG.basis) == 6

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
   S = generators(F)
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

end

@testset "GroupRingElems constructors/basic manipulation" begin
   G = PermutationGroup(3)
   RG = GroupRing(G, full=true)
   a = rand(6)
   @test isa(GroupRingElem(a, RG), GroupRingElem)
   @test isa(RG(a), GroupRingElem)
   @test_throws String GroupRingElem([1,2,3], RG)
   @test isa(RG(G([2,3,1])), GroupRingElem)
   p = G([2,3,1])
   a = RG(p)
   @test length(a) == 6
   @test isa(a.coeffs, SparseVector)

   @test a.coeffs[5] == 1
   @test a[5] == 1
   @test RG([0,0,0,0,1,0]) == a
   @test a[p] == 1
   @test a[G([1,2,3])] == 0

   @test string(a) == "1*[2, 3, 1]"
end
