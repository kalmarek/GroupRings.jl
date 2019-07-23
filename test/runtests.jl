using Test

using AbstractAlgebra
using GroupRings
using SparseArrays
using LinearAlgebra

include("AARing_interface_conformance.jl")

@testset "Group Rings tests" begin
    include("unittests.jl")
    include("usetests.jl")

    let

        R = AbstractAlgebra.zz
        G = PermGroup(4)

        RG = GroupRing(R, G, collect(G), halfradius_length=order(G))

        X = rand(RG, 0.2, -3:3)
        Y = rand(RG, 0.4, -1:1)

        test_ringinterface(X, Y)
    end
end
