module GroupRings

using SparseArrays
using LinearAlgebra
using Markdown
using AbstractAlgebra

import Base: ==, +, -, *, ^, //, /
import AbstractAlgebra: Group, GroupElem, NCRing, NCRingElem, Ring
import AbstractAlgebra: zero!, mul!, add!, addeq!, addmul!

export GroupRing, GroupRingElem, aug, supp, star

include("types.jl")
include("ncring_interface.jl")
include("arithmetic.jl")
include("misc.jl")

end # of module GroupRings
