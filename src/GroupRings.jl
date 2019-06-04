__precompile__()
module GroupRings

using AbstractAlgebra
import AbstractAlgebra: Group, GroupElem, Ring, RingElem, parent, elem_type, parent_type, addeq!, mul!

using SparseArrays
using LinearAlgebra
using Markdown

import Base: convert, show, hash, ==, +, -, *, ^, //, /, length, getindex, setindex!, eltype, one, zero

export GroupRing, GroupRingElem, complete!, create_pm, star, aug, supp




end # of module GroupRings
