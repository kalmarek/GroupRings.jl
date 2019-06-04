__precompile__()
module GroupRings

using AbstractAlgebra
import AbstractAlgebra: Group, GroupElem, Ring, RingElem, parent, elem_type, parent_type, addeq!, mul!

using SparseArrays
using LinearAlgebra
using Markdown

import Base: convert, show, hash, ==, +, -, *, ^, //, /, length, getindex, setindex!, eltype, one, zero

export GroupRing, GroupRingElem, complete!, create_pm, star, aug, supp


function reverse_dict(::Type{I}, iter) where I<:Integer
   length(iter) > typemax(I) && error("Can not produce reverse dict: $(length(iter)) is too large for $T")
   return Dict{eltype(iter), I}(x => i for (i,x) in enumerate(iter))
end

reverse_dict(iter) = reverse_dict(Int, iter)

function create_pm(basis::Vector{T}, basis_dict::Dict{T, Int},
   limit::Int=length(basis); twisted::Bool=false, check=true) where {T<:GroupElem}
   product_matrix = zeros(Int, (limit,limit))
   Threads.@threads for i in 1:limit
      x = basis[i]
      if twisted
         x = inv(x)
      end
      for j in 1:limit
         product_matrix[i,j] = basis_dict[x*basis[j]]
      end
   end

   check && check_pm(product_matrix, basis, twisted)

   return product_matrix
end

create_pm(b::Vector{T}) where {T<:GroupElem} = create_pm(b, reverse_dict(b))

function check_pm(product_matrix, basis, twisted=false)
   idx = findfirst(product_matrix' .== 0)
   if idx != nothing
      @warn("Product is not supported on basis")
      i,j = Tuple(idx)
      x = basis[i]
      if twisted
         x = inv(x)
      end
      throw(KeyError(x*basis[j]))
   end
   return true
end

function complete!(RG::GroupRing)
   isdefined(RG, :basis) || throw(ArgumentError("Provide basis for completion first!"))
   if !isdefined(RG, :pm) 
      initializepm!(RG, fill=false)
      return RG
   end

   warning = false
   for idx in findall(RG.pm .== 0)
      i,j = Tuple(idx)
      g = RG.basis[i]*RG.basis[j]
      if haskey(RG.basis_dict, g)
          RG.pm[i,j] = RG.basis_dict[g]
      else
         if !warning
            warning = true
         end
      end
   end
   warning && @warn("Some products were not supported on basis")
   return RG
end

function initializepm!(RG::GroupRing; fill::Bool=false)
   isdefined(RG, :basis) || throw("For baseless Group Rings You need to provide pm.")
   isdefined(RG, :pm) && return RG
   if fill
      RG.pm = try
         create_pm(RG.basis, RG.basis_dict)
      catch err
         isa(err, KeyError) && throw("Product is not supported on basis, $err.")
         throw(err)
      end
   else
      RG.pm = zeros(Int, length(RG.basis), length(RG.basis))
   end
   return RG
end

end # of module GroupRings
