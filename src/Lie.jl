module Lie

export Element, Generator, SimpleCommutator, Commutator
export Exponential, Product, Id, Term, LinearCombination
export ZeroElement, Logarithm, terms, factors, exponent

export lyndon_words, lyndon_basis, rightnormed_basis

export Word, ⋅, wcoeff

export lie_series

export TreeAlgebra, TreeSeries, generator
export commutator, commutator!
export BCH


include("expressions.jl")
include("lyndon.jl")
include("wcoeff.jl")
include("lie_series.jl")
include("tree_algebra.jl")

end # module
