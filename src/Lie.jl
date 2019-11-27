module Lie

export Element, Generator, SimpleCommutator, Commutator
export Exponential, Product, Id, Term, LinearCombination
export ZeroElement, Logarithm, terms, factors, exponent

export lyndon_words, lyndon_basis

export Word, ⋅, wcoeff

export FreeLieAlgebra, LieSeries, generator, commutator, commutator!
export BCH


include("expressions.jl")
include("lyndon.jl")
include("wcoeff.jl")
include("tree_algebra.jl")

end # module
