module Lie

export lyndon_words, lyndon_basis

export FreeLieAlgebra, LieSeries, generator, commutator, commutator!
export BCH


include("lyndon.jl")
include("tree_algebra.jl")

end # module
