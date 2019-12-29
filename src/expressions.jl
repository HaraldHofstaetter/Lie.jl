abstract type AlgebraElement end

struct Generator <: AlgebraElement
    name ::String
    hash ::UInt64 
    #degree ::Int
    function Generator(name)
        h = hash(name)
        new(name, h)
    end
end

import Base.==

==(g1::Generator, g2::Generator) = g1.hash==g2.hash

Base.show(io::IO, g::Generator) = print(io, g.name)

struct SimpleCommutator <: AlgebraElement 
    x::AlgebraElement
    y::AlgebraElement
end

Base.show(io::IO, sc::SimpleCommutator) = print(io, "[", sc.x, ",", sc.y, "]")

Commutator(g::AlgebraElement) = g
Commutator(x, y) = SimpleCommutator(Commutator(x), Commutator(y))
Commutator(x::Tuple) = SimpleCommutator(Commutator(x[1]),Commutator(x[2]))

function Commutator(x::Vector)
    @assert length(x)==2 "wrong commutator length"
    SimpleCommutator(Commutator(x[1]),Commutator(x[2]))
end


struct Exponential <: AlgebraElement
    e::AlgebraElement
end

exponent(e::Exponential) = e.e

Base.exp(e::AlgebraElement) = Exponential(e)
Base.show(io::IO, e::Exponential) = print(io, "exp(", e.e, ")")


struct Logarithm <: AlgebraElement
    e::AlgebraElement
end

Base.log(e::AlgebraElement) = Logarithm(e)
Base.show(io::IO, e::Logarithm) = print(io, "log(", e.e, ")")



struct Product <: AlgebraElement
    p::Array{AlgebraElement,1}    
end
#Note factors stored form right to left

factors(p::Product) = p.p

const Id = Product([])
Base.one(::Type{T}) where {T<:AlgebraElement} = Id
Base.one(x::T) where {T<:AlgebraElement} = one(T)

function Base.show(io::IO, p::Product) 
    if length(p.p)==0
        print(io, "Id")
    else
        f = factors(p)
        l = length(f)
        for i=1:l
            if isa(f[i], LinearCombination) && l>1
                print(io, "(", f[i], ")")
            else
                print(io, f[i])
            end
            if i<l
                print(io, "*")
            end
        end
    end
end



struct Term <: AlgebraElement
    c::Any
    e::AlgebraElement
end

Base.convert(::Type{Term}, t::Term) = t
Base.convert(::Type{Term}, e::AlgebraElement) = Term(1, e)


function Base.show(io::IO, t::Term)
    if t.c!=1 
        if !(isa(t.c, Real) && t.c>=0)
            print(io, "(")
        end        
        print(io, t.c)
        if !(isa(t.c, Real) && t.c>=0)
            print(io, ")")
        end        
        print(io, "*")
    end
    if isa(t.e, LinearCombination)
        print(io, "(")
    end
    print(io, t.e)
    if isa(t.e, LinearCombination)
        print(io, ")")
    end
end


struct LinearCombination <: AlgebraElement
    l::Array{Term,1}    
end

const ZeroAlgebraElement = LinearCombination([])

Base.zero(::Type{T}) where {T<:AlgebraElement} = ZeroAlgebraElement 
Base.zero(x::T) where {T<:AlgebraElement} = zero(T)

Base.iszero(x::AlgebraElement) = false
Base.iszero(l::LinearCombination) = length(l.l)==0
Base.iszero(t::Term) = t.c==0 || iszero(t.e)

is_id(e::AlgebraElement) = false
is_id(p::Product) = length(factors(p))==0
is_id(t::Term) = is_id(t.e)&&t.c==1

import Base: (*), /, +, -

*(c, e::AlgebraElement) = c==1 ? e : Term(c,e)
*(e::AlgebraElement, c) = c==1 ? e : Term(c,e)
*(c, t::Term) = (c*t.c)*t.e
*(t::Term, c) = (c*t.c)*t.e
#*(c, t::Term) = Term(c*t.c,t.e)
#*(t::Term, c) = Term(c*t.c,t.e)

*(p::Product, x::AlgebraElement) = Product(vcat(p.p, x))
*(x::AlgebraElement, p::Product) = Product(vcat(x, p.p))
*(p1::Product, p2::Product) = Product(vcat(p1.p, p2.p))
*(e1::AlgebraElement, e2::AlgebraElement) = Product([e1, e2])
*(p::Product, t::Term) = t.c*(p*t.e)
*(t::Term, p::Product) = t.c*(t.e*p)
*(t1::Term, t2::Term) = (t1.c*t2.c)*(t1.e*t2.e)
*(t::Term, e::AlgebraElement) = t.c*(t.e*e)
*(e::AlgebraElement, t::Term) = t.c*(e*t.e)

+(l1::LinearCombination, l2::LinearCombination) = LinearCombination(vcat(l1.l, l2.l))
+(l::LinearCombination, t::Term) = LinearCombination(vcat(l.l, t))
+(t::Term, l::LinearCombination) = LinearCombination(vcat(t, l.l))
+(l::LinearCombination, e::AlgebraElement) = LinearCombination(vcat(l.l, vcat(convert(Term, e))))
+(e::AlgebraElement, l::LinearCombination) = LinearCombination(vcat(vcat(convert(Term, e), l.l)))
+(t1::Term, t2::Term) =  LinearCombination(vcat(t1, t2))
+(e1::AlgebraElement, e2::AlgebraElement) = LinearCombination(vcat(convert(Term, e1), convert(Term, e2)))
+(e::AlgebraElement) = e
-(t::Term) = Term(-t.c, t.e)
-(e::AlgebraElement) = Term(-1, e)
-(l::LinearCombination) = LinearCombination([-t for t in terms(l)])
-(e1::AlgebraElement, e2::AlgebraElement) = e1+(-e2)


terms(e::AlgebraElement) = [Term(e)]
terms(x::LinearCombination) = x.l

function Base.show(io::IO, l::LinearCombination) 
    tt=terms(l)
    if length(tt)==0
        print(io, "0")
    else
        join(io, tt, "+")
    end
end

gen_expression(G::Vector{Generator}, b::Int) = G[b+1]
gen_expression(G::Vector{Generator}, b::Vector) = 
    SimpleCommutator(gen_expression(G, b[1]), gen_expression(G, b[2]))


function basis_element(K::Int, i::Int, p1::Vector{Int}, p2::Vector{Int})
    if i<=K
        return i-1
    else
        return [basis_element(K, p1[i], p1, p2), 
                basis_element(K, p2[i], p1, p2)]
    end
end

function gen_expression(G::Vector{Generator}, c::Vector, p1::Vector{Int}, p2::Vector{Int}) 
    @assert length(G)>=2 && allunique(G)
    K = length(G)
    sum([c[i]*gen_expression(G, basis_element(K, i, p1, p2)) 
           for i = 1:length(c) if !iszero(c[i])])
end


function lyndon_basis(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [gen_expression(G, b) for b in lyndon_basis(length(G), n)]
end

function lyndon_basis_graded(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [gen_expression(G, b) for b in lyndon_basis_graded(n, max_grade=length(G))]
end


function rightnormed_basis(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [gen_expression(G, b) for b in rightnormed_basis(length(G), n)]
end

function rightnormed_basis_graded(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [gen_expression(G, b) for b in rightnormed_basis_graded(n, max_grade=length(G))]
end









