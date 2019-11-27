abstract type Element end

struct Generator <: Element
    name   ::String
    degree ::Int
    function Generator(name, degree)
        @assert degree>=1 "degree has to be >=1"
        new(name, degree)
    end
end

Generator(name::String) = Generator(name, 1)

Base.show(io::IO, g::Generator) = print(io, g.name)

struct SimpleCommutator <: Element 
    x::Element
    y::Element
end

Base.show(io::IO, sc::SimpleCommutator) = print(io, "[", sc.x, ",", sc.y, "]")

Commutator(g::Element) = g
Commutator(x, y) = SimpleCommutator(Commutator(x), Commutator(y))
Commutator(x::Tuple) = SimpleCommutator(Commutator(x[1]),Commutator(x[2]))

function Commutator(x::Vector)
    @assert length(x)==2 "wrong commutator length"
    SimpleCommutator(Commutator(x[1]),Commutator(x[2]))
end


struct Exponential <: Element
    e::Element
end

exponent(e::Exponential) = e.e

Base.exp(e::Element) = Exponential(e)
Base.show(io::IO, e::Exponential) = print(io, "exp(", e.e, ")")


struct Logarithm <: Element
    e::Element
end

Base.log(e::Element) = Logarithm(e)
Base.show(io::IO, e::Logarithm) = print(io, "log(", e.e, ")")



struct Product <: Element
    p::Array{Element,1}    
end
#Note factors stored form right to left

factors(p::Product) = p.p

const Id = Product([])
Base.one(::Type{T}) where {T<:Element} = Id
Base.one(x::T) where {T<:Element} = one(T)

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



struct Term <: Element
    c::Any
    e::Element
end

Base.convert(::Type{Term}, t::Term) = t
Base.convert(::Type{Term}, e::Element) = Term(1, e)


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


struct LinearCombination <: Element
    l::Array{Term,1}    
end

const ZeroElement = LinearCombination([])

Base.zero(::Type{T}) where {T<:Element} = ZeroElement 
Base.zero(x::T) where {T<:Element} = zero(T)

Base.iszero(x::Element) = false
Base.iszero(l::LinearCombination) = length(l.l)==0
Base.iszero(t::Term) = t.c==0 || iszero(t.e)

is_id(e::Element) = false
is_id(p::Product) = length(factors(p))==0
is_id(t::Term) = is_id(t.e)&&t.c==1

import Base: (*), /, +, -

*(c, e::Element) = c==1 ? e : Term(c,e)
*(e::Element, c) = c==1 ? e : Term(c,e)
*(c, t::Term) = (c*t.c)*t.e
*(t::Term, c) = (c*t.c)*t.e
#*(c, t::Term) = Term(c*t.c,t.e)
#*(t::Term, c) = Term(c*t.c,t.e)

*(p::Product, x::Element) = Product(vcat(p.p, x))
*(x::Element, p::Product) = Product(vcat(x, p.p))
*(p1::Product, p2::Product) = Product(vcat(p1.p, p2.p))
*(e1::Element, e2::Element) = Product([e1, e2])
*(p::Product, t::Term) = t.c*(p*t.e)
*(t::Term, p::Product) = t.c*(t.e*p)
*(t1::Term, t2::Term) = (t1.c*t2.c)*(t1.e*t2.e)
*(t::Term, e::Element) = t.c*(t.e*e)
*(e::Element, t::Term) = t.c*(e*t.e)

+(l1::LinearCombination, l2::LinearCombination) = LinearCombination(vcat(l1.l, l2.l))
+(l::LinearCombination, t::Term) = LinearCombination(vcat(l.l, t))
+(t::Term, l::LinearCombination) = LinearCombination(vcat(t, l.l))
+(l::LinearCombination, e::Element) = LinearCombination(vcat(l.l, vcat(convert(Term, e))))
+(e::Element, l::LinearCombination) = LinearCombination(vcat(vcat(convert(Term, e), l.l)))
+(t1::Term, t2::Term) =  LinearCombination(vcat(t1, t2))
+(e1::Element, e2::Element) = LinearCombination(vcat(convert(Term, e1), convert(Term, e2)))
+(e::Element) = e
-(t::Term) = Term(-t.c, t.e)
-(e::Element) = Term(-1, e)
-(l::LinearCombination) = LinearCombination([-t for t in terms(l)])
-(e1::Element, e2::Element) = e1+(-e2)


terms(e::Element) = [Term(e)]
terms(x::LinearCombination) = x.l

function Base.show(io::IO, l::LinearCombination) 
    tt=terms(l)
    if length(tt)==0
        print(io, "0")
    else
        join(io, tt, "+")
    end
end

trafo(G::Vector{Generator}, b::Int) = G[b+1]
trafo(G::Vector{Generator}, b::Vector) = SimpleCommutator(trafo(G, b[1]), trafo(G, b[2]))


function lyndon_basis(G::Vector{Generator}, n::Int)
    @assert length(G)>1 && allunique(G)
    [trafo(G, b) for b in lyndon_basis(length(G), n)]
end

function lyndon_basis(G::Vector{Generator}, nn::Vector{Int})
    @assert length(G)>1 && allunique(G)
    vcat([[trafo(G, b) for b in lyndon_basis(length(G), n)] for n in nn]...)
end

function rightnormed_basis(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [trafo(G, b) for b in rightnormed_basis(length(G), n)]
end







