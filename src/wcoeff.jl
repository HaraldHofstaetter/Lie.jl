struct Word 
    w::Array{Generator,1}
end

Word(x::Vararg{Generator}) = Word([x...])

Base.length(w::Word) = length(w.w)
Base.IndexStyle(::Type{<:Word}) = IndexLinear()
Base.getindex(w::Word, i::Int) = w.w[i]
Base.getindex(w::Word, i) = Word(w.w[i])


function Base.show(io::IO, w::Word) 
    if length(w)==0
        print(io, "∅")
    else
        join(io, w.w, "⋅") # \cdot
    end
end

⋅(w1::Word, w2::Word) = Word(vcat(w.w1,w.w2))
⋅(g::Generator, w::Word) = Word(vcat(g,w.w))
⋅(w::Word, g::Generator) = Word(vcat(w.w,g))
⋅(g1::Generator, g2::Generator) = Word(g1,g2)


function lyndon_words(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [Word(G[w .+ 1]) for w in lyndon_words(length(G), n)]
end


phi(w::Word, g::Generator) = diagm([a==g ? 1 : 0 for a in w], 1)
phi(w::Word, t::Term) = t.c*phi(w, t.e)
phi(w::Word, l::LinearCombination) = sum([phi(w, t) for t in terms(l)])
phi(w::Word, p::Product) = length(factors(p))==0 ? eye(Int,length(w)+1) : prod([phi(w, f) for f in factors(p)])
phi(w::Word, c::SimpleCommutator) = phi(w, c.x)*phi(w, c.y)-phi(w, c.y)*phi(w, c.x)

function phi(w::Word, e::Exponential)
    x = phi(w, e.e)
    @assert iszero(diag(x)) "exponent with constant term"
    y = copy(x)
    r = copy(x)
    for k=2:length(w)
        y = x*y
        if iszero(y)
            break
        end
        r += y*1//factorial(k)
    end
    r += eye(Int, length(w)+1)
    r
end

function phi(w::Word, l::Logarithm)
    x = phi(w, l.e)
    xm1= x - eye(Int, length(w)+1)
    y = copy(x)
    r = copy(x)
    for k=2:length(w)
        y = xm1*y
        if iszero(y)
            break
        end
        r += ((-1)^(k+1)//k)*y
    end
    r
end


phi(w::Word, g::Generator, v::Vector) = vcat([(w[j]==g ? v[j+1] : 0) for j=1:length(w)],0)
phi(w::Word, t::Term, v::Vector) = t.c .* phi(w, t.e, v)
phi(w::Word, l::LinearCombination, v::Vector) = sum([phi(w, t, v) for t in terms(l)])

function phi(w::Word, p::Product, v::Vector) 
    v1 = copy(v)
    for f in reverse(factors(p))
        if iszero(v1)
            return v1
        end
        v1 = phi(w, f, v1)
    end
    v1
end

phi(w::Word, c::SimpleCommutator, v::Vector) = phi(w, c.x, phi(w, c.y, v))-phi(w, c.y, phi(w, c.x, v))

function phi(w::Word, e::Exponential, v::Vector)
    y = copy(v)
    r = copy(v)
    for k=1:length(w)
        y = phi(w, e.e, y)
        if iszero(y)
            return r
        end
        r += y*1//factorial(k)
    end
    r
end

function phi(w::Word, l::Logarithm, v::Vector)
    y = copy(v)
    lm1 = l.e-Id
    r = copy(v)
    for k=1:length(w)
        y = phi(w, lm1, y)
        if iszero(y)
            return r
        end
        r += ((-1)^(k+1)//k)*y
    end
    r
end


wcoeff(w::Word, S::AlgebraElement; T::Type=Rational{Int}) = phi(w, S, vcat(zeros(T,length(w)), one(T)))[1] 
#wcoeff(W::Array{Word,1}, S::AlgebraElement; T::Type=Rational{Int}) = [wcoeff(w, S, T=T) for w in W]

function wcoeff(W::Array{Word,1}, S::AlgebraElement; T::Type=Rational{Int}) 
    c = zeros(T, length(W))
    Threads.@threads for i=1:length(W)
        c[i] = wcoeff(W[i], S, T=T)
    end
    c
end

