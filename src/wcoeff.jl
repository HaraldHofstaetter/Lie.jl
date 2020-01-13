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

function lyndon_words_graded(G::Vector{Generator}, n::Union{Int, Vector{Int}})
    @assert length(G)>1 && allunique(G)
    [Word(G[w .+ 1]) for w in lyndon_words_graded(n, max_grade=length(G))]
end

import LinearAlgebra

phi(w::Word, g::Generator) = LinearAlgebra.diagm(1 => [a==g ? 1 : 0 for a in w.w])
phi(w::Word, t::Term) = t.c*phi(w, t.e)
phi(w::Word, l::LinearCombination) = sum([phi(w, t) for t in terms(l)])
phi(w::Word, p::Product) = length(factors(p))==0 ? LinearAlgebra.I : prod([phi(w, f) for f in factors(p)])
phi(w::Word, c::SimpleCommutator) = phi(w, c.x)*phi(w, c.y)-phi(w, c.y)*phi(w, c.x)

function phi(w::Word, e::Exponential)
    x = phi(w, e.e)
    @assert iszero(LinearAlgebra.diag(x)) "exponent with constant term"
    y = copy(x)
    r = copy(x)
    for k=2:length(w)
        y = x*y
        if iszero(y)
            break
        end
        r += y*1//factorial(k)
    end
    r += LinearAlgebra.I 
    r
end

function phi(w::Word, l::Logarithm)
    x = phi(w, l.e)
    xm1= x - LinearAlgebra.I 
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

################################
function phi!(y::Vector{T}, w::Word, g::Generator, v::Vector{T}) where T 
    n = length(w)
    for j=1:n
        @inbounds if w[j]==g
            @inbounds y[j] = v[j+1]
        else
            @inbounds y[j] = zero(T) 
        end
    end
    @inbounds y[n+1] = zero(T) 
end


function phi!(y::Vector{T}, w::Word, t::Term, v::Vector{T}) where T 
    phi!(y, w, t.e, v)
    y[:] *= t.c
end

function phi!(y::Vector{T}, w::Word, l::LinearCombination, v::Vector{T}) where T 
    s = zeros(T, length(w)+1) 
    z = similar(y)
    for i=1:length(l.l)
        @inbounds phi!(z, w, l.l[i], v)
        s[:] += z
    end
    copyto!(y, s)
end

function phi!(y::Vector{T}, w::Word, p::Product, v::Vector{T}) where T
    copyto!(y, v)
    for i=length(p.p):-1:1
        if iszero(y)
            return 
        end
        @inbounds phi!(y, w, p.p[i], y)
    end
end

function phi!(y::Vector{T}, w::Word, c::SimpleCommutator, v::Vector{T}) where T 
    z1 = similar(v)
    z2 = similar(v)
    phi!(z1, w, c.y, v)
    phi!(z1, w, c.x, z1)
    phi!(z2, w, c.x, v)
    phi!(z2, w, c.y, z2)
    y[:] += z1
    y[:] -= z2
end

function phi!(y::Vector{T}, w::Word, e::Exponential, v::Vector{T}) where T
    z = copy(v)
    copyto!(y, v)
    for k=1:length(w)
        phi!(z, w, e.e, z)
        if iszero(z)
            return 
        end
        f = factorial(k)
        for i=1:length(w)+1
            @inbounds y[i] += z[i]/f
        end
    end
end

#following variant of last one needed for words of length >=21 
function phi!(y::Vector{Rational{T}}, w::Word, e::Exponential, v::Vector{Rational{T}}) where T<:Integer
    z = copy(v)
    copyto!(y, v)
    for k=1:length(w)
        phi!(z, w, e.e, z)
        if iszero(z)
            return 
        end
        f = factorial(T(k)) # compute factorial with Integer type T
        for i=1:length(w)+1
            @inbounds y[i] += z[i]/f
        end
    end
end


function phi!(y::Vector{T}, w::Word, l::Logarithm, v::Vector{T}) where T
    z = copy(v)
    lm1 = l.e-Id
    copyto!(y, v)
    for k=1:length(w)
        phi!(z, w, lm1, z)
        if iszero(z)
            return 
        end
        f = (-1)^(k+1)*k
        for i=1:length(w)+1
            @inbounds y[i] += z[i]/f
        end
    end
end

#for pure Integer arithmetic:

function phi!(y::Vector{T}, w::Word, e::Exponential, v::Vector{T}) where T<:Integer
    z = copy(v)
    copyto!(y, v)
    for k=1:length(w)
        phi!(z, w, e.e, z)
        if iszero(z)
            return 
        end
        f = factorial(T(k))
        for i=1:length(w)+1
            #@inbounds y[i] += div(z[i], f)
            @inbounds (d, r) = divrem(z[i], f)
            @assert iszero(r) "$(z[i]) not divisible by $f"
            @inbounds y[i] += d 
        end
    end
end

function phi!(y::Vector{T}, w::Word, l::Logarithm, v::Vector{T}) where T<:Integer
    z = copy(v)
    lm1 = l.e-Id
    copyto!(y, v)
    for k=1:length(w)
        phi!(z, w, lm1, z)
        if iszero(z)
            return 
        end
        f = (-1)^(k+1)*k
        for i=1:length(w)+1
            #@inbounds y[i] += div(z[i], f)
            @inbounds (d, r) = divrem(z[i], f)
            @assert iszero(r) "$(z[i]) not divisible by $f"
            @inbounds y[i] += d 
        end
    end
end



################################


wcoeff(w::Word, S::AlgebraElement; T::Type=Rational{Int}) = phi(w, S, vcat(zeros(T,length(w)), one(T)))[1] 
#wcoeff(W::Array{Word,1}, S::AlgebraElement; T::Type=Rational{Int}) = [wcoeff(w, S, T=T) for w in W]

function wcoeff(W::Array{Word,1}, S::AlgebraElement; T::Type=Rational{Int}) 
    c = zeros(T, length(W))
    Threads.@threads for i=1:length(W)
        c[i] = wcoeff(W[i], S, T=T)
    end
    c
end



