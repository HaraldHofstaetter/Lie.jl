mutable struct ColoredRootedTree
    T::Vector{Vector{Int}}
    Ti::Dict{Vector{Int},Int}
    ColoredRootedTree() = new(Vector{Int}[], Dict{Vector{Int},Int}())
end

function new_tree!(RT::ColoredRootedTree, t::Vector{Int})
    t1 =vcat(t[1], sort(t[2:end]))
    get!(RT.Ti, t1) do
        push!(RT.T, t1)
        length(RT.T)
    end
end

circ!(RT::ColoredRootedTree, t1::Vector{Int}, t2::Vector{Int}) = new_tree!(RT, vcat(t1, new_tree!(RT, t2)))

circ!(RT::ColoredRootedTree, t1::Int, t2::Int) =   circ!(RT, RT.T[t1], RT.T[t2])

mutable struct FreeLieAlgebra
    N::Int
    dim::Int
    ntrees::Int
    p1::Vector{Int}
    p2::Vector{Int}
    nn::Vector{Int}
    sigma::Vector{Int}
    S::Vector{Vector{Tuple{Int,Int}}}
    #T::ColoredRootedTree
end

function gen_hall_data(N::Int)
    p1=[1,2]
    p2=[0,0]
    nn=[1,1]
    i=3
    for n=2:N
        for j=1:i-1
            for k=j+1:i-1
                if nn[j]+nn[k]==n && j>=p2[k]
                    push!(p1, k)
                    push!(p2, j)
                    push!(nn, n)
                    i+=1
                end
            end
        end
    end       
    p1, p2, nn
end

function gen_lyndon_data(N::Int)
    p1=[1,2]
    p2=[0,0]
    nn=[1,1]
    wordindex = Dict{Vector{Int},Int}([0]=>1, [1]=>2)
    i=3
    for n=2:N
        W,f = lyndon_words_factored(2, n)
        for j=1:length(W)
            w = W[j]
            s1 = w[1:f[j]-1]
            s2 = w[f[j]:end]
            wordindex[w]=i
            push!(p1, wordindex[s1])
            push!(p2, wordindex[s2])
            push!(nn, n)
            i += 1
        end
    end
    p1, p2, nn
end


function FreeLieAlgebra(N::Int; lyndon_basis::Bool=false)
    if lyndon_basis
        p1, p2, nn = gen_lyndon_data(N)
    else
        p1, p2, nn = gen_hall_data(N)
    end
    dim = length(p1)

    T = ColoredRootedTree()
    new_tree!(T,[0])
    new_tree!(T,[1])
    for i = 3:dim
        circ!(T, p1[i], p2[i])    
    end

    d1 = 3
    d2 = dim
    ntrees = dim
    S = fill(Tuple{Int,Int}[],2)
    while true 
        append!(S, fill(Tuple{Int,Int}[], d2-d1+1))
        for i = d1:d2
            v = new_tree!(T, (T.T[i])[1:end-1])
            w = (T.T[i])[end]
            vv = S[v]
            ww = S[w]
            p = length(vv)
            q = length(ww)
            S[i] = vcat((w,v), 
                        [(vv[j][1], circ!(T, vv[j][2], w)) for j=1:p], 
                        [(ww[j][1], circ!(T, v, ww[j][2])) for j=1:q])
        end
        ntrees = length(T.T)
        if ntrees==d2
            break
        end
        (d1, d2) = (d2+1, ntrees)
    end

    kappa = zeros(Int, dim)
    sigma = zeros(Int, dim)
    sigma[1]=1
    sigma[2]=1
    for i = 3:dim
        kappa[i] = (p2[p1[i]]==p2[i]) ? kappa[p1[i]]+1 : 1
        sigma[i] = kappa[i]*sigma[p1[i]]*sigma[p2[i]]
    end

    FreeLieAlgebra(N, dim, ntrees, p1, p2, nn, sigma, S) #, T)
end

mutable struct LieSeries{T}
    L::FreeLieAlgebra
    c::Vector{T}
end

Base.zero(L::FreeLieAlgebra; T::Type=Rational{Int}) = LieSeries{T}(L, zeros(T, L.ntrees))

function generator(L::FreeLieAlgebra, k:: Int; T::Type=Rational{Int}) 
    c = zeros(T, L.ntrees)
    c[k] = 1
    LieSeries{T}(L,c)
end

import Base.+
function +(alpha::LieSeries{T}, beta::LieSeries{T}) where T
    @assert alpha.L == beta.L
    LieSeries{T}(alpha.L, alpha.c+beta.c)
end

import Base.*
*(f, alpha::LieSeries{T}) where T = LieSeries{T}(alpha.L, f*alpha.c)

import LinearAlgebra: axpy!

function axpy!(a, X::LieSeries{T}, Y::LieSeries{T}) where T
    @assert X.L == X.L
    axpy!(a, X.c, Y.c)
end

import Base: copyto!
function copyto!(dest::LieSeries{T}, src::LieSeries{T}) where T
    @assert dest.L == src.L
    copyto!(dest.c, src.c)
end

function commutator!(gamma::LieSeries{T}, alpha::LieSeries{T}, beta::LieSeries{T}; 
                     order::Int=alpha.L.N) where T
    @assert alpha.L == beta.L && alpha.L == gamma.L
    @assert gamma!=alpha && gamma!=beta
    L = alpha.L
    Threads.@threads for i=1:L.ntrees
        uu = L.S[i]
        m = length(uu) 
        if m<order
            h = zero(T)
            for j=1:length(uu)
                #TODO: Check -= (otherwise even degree trees have wrong sign)
                h -= alpha.c[uu[j][1]]*beta.c[uu[j][2]] - beta.c[uu[j][1]]*alpha.c[uu[j][2]]
            end
            gamma.c[i] = h
        end
    end
end


function commutator(alpha::LieSeries{T}, beta::LieSeries{T}) where T
    @assert alpha.L == beta.L
    gamma = zero(alpha.L, T=T)
    commutator!(gamma, alpha, beta)
    gamma
end

function BCH(L::FreeLieAlgebra; T::Type=Rational{Int}, verbose::Bool=false)
    bernoulli_numbers = [ -1//2, 1//6, 0//1, -1//30, 0//1, 1//42, 0//1, -1//30, 0//1, 
       5//66, 0//1, -691//2730, 0//1, 7//6, 0//1, -3617//510, 0//1, 43867//798, 0//1, 
       -174611//330, 0//1, 854513//138, 0//1, -236364091//2730, 0//1, 8553103//6, 0//1, 
       -23749461029//870, 0//1, 8615841276005//14322]
    
    t0 = time()
    H = zero(L, T=T)
    U = zero(L, T=T)
    V = zero(L, T=T)

    # Z = X+Y
    Z = zero(L, T=T)
    Z.c[1] = 1
    Z.c[2] = 1
    for n=2:L.N        
        if verbose
            print("n=$(n), p=")
        end
        V.c[:] .= 0
        # U = X+Y
        U.c[:] .= 0
        U.c[1] = 1
        U.c[2] = 1
        for p=1:div(n-1, 2)
            if verbose
                print("$(p),")
            end
            commutator!(H,Z,U,order=n) #H=[Z,U]
            commutator!(U,Z,H,order=n) #U=[Z,H]
            axpy!(bernoulli_numbers[2*p]/factorial(2*p), U, V)
        end
        # U = X-Y
        U.c[:] .= 0
        U.c[1] = 1
        U.c[2] = -1
        commutator!(H,U,Z,order=n)
        axpy!(1//2, H, V)
        for i=1:L.ntrees
            if length(L.S[i])+1==n
                Z.c[i] = V.c[i]/n
            end
        end
        if verbose
            println(" time=",time()-t0);
        end
    end
    Z
end


