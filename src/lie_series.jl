function multi_degree(K::Int, w::Vector{Int}, l::Int, r::Int)
    h = zeros(Int, K)
    for i=l:r 
        @inbounds h[w[i]+1] += 1
    end
    h
end

function hom_index(x::Vector{Int}, K::Int)
   if K==1
       return x[1],x[1]
   end
   s, i = hom_index(x, K-1) 
   n = s+x[K]
   n, binomial(K+n-1, n-1) + i
end

hom_index(x::Vector{Int}) = hom_index(x, length(x))[2]

multi_degree_index(K::Int, w::Vector{Int}, l::Int, r::Int) =  hom_index(multi_degree(K, w, l, r))


@inline function word_index(K::Int, w::Vector{Int}, l::Int, r::Int)
    @inbounds x = w[r]
    y = K
    for j=r-1:-1:l
        @inbounds x += w[j]*y
        y *= K
    end
    x + div(y-1, K-1)
end


function coeff(K::Int, w::Vector{Int}, l::Int, r::Int, j::Int, 
               p1::Vector{Int}, p2::Vector{Int}, 
               nn::Vector{Int}, 
               h::Vector{Int},
               H::Matrix{Int},
               WI::Vector{Int},
               W2I::Matrix{Int},
               CT::Matrix{Int},
               M::Int)
    if l==r 
        return @inbounds w[l]==j-1 ? 1 : 0
    end

    if r-l+1<=M # use lookup table
        return @inbounds CT[j, W2I[l,r]]
    end

    if @inbounds H[l,r]!=h[j] || W2I[l,r]<WI[j] 
       return 0
    end

    if @inbounds W2I[l,r]==WI[j]
        return 1
    end


@inbounds j1 =p1[j]
@inbounds j2 =p2[j]
@inbounds m1 = nn[j1]
@inbounds m2 = nn[j2]

    @inbounds if WI[j1]<WI[j2]
        c1 = coeff(K, w, l, l+m1-1, j1, p1, p2, nn, h, H, WI, W2I, CT, M)
        if c1!=0
            c1 *= coeff(K, w, l+m1, r, j2, p1, p2, nn, h, H, WI, W2I, CT, M)
        end
    
        c2 = coeff(K, w, l+m2, r,  j1, p1, p2, nn, h, H, WI, W2I, CT, M)
        if c2!=0
            c2 *= coeff(K, w, l, l+m2-1, j2, p1, p2, nn, h, H, WI, W2I, CT, M)
        end
    else
        c1 = coeff(K, w, l+m1, r, j2, p1, p2, nn, h, H, WI, W2I, CT, M)
        if c1!=0
            c1 *= coeff(K, w, l, l+m1-1, j1, p1, p2, nn, h, H, WI, W2I, CT, M)
        end
    
        c2 = coeff(K, w, l, l+m2-1, j2, p1, p2, nn, h, H, WI, W2I, CT, M)
        if c2!=0
            c2 *= coeff(K, w, l+m2, r,  j1, p1, p2, nn, h, H, WI, W2I, CT, M)
        end
    end

    c1 - c2
end

function init_lie(K::Int, N::Int, M::Int)
    WW = [[c] for c=0:K-1]
    p1 = collect(1:K)
    p2 = zeros(Int, K)
    nn = ones(Int, K)
    hh = [multi_degree_index(K, [c], 1, 1) for c=0:K-1]
    lynw_index = Dict{Vector{Int},Int}([[i-1]=>i for i=1:K]...)
    index = K+1
    ii = zeros(Int, N+1)
    ii[1] = 1 
    ii[2] = index 
    for n=2:N
        W,f = lyndon_words_factored(K, n)
        for j=1:length(W)
            w = W[j]
            s1 = w[1:f[j]-1]
            s2 = w[f[j]:end]
            lynw_index[w]=index
            push!(p1, lynw_index[s1])
            push!(p2, lynw_index[s2])
            push!(nn, n)
            push!(hh, multi_degree_index(K, w, 1, n))
            index += 1
        end
        append!(WW, W)
        ii[n+1] = index
    end

    WI = [Lie.word_index(2, w, 1, length(w)) for w in WW]

    # generate coefficients lookup table
    CT = zeros(Int, ii[M+1]-1, div(K^(M+1)-1, K-1)-1) 
    for n=1:M
        i1 = ii[n]
        i2 = ii[n+1]-1 
        for k=0:K^n-1
            w = [parse(Int, c) for c in string(k, base=K, pad=n)]
            H = Int[l<=r ? multi_degree_index(K, w, l,r) : 0 for l=1:n, r=1:n]
            W2I = Int[l<=r && r-l+1<=M ? word_index(K, w, l,r) : 0
                                                 for l=1:n, r=1:n]
            wi = word_index(K, w, 1, n)
            for j=i1:i2
                c = coeff(K, w, 1, n, j, p1, p2, nn, hh, H, WI, W2I, CT, n-1)
                if c!=0
                    CT[j, wi] = c
                end
            end
        end
    end
    p1, p2, nn, WW, ii, hh, CT, WI
end



function lie_series(G::Vector{Generator}, S::AlgebraElement, N::Int; 
               T::Type=Rational{Int}, verbose::Bool=false, M::Int=0,
               lists_output::Bool=false, bch_specific::Bool=false)
    t0 = time()
    if verbose
        print("initializing...")
    end
    K = length(G)
    @assert K>=2 && allunique(G)

    if bch_specific
        K = 2
        S = log(exp(G[1])*exp(G[2]))
    end

    M = min(M, N)

    p1, p2, nn, WW, ii, hh, CT, WI = init_lie(K, N, M)

    if verbose
        println("time=", time()-t0)
        print("coeffs of words...")
    end

    c = zeros(T, length(WW))

    p = Threads.nthreads()
    tt = [zeros(T, N+1) for i=1:p]

    t1 = zeros(T, 2)
    phi!(t1, Word(G[WW[1] .+ 1]), S, T[0,1] )
    c[1] = t1[1]

    e = vcat(zeros(T, N), one(T))
    Threads.@threads for i=ii[N]:ii[N+1]-1
        t = tt[Threads.threadid()]
        if bch_specific && iseven(N) && p1[i]!=1
            continue
        end
        @inbounds w = Word(G[WW[i] .+ 1])
        phi!(t, w, S, e)
        @inbounds c[i] = t[1]
        k = 1
        j = i
        @inbounds while p1[j]==1
            k += 1            
            @inbounds j = p2[j]
            @inbounds c[j] = t[k]
        end
    end

    if verbose
        println("time=", time()-t0)
        print("coeffs of basis elements...")
    end

    den = lcm(denominator.(c))
    cc = numerator.(den*c)

    for n=1:N
        i1 = ii[n]
        i2 = ii[n+1]-1 

        hu = n==1 ? (1:K) : (Lie.hom_index(vcat(zeros(Int, K-1),n))+1:Lie.hom_index(vcat(n,zeros(Int, K-1)))-1) 
        hu = vcat([hu[j:p:end] for j=1:p]...)
        Threads.@threads for h in hu

            H = zeros(Int, n, n)
            W2I = zeros(Int, n, n)

            for i=i1:i2
            @inbounds if h==hh[i]
                 if bch_specific && iseven(n) && p1[i]!=1
                     cc[i]=0
                     continue
                 end
                 @inbounds w = WW[i]

                 for l=1:n
                     for r=1:n
                         @inbounds H[l, r] = l<=r ? multi_degree_index(K, w, l, r) : 0 
                     end
                 end

                 for l=1:n
                     for r=l:n
                         @inbounds W2I[l,r] = word_index(K, w, l,r) 
                     end
                 end
                                                      
                 for j=i1:i-1
                     @inbounds if h==hh[j] && !iszero(cc[j])
                         @inbounds cc[i] -= coeff(K, w, 1, n, j, p1, p2, nn, hh, H, WI, W2I, CT, M)*cc[j]
                     end
                 end
             end
             end
         end
    end

    c = cc//den

    if verbose
        println("time=", time()-t0)
    end
    
    if lists_output
        return p1, p2, nn, c
    else
        return gen_expression(G, c, p1, p2)
    end
end


mutable struct LieAlgebra
    K::Int # number of generators
    N::Int # maximum order 
    dim::Int
    p1::Vector{Int}
    p2::Vector{Int}
    nn::Vector{Int}
    ii::Vector{Int}
    S::Vector{Vector{Vector{Int}}} 
end

            
@inline function SSS(cc::Matrix{Int}, C::Vector{Int}, k::Int, l::Int)::Int
    c = 0
    @simd for j=1:k-1
        @inbounds c += cc[j,l]*C[j]
    end
    c
end


function LieAlgebra(K::Int, N::Int; M::Int=0, verbose::Bool=false, t0::Float64=time())
    @assert K>=2

    M = min(M, N)
    p1, p2, nn, WW, ii, hh, CT, WI = init_lie(K, N, M)

    dim = length(WW)
    S = fill(Array{Int,1}[], dim)

    MD = [multi_degree(K, w, 1, length(w)) for w in WW]

    p = Threads.nthreads()

    for n=1:N
        if verbose
            print("n=$n ... ")
        end
        i1 = ii[n]
        i2 = ii[n+1]-1 
        MDu = unique(MD[i1:i2])

        for md in MDu 
            h = hom_index(md) 
            m = sum([1 for i=i1:i2 if h==hh[i]])
            @inbounds f1 = [j1 for n1 = 1:div(n,2)
                            for j1 = ii[n1] : ii[n1+1]-1
                            for j2 = max(j1+1, ii[n-n1]) : ii[n-n1+1]-1
                            if MD[j1]+MD[j2]==md]  
            @inbounds f2 = [j2 for n1 = 1:div(n,2)
                            for j1 = ii[n1] : ii[n1+1]-1
                            for j2 = max(j1+1, ii[n-n1]) : ii[n-n1+1]-1
                            if MD[j1]+MD[j2]==md] 
            cc = zeros(Int, m, length(f1)) 
            H = zeros(Int, n, n)
            W2I = zeros(Int, n, n)
            C = zeros(Int, m)
        
            k = 0
            for i=i1:i2
            if h==hh[i]
                k += 1
                n = nn[i]
                w = WW[i]
        
                for l=1:n
                    for r=l:n
                        @inbounds H[l, r] = multi_degree_index(K, w, l, r) 
                    end
                end
        
                for l=1:n
                    for r=l:n
                        @inbounds W2I[l, r] = word_index(K, w, l, r) 
                    end
                end

                @inbounds J = [j for j=i1:i-1 if h==hh[j]]
                LI = 1:length(J)
                LI = vcat([LI[j:p:end] for j=1:p]...)
                Threads.@threads for li = 1:length(LI)
                    @inbounds jj = LI[li]
                    @inbounds j = J[jj]
                    @inbounds C[jj] = coeff(K, w, 1, n, j, p1, p2, nn, hh, H, WI, W2I, CT, M) 
                end

                Threads.@threads for l = 1:length(f1)
                    @inbounds j1 = f1[l]
                    @inbounds j2 = f2[l]
                    @inbounds n1 = nn[j1]
                    @inbounds n2 = nn[j2]
                    #c1 = coeff(K, w, 1, n1, j1, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    #if c1!=0
                    #    c1 *= coeff(K, w, n1+1, n, j2, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    #end
                    #c2 = coeff(K, w, n2+1, n,  j1, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    #if c2!=0
                    #    c2 *= coeff(K, w, 1, n2, j2, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    #end
        
                    c1 = coeff(K, w, n1+1, n, j2, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    if c1!=0
                        c1 *= coeff(K, w, 1, n1, j1, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    end
                    c2 = coeff(K, w, 1, n2, j2, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    if c2!=0
                        c2 *= coeff(K, w, n2+1, n,  j1, p1, p2, nn, hh, H, WI, W2I, CT, M)
                    end
        
                    @inbounds cc[k, l] = c1 - c2 - SSS(cc, C, k, l)
                end
                @inbounds S[i] = [[f1[l], f2[l], cc[k,l]] 
                                     for l=1:length(f1) if !iszero(cc[k,l])]
            end
            end
        end
        if verbose
            println("time=", time()-t0)
        end
    end

    LieAlgebra(K, N, dim, p1, p2, nn, ii, S) 
end


mutable struct LieSeries{T}
    L::LieAlgebra
    c::Vector{T}
end


Base.zero(L::LieAlgebra; T::Type=Rational{Int}) = LieSeries{T}(L, zeros(T, L.dim))

function generator(L::LieAlgebra, k:: Int; T::Type=Rational{Int}) 
    c = zeros(T, L.dim)
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
    Threads.@threads for i=1:L.dim
        @inbounds if L.nn[i] > order
            @inbounds gamma.c[i] = 0
        else
        @inbounds uu = L.S[i]
        m = length(uu)
        h = zero(T)
        for j=1:length(uu)
            @inbounds h += uu[j][3]*(alpha.c[uu[j][1]]*beta.c[uu[j][2]] - beta.c[uu[j][1]]*alpha.c[uu[j][2]])
        end
        @inbounds gamma.c[i] = h
        end
    end
end


function commutator(alpha::LieSeries{T}, beta::LieSeries{T}) where T
    @assert alpha.L == beta.L
    gamma = zero(alpha.L, T=T)
    commutator!(gamma, alpha, beta)
    gamma
end

function BCH(L::LieAlgebra; T::Type=Rational{Int}, verbose::Bool=false, t0::Float64=time())
    bernoulli_numbers = [ -1//2, 1//6, 0//1, -1//30, 0//1, 1//42, 0//1, -1//30, 0//1, 
       5//66, 0//1, -691//2730, 0//1, 7//6, 0//1, -3617//510, 0//1, 43867//798, 0//1, 
       -174611//330, 0//1, 854513//138, 0//1, -236364091//2730, 0//1, 8553103//6, 0//1, 
       -23749461029//870, 0//1, 8615841276005//14322]
    
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
        for i=1:L.dim
            if L.nn[i]==n
                Z.c[i] = V.c[i]/n
            end
        end
        if verbose
            println(" time=",time()-t0);
        end
    end
    Z
end


function BCH1(G::Vector{Generator}, N::Int; 
             T::Type=Rational{Int}, verbose::Bool=false, M::Int=0)
    @assert length(G)==2 && allunique(G)
    t0 = time()
    if verbose
        println("initializing Lie algebra ...")
    end
    L = LieAlgebra(2, N, M=M, verbose=verbose, t0=t0)
    if verbose
        println("evaluating recursion formula ...")
    end
    Z = BCH(L, T=T, verbose=verbose, t0=t0)
    gen_expression(G, Z.c[1:L.dim], L.p1, L.p2)
end             
