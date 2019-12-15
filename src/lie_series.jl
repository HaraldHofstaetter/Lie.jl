function hom_class(K::Int, w::Vector{Int}, l::Int, r::Int)
    h = zeros(Int, K)
    for i=l:r 
        h[w[i]+1] += 1
    end
    h
end


function word_to_index(K::Int, w::Vector{Int}, l::Int, r::Int)
    x = w[r]
    y = K
    for j=r-1:-1:l
        x += w[j]*y
        y *= K
    end
    x + div(y-1, K-1)
end


function coeff(K::Int, w::Vector{Int}, l::Int, r::Int, j::Int, 
               p1::Vector{Int}, p2::Vector{Int}, 
               nn::Vector{Int}, h::Vector{Vector{Int}},
               H::Matrix{Vector{Int}},
               W2I::Matrix{Int},
               #CT::Dict{Tuple{Int, Int}, Int},
               CT::Matrix{Int},
               M::Int)
    if l==r 
        return @inbounds w[l]==j-1 ? 1 : 0
    end

    if @inbounds H[l,r]!=h[j]
        return 0
    end

    if r-l+1<=M # use lookup table
        #return get(CT, (j, W2I[l,r]), 0)  
        return @inbounds CT[j, W2I[l,r]]
    end

@inbounds j1 =p1[j]
@inbounds j2 =p2[j]
@inbounds m1 = nn[j1]
@inbounds m2 = nn[j2]

    if m1<m2
        c1 = coeff(K, w, l, l+m1-1, j1, p1, p2, nn, h, H, W2I, CT, M)
        if c1!=0
            c1 *= coeff(K, w, l+m1, r, j2, p1, p2, nn, h, H, W2I, CT, M)
        end
    
        c2 = coeff(K, w, l+m2, r,  j1, p1, p2, nn, h, H, W2I, CT, M)
        if c2!=0
            c2 *= coeff(K, w, l, l+m2-1, j2, p1, p2, nn, h, H, W2I, CT, M)
        end
    else
        c1 = coeff(K, w, l+m1, r, j2, p1, p2, nn, h, H, W2I, CT, M)
        if c1!=0
            c1 *= coeff(K, w, l, l+m1-1, j1, p1, p2, nn, h, H, W2I, CT, M)
        end
    
        c2 = coeff(K, w, l, l+m2-1, j2, p1, p2, nn, h, H, W2I, CT, M)
        if c2!=0
            c2 *= coeff(K, w, l+m2, r,  j1, p1, p2, nn, h, H, W2I, CT, M)
        end
    end

    c1 - c2
end

function init_lie(K::Int, N::Int, M::Int)
    WW = [[c] for c=0:K-1]
    p1 = collect(1:K)
    p2 = zeros(Int, K)
    nn = ones(Int, K)
    hh = [hom_class(K, [c], 1, 1) for c=0:K-1]
    wordindex = Dict{Vector{Int},Int}([[i-1]=>i for i=1:K]...)
    index = K+1
    ii = zeros(Int, N)
    ii[1] = index 
    for n=2:N
        W,f = lyndon_words_factored(K, n)
        for j=1:length(W)
            w = W[j]
            s1 = w[1:f[j]-1]
            s2 = w[f[j]:end]
            wordindex[w]=index
            push!(p1, wordindex[s1])
            push!(p2, wordindex[s2])
            push!(nn, n)
            push!(hh, hom_class(K, w, 1, n))
            index += 1
        end
        append!(WW, W)
        ii[n] = index
    end

    # generate coefficients lookup table

    #CT = Dict{Tuple{Int, Int}, Int}()
    #for n=1:M
    #    i1 = n==1 ? 1 : ii[n-1]
    #    i2 = ii[n]-1 
    #    for k=0:K^n-1
    #        w = [parse(Int, c) for c in string(k, base=K, pad=n)]
    #        H = Vector{Int}[l<=r ? hom_class(K, w, l,r) : [0,0] for l=1:n, r=1:n]
    #        M2I = Int[l<=r && r-l+1<=M ? word_to_index(K, w, l,r) : 0
    #                                             for l=1:n, r=1:n]
    #        wi = word_to_index(K, w, 1, n)
    #        for j=i1:i2
    #            c = coeff(K, w, 1, n, j, p1, p2, nn, hh, H, M2I, CT, n-1)
    #            if c!=0
    #                CT[(j, wi)] = c
    #            end
    #        end
    #    end
    #end

    CT = zeros(Int, M==0 ? 0 : ii[M]-1, div(K^(M+1)-1, K-1)-1)
    for n=1:M
        i1 = n==1 ? 1 : ii[n-1]
        i2 = ii[n]-1 
        for k=0:K^n-1
            w = [parse(Int, c) for c in string(k, base=K, pad=n)]
            H = Vector{Int}[l<=r ? hom_class(K, w, l,r) : [0,0] for l=1:n, r=1:n]
            M2I = Int[l<=r && r-l+1<=M ? word_to_index(K, w, l,r) : 0
                                                 for l=1:n, r=1:n]
            wi = word_to_index(K, w, 1, n)
            for j=i1:i2
                c = coeff(K, w, 1, n, j, p1, p2, nn, hh, H, M2I, CT, n-1)
                if c!=0
                    CT[j, wi] = c
                end
            end
        end
    end
    p1, p2, nn, WW, ii, hh, CT
end



function lie_series(G::Vector{Generator}, S::AlgebraElement, N::Int; 
               T::Type=Rational{Int}, verbose::Bool=false, M::Int=0,
               lists_output::Bool=false)
    t0 = time()
    if verbose
        print("initializing...")
    end
    K = length(G)
    @assert K>=2 && allunique(G)

    p1, p2, nn, WW, ii, hh, CT = init_lie(K, N, M)

    if verbose
        println("time=", time()-t0)
        print("coeffs of words...")
    end

    cc = zeros(T, length(WW))
    Threads.@threads for i=1:length(WW)
        cc[i] = wcoeff(Word(G[WW[i] .+ 1]), S, T=T)
    end

    if verbose
        println("time=", time()-t0)
        print("coeffs of basis elements...")
    end

    for n=1:N
        i1 = n==1 ? 1 : ii[n-1]
        i2 = ii[n]-1 
        hu = unique(hh[i1:i2])
        Threads.@threads for h in hu 
            for i=i1:i2
            if h==hh[i]
                 H = Vector{Int}[l<=r ? hom_class(K, WW[i], l,r) : [0,0] for l=1:n, r=1:n]
                 W2I = Int[l<=r && r-l+1<=M ? word_to_index(K, WW[i], l,r) : 0 
                                                      for l=1:n, r=1:n]
                 for j=i1:i-1
                 if h==hh[j]
                     if !iszero(cc[j])
                         cc[i] -= coeff(K, WW[i], 1, n, j, p1, p2, nn, hh, H, W2I, CT, M)*cc[j]
                     end
                 end
                 end
             end
             end
         end
    end

    if verbose
        println("time=", time()-t0)
    end
    
    if lists_output
        return p1, p2, nn, cc
    else
        return gen_expression(G, cc, p1, p2)
    end
end


mutable struct LieAlgebra
    K::Int # number of generators
    N::Int # maximum order 
    dim::Int
    p1::Vector{Int}
    p2::Vector{Int}
    nn::Vector{Int}
    S::Vector{Vector{Tuple{Int,Int,Int}}}
end



function LieAlgebra(K::Int, N::Int; M::Int=0)
    @assert K>=2

    p1, p2, nn, WW, ii, hh, CT = init_lie(K, N, M)

    for i=1:length(WW)
        println("i=$i ---------------------------------")
        n = nn[i]
        h = hh[i]
        w = WW[i]
        H = Vector{Int}[l<=r ? hom_class(K, w, l,r) : [0,0] for l=1:n, r=1:n]
        W2I = Int[l<=r && r-l+1<=M ? word_to_index(K, w, l,r) : 0 for l=1:n, r=1:n]
        for n1 = 1:div(n,2)
            n2 = n-n1
            for j1 = (n1==1 ? 1 : ii[n1-1]) : ii[n1]-1
            for j2 = (n2==1 ? 1 : ii[n2-1]) : ii[n2]-1
                if j1<j2 && hh[j1]+hh[j2]==h
                    c1 = coeff(K, w, 1, n1, j1, p1, p2, nn, hh, H, W2I, CT, M)
                    if c1!=0
                        c1 *= coeff(K, w, n1+1, n, j2, p1, p2, nn, hh, H, W2I, CT, M)
                    end
    
                    c2 = coeff(K, w, n2+1, n,  j1, p1, p2, nn, hh, H, W2I, CT, M)
                    if c2!=0
                        c2 *= coeff(K, w, 1, n2, j2, p1, p2, nn, hh, H, W2I, CT, M)
                    end
                    c = c1 - c2
                    if c!=0 
                        print("($j1, $j2)=>$c, ") 
                    end
                end
            end
            end
        end
        println()
    end

#    for n=1:N
#        i1 = n==1 ? 1 : ii[n-1]
#        i2 = ii[n]-1 
#        hu = unique(hh[i1:i2])
#        Threads.@threads for h in hu 
#            for i=i1:i2
#            if h==hh[i]
#                 H = Vector{Int}[l<=r ? hom_class(K, WW[i], l,r) : [0,0] for l=1:n, r=1:n]
#                 M2I = Int[l<=r && r-l+1<=M ? word_to_index(K, WW[i], l,r) : 0 
#                                                      for l=1:n, r=1:n]
#                 for j=i1:i-1
#                 if h==hh[j]
#                     if !iszero(cc[j])
#                         cc[i] -= coeff(K, WW[i], 1, n, j, p1, p2, nn, hh, H, M2I, CT, M)*cc[j]
#                     end
#                 end
#                 end
#             end
#             end
#         end
#    end
    
end
