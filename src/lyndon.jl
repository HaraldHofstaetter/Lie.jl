
########################################
#Algorithm 2.1 from
#  K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms to generate necklaces, 
#  unlabeled necklaces and irreducible polynomials over GF(2), J. Algorithms 37 (2) (2000) 267–282
function genLW(k::Int, n:: Int, t::Int, p::Int, a::Vector{Int}, W::Vector{Vector{Int}})
    if t>n
        if p==n
            push!(W, a[2:end])
        end
    else
        a[t+1] = a[t-p+1]
        genLW(k, n, t+1, p, a, W)
        for j=a[t-p+1]+1:k-1
            a[t+1] = j
            genLW(k, n, t+1, t, a, W)
        end
    end
end

function lyndon_words(k::Int, n::Int)
    a = zeros(Int, n+1)
    W = Vector{Int}[]
    genLW(k, n, 1, 1, a, W)
    W
end

function lyndon_words(k::Int, nn::Vector{Int})
    vcat([lyndon_words(k, n) for n in nn]...)
end



########################################
#Algorithm from
#  J. Sawada, F. Ruskey, Generating Lyndon brackets. An addendum to: Fast algorithms 
#  to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2),
#  J. Algorithms 46 (2003) 21–26
function gen_brackets(l::Int, r::Int, a::Vector{Int}, split::Matrix{Int})
    if l==r
        return a[l+1]
    else
        return [gen_brackets(l, split[l,r]-1, a, split), 
                gen_brackets(split[l,r], r, a, split)]
    end
end

function genLB(k::Int, n:: Int, t::Int, 
        p::Vector{Int}, split::Matrix{Int}, a::Vector{Int}; 
        W::Union{Nothing, Vector{Vector{Int}}}=nothing, 
        f::Union{Nothing, Vector{Int}}=nothing, 
        B::Union{Nothing, Vector{Any}}=nothing)
    if t>n
        if p[1]==n
            if !isnothing(W) 
                push!(W, a[2:end])
            end
            if !isnothing(f)
                push!(f, split[1,n])
            end
            if !isnothing(B)
                push!(B, gen_brackets(1, n, a, split))
            end
        end
    else
        q = copy(p)
        for j=a[t-p[1]+1]:k-1
            a[t+1] = j
            for i=1:t-1
                if a[t+1]<a[t-p[i]+1] 
                    p[i] = 0
                end 
                if a[t+1]>a[t-p[i]+1] 
                    p[i] = t-i+1
                end 
            end
            for i=t-1:-1:1 
                if p[i+1]==t-i 
                    split[i,t] = i+1
                else
                    split[i,t] = split[i+1,t]
                end 
            end
            genLB(k, n, t+1, p, split, a, W=W, f=f, B=B)
            p = copy(q)
        end
    end
end


function lyndon_basis(k::Int, n::Int)
    a = zeros(Int, n+1)
    p = ones(Int, n)
    split = zeros(Int, n, n)
    B = Any[]
    genLB(k, n, 1, p, split, a, B=B)
    B
end

function lyndon_basis(k::Int, nn::Vector{Int})
    vcat([lyndon_basis(k, n) for n in nn]...)
end



function lyndon_words_factored(k::Int, n::Int)
    a = zeros(Int, n+1)
    W = Vector{Int}[]
    p = ones(Int, n)
    split = zeros(Int, n, n)
    f = Int[]
    genLB(k, n, 1, p, split, a, W=W, f=f)
    W,f
end


function hom_class(K::Int, w::Vector{Int}, l::Int, r::Int)
    h = zeros(Int, K)
    for i=l:r 
        h[w[i]+1] += 1
    end
    h
end


#function word_to_index(K::Int, w::Vector{Int}, l::Int, r::Int)
#    x = w[r]
#    y = K
#    for j=r-1:-1:l
#        x += w[j]*y
#        y *= K
#    end
#    x
#end


function coeff(K::Int, w::Vector{Int}, l::Int, r::Int, j::Int, 
               p1::Vector{Int}, p2::Vector{Int}, 
               nn::Vector{Int}, h::Vector{Vector{Int}},
               H::Matrix{Vector{Int}})
  #             HT::Dict{Tuple{Int, Int, Int}, Int}, M::Int)
    if l==r 
        return @inbounds w[l]==j-1 ? 1 : 0
    end

 #   if r-l+1<=M # use hash table
 #       return get(HT, (j, r-l+1, word_to_index(K, w, l, r)), 0)  
 #   end

    if @inbounds H[l,r]!=h[j]
        return 0
    end

@inbounds j1 =p1[j]
@inbounds j2 =p2[j]
@inbounds m1 = nn[j1]
@inbounds m2 = nn[j2]

    if m1>m2
        c1 = coeff(K, w, l, l+m1-1, j1, p1, p2, nn, h, H)#, HT, M)
        if c1!=0
            c1 *= coeff(K, w, l+m1, r, j2, p1, p2, nn, h, H)#, HT, M)
        end
    
        c2 = coeff(K, w, l+m2, r,  j1, p1, p2, nn, h, H)#, HT, M)
        if c2!=0
            c2 *= coeff(K, w, l, l+m2-1, j2, p1, p2, nn, h, H)#, HT, M)
        end
    else
        c1 = coeff(K, w, l+m1, r, j2, p1, p2, nn, h, H)#, HT, M)
        if c1!=0
            c1 *= coeff(K, w, l, l+m1-1, j1, p1, p2, nn, h, H)#, HT, M)
        end
    
        c2 = coeff(K, w, l, l+m2-1, j2, p1, p2, nn, h, H)#, HT, M)
        if c2!=0
            c2 *= coeff(K, w, l+m2, r,  j1, p1, p2, nn, h, H)#, HT, M)
        end
    end

    c1 - c2
end

function lyndon_words_basis_trafo(K::Int, N::Int; verbose::Bool=false, M::Int=5)
    t0 = time()
    if verbose
        print("initializing...")
    end
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

    # generate hash table
    HT = Dict{Tuple{Int, Int, Int}, Int}()
    for n=2:M
        j1 = ii[n-1]
        j2 = ii[n]-1 
        for k=0:K^n-1
            w = [parse(Int, c) for c in string(k, base=K, pad=n)]
            for j=j1:j2
                c = coeff(K, w, 1, n, j, p1, p2, nn, hh, HT, n-1)
                if c!=0
                    HT[(j, n, k)] = c
                end
            end
        end
    end

    if verbose
        println("time=", time()-t0)
    end


    T = [Tuple{Int,Int}[] for i=1:ii[N]]
    for n=2:N
        if verbose
            print("n=$n: ")
        end
        j1 = ii[n-1]
        j2 = ii[n]-1 
        Threads.@threads for j=j1:j2
            for i=j+1:j2
                c = coeff(K, WW[i], 1, n, j, p1, p2, nn, hh, HT, M)
                if c!=0
                    push!(T[i], (j,c))
                end
            end
        end
        if verbose
            println("time=", time()-t0)
        end
    end

    WW, p1, p2, nn, T
end


function lyndon_basis_coeffs(G::Vector{Generator}, S::Element, N::Int; 
               T::Type=Rational{Int}, verbose::Bool=false, M::Int=0)
    t0 = time()
    if verbose
        print("initializing...")
    end
    K = length(G)
    @assert K>=2 && allunique(G)

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

#    # generate hash table
#    HT = Dict{Tuple{Int, Int, Int}, Int}()
#    for n=2:M
#        j1 = ii[n-1]
#        j2 = ii[n]-1 
#        for k=0:K^n-1
#            w = [parse(Int, c) for c in string(k, base=K, pad=n)]
#            for j=j1:j2
#                c = coeff(K, w, 1, n, j, p1, p2, nn, hh, HT, n-1)
#                if c!=0
#                    HT[(j, n, k)] = c
#                end
#            end
#        end
#    end
    if verbose
        println("time=", time()-t0)
    end

    cc = zeros(T, ii[N]-1)

 #   for n=1:N
 #       if verbose
 #           print("n=$n: ")
 #       end
 #       j1 = n==1 ? 1 : ii[n-1]
 #       j2 = ii[n]-1 
 #     # Threads.@threads 
 #       for i=j1:j2
 #         w = Word(G[WW[i] .+ 1])
 #           c = wcoeff(w, S, T=T)
 #           for j=1:i-1
 #               if !iszero(cc[j])
 #                   #c -= coeff(K, WW[i], 1, n, j, p1, p2, nn, hh, HT, M)*cc[j]
 #                   c -= coeff(K, WW[i], 1, n, j, p1, p2, nn, hh)*cc[j]
 #               end
 #           end
 #           cc[i] = c
 #       end
 #       if verbose
 #           println("time=", time()-t0)
 #       end
 #   end

    Threads.@threads for h in unique(hh)
       j1 = findfirst(x->x==h, hh)
       j2 = findlast(x->x==h, hh)
       for i=j1:j2
       if h==hh[i]
            n = nn[i]
            w = Word(G[WW[i] .+ 1])
            H = Vector{Int}[l<=r ? hom_class(K, WW[i], l,r) : [0,0] for l=1:n, r=1:n]
            c = wcoeff(w, S, T=T)
            for j=1:i-1
            if h==hh[j]
                if !iszero(cc[j])
                    #c -= coeff(K, WW[i], 1, n, j, p1, p2, nn, hh, HT, M)*cc[j]
                    c -= coeff(K, WW[i], 1, n, j, p1, p2, nn, hh, H)*cc[j]
                end
            end
            end
            cc[i] = c
        end
        end
    end

    WW, p1, p2, nn, cc, hh 
end






########################################
#Implemented by H. Hofstätter after the method described in
#  E.S. Chibrikov, A right normed basis for free Lie algebras
#  and Lyndon-Shirshov words, Journal of Algebra 302 (2006) 593–612
function analyze_lyndon_word(w::Array{Int,1})
    #println(w)
    q = maximum(w)
    A = Dict{Array{Int64,1}, Int}([[x]=>x for x in 1:q])
    w1 = Int[]
    
    lw = length(w)
    s = 1
    m1 = 1
    m2 = 0
    
    # get a
    a = minimum(w) 
    @assert w[s]==a
    
    #get av
    s += 1
    while s<=lw && w[s]!=a
        s += 1
    end
    v = w[2:s-1]   
    av = vcat(a,v)  
    #println("a=",a)
    #println("v=",v)
    lav = length(av)  
    while s<=lw
        if m2!=0 # do not change m2 in 1st iteration
            m1 = s
        end
        # get n
        n = 0
        while s+lav<=lw && w[s+lav]==a && w[s:s+lav-1]==av     
            s += lav
            n += 1
        end
        #println("s=",s ," n=", n)
        @assert w[s]==a
        s+=1     
    
        #get uu
        k = findnext(x->x==a, w, s)
        if k!=nothing
            uu = w[s:k-1]
            s = k
        else
            uu = w[s:end]
            s = lw+1
        end
        #do something with uu 
        j = 1
        #while !(lexless(v,uu[1:j])&&!lexless(v,uu[1:j-1]))
        while !((v<uu[1:j])&&!(v<uu[1:j-1]))
            j += 1
        end
        u = uu[1:j]
        u1 = uu[j+1:end]  
        m2 = s-length(u1)-1
        x = get!(A, w[m1:m2]) do
            q += 1
        end
        w1 = vcat(w1, x, u1)
        #println("n=",n," uu=",uu, " u=",u, " u1=",u1)
        #println("A_=", w[m1:m2])
    end   
    #println("w1=", w1)
    #pp = invperm([A[x] for x in sort(collect(keys(A)), lt=lexless)])
    pp = invperm([A[x] for x in sort(collect(keys(A)), lt=isless)])
    w2 = [pp[x] for x in  w1]
    tt = fill(Int[],q)
    for (x,y) in A
        tt[pp[y]] = x
    end    
    #println("---------------------")
    w2, tt
end


function lyndon2rightnormed(w::Array{Int, 1})
    aa = minimum(w)
    k=0 # number of occurences of a in w
    for x in w
        if x==aa
            k+=1
        end
    end
    if k==1
        return reverse(w)
    end
    w_1, tt = analyze_lyndon_word(w)
    u_1 = lyndon2rightnormed(w_1)
    y = tt[u_1[end]]
    a = y[1] 
    k0 = findnext(x->x==a, y, 2)
    k1 = findlast(x->x==a, y)
    v = y[2:k0-1]
    avn = y[k0:k1-1]
    u1 = y[k1+1:end]
    u = vcat(tt[u_1[1:end-1]]...,
             avn, a, u1, reverse(v), a)
end


function rightnormed_bracketing(w::Vector{Int})
    if length(w) == 1
        return w[1]
    end
    [w[1], rightnormed_bracketing(w[2:end])]
end

rightnormed_basis(k::Integer, n::Union{Int, Vector{Int}}) = 
  [rightnormed_bracketing(lyndon2rightnormed(w))  for w in lyndon_words(k, n)]


