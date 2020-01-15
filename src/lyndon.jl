# from https://mathoverflow.net/questions/99473/calculating-m%C3%B6bius-function
# (answer by reuns)
function moebius_mu(N)
    mu = zeros(Int, N)
    mu[1] = 1
    for n = 1:div(N,2)
        mu[2*n:n:end] .-= mu[n]
    end
    mu 
end


# Witt's formula:

function number_of_lyndon_words(K::Integer, N::Int, N0::Int=N)
    if N0>N
        (N0, N) = (N, N0)
    end
    mu = moebius_mu(N)
    nn = zeros(Int, N-N0+1)
    for n=N0:N
        d = 1
        h = 0
        while d^2 < n
            (d1, r) = divrem(n, d)
            if r==0
               h += mu[d]*K^d1+mu[d1]*K^d
            end
            d += 1
        end
        if d^2 == n
            h +=mu[d]*K^d
        end
        nn[n-N0+1] = div(h, n)
    end
    N==N0 ? nn[1] : nn
end


########################################
#Algorithm 2.1 from
#  K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms to generate necklaces, 
#  unlabeled necklaces and irreducible polynomials over GF(2), J. Algorithms 37 (2) (2000) 267–282

function transform_to_graded(w::Vector{Int})
    if w==[0]
        return Int[]
    end
    w1 = Int[]
    c = 0
    for x in w[2:end]
        if x==1
            c +=1
        else
            push!(w1, c)
            c = 0
        end
    end
    push!(w1, c)
    w1
end


function genLW(k::Int, n:: Int, t::Int, p::Int, a::Vector{Int}, W::Vector{Vector{Int}}; 
               max_grade::Int=1)
    if t>n
        if p==n
            if max_grade>1
                w1 = transform_to_graded(a[2:end])
                if length(w1)>0 && maximum(w1)<max_grade
                    push!(W, w1)
                end
            else
                push!(W, a[2:end])
            end
        end
    else
        a[t+1] = a[t-p+1]
        genLW(k, n, t+1, p, a, W, max_grade=max_grade)
        for j=a[t-p+1]+1:k-1
            a[t+1] = j
            genLW(k, n, t+1, t, a, W, max_grade=max_grade)
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

function lyndon_words_graded(n::Int; max_grade::Int=typemax(Int))
    @assert max_grade > 1
    a = zeros(Int, n+1)
    W = Vector{Int}[]
    genLW(2, n, 1, 1, a, W, max_grade=max_grade)
    W
end

function lyndon_words_graded(nn::Vector{Int}; max_grade::Int=typemax(Int))
    vcat([lyndon_words_graded(n, max_grade=max_grade) for n in nn]...)
end




########################################
#Algorithm from
#  J. Sawada, F. Ruskey, Generating Lyndon brackets. An addendum to: Fast algorithms 
#  to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2),
#  J. Algorithms 46 (2003) 21–26
function gen_brackets(l::Int, r::Int, a::Vector{Int}, split::Matrix{Int}; graded::Bool=false)
    if l==r
        if graded 
            0 
        else
            return a[l+1]
        end
    elseif graded && a[l+1]==0 && a[l+2:r+1]==ones(Int, r-l)
        return r-l
    else
        return [gen_brackets(l, split[l,r]-1, a, split, graded=graded), 
                gen_brackets(split[l,r], r, a, split, graded=graded)]
    end
end

function genLB(k::Int, n:: Int, t::Int, 
        p::Vector{Int}, split::Matrix{Int}, a::Vector{Int}; 
        W::Union{Nothing, Vector{Vector{Int}}}=nothing, 
        f::Union{Nothing, Vector{Int}}=nothing, 
        B::Union{Nothing, Vector{Any}}=nothing,
        max_grade::Int=1)
    if t>n
        if p[1]==n
            if max_grade>1
                w1 = transform_to_graded(a[2:end])
                if length(w1)>0 && maximum(w1)<max_grade
                    if !isnothing(W) 
                        push!(W, w1)
                    end
                    if !isnothing(f)
                        push!(f, split[1,n]) # TODO: implement correctly for graded...
                    end
                    if !isnothing(B)
                        push!(B, gen_brackets(1, n, a, split, graded=true))
                    end
                end
            else
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
            genLB(k, n, t+1, p, split, a, W=W, f=f, B=B, max_grade=max_grade)
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


function lyndon_basis_graded(n::Int; max_grade::Int=typemax(Int))
    @assert max_grade > 1
    a = zeros(Int, n+1)
    p = ones(Int, n)
    split = zeros(Int, n, n)
    B = Any[]
    genLB(2, n, 1, p, split, a, B=B, max_grade=max_grade)
    B
end

function lyndon_basis_graded(nn::Vector{Int}; max_grade::Int=typemax(Int))
    vcat([lyndon_basis_graded(n, max_grade=max_grade) for n in nn]...)
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

rightnormed_basis_graded(n::Union{Int, Vector{Int}}; max_grade::Int=typemax(Int)) = 
  [rightnormed_bracketing(lyndon2rightnormed(w))  for w in lyndon_words_graded(n, max_grade=max_grade)]


