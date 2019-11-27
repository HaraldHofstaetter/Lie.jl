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


function lyndon_basis(k::Int, n::Int; lyndon_words::Bool=false)
    a = zeros(Int, n+1)
    W = lyndon_words ? Vector{Int}[] : nothing
    p = ones(Int, n)
    split = zeros(Int, n, n)
    B = Any[]
    genLB(k, n, 1, p, split, a, W=W, B=B)
    if lyndon_words
        return W, B
    else
        return B
    end
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
