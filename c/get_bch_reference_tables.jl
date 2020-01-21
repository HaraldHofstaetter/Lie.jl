function word(i::Int, p1::Array{Int, 1}, p2::Array{Int, 1})
    if i<=2
        return [i-1]
    else
        return vcat(word(p1[i], p1, p2), word(p2[i], p1, p2))
    end
end

function transform_bchLyndon_table(in::String, out::String) 
    X = readlines(in)[1:2:end] # [1:2:end] for removing empty lines 
    len = length(X)

    W = fill(Int[],len)
    nn = zeros(Int, len)
    p1 = zeros(Int, len)
    p2 = zeros(Int, len)
    num = zeros(Int128, len)
    den = zeros(Int128, len)
    
    for i=1:len
        s = split(X[i])
        p1[i] = parse(Int, s[2])
        p2[i] = parse(Int, s[3])
        num[i] = parse(Int128, s[4])
        den[i] = parse(Int128, s[5])
        W[i] = word(i, p1, p2)
        nn[i] = length(W[i])
    end
    p2[1] = 1
    p2[2] = 1

    # order Lyndon words primarily by length, secondarily by lexicographical order
    P = sort(1:len, lt=(x,y)->(nn[x]<nn[y] || (nn[x]==nn[y] && W[x]<W[y])))
    Q = invperm(P)

    open(out, "w") do io
        for i=1:len
            println(io, "$(i-1)\t$(nn[P[i]])\t$(Q[p1[P[i]]]-1)\t$(Q[p2[P[i]]]-1)\t$(num[P[i]])/$(den[P[i]])")
        end
    end
end

transform_bchLyndon_table(download("http://www.ehu.eus/ccwmuura/research/bchLyndon20.dat"), 
                          "bch_N20_reference.txt") 
transform_bchLyndon_table(download("http://www.ehu.eus/ccwmuura/research/sbchLyndon19.dat"), 
                          "sbch_N19_reference.txt") 
 
