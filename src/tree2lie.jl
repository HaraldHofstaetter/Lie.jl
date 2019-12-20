function tree2lie(T::TreeAlgebra; verbose::Bool=false, t0::Float64=time())

    ii=vcat([findfirst(x->x==n, T.nn) for n=1:T.N], T.dim+1)
    hh = [ [j==k ? 1 : 0 for j=1:T.K] for k=1:T.K ]
    for j=T.K+1:T.ntrees
        @inbounds push!(hh, hh[T.T.T[j][1]+1]+sum([hh[T.T.T[j][i]] for i=2:length(T.T.T[j])]))
    end

    X = [Dict{Int, Int}() for i=1:T.dim]
    for i=1:T.K
        X[i][i] = 1
    end

    for j=T.K+1:T.dim
        @inbounds j1 = T.p1[j]
        @inbounds j2 = T.p2[j]
        @inbounds n = T.nn[j]

        @inbounds X[j][j] = T.sigma[j] 
        for i=T.dim+1:T.ntrees
            uu = T.S[i]
            @inbounds if T.nn[i]==n && hh[i]==hh[j1]+hh[j2]
                c = 0
                for j=1:length(uu)
                    @inbounds c += get(X[j1], uu[j][1], 0)*get(X[j2], uu[j][2], 0) - 
                         get(X[j2], uu[j][1], 0)*get(X[j1], uu[j][2], 0)
                end
                if c!=0
                   @inbounds X[j][i] = c
                end
            end
       end
    end

    S = [Array{Int,1}[] for i=1:T.dim]

    for n=1:T.N
        if verbose
            print("n=$n ... ")
        end
        i1 = ii[n]
        i2 = ii[n+1]-1 
        hu = unique(hh[i1:i2])
        for h in hu
            factors = [[j1, j2] for n1 = 1:div(n,2)
                    for j1 = ii[n1] : ii[n1+1]-1
                    for j2 = ii[n-n1] : ii[n-n1+1]-1
                    if j1<j2 && hh[j1]+hh[j2]==h]
            for i=i1:i2
                if h==hh[i]
                    uu = T.S[i]
                    for l = 1:length(factors)
                        j1 = factors[l][1]
                        j2 = factors[l][2]
                        c = 0
                        for j=1:length(uu)
                            c += get(X[j1], uu[j][1], 0)*get(X[j2], uu[j][2], 0) - 
                                 get(X[j2], uu[j][1], 0)*get(X[j1], uu[j][2], 0)
                        end
                        if c!=0
                            push!(S[i], [j1, j2, div(c, T.sigma[i])])
                        end
                    end
                end
            end
        end
        if verbose
            println(time()-t0)
        end
    end

    LieAlgebra(T.K, T.N, T.dim, T.p1, T.p2, T.nn[1:T.dim], S)
end



