function LieAlgebra(T::TreeAlgebra; verbose::Bool=false, t0::Float64=time())
    #counter = 0
    #CCC =Int[]
    #TTT =Float64[]

    ii=vcat([findfirst(x->x==n, T.nn) for n=1:T.N], T.dim+1)

    X = [Dict{Int, Int}() for i=1:T.dim]
    for i=1:T.K
        X[i][i] = 1
    end

    for j=T.K+1:T.dim
        @inbounds j1 = T.p1[j]
        @inbounds j2 = T.p2[j]
        @inbounds X1 = X[j1]
        @inbounds X2 = X[j2]
        @inbounds h = T.hh[j1]+T.hh[j2]
        @inbounds n = T.nn[j]

        @inbounds X[j][j] = T.sigma[j] 
        for i=T.dim+1:T.ntrees
            uu = T.S[i]
            @inbounds if T.nn[i]==n && T.hh[i]==h
                c = 0
                for j=1:length(uu)
                    @inbounds u1 = uu[j][1]
                    @inbounds u2 = uu[j][2]
                    c1 = get(X1, u1, 0)
                    if c1 != 0
                        c1 *= get(X2, u2, 0) 
                    end
                    c2 = get(X2, u1, 0)
                    if c2 != 0
                        c2 *= get(X1 , u2, 0)
                    end
                    c += c1 - c2
                end
                if c!=0
                   @inbounds X[j][i] = c
                end
            end
       end
    end

    S = [Array{Int,1}[] for i=1:T.dim]

    #t1 = time()
    for n=1:T.N
        if verbose
            print("n=$n ... ")
        end
        @inbounds i1 = ii[n]
        @inbounds i2 = ii[n+1]-1 
        @inbounds hu = unique(T.hh[i1:i2])
        Threads.@threads for h in hu
            #@inbounds factors = [[j1, j2] for n1 = 1:div(n,2)
            #                              for j1 = ii[n1] : ii[n1+1]-1 
            #                              for j2 = max(j1+1, ii[n-n1]) : ii[n-n1+1]-1 
            #                              if T.hh[j1]+T.hh[j2]==h]
            @inbounds f1 = [j1 for n1 = 1:div(n,2)
                    for j1 = ii[n1] : ii[n1+1]-1
                    for j2 = max(j1+1, ii[n-n1]) : ii[n-n1+1]-1
                    if T.hh[j1]+T.hh[j2]==h]
            @inbounds f2 = [j2 for n1 = 1:div(n,2)
                    for j1 = ii[n1] : ii[n1+1]-1
                    for j2 = max(j1+1, ii[n-n1]) : ii[n-n1+1]-1
                    if T.hh[j1]+T.hh[j2]==h]
            for i=i1:i2
                @inbounds if h==T.hh[i]
                    uu = T.S[i]
                    len_u = length(uu)
                    #for l = 1:length(factors)
                    #    @inbounds j1 = factors[l][1]
                    #    @inbounds j2 = factors[l][2]
                    for l = 1:length(f1)
                        @inbounds j1 = f1[l]
                        @inbounds j2 = f2[l]
                        @inbounds X1 = X[j1]
                        @inbounds X2 = X[j2]
                        c = 0
                        for j=1:len_u
                            @inbounds u1 = uu[j][1]
                            @inbounds u2 = uu[j][2]
                            c1 = get(X1, u1, 0)
                            if c1 != 0
                                c1 *= get(X2, u2, 0) 
                            end
                            c2 = get(X2, u1, 0)
                            if c2 != 0
                                c2 *= get(X1, u2, 0)
                            end
                            c += c1 - c2
                        end
                        if c!=0
                            @inbounds push!(S[i], [j1, j2, div(c, T.sigma[i])])
                        end
                        #counter += 1
                    end
                end
            end
        end
        if verbose
            println(time()-t0)
        end
        #push!(CCC, counter)
        #push!(TTT, time()-t1)
    end

    LieAlgebra(T.K, T.N, T.dim, T.p1, T.p2, T.nn[1:T.dim], S) #, CCC, TTT
end



