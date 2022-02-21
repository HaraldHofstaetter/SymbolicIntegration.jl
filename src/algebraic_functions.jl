
function HermiteReduce(f::AbstractAlgebra.ResFieldElem{P}, DE::AlgebraicExtensionDerivation) where 
    {T<:FieldElement, P<:PolyElem{T}}    
    iscompatible(f, DE) || error("rational function f must be in the domain of derivation D")

    E = parent(f)
    F = base_ring(base_ring(E))
    y = E(gen(base_ring(E)))
    p = modulus(E)
    n = degree(p)
    M_n_n = MatrixSpace(F, n, n)
    M_n = MatrixSpace(F, n, 1)   

    g = zero(E)

    if all([iszero(coeff(p, j)) for j=1:n-1]) # simple radical extension    
        @assert isone(leading_coefficient(p))
        a = constant_coefficient(p)
        A = numerator(a)
        D = denominator(a)
        As = Squarefree(A*D^(n-1))
        k = length(As)
        qrs = [divrem(i, n) for i=1:k]
        qs = [q for (q, r) in qrs]
        rs = [r for (q, r) in qrs]
        F = prod([As[i]^qs[i] for i=1:k])
        H = prod([As[i]^rs[i] for i=1:k])
        z = y*D//F
        Hs = Squarefree(H)
        m = length(Hs)
        ws = [z^(i-1)*1//prod([Hs[j]^div((i-1)*j, n) for j=1:m]) for i=1:n]
        Ds = [prod([Hs[j]^div((i-1)*j, n) for j=1:m]) for i=1:n] # note: index shift in i
        dDs_over_Ds = [derivative(D)//D for D in Ds]
        dH_over_H = derivative(H)//H
        Winv = inv(M_n_n([coeff(data(w), j) for j=0:n-1, w in ws]))
        while true            
            fs = Winv*M_n([coeff(data(f), i) for i=0:n-1])
            D = lcm(denominator.(fs)[:,1])
            As = [numerator(f*D) for f in fs]
            if degree(gcd(D, derivative(D)))<= 0 #  D squarefree?
                return g, f, ws, As, D
            end

            Ds1 = Squarefree(D) # "Ds1" because "Ds" already in use and needed below
            m = length(Ds1)
            V = Ds1[m]
            U = divexact(D, V^m)
            dV = derivative(V)

            fs = [As[i]//(U*(V*((i-1)//n*dH_over_H - dDs_over_Ds[i]) - (m-1)*dV)) for i=1:n]
            Q = lcm(denominator.(fs)[:,1])
            Ts = [numerator(f*Q) for f in fs]
            _, _, R = gcdx(V, Q)            
            B = sum([rem(R*Ts[i], V)*ws[i] for i=1:n])*1//V^(m - 1)
            g += B
            f -= DE(B)
        end
    end
 
    ws = [y^j for j=0:n-1]
    Winv = M_n_n(1) 

    while true        
        fs = Winv*M_n([coeff(data(f), i) for i=0:n-1])
        D = lcm(denominator.(fs)[:,1])
        As = [numerator(f*D) for f in fs]
        if degree(gcd(D, derivative(D)))<= 0 #  D squarefree?
            return g, f, ws, As, D
        end

        Ds = Squarefree(D)
        m = length(Ds)
        V = Ds[m]
        U = divexact(D, V^m)

        Ss = [U*V^m*DE(w*1//V^(m-1)) for w in ws]

        SM = M_n_n([coeff(data(S), j) for j=0:n-1, S in Ss])
        d, N = nullspace(SM)        
        if d>0 # Theorem 1
            _, N = nullspace(SM)            
            w0 = U//V*sum(N[i,1]*ws[i] for i=1:n)
        else
            fs = solve(SM, M_n(As))
            Q = lcm(denominator.(fs)[:,1])            
            Ts = [numerator(f*Q) for f in fs]
            w0 = zero(parent(f))
            gcdVQ = gcd(V, Q)
            if degree(gcdVQ)>=1 # Theorem 2
                w0 = U*divexact(V, gcdVQ)//gcdVQ*sum([Ts[i]*ws[i] for i=1:n])
            else                
                j = 1                
                while j<=n
                    dw = DE(ws[j])
                    dws = Winv*M_n([coeff(data(dw), i) for i=0:n-1])
                    F = lcm(denominator.(dws)[:,1])
                    if degree(gcd(F, derivative(F)))>=1 # denominator F of ws[j]' not squarefree, apply Theorem 3
                        w0 = prod(Squarefree(F))*dw
                        break
                    end
                    j += 1
                end                
                if j>n # all denominators of the ws[j]' squarefree, do the reduction
                    _, _, R = gcdx(V, Q)
                    B = sum([rem(R*Ts[i], V)*ws[i] for i=1:n])*1//V^(m - 1)
                    g += B
                    f -= DE(B)
                    ws = [y^j for j=0:n-1]
                    Winv = M_n_n(1)
                    continue
                end
            end
        end

        C0s = solve(M_n_n([coeff(data(w), j) for j=0:n-1, w in ws]), M_n([coeff(data(w0), i) for i=0:n-1]))
        F = lcm(denominator.(C0s)[:,1])
        Cs = [numerator(C0*F) for C0 in C0s]

        C = zero_matrix(parent(F), n+1, n)
        for j=1:n
            C[j,j] = F
        end
        for j=1:n
            C[n+1,j] = Cs[j]
        end
        C = hnf(C)

        ws = [sum([C[i,j]*ws[j] for j=1:n])*1//F for i=1:n]                
        Winv = inv(M_n_n([coeff(data(w), j) for j=0:n-1, w in ws]))        
    end    
end