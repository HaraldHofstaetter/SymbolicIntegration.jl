# This file contains algorithms needed for the integratiorn of
# rational functions from chapter 2 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


function HermiteReduce_original(A::PolyElem{T}, D::PolyElem{T}) where T <: FieldElement
    # See Bronstein's book, Section 2.2, p. 40
    Ds = Squarefree(D)
    n = length(Ds)
    P, As = PartialFraction(A, [Ds[j]^j for j=1:n])
    g = zero(D)//one(D) # rational function with value 0
    h = P + As[1]//Ds[1] # rational function
    for k=2:n
        if degree(Ds[k])>0
            V = Ds[k]
            for j=k-1:-1:1
                B, C = gcdx(derivative(V), V, -divexact(As[k], j))
                g += B//V^j
                As[k] = -j*C - derivative(B)
            end
            h += As[k]//V
        end
    end
    g, h
end

function HermiteReduce_quadratic(A::PolyElem{T}, D::PolyElem{T}) where T <: FieldElement
    # See Bronstein's book, Section 2.2, p. 41
    g = zero(D)//one(D) # rational function with value 0
    Ds = Squarefree(D)
    m = length(Ds)
    for i=2:m
        if degree(Ds[i])>0
            V = Ds[i]
            U = divexact(D, V^i)
            for j=i-1:-1:1
                B, C = gcdx(U*derivative(V), V, -divexact(A, j))
                g += B//V^j
                A = -j*C - U*derivative(B)
            end
            D = U*V
        end
    end
    g, A//D
end

function HermiteReduce(A::PolyElem{T}, D::PolyElem{T}) where T <: FieldElement
    # See Bronstein's book, Section 2.2, p. 44
    g = zero(D)//one(D) # rational function with value 0
    Dminus = gcd(D, derivative(D))
    Dstar = divexact(D, Dminus)
    while degree(Dminus)>0
        Dminus2 = gcd(Dminus, derivative(Dminus))
        Dminusstar = divexact(Dminus, Dminus2)
        B, C = gcdx(-divexact(Dstar*derivative(Dminus), Dminus), Dminusstar, A)
        A = C - divexact(derivative(B)*Dstar, Dminusstar)
        g += B//Dminus
        Dminus = Dminus2
    end
    return g, A//Dstar
end

struct SumOfLogTerms{T<:FieldElement, P<:PolyElem{T}} <: Term
    R::P
    S::PolyElem{P}
end

function Base.show(io::IO, t::SumOfLogTerms)
    s = string(parent(t.R).S)
    print(io, "Σ_{$s: ")
    show(io, t.R)
    print(io, " = 0}$s*log(")
    show(io, t.S)
    print(io, ")")
end

function IntRationalLogPart(A::PolyElem{T}, D::PolyElem{T}; make_monic::Bool=false, symbol=:α) where T <: FieldElement
    # See Bronstein's book, Section 2.5, p. 51 
    F = base_ring(A)
    Ft, t = PolynomialRing(F, symbol)
    FtX, X = PolynomialRing(Ft, symbols(parent(A))[1])
    R, Rs = SubResultant(D(X), A(X)-t*derivative(D)(X))
    Qs = Squarefree(R)
    ds = degree.(Qs)
    Qs = [f for f in Qs if degree(f)>0]
    Ss = typeof(X)[] 
    ii = 1
    for i=1:length(ds)
        if ds[i]>0
            if i==degree(D)
                S = D(X)
            else
                m = findfirst(z->z==i, degree.(Rs))
                S =  Rs[m]
                As = Squarefree(leading_coefficient(S))
                for j=1:length(As)
                    S = divexact(S, gcd(As[j],Qs[ii])^j)
                end
            end     
            if make_monic
                Qs[ii] = divexact(Qs[ii], leading_coefficient(Qs[ii]))
                h = invmod(leading_coefficient(S), Qs[ii])
                S = FtX([rem(h*c, Qs[ii]) for c in coefficients(S)])
            else
                S = FtX([rem(c, Qs[ii]) for c in coefficients(S)])                            
            end
            push!(Ss, S)
            ii+=1                        
        end
    end
    [SumOfLogTerms(Q, S) for (Q, S) in zip(Qs, Ss)]
end

function IntegrateRationalFunction(f::FracElem{P}; symbol=:α) where {T<:FieldElement, P<:PolyElem{T}}    
    # See Bronstein's book, Section 2.5, p. 52 
    g, h = HermiteReduce(numerator(f), denominator(f))
    Q, R = divrem(numerator(h), denominator(h))
    result = [IdTerm(integral(Q)), IdTerm(g)]
    if !iszero(R)
        result = vcat(result, IntRationalLogPart(R, denominator(h), make_monic=true, symbol=symbol)...)
    end
    result
end

function Complexify(R::PolyElem{T}; symbols=[:α, :β]) where T <: FieldElement
    F = base_ring(R)
    Fuv, uv = PolynomialRing(F, symbols)
    u = uv[1]
    v = uv[2]
    c = collect(coefficients(R))
    d = length(c)-1
    P = sum([sum([(-1)^div(k,2)*binomial(n,k)*c[n+1]*u^(n-k)*v^k for k=0:n if iseven(k)]) for n=0:d])
    if (d==0)
        Q = zero(Fuv)
    else
        Q = sum([sum([(-1)^div(k,2)*binomial(n,k)*c[n+1]*u^(n-k)*v^k for k=1:n if isodd(k)]) for n=1:d])   
    end
    P,Q
end

function LogToAtan(A::PolyElem{T}, B::PolyElem{T}) where T <: FieldElement
    # See Bronstein's book, Section 2.8, p. 63 
    Q, R = divrem(A, B)
    if iszero(R)
        return [FunctionTerm(atan, 2, Q)]
    end
    if degree(A)<degree(B)
        return LogToAtan(-B, A)
    end
    G, D, C = gcdx(B, -A)
    return vcat(FunctionTerm(atan, 2, divexact(A*D+B*C, G)), LogToAtan(D, C))
end

struct SumOfRealTerms <: Term
    R
    S
    P
    Q
    LT::Term # log term
    ATs::Vector{Term} #atan terms
end

function Base.show(io::IO, t::SumOfRealTerms)
    s = string.(parent(t.P).S)
    print(io, "Σ_{$(s[1]),$(s[2]): $(s[2])>0, ")
    show(io, t.P)
    print(io, " = ") 
    show(io, t.Q)
    print(io, " = 0}")
    show(io, t.LT)
    print(io, " + $(s[2])*(")
    print(io, join(string.(t.ATs), "+"))
    print(io, "))")
    s0 = string(parent(t.R).S)
    print(io, " + Σ_{$s0: Im($s0)=0, ")
    show(io, t.R)
    print(io, " = 0}$s0*log(")
    show(io, t.S)
    print(io, ")")

end

function LogToReal(t::SumOfLogTerms; symbols=[:α, :β]) #{T, PP}) where {T<:FieldElement, PP<:PolyElem{T}}
    # See Bronstein's book, Section 2.8, p. 69 
    F = base_ring(t.R)
    R, uv = PolynomialRing(F, symbols)
    K = FractionField(R)
    Kx, x = PolynomialRing(K, "x")
    P, Q = Complexify(t.R)
    cc =[Complexify(c) for c in coefficients(t.S)]
    A = Kx([c[1] for c in cc])
    B = Kx([c[2] for c in cc])
    SumOfRealTerms(t.R, t.S, P, Q, FunctionTerm(log, 1, A^2+B^2), LogToAtan(A, B))
end

