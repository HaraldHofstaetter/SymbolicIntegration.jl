function HermiteReduce(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    fp, fs, fn = CanonicalRepresentation(f, D)
    a = numerator(f)
    d = denominator(f)
    ds = Squarefree(d)
    g = zero(f)
    for i=2:length(ds)
        if degree(ds[i])>0
            v = ds[i]
            u = divexact(d, v^i)
            for j=i-1:-1:1
                b, c = gcdx(u*D(v), v, -1//j*a)
                g += b//v^j
                a = -j*c-u*D(b)
            end
            d = u*v
        end
    end
    q, r = divrem(a, d)
    g, r//d, q+fp+fs
end


function PolynomialReduce(p::P, D::ExtensionDerivation) where {T<:FieldElement, P<:PolyElem{T}}
    δ = degree(D.H)
    δ > 1 || error("not a nonlinear monomial")
    t = gen(parent(D.H))
    if degree(p)<δ
        return (0, p)
    end
    m = degree(p) - δ +1
    q0 = (leading_coefficient(p)//(m*leading_coefficient(D.H)))*t^m
    q, r = PolynomialReduce(p-D(q0), D)
    q0+q, r
end


function ResidueReduce(f::F, D::Derivation; symbol=:α) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    d = denominator(f)
    (p,a) = divrem(numerator(f), d)
    kz, z = PolynomialRing(base_ring(d), symbol)    
    kzt, t = PolynomialRing(kz, var(parent(p)))
    if degree(D(d))<=degree(d)
        r, Rs = SubResultant(d(t), a(t)-z*D(d)(t))
    else
        r, Rs = SubResultant(a(t)-z*D(d)(t), d(t))
    end
    κD = CoefficientLiftingDerivation(kz, BaseDerivation(D))
    ns, ss = SplitSquarefreeFactor(r, κD)    
    ds = degree.(ss)
    ss = [ss[i] for i=1:length(ss) if ds[i]>0]
    Ss = typeof(t)[] 
    ii = 1
    for i=1:length(ds)
        if ds[i]>0
            if i==degree(d)
                S = d(t)
            else
                m = findfirst(z->z==i, degree.(Rs))
                S =  Rs[m]
                As = Squarefree(leading_coefficient(S))
                for j=1:length(As)
                    S = divexact(S, gcd(As[j],ss[ii])^j)
                end
            end
            push!(Ss, S)
            ii+=1                          
        end
    end
    b = degree(prod(ns))==0
    [SumOfLogTerms(s, S) for (s, S) in zip(ss, Ss)], b
end


