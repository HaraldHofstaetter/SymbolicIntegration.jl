# This file contains algorithms needed for the integratiorn of 
# transcendental functions from chapter 5 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


function HermiteReduce(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 5.3, p. 139
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


function PolynomialReduce(p::P, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 5.4, p. 141
    H = MonomialDerivative(D)
    δ = degree(H)
    δ > 1 || error("not a nonlinear monomial")
    t = gen(parent(H))
    if degree(p)<δ
        return (0, p)
    end
    m = degree(p) - δ +1
    q0 = (leading_coefficient(p)//(m*leading_coefficient(H)))*t^m
    q, r = PolynomialReduce(p-D(q0), D)
    q0+q, r
end


function ResidueReduce(f::F, D::Derivation; symbol=:α) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.6, p. 151
    d = denominator(f)
    (p,a) = divrem(numerator(f), d)
    # For SubResultant with respect to t we have to construct the 
    # polynomial ring k[z][t] with z, t in this order (!)
    kz, z = PolynomialRing(base_ring(d), symbol)
    kzt, t = PolynomialRing(kz, var(parent(d)))
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
    ss, Ss, b
end

function IntegrateHyperexponentialPolynomial(p::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.9, p. 162
    t = gen(base_ring(parent(p)))
    w = coeff(MonomialDerivative(D), 1) # Dt/t
    q = zero(p)
    β = 1
    for i=valuation(p, i):-valuation_infinity(p)
        if i!=0
            a = coeff(p, i)
            v, β1 = RischDE(i*w, a, BaseDerivation(D))
            if β1==0
                β = 0
            else 
                q += v*t^i
            end
        end
    end
    q, β
end

function InFieldDerivative(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 175
    Z = zero(f)
    g, h, r = HermiteReduce(f, D)
    if !isone(denominator(h))
        return Z, 0 # no solution
    end
    p = h + r # reduced 
    H = MonomialDerivative(D)
    δ = degree(H)
    if δ==0 # primitive case
        # p reduced => polynomial in this case
        p = numerator(p)
        q, β = IntegratePrimitivePolynomial(p, D)
        β>=1 || return Z, β
        a = constant_coefficient(p - D(q)) # p-D(q) \in k
        v, c = LimitedIntegrate(a, constant_coefficient(H), BaseDerivation(D)) # not yet implemented
        return g + q + v +c*H, 1
    else # δ>=1 
        q, β = IntegrateHyperexponentialPolynomial(p, D)
        β>=1 || return Z, β
        a = constant_coefficient(numerator(p - D(q))) # p-D(q) \in k
        v, β = InFieldDerivative(a, BaseDerivation(B))
        β>=1 || return Z, β
        return g + q + v, 1
    end

end

function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation) where F<:FieldElement
    # base case f \in constant field, D must be the null derivation
    if iszero(f)
        return 1, one(f), 1
    else
        return 0, zero(f), 0 # no solution (n must be !=0)
    end
end

function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 177
    if iszero(f)
        return 1, one(f), 1
    end
    Z = zero(f)
    if degree(gcd(denominator(f), D(denominator(f))))>0 # f not simple
        return 0, Z, 0 
    end
    if isone(denominator(f))
        m = 1
        dg = Z 
        v = one(f)
    else
        Rs, Ss,  β = ResidueReduce(f, D)
        if length(Rs)==0
            m = 1
            dg = Z 
            v = one(f)
        else
            if !all([degree(R)==1 for R in Rs])
                # not all roots of the Rs are rational
                return 0, Z, 0
            end
            as0 = [-constant_coefficient(R)//leading_coefficient(R) for R in Rs]
            if !all([isrational(a) for a in as0])
                # not all roots of the R[i].R are rational
                return 0, Z, 0
            end
            as = [rationalize_over_Int(a) for a in as0]
            m = gcd(denominator.(as))
            gs = [map_coefficients(c->c(as[i]), Ss[i]) for i=1:length(as)]
            dg = sum([as[i]*D(gs[i])//gs[i] for i=1:length(as)])
            # Make gs[i] = gs[i] + Z an element of the field k(t),
            # otherwise exponentiation with negative numbers would not work.
            v = prod([(gs[i]+Z)^numerator(m*as[1]) for i=1:length(as)])
        end
    end
    p = f - dg
    if iszero(p)
        return m, v, 1
    end
    H = MonomialDerivative(D)
    if degree(H) <= 0 # basic derivation or primitive case
        # p \in k, p0 = p as element of k
        p0 = constant_coefficient(numerator(p))
        n, u, success = InFieldLogarithmicDerivativeOfRadical(p0, BaseDerivation(D))
        if success<=0
            return 0, Z, success
        end
        N = lcm(n, m)
        # Make u = u + Z an element of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)
        return N, U, 1
    end
    if degree(H)==1 && iszero(constant_coefficient(H)) # hyperexponential case
        # p \in k, p0 = p as element of k
        p0 = constant_coefficient(numerator(p))
        w = coeff(H, 1)
        n, e, u, success = ParametricLogarithmicDerivative(p0, w, BaseDerivation(D))  
        if success<=0
            return 0, Z, success
        end
        N = lcm(n, m)
        t = gen(parent(numerator(f)))
        # Make u = u + Z, t = t + Z elements of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)*(t+Z)^div(e*N, n)
        return N, U, 1
    end
    # TODO: hypertangent case 
    0, Z, -1 # failure, not implemented for given monomial 
end

