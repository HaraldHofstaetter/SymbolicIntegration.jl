# This file contains algorithms needed for the integratiorn of 
# transcendental functions from chapter 5 of the book
#
#    Manuel Bronstein, Symbolic Integration I: Transcendental Functions,
#    2nd ed., Springer 2005. 
#


function HermiteReduce(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 5.3, p. 139
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
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
    iscompatible(p, D) || error("polynomial p must be in the domain of derivation D")
    isnonlinear(D) || error("monomial of derivation D must be nonlinear")
    δ = degree(D)
    λ = leading_coefficient(D)
    t = gen(domain(D))
    if degree(p)<δ
        return (0, p)
    end
    m = degree(p) - δ +1
    q0 = (leading_coefficient(p)//(m*λ))*t^m
    q, r = PolynomialReduce(p-D(q0), D)
    q0+q, r
end

function ResidueReduce(f::F, D::Derivation; symbol=:α) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.6, p. 151
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    issimple(f, D) || error("rational function f must be simple with respect to derivation D")
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
    iscompatible(p, D) || error("rational function p must be in the domain of derivation D")
    ishyperexponential(D) || error("monomial of derivation D must be hyperexponential")
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

using Logging


function InFieldDerivative(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 175
    iscompatible(p, D) || error("rational function f must be in the domain of derivation D")
    Z = zero(f)
    g, h, r = HermiteReduce(f, D)
    if !isone(denominator(h))
        @info "InFieldDerivative: no solution, h returned by HermiteReduce was not a polynomial"
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
    iscompatible(f, D) || error("field element f must be in the domain of derivation D")
    if iszero(f)
        return 1, one(f), 1
    else
        @info "InFieldLogarithmicDerivativeOfRadical: no solution, f was nonzero in basecase (D=Null derivation)"
        return 0, zero(f), 0 # no solution (n must be !=0)
    end
end

function InFieldLogarithmicDerivativeOfRadical(f::F, D::Derivation) where 
    {T<:RingElement, P<:PolyElem{T}, F<:FracElem{P}}
    # See Bronstein's book, Section 5.12, p. 177
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    if iszero(f)
        return 1, one(f), 1
    end
    Z = zero(f)
    if !issimple(f, D)
        @info "InFieldLogarithmicDerivativeOfRadical: no solution,  f was not simple"
        return 0, Z, 0 
    end
    if isone(denominator(f))
        m = 1
        Dg = Z 
        v = one(f)
    else
        Rs, Gs, β = ResidueReduce(f, D)
        if length(Rs)==0
            m = 1
            Dg = Z 
            v = one(f)
        else
            if !all([all(isrational.(coefficients(R))) for R in Rs])
                @info "InFieldLogarithmicDerivativeOfRadical: no solution, Rothstein-Trager resultant did not have rational coefficients"
                return 0, Z, 0
            end
            Rs1 = [map_coefficients(c->convert(fmpq, rationalize(c)), R) for R in Rs]
            As1 = [roots(R) for R in Rs1]
            if !(all([length(As1[i])==degree(Rs1[i]) for i=1:length(As1)]) &&
                all([all(isrational.(As1[i])) for i=1:length(As1)]) )
                @info "InFieldLogarithmicDerivativeOfRadical: no solution, not all roots of the the Rothstein-Trager were rational"
                return 0, Z, 0
            end
            As = [[rationalize_over_Int(a) for a in as] for as in As1]
            m = gcd([gcd(denominator.(as)) for as in As])
            Dg = Z
            v = one(f)
            for i=1:length(As)
                for a in As[i]
                    lc = leading_coefficient(Gs[i])(a) # make monic (!!!)
                    g = map_coefficients(c->c(a)//lc, Gs[i]) 
                    Dg += a*D(g)//g
                    # Make g = g+Z an element of the field k(t),
                    # otherwise exponentiation with negative numbers would not work.
                    v *= (g+Z)^numerator(m*a)
                end
            end
        end
    end
    @info "InFieldLogarithmicDerivativeOfRadical: m=$m, Dg=$Dg, v=$v"
    p = f - Dg
    if iszero(p)
        return m, v, 1
    end
    if !(isone(denominator(p)))
        @info "InFieldLogarithmicDerivativeOfRadical: no solution, p=f-Dg was not a polynomial"
        return 0, Z, 0
    end
    if !(degree(numerator(p))<max(1,degree(D)))
        @info "InFieldLogarithmicDerivativeOfRadical: no solution, degree(p) was not < max(1,degree(D))"
        return 0, Z, 0
    end
    H = MonomialDerivative(D)
    if isprimitive(D)
        p0 = constant_coefficient(numerator(p))
        n, u, success = InFieldLogarithmicDerivativeOfRadical(p0, BaseDerivation(D))
        if success<=0
            @info "InFieldLogarithmicDerivativeOfRadical: no solution, recursive call of itself returned success=$(success)"
            return 0, Z, success
        end
        N = lcm(n, m)
        # Make u = u + Z an element of the field k(t),
        # otherwise exponentiation with negative numbers would not work.
        U = v^div(N, m)*(u+Z)^div(N, n)
        return N, U, 1
    elseif ishyperexponential(D)        
        p0 = constant_coefficient(numerator(p))
        w = coeff(H, 1)
        n, e, u, success = ParametricLogarithmicDerivative(p0, w, BaseDerivation(D))  
        if success<=0
            @info "InFieldLogarithmicDerivativeOfRadical: no solution, ParametricLogarithmicDerivative(p0, w, D) 
 with p0=$p0, w=$w returned success=$(success)"
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
    @error "InFieldLogarithmicDerivativeOfRadical: Something not implemented"
    0, Z, -1 # failure, not implemented for given monomial 
end

