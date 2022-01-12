export Derivation, NullDerivation, BasicDerivation, ExtensionDerivation,
   CoefficientLiftingDerivation,
   BaseDerivation, MonomialDerivative, domain,
   isbasic, isprimitive, ishyperexponential, isnonlinear, ishypertangent,
   iscompatible, isnormal, isspecial, issimple, isreduced


abstract type Derivation end

domain(D::Derivation) = D.domain
iscompatible(p::RingElement, D::Derivation) = parent(p)==domain(D)
iscompatible(f::FracElem{P}, D::Derivation) where P<:PolyElem =
    base_ring(parent(f))==D.domain


struct NullDerivation <: Derivation
    domain #::Ring does not work ... :(
end

NullDerivation(domain::FracField{T}) where T<:RingElement = NullDerivation(base_ring(domain))

function (D::NullDerivation)(p::RingElement)
    parent(p)==D.domain || error("p not in domain of D")
    zero(p)
end

function (D::NullDerivation)(f::FracElem{T}) where {T<:RingElement}
    base_ring(parent(f))==D.domain || error("f not in domain of D")
    zero(f)
end



struct BasicDerivation{T<:RingElement} <: Derivation
    domain::PolyRing{T}
end

BasicDerivation(domain::FracField{P}) where P<:PolyElem = BasicDerivation(base_ring(domain))

function (D::BasicDerivation{T})(p::PolyElem{T}) where T<:RingElement 
    iscompatible(p, D) || error("p not in domain of D")
    derivative(p)
end

function (D::BasicDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    derivative(f)
end

BaseDerivation(D::BasicDerivation) = NullDerivation(base_ring(D.domain))
MonomialDerivative(D::BasicDerivation) = one(D.domain)


struct ExtensionDerivation{T<:RingElement} <: Derivation
    domain::PolyRing{T}
    D::Derivation
    H::PolyElem{T}
    function ExtensionDerivation(domain::PolyRing{R}, D::Derivation, H::PolyElem{R}) where R<:RingElement
        base_ring(domain)==D.domain || error("base ring of domain must be domain of D")
        new{R}(domain, D, H)
    end

    function ExtensionDerivation(domain::PolyRing{F}, D::Derivation, H::PolyElem{F}) where 
        {R<:RingElement, F<:FracElem{R}}
        base_ring(base_ring(domain))==D.domain || error("base ring of domain must be domain of D")
        new{F}(domain, D, H)
    end
end

function ExtensionDerivation(domain::FracField{P}, D::Derivation, H::P) where {T<:RingElement, P<:PolyElem{T}}
    ExtensionDerivation(base_ring(domain), D, H)
end

function CoefficientLiftingDerivation(domain::PolyRing{T}, D::Derivation) where T<:RingElement
    ExtensionDerivation(domain, D, zero(domain))
end

function CoefficientLiftingDerivation(domain::FracField{T}, D::Derivation) where T<:RingElement
    ExtensionDerivation(base_ring(domain), D, zero(base_ring(domain)))
end

function (D::ExtensionDerivation{T})(p::PolyElem{T}) where T<:RingElement
    iscompatible(p, D) || error("p not in domain of D")
    if iszero(D.H)
        return map_coefficients(c->D.D(c), p)
    else
        return map_coefficients(c->D.D(c), p) + D.H*derivative(p)
    end
end

function (D::ExtensionDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    a = numerator(f)
    b = denominator(f)
    if isone(b)
        if iszero(D.H)
            return map_coefficients(c->D.D(c), a) + zero(f)
        else
            return map_coefficients(c->D.D(c), a) + D.H*derivative(a) + zero(f)
        end
    else
        if iszero(D.H)
            da = map_coefficients(c->D.D(c), a) 
            db = map_coefficients(c->D.D(c), b) 
        else
            da = map_coefficients(c->D.D(c), a) + D.H*derivative(a)
            db = map_coefficients(c->D.D(c), b) + D.H*derivative(b)
        end
        return (b*da - a*db)//b^2
    end
end


BaseDerivation(D::ExtensionDerivation) = D.D 
MonomialDerivative(D::ExtensionDerivation) = D.H 

AbstractAlgebra.degree(D::Derivation) = 
    degree(MonomialDerivative(D)) # \delta(t), see Def. 3.4.1
AbstractAlgebra.leading_coefficient(D::Derivation) = 
leading_coefficient(MonomialDerivative(D)) # \lambda(t), see Def. 3.4.1
Base.iszero(D::Derivation) = false
Base.iszero(D::NullDerivation) = true
isbasic(D::Derivation) = false
isbasic(D::BasicDerivation) = true
isprimitive(D::Derivation) = degree(D)==0 # see Def. 5.1.1 
ishyperexponential(D::Derivation) = # see Def, 5.1.1
    degree(D)==1 && izero(constant_coefficient(MonomialDerivative(D)))
isnonlinear(D::Derivation) = degree(D)>=2 # see Def. 3.4.1  

function ishypertangent(D::Derivation) 
    # see Def. 5.10.1
    t = gen(domain(D))
    q, r = divrem(MonomialDerivative(D), t^2+1)
    iszero(r) && degree(q)<=0
end


isnormal(p::PolyElem, D::Derivation) =
    # see Def. 3.4.2
    iscompatible(p, D) && degree(gcd(p, MonomialDerivative(D)))==0

isspecial(p::PolyElem, D::Derivation) =
    # see Def. 3.4.2
    iscompatible(p, D) && iszero(rem(MonomialDerivative(D),p))

issimple(f::FracElem{P}, D::Derivation) where P<:PolyElem =
    #see Def. 3.5.2.
    iscompatible(f, D) && isnormal(denominator(f), D)

isreduced(f::FracElem{P}, D::Derivation) where P<:PolyElem =
    #see Def. 3.5.2.
    iscompatible(f, D) && isspecial(denominator(f), D)


    

function SplitFactor(p::PolyElem{T}, D::Derivation) where T<:RingElement
    # See Bronstein's book, Section 3.5, p. 100
    S = divexact(gcd(p, D(p)), gcd(p, derivative(p)))
    if degree(S)==0
        return(p, one(p))
    end
    (qn, qs) = SplitFactor(divexact(p, S), D)
    qn, S*qs
end

function SplitSquarefreeFactor(p::PolyElem{T}, D::Derivation) where T<:RingElement
    # See Bronstein's book, Section 3.5, p. 102
    ps = Squarefree(p)
    Ss = [gcd(ps[i], D(ps[i])) for i=1:length(ps)]
    Ns = [divexact(ps[i], Ss[i]) for i=1:length(ps)]
    return Ns, Ss
end

function CanonicalRepresentation(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    # See Bronstein's book, Section 3.5, p. 103
    a = numerator(f)
    d = denominator(f)
    q, r = divrem(a, d)
    dn, ds = SplitFactor(d, D)
    b, c = gcdx(dn, ds, r)
    q, b//ds, c//dn
end

