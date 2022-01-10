abstract type Derivation end


struct NullDerivation <: Derivation
    domain #Ring does not work ... :(
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
    parent(p)==D.domain || error("p not in domain of D")
    derivative(p)
end

function (D::BasicDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyElem{T}}
    base_ring(parent(f))==D.domain || error("f not in domain of D")
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

    function ExtensionDerivation(domain::PolyRing{F}, D::SymbolicIntegration.Derivation, H::PolyElem{F}) where 
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
    parent(p)==D.domain || error("p not in domain of D")
    if iszero(D.H)
        return map_coefficients(c->D.D(c), p)
    else
        return map_coefficients(c->D.D(c), p) + D.H*derivative(p)
    end
end

function (D::ExtensionDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyElem{T}}
    base_ring(parent(f))==D.domain || error("f not in domain of D")
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

    

function SplitFactor(p::PolyElem{T}, D::Derivation) where T<:RingElement
    S = divexact(gcd(p, D(p)), gcd(p, derivative(p)))
    if degree(S)==0
        return(p, one(p))
    end
    (qn, qs) = SplitFactor(divexact(p, S), D)
    qn, S*qs
end

function SplitSquarefreeFactor(p::PolyElem{T}, D::Derivation) where T<:RingElement
    ps = Squarefree(p)
    Ss = [gcd(ps[i], D(ps[i])) for i=1:length(ps)]
    Ns = [divexact(ps[i], Ss[i]) for i=1:length(ps)]
    return Ns, Ss
end

function CanonicalRepresentation(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
    a = numerator(f)
    d = denominator(f)
    q, r = divrem(a, d)
    dn, ds = SplitFactor(d, D)
    b, c = gcdx(dn, ds, r)
    q, b//ds, c//dn
end

