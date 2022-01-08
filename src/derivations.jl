abstract type Derivation end


struct BasicPolyDerivation{T<:RingElement} <: Derivation 
    domain::PolyRing{T}
end

function (D::BasicPolyDerivation{T})(p::PolyElem{T}) where T<:RingElement 
    parent(p)==D.domain || error("p not in domain of D")
    derivative(p)
end


struct BasicFracDerivation{P<:PolyElem} <: Derivation 
    domain::FracField{P}
end

function (D::BasicFracDerivation{P})(p::P) where P<:PolyElem
    parent(p)==base_ring(D.domain) || error("p not in domain of D")
    derivative(p)
end

function (D::BasicFracDerivation{P})(f::FracElem{P}) where P<:PolyElem
    parent(f)==D.domain || error("f not in domain of D")
    derivative(f)
end


BasicDerivation(domain::PolyRing) = BasicPolyDerivation(domain)

BasicDerivation(domain::FracField{P}) where P<:PolyElem = BasicFracDerivation(domain)


struct CoefficientLiftingDerivation{T<:RingElement} <:Derivation
    domain::PolyRing{T}
    D::Derivation
    function CoefficientLiftingDerivation{T}(R::PolyRing{T}, D::Derivation) where T<:RingElement
        base_ring(R)==D.domain || error("domain of D must be base ring S of R=S[t]")
        new(R, D)
    end
end

CoefficientLiftingDerivation(R::PolyRing{T}, D::Derivation) where T<:RingElement = 
    CoefficientLiftingDerivation{T}(R, D)

function (D::CoefficientLiftingDerivation{T})(p::PolyElem{T}) where T<:RingElement
    parent(p)==D.domain || error("p not in domain of D")
    map_coefficients(c->D.D(c), p)
end




struct FracExtensionDerivation{P<:PolyElem} <: Derivation 
    domain::FracField{P}
    D::Derivation 
end

function (D::FracExtensionDerivation{P})(p::P) where P<:PolyElem 
    parent(p)==base_ring(D.domain) || error("p not in domain of D")
    D.D(p)
end

function(D::FracExtensionDerivation{P})(f::FracElem{P}) where P<:PolyElem
    parent(f)==D.domain || error("f not in domain of D")
    a = numerator(f)
    b = denominator(f)
    (b*D.D(a) - a*D.D(b))//b^2
end

function ExtensionDerivation(F::FracField{P}, D::Derivation) where P<:PolyElem 
    base_ring(F)==D.domain || error("domain of D must be base ring of F")
    FracExtensionDerivation(F, D)
end



struct MonomialPolyExtensionDerivation{T<:RingElement} <: Derivation 
    domain::PolyRing{T}
    D::Derivation 
    H::PolyElem{T}
end

function (D::MonomialPolyExtensionDerivation{T})(p::PolyElem{T}) where T<:RingElement
    parent(p)==D.domain || error("p not in domain of D")
    map_coefficients(c->D.D(c), p) + D.H*derivative(p)
end

struct MonomialFracExtensionDerivation{P<:PolyElem} <: Derivation
    domain::FracField{P}
    D::Derivation 
    H::P
end

function (D::MonomialFracExtensionDerivation{P})(p::P) where P<:PolyElem 
    parent(p)==base_ring(D.domain) || error("p not in domain of D")
    map_coefficients(c->D.D(c), p) + D.H*derivative(p)
end

function(D::MonomialFracExtensionDerivation{P})(f::FracElem{P}) where P<:PolyElem
    parent(f)==D.domain || error("f not in domain of D")
    a = numerator(f)
    da = map_coefficients(c->D.D(c), a) + D.H*derivative(a)
    b = denominator(f)
    db = map_coefficients(c->D.D(c), b) + D.H*derivative(b)
    (b*da - a*db)//b^2
end


function MonomialExtensionDerivation(R::PolyRing{T}, D::Derivation, H::PolyElem{T}) where T<:RingElement 
    base_ring(R)==D.domain || error("domain of D must be base ring S of R=S[t]")
    MonomialPolyExtensionDerivation(R, D, H)
end


function MonomialExtensionDerivation(F::FracField{P}, D::Derivation, H::P) where P<:PolyElem 
    base_ring(base_ring(F))==D.domain || error("domain of D must be base ring R of F=R(t)")
    MonomialFracExtensionDerivation(F, D, H)
end

    

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

