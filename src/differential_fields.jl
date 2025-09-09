export Derivation, NullDerivation, BasicDerivation, ExtensionDerivation,
   CoefficientLiftingDerivation, TowerOfDifferentialFields,
   BaseDerivation, MonomialDerivative, domain, constant_field,
   isbasic, isprimitive, ishyperexponential, isnonlinear, ishypertangent,
   iscompatible, isnormal, isspecial, issimple, isreduced, is_Sirr1_eq_Sirr


abstract type Derivation end

domain(D::Derivation) = D.domain
iscompatible(p::RingElement, D::Derivation) = parent(p)==domain(D)
iscompatible(f::FracElem, D::Derivation) =
    base_ring(parent(f))==D.domain

is_Sirr1_eq_Sirr(D::Derivation) = true
# For the time being it is assumed that S₁ⁱʳʳ==Sⁱʳʳ for all derivations
# to be considered.
# See Bronstein's book, Theorems 5.1.1, 5.1.2, 5.10.1 .


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

function constant_field(D::NullDerivation) 
    R = D.domain
    if isa(R, AbstractAlgebra.Field)
        return R
    else
        return fraction_field(R)
    end
end


Base.show(io::IO, D::NullDerivation) = print(io, "Null derivation D=0 on ", domain(D))



struct BasicDerivation{T<:RingElement} <: Derivation
    domain::PolyRing{T}
end

BasicDerivation(domain::FracField{P}) where P<:PolyRingElem = BasicDerivation(base_ring(domain))

function (D::BasicDerivation{T})(p::PolyRingElem{T}) where T<:RingElement 
    iscompatible(p, D) || error("p not in domain of D")
    derivative(p)
end

function (D::BasicDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyRingElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    derivative(f)
end

BaseDerivation(D::BasicDerivation) = NullDerivation(base_ring(D.domain))
MonomialDerivative(D::BasicDerivation) = one(D.domain)
function constant_field(D::BasicDerivation) 
    R = base_ring(D.domain)
    if isa(R, AbstractAlgebra.Field)
        return R
    else
        return fraction_field(R)
    end
end

Base.show(io::IO, D::BasicDerivation) = print(io, "Basic derivation D=d/d", gen(domain(D)), " on ", domain(D))


struct ExtensionDerivation{T<:RingElement} <: Derivation
    domain::PolyRing{T}
    D::Derivation
    H::PolyRingElem{T}
    function ExtensionDerivation(domain::PolyRing{R}, D::Derivation, H::PolyRingElem{R}) where R<:RingElement
        base_ring(domain)==D.domain || error("base ring of domain must be domain of D")
        new{R}(domain, D, H)
    end

    function ExtensionDerivation(domain::PolyRing{F}, D::Derivation, H::PolyRingElem{F}) where 
        {R<:RingElement, F<:FracElem{R}}
        base_ring(base_ring(domain))==D.domain || error("base ring of domain must be domain of D")
        new{F}(domain, D, H)
    end
end

function ExtensionDerivation(domain::FracField{P}, D::Derivation, H::P) where {T<:RingElement, P<:PolyRingElem{T}}
    ExtensionDerivation(base_ring(domain), D, H)
end

function CoefficientLiftingDerivation(domain::PolyRing{T}, D::Derivation) where T<:RingElement
    ExtensionDerivation(domain, D, zero(domain))
end

function CoefficientLiftingDerivation(domain::FracField{T}, D::Derivation) where T<:RingElement
    ExtensionDerivation(base_ring(domain), D, zero(base_ring(domain)))
end

function (D::ExtensionDerivation{T})(p::PolyRingElem{T}) where T<:RingElement
    iscompatible(p, D) || error("p not in domain of D")
    if iszero(D.H)
        return map_coefficients(c->D.D(c), p)
    else
        return map_coefficients(c->D.D(c), p) + D.H*derivative(p)
    end
end

function (D::ExtensionDerivation{T})(f::FracElem{P}) where {T<:RingElement, P<:PolyRingElem{T}}
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
constant_field(D::ExtensionDerivation) = constant_field(D.D)

Base.show(io::IO, D::ExtensionDerivation) = print(io, "Extension by D", 
    gen(domain(D))," = ", MonomialDerivative(D),
    " of ", BaseDerivation(D), " on ", domain(D))


struct AlgebraicExtensionDerivation{T<:FieldElement, P<:PolyRingElem{T}} <: Derivation
    domain::AbstractAlgebra.ResField{P}
    D::Derivation
    dy::AbstractAlgebra.ResFieldElem{P}
    function AlgebraicExtensionDerivation(domain::AbstractAlgebra.ResField{P}, D::Derivation) where {T<:FieldElement, P<:PolyRingElem{T}}
        base_ring(base_ring(base_ring(domain)))==D.domain || error("base ring of domain must be domain of D")
        p = modulus(domain)
        y = domain(gen(base_ring(domain)))
        dy = -map_coefficients(derivative, p)(y)//derivative(p)(y)
        new{T,P}(domain, D, dy)
    end
end

function (D::AlgebraicExtensionDerivation)(f::AbstractAlgebra.ResFieldElem{P}) where {T<:FieldElement, P<:PolyRingElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    map_coefficients(derivative, data(f)) + derivative(data(f))*D.dy
end

BaseDerivation(D::AlgebraicExtensionDerivation) = D.D 
#Note: implementation of constant_field requires further thought ...
#constant_field(D::AlgebraicExtensionDerivation) = constant_field(D.D)

Base.show(io::IO, D::AlgebraicExtensionDerivation) = print(io, "Algebraic extension of ", 
    BaseDerivation(D), " on ", domain(D))



AbstractAlgebra.degree(D::Derivation) = 
    degree(MonomialDerivative(D)) # \delta(t), see Def. 3.4.1
AbstractAlgebra.leading_coefficient(D::Derivation) = 
leading_coefficient(MonomialDerivative(D)) # \lambda(t), see Def. 3.4.1
Base.iszero(D::Derivation) = false
Base.iszero(D::NullDerivation) = true
isbasic(D::Derivation) = false
isbasic(D::BasicDerivation) = true
isbasic(D::ExtensionDerivation) = 
    iszero(BaseDerivation(D)) && isone(MonomialDerivative(D))
isprimitive(D::Derivation) = degree(D)==0 # see Def. 5.1.1 
ishyperexponential(D::Derivation) = # see Def, 5.1.1
    degree(D)==1 && iszero(constant_coefficient(MonomialDerivative(D)))
isnonlinear(D::Derivation) = degree(D)>=2 # see Def. 3.4.1  

function ishypertangent(D::Derivation) 
    # see Def. 5.10.1
    isnonlinear(D) || return false
    t = gen(domain(D))
    q, r = divrem(MonomialDerivative(D), t^2+1)
    iszero(r) && degree(q)<=0
end


isnormal(p::PolyRingElem, D::Derivation) =
    # see Def. 3.4.2
    iscompatible(p, D) && degree(gcd(p, D(p)))==0

isspecial(p::PolyRingElem, D::Derivation) =
    # see Def. 3.4.2
    iscompatible(p, D) && iszero(rem(D(p), p)) # gcd(p, D(p))==p

issimple(f::FracElem{P}, D::Derivation) where P<:PolyRingElem =
    #see Def. 3.5.2.
    iscompatible(f, D) && isnormal(denominator(f), D)

isreduced(f::FracElem{P}, D::Derivation) where P<:PolyRingElem =
    #see Def. 3.5.2.
    iscompatible(f, D) && isspecial(denominator(f), D)


function isconstant(x::T, D::NullDerivation) where T<:RingElement 
    @assert iscompatible(x, D)
    true
end

function isconstant(x::F, D::NullDerivation) where {P<:PolyRingElem, F<:FracElem{P}}
    #this version for disambiguation
    @assert iscompatible(x, D)
    true
end
    
function isconstant(x::T, D::Derivation) where T<:RingElement 
    @assert iscompatible(x, D)
    false
end

function isconstant(x::P, D::BasicDerivation) where P<:PolyRingElem 
    @assert iscompatible(x, D)
    degree(x)<=0
end

function isconstant(x::P, D::ExtensionDerivation) where P<:PolyRingElem
    @assert iscompatible(x, D)
    if degree(x)>0 
        return false
    else
        return isconstant(constant_coefficient(x), BaseDerivation(D))
    end
end

function isconstant(x::F, D::Derivation) where {P<:PolyRingElem, F<:FracElem{P}}
    @assert iscompatible(x, D)
    isone(denominator(x)) && isconstant(numerator(x), D) 
end


function constantize(x::T, D::NullDerivation) where T<:RingElement 
    @assert iscompatible(x, D)
    x
end

function constantize(x::F, D::NullDerivation) where {P<:PolyRingElem, F<:FracElem{P}}
    #this version for disambiguation
    @assert iscompatible(x, D)
    x
end

function constantize(x::T, D::Derivation) where T<:RingElement 
    @assert iscompatible(x, D)
    error("not a constant")
end

function constantize(x::P, D::BasicDerivation) where P<:PolyRingElem 
    @assert iscompatible(x, D)
    degree(x)<=0 || error("not a constant")
    constant_coefficient(x)
end

function constantize(x::P, D::ExtensionDerivation) where P<:PolyRingElem
    @assert iscompatible(x, D)
    degree(x)<=0 || error("not a constant")
    constantize(constant_coefficient(x), BaseDerivation(D))
end

function constantize(x::F, D::Derivation) where {P<:PolyRingElem, F<:FracElem{P}}
    @assert iscompatible(x, D)
    isone(denominator(x)) || error("not a constant")
    constantize(numerator(x), D)
end

function constant_roots(f::PolyRingElem{T}, D::Derivation; useQQBar::Bool=false) where T<:FieldElement
    @assert iscompatible(f, D)
    p = map_coefficients(c->constantize(c, BaseDerivation(D)), constant_factors(f)) 
    if useQQBar
        return roots(p) 
    else
        return roots(p)
    end
end

function constant_roots(f::PolyRingElem{T}, D::Derivation; useQQBar::Bool=false) where 
    {T<:AbstractAlgebra.ResFieldElem}
    @assert iscompatible(f, D)
    p = map_coefficients(c->constantize(c, BaseDerivation(D)), constant_factors(f)) 
    pp = map_coefficients(c->real(c), p*map_coefficients(c->conj(c), p))
    g = gcd(pp, derivative(pp))
    if useQQBar
        return roots(g) 
    else
        return roots(g)
    end
end

"""
    SplitFactor(p, D) -> (pₙ, pₛ)

Splitting factorization.
    
Given a field `k`, a derivation `D` on `k[t]` and `p` in `k[t]`, return
`pₙ`, `pₛ` in `k[t]` such that `p=pₙ*pₛ`, `pₛ` is special, and each squarefree 
factor of `pₙ` is normal.
    
See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 3.5, p. 100.
"""
function SplitFactor(p::PolyRingElem{T}, D::Derivation) where T<:FieldElement
    iscompatible(p, D) || error("polynomial p must be in the domain of derivation D")
    S = divexact(gcd(p, D(p)), gcd(p, derivative(p)))
    if degree(S)==0
        return(p, one(p))
    end
    (qn, qs) = SplitFactor(divexact(p, S), D)
    qn, S*qs
end

"""
    SplitSquarefreeFactor(p, D) -> (Ns, Ss)

Splitting squarefree factorization.
    
Given a field `k`, a derivation `D` on `k[t]` and `p` in `k[t]`, return
`Ns=[N₁,...,Nₘ]`, `Ss=[S₁,...,Sₘ]` with  `Nᵢ`, `Sᵢ` in `k[t]` such that
`p=(N₁*N₂²*...*Nₘᵐ)*(S₁*S₂²*...*Sₘᵐ)` is a splitting factorization of `p`
and the `Nᵢ` and `Sᵢ` are squarefree and coprime.
    
See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 3.5, p. 102.
"""
function SplitSquarefreeFactor(p::PolyRingElem{T}, D::Derivation) where T<:FieldElement    
    iscompatible(p, D) || error("polynomial p must be in the domain of derivation D")
    ps = Squarefree(p)
    Ss = [gcd(ps[i], D(ps[i])) for i=1:length(ps)]
    Ns = [divexact(ps[i], Ss[i]) for i=1:length(ps)]
    return Ns, Ss
end

"""
CanonicalRepresentation(f, D) -> (fₚ, fₛ, fₙ)

Canonical representation.

Given a field `k`, a derivation `D` on `k[t]` and `f` in `k(t)`, return
fₚ, fₛ, fₙ in `k(t)` such that `f=fₚ+fₛ+fₙ` is the canonical representation
of `f`.
    
See [Bronstein's book](https://link.springer.com/book/10.1007/b138171), Section 3.5, p. 103.
"""
function CanonicalRepresentation(f::FracElem{P}, D::Derivation) where {T<:FieldElement, P<:PolyRingElem{T}}
    # See Bronstein's book, Section 3.5, p. 103
    iscompatible(f, D) || error("rational function f must be in the domain of derivation D")
    a = numerator(f)
    d = denominator(f)
    q, r = divrem(a, d)
    dn, ds = SplitFactor(d, D)
    b, c = gcdx(dn, ds, r)
    q, b//ds, c//dn
end

