

struct ComplexExtensionDerivation{T<:FieldElement, P<:PolyElem{T}} <: Derivation
    domain::AbstractAlgebra.ResField{P}
    D::Derivation    
    function ComplexExtensionDerivation(domain::AbstractAlgebra.ResField{P}, D::Derivation) where {T<:FieldElement, P<:PolyElem{T}}
        base_ring(base_ring(base_ring(domain)))==D.domain || error("base ring of domain must be domain of D")
        m = modulus(domain)
        degree(m)==2 && isone(coeff(m, 0)) && iszero(coeff(m, 1)) && isone(coeff(m,2)) ||
            error("domain must be residue field modulo X^2+1.")
        new{T,P}(domain, D)
    end
end

Base.iszero(D::ComplexExtensionDerivation) = iszero(D.D)
isbasic(D::ComplexExtensionDerivation) = isbasic(D.D)
MonomialDerivative(D::ComplexExtensionDerivation) = MonomialDerivative(D.D)
BaseDerivation(D::ComplexExtensionDerivation) = D.D 


# TODO: constantize, isconstant, constant_field (should be complex !?!?)

function (D::ComplexExtensionDerivation)(f::AbstractAlgebra.ResFieldElem{P}) where {T<:FieldElement, P<:PolyElem{T}}
    iscompatible(f, D) || error("f not in domain of D")
    #m = modulus(f)
    #degree(m)==2 && isone(coeff(m, 0)) && iszero(coeff(m, 1)) && isone(coeff(m,2)) ||
    #    error("f must be element of residue field modulo X^2+1.")
    u = coeff(data(f), 0)
    v = coeff(data(f), 1)
    kI = parent(f)
    I = gen(base_ring(kI))
    kI(D.D(u)+I*D.D(v))
end

"""
    Complexify(k, D) -> k1, I, D1

Given a field `k` and a derivation `D` on `k`, return the complexified field
`k1=k(√-1)`, the generator `I≈√-1` of this field and the unique extension derivation `D1` on `k1` of `D` that
satisfies `D1(√-1)=0`. 
"""
function Complexify(k::AbstractAlgebra.Field, D::Derivation) # where {T <:FieldElement, F<: AbstractAlgebra.Field{T}}
    kz, I = PolynomialRing(k, :I)
    kI = ResidueField(kz, I^2+1)
    DI = ComplexExtensionDerivation(kI, D)
    kI, kI(I), DI
end

function Base.real(f::AbstractAlgebra.ResFieldElem{P}) where {T<:FieldElement, P<:PolyElem{T}}
    #m = modulus(f)
    #degree(m)==2 && isone(coeff(m, 0)) && iszero(coeff(m, 1)) && isone(coeff(m,2)) ||
    #    error("f must be element of residue field modulo X^2+1.")
    coeff(data(f), 0)
end

function Base.imag(f::AbstractAlgebra.ResFieldElem{P}) where {T<:FieldElement, P<:PolyElem{T}}
    #m = modulus(f)
    #degree(m)==2 && isone(coeff(m, 0)) && iszero(coeff(m, 1)) && isone(coeff(m,2)) ||
    #    error("f must be element of residue field modulo X^2+1.")
    coeff(data(f), 1)
end 

"""
    switch_t_i(K, D) -> (K1, t, I, D1)

Switch generators in `k(t)(√-1)``

Given a complexified field of the form `K=k(t)(√-1)` and a derivation `D` on `K`,
return the field `K1=k(√-1)(t)`, the generators `t` and `I≈√-1` for `K1`, and
the derivation `D1` on `K1` corresponding to `D`
such that the differential fields `(K,D)` and `(K1,D1)` are isomorphic.
"""
function switch_t_i(K::AbstractAlgebra.ResField{P}, D::Derivation) where {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}}
    domain(D)==K || error("K must be the domain of D")        
    k = base_ring(base_ring(base_ring(base_ring(K))))
    D0 = BaseDerivation(BaseDerivation(D))
    kI, I, D0I = Complexify(k, D0)
    v = var(base_ring(base_ring(base_ring(K))))
    kIt, t = PolynomialRing(kI, v)
    K1 = FractionField(kIt)
    H = MonomialDerivative(D)(t)
    D1 = ExtensionDerivation(kIt, D0I, H)
    K1, t, I, D1
end

"""
    transform(f, t, I) -> f1

transform elements of `k(t)(√-1)` to elements of `k(√-1)(t)`.

Given an element `f` of a complexified field of the form `K=k(t)(√-1)`
and the generators `t` and `I≈√-1` for the field `K1=k(√-1)(t)` 
(as returned by `switch_t_i`), return the corresponding element
`f1` in `K1`
"""
function transform(f::K, t, I) where 
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    a = numerator(real(f))(t)
    b = denominator(real(f))(t)
    c = numerator(imag(f))(t)
    d = denominator(imag(f))(t)
    (a*d+c*b*I)//(b*d)
end

"""
    backtransform(f, t, I) -> f1

transform elements of `k(√-1)(t)` to elements of `k(t)(√-1)`.

Given an element `f` of a field of the form `K=k(√-1)(t)`
and the generators `t` and `I≈√-1` for the isomorphic 
field `K1=k(t)(√-1)`, return the corresponding element
`f1` in `K1`
"""
function backtransform(f::K, t, I) where
    {T<:AbstractAlgebra.ResFieldElem, P<:PolyElem{T}, K<:FracElem{P}}
    u = map_coefficients(c->real(c), numerator(f))(t)
    v = map_coefficients(c->imag(c), numerator(f))(t)
    z = map_coefficients(c->real(c), denominator(f))(t)
    w = map_coefficients(c->imag(c), denominator(f))(t)
    d = z^2 + w^2
    (u*z-v*w)//d  + ((v*z-u*w)//d)*I
end


function InFieldDerivative(f::K, D::Derivation) where 
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    ktI = parent(f)
    I0 = ktI(gen(base_ring(ktI)))
    t0 = gen(base_ring(base_ring(base_ring(ktI))))
    _, I, D = Complexify(base_ring(base_ring(ktI)), D)
    f = transform(f, t, I)
    u, ρ = InFieldDerivative(f, D)
    backtransform(u, t0, I0), ρ
end

#Note: InFieldLogarithmicDerivative is merely a wrapper for InFieldLogarithmicDerivativeOfRadical

function InFieldLogarithmicDerivativeOfRadical(f::K, D::Derivation; expect_one::Bool=false) where 
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    ktI = parent(f)
    I0 = ktI(gen(base_ring(ktI)))
    t0 = gen(base_ring(base_ring(base_ring(ktI))))
    _, I, D = Complexify(base_ring(base_ring(ktI)), D)    
    f = transform(f, t, I)
    u, ρ = InFieldLogarithmicDerivativeOfRadical(f, D, expect_one=expect_one)
    backtransform(u, t0, I0), ρ
end

function RischDE(f::F, g::K, D::Derivation) where 
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    ktI = parent(f)
    I0 = ktI(gen(base_ring(ktI)))
    t0 = gen(base_ring(base_ring(base_ring(ktI))))
    _, I, D = Complexify(base_ring(base_ring(ktI)), D)    
    f = transform(f, t, I)
    g = transform(g, t, I)
    y, ρ = RischDE(f, g, D) 
    backtransform(y, t0, I0), ρ
end

function ParamRischDE(f::F, gs::Vector{K}, D::Derivation) where 
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    ktI = parent(f)
    I0 = ktI(gen(base_ring(ktI)))
    t0 = gen(base_ring(base_ring(base_ring(ktI))))
    _, I, D = Complexify(base_ring(base_ring(ktI)), D)    
    f = transform(f, t, I)
    gs = [transform(g, t, I) for g in gs]
    hs, A = ParamRischDE(f, gs, D) # could A have complex entries ???? 
    [backtransform(h, t0, I0) for h in hs], A
end

function LimitedIntegrate(f::F, w::K, D::Derivation) where 
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    ktI = parent(f)
    I0 = ktI(gen(base_ring(ktI)))
    t0 = gen(base_ring(base_ring(base_ring(ktI))))
    _, I, D = Complexify(base_ring(base_ring(ktI)), D)        
    f = transform(f, t, I)
    w = transform(w, t, I)
    v, cs, ρ = LimitedIntegrate(f, w, D) # could cs have complex elements ???
    backtransform(v, t0, I0), cs, ρ
end

function ParametricLogarithmicDerivative(f::F, w::K, D::Derivation) where
    {R<:PolyElem, F<:FracElem{R}, P<:PolyElem{F}, K<:AbstractAlgebra.ResFieldElem{P}}
    ktI = parent(f)
    I0 = ktI(gen(base_ring(ktI)))
    t0 = gen(base_ring(base_ring(base_ring(ktI))))
    _, I, D = Complexify(base_ring(base_ring(ktI)), D)    
    f = transform(f, t, I)
    w = transform(w, t, I)
    n, m, v, ρ = ParametricLogarithmicDerivative(f, w, D) 
    n, m, backtransform(v, t0, I0), ρ
end