# SymbolicIntegration.jl
This package contains Julia implementations of algorithms for symbolic integration.

The basic algorithms are implemented in a generic way using the 
[AbstractAlgebra.jl](https://nemocas.github.io/AbstractAlgebra.jl/dev/) package.
More advanced algorithms require the
[Nemo.jl](https://nemocas.github.io/Nemo.jl/dev/) computer algebra package
for calculations with algebraic numbers.

Currently, only algorithms for the integration of rational functions are provided which were taken from chapters 1 and 2 of the book

> Manuel Bronstein, [Symbolic Integration I: Transcentental Functions](https://link.springer.com/book/10.1007/b138171), 2nd ed, Springer 2005.

Based on the [AbstractAlgebra.jl](https://nemocas.github.io/AbstractAlgebra.jl/dev/) framework,
the task of translating the book's pseudocode into Julia code was remarkably straightforward.

## Installation
```julia
julia> using Pkg; Pkg.add(PackageSpec(url="https://github.com/HaraldHofstaetter/SymbolicIntegration.jl"))
```

## Usage
```julia
julia> using SymbolicIntegration

julia> using Nemo

julia> QQx, x = PolynomialRing(QQ, :x)
(Univariate Polynomial Ring in x over Rational Field, x)

julia> f = (x^3 + x^2 + x + 2)//(x^4 + 3*x^2 + 2)
(x^3 + x^2 + x + 2)//(x^4 + 3*x^2 + 2)

julia> SymbolicIntegration.integrate(f)
atan(x) + 1//2*log(x^2 + 2)
```

## Tests
Some test problems taken from the
[Rubi Integration Test-suites](https://rulebasedintegration.org/testProblems.html)
are provided by the [test_integrate_rational.jl](https://github.com/HaraldHofstaetter/SymbolicIntegration.jl/blob/main/test/test_integrate_rational.jl)
program. This test program produces the following output: [test_integrate_rational.out](https://github.com/HaraldHofstaetter/SymbolicIntegration.jl/blob/main/test/test_integrate_rational.out). 
