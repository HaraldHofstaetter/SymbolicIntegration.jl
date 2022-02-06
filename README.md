# SymbolicIntegration.jl
This package provides Julia implementations of symbolic integration algorithms.

The front-end (i.e., the user interface) requires [SymbolicUtils.jl](https://symbolicutils.juliasymbolics.org/).
The actual integration algorithms are implemented in a generic way using [AbstractAlgebra.jl](https://nemocas.github.io/AbstractAlgebra.jl/dev/).
Some algorithms require [Nemo.jl](https://nemocas.github.io/Nemo.jl/dev/) for calculations with algebraic numbers.

`SymbolicIntegration.jl` is based on the algorithms from the book

> Manuel Bronstein, [Symbolic Integration I: Transcentental Functions](https://link.springer.com/book/10.1007/b138171), 2nd ed, Springer 2005,

for which a pretty complete set of reference implementations is provided.
Currently, `SymbolicIntegration.jl` can integrate rational functions and integrands involving transcendental elementary 
functions like `exp`, `log`, `sin`, etc.
As in the book, integrands involving algebraic functions like `sqrt` and non-integer powers are not treated.

Note that `SymbolicIntegration.jl` is still in an early stage of development and should not be expected to run stably in all situations.
It comes with absolutely no warranty whatsoever.



## Installation
```julia
julia> using Pkg; Pkg.add("SymbolicIntegration")
```

## Usage
```julia
julia> using SymbolicIntegration, SymbolicUtils

julia> @syms x
(x,)

julia> f = (x^3 + x^2 + x + 2)//(x^4 + 3*x^2 + 2)
(2 + x + x^2 + x^3) / (2 + x^4 + 3(x^2))

julia> integrate(f, x)
(1//2)*log(2 + x^2) + atan(x)

julia> f = 1/(x*log(x))
1 / (x*log(x))

julia> integrate(f, x)
log(log(x))

julia> f = 1/(1+2*cos(x))
1 / (1 + 2cos(x))

julia> g = integrate(f, x)
log(-4 - sqrt(16//3)*tan((1//2)*x))*sqrt(1//3) - log(sqrt(16//3)*tan((1//2)*x) - 4)*sqrt(1//3)
```

## Tests
Some test problems taken from the
[Rubi Integration Test-suites](https://rulebasedintegration.org/testProblems.html)
are provided by the [test_integrate_rational.jl](https://github.com/HaraldHofstaetter/SymbolicIntegration.jl/blob/main/test/test_integrate_rational.jl)
program. This test program produces the following output: [test_integrate_rational.out](https://github.com/HaraldHofstaetter/SymbolicIntegration.jl/blob/main/test/test_integrate_rational.out). 
