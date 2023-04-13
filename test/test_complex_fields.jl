using AbstractAlgebra
using Nemo
using SymbolicIntegration
SI = SymbolicIntegration

using Test

@testset "Complex fields" begin
    QQx, x = PolynomialRing(Nemo.QQ, :x)
    k = FractionField(QQx)
    D0 = BasicDerivation(k)
    kI, I, D = SI.Complexify(k, D0)
    kI1, x1, I1, D1 = SI.switch_t_i(kI, D)

    f = (x^2+3x-1)//(x-7)*I + x^2//(1+x^3)
    f1 = SI.transform(f, x1, I1)
    f2 = SI.backtransform(f1, x, I)
    @test f2==f

    fd = D(f)
    fd1 = SI.transform(fd, x1, I1)
    f1d = D1(f1)
    @test fd1==f1d
end

@testset "ParametricLogarithmicDerivative complexified" begin
    QQx, x = PolynomialRing(Nemo.QQ, :x)
    k = FractionField(QQx)
    D0 = SI.BasicDerivation(k)
    kI, I, D0I = SI.Complexify(k, D0)

    kIt, t = PolynomialRing(kI, :t)

    H = 1//x+0*t
    D = SI.ExtensionDerivation(kIt, D0I, H)

    w = -I*1//(x*t^2)
    u = x^5*t+3*x*I
    n = 2
    m = 6

    f = (D(u)//u+m*w)//n
    n1, m1, u1, ρ = SI.ParametricLogarithmicDerivative(f, w, D)

    @test n1*f == D(u1)//u1 + m1*w
end
