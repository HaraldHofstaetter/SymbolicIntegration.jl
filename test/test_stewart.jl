import SymbolicIntegration as SI # Avoid namespace collision with Nemo
using SymbolicUtils: @syms
using Symbolics: Symbolics # for derivative

@syms x t y Pi p q r
n =7
a = 2//3
b = -1//5
c = 5//4

#Integration Test Problems from
#https:////rulebasedintegration.org//testProblems.html

#Stewart Problems
# James Stewart - Calculus (1987)

problems = [

# Section 7.1 - Integration by Parts
[x^n,	x,	1,	x^(1+n)/(1+n)],
[exp(x),	x,	1,	exp(x)],
[1/x,	x,	1,	log(x)],
[a^x,	x,	1,	a^x/log(a)],
[sin(x),	x,	1,	-cos(x)],
[cos(x),	x,	1,	sin(x)],
[sec(x)^2,	x,	2,	tan(x)],
[csc(x)^2,	x,	2,	-cot(x)],
[sec(x)*tan(x),	x,	2,	sec(x)],
[cot(x)*csc(x),	x,	2,	-csc(x)],
[sinh(x),	x,	1,	cosh(x)],
[cosh(x),	x,	1,	sinh(x)],
[tan(x),	x,	1,	-log(cos(x))],
[cot(x),	x,	1,	log(sin(x))],
[x*sin(x),	x,	2,	-x*cos(x)+sin(x)],
[log(x),	x,	1,	-x+x*log(x)],
[exp(x)*x^2,	x,	3,	2*exp(x)-2*exp(x)*x+exp(x)*x^2],
[exp(x)*sin(x),	x,	1,	-1//2*exp(x)*cos(x)+1//2*exp(x)*sin(x)],
[atan(x),	x,	2,	x*atan(x)-1//2*log(1+x^2)],
[exp(2*x)*x,	x,	2,	-1//4*exp(2*x)+1//2*exp(2*x)*x],
[x*cos(x),	x,	2,	cos(x)+x*sin(x)],
[x*sin(4*x),	x,	2,	-1//4*x*cos(4*x)+1//16*sin(4*x)],
[x*log(x),	x,	1,	-1//4*x^2+1//2*x^2*log(x)],
[x^2*cos(3*x),	x,	3,	2//9*x*cos(3*x)-2//27*sin(3*x)+1//3*x^2*sin(3*x)],
[x^2*sin(2*x),	x,	3,	1//4*cos(2*x)-1//2*x^2*cos(2*x)+1//2*x*sin(2*x)],
[log(x)^2,	x,	2,	2*x-2*x*log(x)+x*log(x)^2],
[asin(x),	x,	2,	x*asin(x)+sqrt(1-x^2),  SI.NotImplementedError],	# asin not implemented
[t*cos(t)*sin(t),	t,	3,	-1//4*t+1//4*cos(t)*sin(t)+1//2*t*sin(t)^2],
[t*sec(t)^2,	t,	2,	log(cos(t))+t*tan(t)],
[t^2*log(t),	t,	1,	-1//9*t^3+1//3*t^3*log(t)],
[exp(t)*t^3,	t,	4,	-6*exp(t)+6*exp(t)*t-3*exp(t)*t^2+exp(t)*t^3],
[exp(2*t)*sin(3*t),	t,	1,	-3//13*exp(2*t)*cos(3*t)+2//13*exp(2*t)*sin(3*t)],
[cos(3*t)/exp(t),	t,	1,	-1//10*cos(3*t)/exp(t)+3//10*sin(3*t)/exp(t)],
[y*sinh(y),	y,	2,	y*cosh(y)-sinh(y)],
[y*cosh(a*y),	y,	2,	-cosh(a*y)/a^2+y*sinh(a*y)/a],
[t/exp(t),	t,	2,	(-1)/exp(t)-t/exp(t)],
[log(t)*sqrt(t),	t,	1,	-4//9*t^(3//2)+2//3*t^(3//2)*log(t),    SI.NotImplementedError],
[x*cos(2*x),	x,	2,	1//4*cos(2*x)+1//2*x*sin(2*x)],
[x^2/exp(x),	x,	3,	(-2)/exp(x)-2*x/exp(x)-x^2/exp(x)],
[acos(x),	x,	2,	x*acos(x)-sqrt(1-x^2), SI.NotImplementedError], #acos
[x*csc(x)^2,	x,	2,	-x*cot(x)+log(sin(x))],
[cos(5*x)*sin(3*x),	x,	1,	1//4*cos(2*x)-1//16*cos(8*x)],
[sin(2*x)*sin(4*x),	x,	1,	1//4*sin(2*x)-1//12*sin(6*x)],
[cos(x)*log(sin(x)),	x,	2,	-sin(x)+log(sin(x))*sin(x)],
[exp(x^2)*x^3,	x,	2,	-1//2*exp(x^2)+1//2*exp(x^2)*x^2],
[exp(x)*(3+2*x),	x,	2,	-2*exp(x)+exp(x)*(3+2*x)],
[5^x*x,	x,	2,	-5^x/log(5)^2+5^x*x/log(5)],
[cos(log(x)),	x,	1,	1//2*x*cos(log(x))+1//2*x*sin(log(x))],
[exp(sqrt(x)),	x,	3,	-2*exp(sqrt(x))+2*exp(sqrt(x))*sqrt(x), SI.NotImplementedError],
[log(sqrt(x)),	x,	1,	-1//2*x+x*log(sqrt(x)), SI.NotImplementedError],
[sin(log(x)),	x,	1,	-1//2*x*cos(log(x))+1//2*x*sin(log(x))],
[sin(sqrt(x)),	x,	3,	2*sin(sqrt(x))-2*cos(sqrt(x))*sqrt(x),  SI.NotImplementedError],
[x^5*cos(x^3),	x,	3,	1//3*cos(x^3)+1//3*x^3*sin(x^3)],
[exp(x^2)*x^5,	x,	3,	exp(x^2)-exp(x^2)*x^2+1//2*exp(x^2)*x^4],
[x*atan(x),	x,	3,	-1//2*x+1//2*atan(x)+1//2*x^2*atan(x)],
[x*cos(Pi*x),	x,	2,	cos(Pi*x)/Pi^2+x*sin(Pi*x)/Pi, SI.NotImplementedError],	# Pi
[log(x)*sqrt(x),	x,	1,	-4//9*x^(3//2)+2//3*x^(3//2)*log(x), SI.NotImplementedError],

# Section 7.2 - Trigonometric Integrals
[sin(3*x)^2,	x,	2,	1//2*x-1//6*cos(3*x)*sin(3*x)],
[cos(x)^2,	x,	2,	1//2*x+1//2*cos(x)*sin(x)],
[cos(x)^4,	x,	3,	3//8*x+3//8*cos(x)*sin(x)+1//4*cos(x)^3*sin(x)],
[sin(x)^3,	x,	2,	-cos(x)+1//3*cos(x)^3],
[cos(x)^4*sin(x)^3,	x,	3,	-1//5*cos(x)^5+1//7*cos(x)^7],
[cos(x)^3*sin(x)^4,	x,	3,	1//5*sin(x)^5-1//7*sin(x)^7],
[cos(x)^2*sin(x)^4,	x,	4,	1//16*x+1//16*cos(x)*sin(x)-1//8*cos(x)^3*sin(x)-1//6*cos(x)^3*sin(x)^3],
[cos(x)^2*sin(x)^2,	x,	3,	1//8*x+1//8*cos(x)*sin(x)-1//4*cos(x)^3*sin(x)],
[(1-sin(2*x))^2,	x,	1,	3//2*x+cos(2*x)-1//4*cos(2*x)*sin(2*x)],
[cos(x)*sin(1//6*Pi+x),	x,	3,	1//4*x-1//4*cos(1//6*Pi+2*x), SI.NotImplementedError],	# Pi
[cos(x)^5*sin(x)^5,	x,	4,	1//6*sin(x)^6-1//4*sin(x)^8+1//10*sin(x)^10],
[sin(x)^6,	x,	4,	5//16*x-5//16*cos(x)*sin(x)-5//24*cos(x)*sin(x)^3-1//6*cos(x)*sin(x)^5],
[cos(x)^6,	x,	4,	5//16*x+5//16*cos(x)*sin(x)+5//24*cos(x)^3*sin(x)+1//6*cos(x)^5*sin(x)],
[cos(2*x)^4*sin(2*x)^2,	x,	4,	1//16*x+1//32*cos(2*x)*sin(2*x)+1//48*cos(2*x)^3*sin(2*x)-1//12*cos(2*x)^5*sin(2*x)],
[sin(x)^5,	x,	2,	-cos(x)+2//3*cos(x)^3-1//5*cos(x)^5],
[cos(x)^4*sin(x)^4,	x,	5,	3//128*x+3//128*cos(x)*sin(x)+1//64*cos(x)^3*sin(x)-1//16*cos(x)^5*sin(x)-1//8*cos(x)^5*sin(x)^3],
[sin(x)^3*sqrt(cos(x)),	x,	3,	-2//3*cos(x)^(3//2)+2//7*cos(x)^(7//2), SI.NotImplementedError],
[cos(x)^3*sqrt(sin(x)),	x,	3,	2//3*sin(x)^(3//2)-2//7*sin(x)^(7//2), SI.NotImplementedError],
[cos(sqrt(x))^2/sqrt(x),	x,	3,	cos(sqrt(x))*sin(sqrt(x))+sqrt(x), SI.NotImplementedError],
[x*sin(x^2)^3,	x,	3,	-1//2*cos(x^2)+1//6*cos(x^2)^3],
[cos(x)^2*tan(x)^3,	x,	3,	1//2*cos(x)^2-log(cos(x))],
[cot(x)^5*sin(x)^2,	x,	4,	-1//2*csc(x)^2-2*log(sin(x))+1//2*sin(x)^2],
[(1-sin(x))/cos(x),	x,	2,	log(1+sin(x))],
[1/(1-sin(x)),	x,	1,	cos(x)/(1-sin(x))],
[tan(x)^2,	x,	2,	-x+tan(x)],
[tan(x)^4,	x,	3,	x-tan(x)+1//3*tan(x)^3],
[sec(x)^4,	x,	2,	tan(x)+1//3*tan(x)^3],
[sec(x)^6,	x,	2,	tan(x)+2//3*tan(x)^3+1//5*tan(x)^5],
[sec(x)^2*tan(x)^4,	x,	2,	1//5*tan(x)^5],
[sec(x)^4*tan(x)^2,	x,	3,	1//3*tan(x)^3+1//5*tan(x)^5],
[sec(x)^3*tan(x),	x,	2,	1//3*sec(x)^3],
[sec(x)^3*tan(x)^3,	x,	3,	-1//3*sec(x)^3+1//5*sec(x)^5],
[tan(x)^5,	x,	3,	-log(cos(x))-1//2*tan(x)^2+1//4*tan(x)^4],
[tan(x)^6,	x,	4,	-x+tan(x)-1//3*tan(x)^3+1//5*tan(x)^5],
[sec(x)*tan(x)^5,	x,	3,	sec(x)-2//3*sec(x)^3+1//5*sec(x)^5],
[sec(x)^3*tan(x)^5,	x,	3,	1//3*sec(x)^3-2//5*sec(x)^5+1//7*sec(x)^7],
[sec(x)^6*tan(x),	x,	2,	1//6*sec(x)^6],
[sec(x)^6*tan(x)^3,	x,	3,	-1//6*sec(x)^6+1//8*sec(x)^8],
[sec(x)^2/cot(x),	x,	2,	1//2*sec(x)^2],
[sec(x)*tan(x)^2,	x,	2,	-1//2*atanh(sin(x))+1//2*sec(x)*tan(x)],
[cot(x)^2,	x,	2,	-x-cot(x)],
[cot(x)^3,	x,	2,	-1//2*cot(x)^2-log(sin(x))],
[cot(x)^4*csc(x)^4,	x,	3,	-1//5*cot(x)^5-1//7*cot(x)^7],
[cot(x)^3*csc(x)^4,	x,	3,	1//4*csc(x)^4-1//6*csc(x)^6],
[csc(x),	x,	1,	-atanh(cos(x))],
[csc(x)^3,	x,	2,	-1//2*atanh(cos(x))-1//2*cot(x)*csc(x)],
[cos(x)^2/sin(x),	x,	3,	-atanh(cos(x))+cos(x)],
[1/sin(x)^4,	x,	2,	-cot(x)-1//3*cot(x)^3],
[sin(2*x)*sin(5*x),	x,	1,	1//6*sin(3*x)-1//14*sin(7*x)],
[cos(x)*sin(3*x),	x,	1,	-1//4*cos(2*x)-1//8*cos(4*x)],
[cos(3*x)*cos(4*x),	x,	1,	1//2*sin(x)+1//14*sin(7*x)],
[sin(3*x)*sin(6*x),	x,	1,	1//6*sin(3*x)-1//18*sin(9*x)],
[cos(x)^5*sin(x),	x,	2,	-1//6*cos(x)^6],
[cos(x)*cos(2*x)*cos(3*x),	x,	5,	1//4*x+1//8*sin(2*x)+1//16*sin(4*x)+1//24*sin(6*x)],
[(1-tan(x)^2)/sec(x)^2,	x,	2,	cos(x)*sin(x)],
[(cos(x)+sin(x))/sin(2*x),	x,	6,	-1//2*atanh(cos(x))+1//2*atanh(sin(x))],
[sin(x)^2*tan(x),	x,	3,	1//2*cos(x)^2-log(cos(x))],
[cos(x)^2*cot(x)^3,	x,	4,	-1//2*csc(x)^2-2*log(sin(x))+1//2*sin(x)^2],
[sec(x)^3*tan(x),	x,	2,	1//3*sec(x)^3],
[sec(x)^3*tan(x)^3,	x,	3,	-1//3*sec(x)^3+1//5*sec(x)^5],

# Section 7.3 - Trigonometric Substitution
[sqrt(9-x^2)/x^2,	x,	2,	-asin(1//3*x)-sqrt(9-x^2)/x, SI.NotImplementedError],
[1/(x^2*sqrt(4+x^2)),	x,	1,	-1//4*sqrt(4+x^2)/x, SI.NotImplementedError],
[x/sqrt(4+x^2),	x,	1,	sqrt(4+x^2), SI.NotImplementedError],
[1/sqrt(-a^2+x^2),	x,	2,	atanh(x/sqrt(-a^2+x^2)), SI.NotImplementedError],	# sqrt, a
[x^3/(9+4*x^2)^(3//2),	x,	3,	9//16/sqrt(9+4*x^2)+1//16*sqrt(9+4*x^2), SI.NotImplementedError],	# exponent 3//2
[x/sqrt(3-2*x-x^2),	x,	3,	asin(1//2*(-1-x))-sqrt(3-2*x-x^2), SI.NotImplementedError],
[1/(x^2*sqrt(1-x^2)),	x,	1,	-sqrt(1-x^2)/x, SI.NotImplementedError],
[x^3*sqrt(4-x^2),	x,	3,	-4//3*(4-x^2)^(3//2)+1//5*(4-x^2)^(5//2), SI.NotImplementedError],
[x/sqrt(1-x^2),	x,	1,	-sqrt(1-x^2), SI.NotImplementedError],
[x*sqrt(4-x^2),	x,	1,	-1//3*(4-x^2)^(3//2), SI.NotImplementedError],
[sqrt(1-4*x^2),	x,	2,	1//4*asin(2*x)+1//2*x*sqrt(1-4*x^2), SI.NotImplementedError],
[x^3/sqrt(4+x^2),	x,	3,	1//3*(4+x^2)^(3//2)-4*sqrt(4+x^2), SI.NotImplementedError],
[1/sqrt(9+x^2),	x,	1,	asinh(1//3*x), SI.NotImplementedError],
[sqrt(1+x^2),	x,	2,	1//2*asinh(x)+1//2*x*sqrt(1+x^2), SI.NotImplementedError],
[1/(x^3*sqrt(-16+x^2)),	x,	4,	1//128*atan(1//4*sqrt(-16+x^2))+1//32*sqrt(-16+x^2)/x^2, SI.NotImplementedError],
[sqrt(-a^2+x^2)/x^4,	x,	1,	1//3*(-a^2+x^2)^(3//2)/(a^2*x^3), SI.NotImplementedError],	# sqrt, a
[sqrt(-4+9*x^2)/x,	x,	4,	-2*atan(1//2*sqrt(-4+9*x^2))+sqrt(-4+9*x^2), SI.NotImplementedError],
[1/(x^2*sqrt(-9+16*x^2)),	x,	1,	1//9*sqrt(-9+16*x^2)/x, SI.NotImplementedError],
[x^2/(a^2-x^2)^(3//2),	x,	3,	-atan(x/sqrt(a^2-x^2))+x/sqrt(a^2-x^2), SI.NotImplementedError],  # exponent 3//2, a
[x^2/sqrt(5-x^2),	x,	2,	5//2*asin(x/sqrt(5))-1//2*x*sqrt(5-x^2), SI.NotImplementedError],
[1/(x*sqrt(3+x^2)),	x,	3,	-atanh(sqrt(3+x^2)/sqrt(3))/sqrt(3), SI.NotImplementedError],
[x/(4+x^2)^(5//2),	x,	1,	(-1//3)//(4+x^2)^(3//2), SI.NotImplementedError],	# exponent 5//2
[x^3*sqrt(4-9*x^2),	x,	3,	-4//243*(4-9*x^2)^(3//2)+1//405*(4-9*x^2)^(5//2), SI.NotImplementedError],
[x^2*sqrt(9-x^2),	x,	3,	81//8*asin(1//3*x)-9//8*x*sqrt(9-x^2)+1//4*x^3*sqrt(9-x^2), SI.NotImplementedError],
[5*x*sqrt(1+x^2),	x,	2,	5//3*(1+x^2)^(3//2), SI.NotImplementedError],
[1/(-25+4*x^2)^(3//2),	x,	1,	-1//25*x/sqrt(-25+4*x^2), SI.NotImplementedError],
[sqrt(2*x-x^2),	x,	3,	-1//2*asin(1-x)-1//2*(1-x)*sqrt(2*x-x^2), SI.NotImplementedError],
[1/sqrt(8+4*x+x^2),	x,	2,	asinh(1//2*(2+x)), SI.NotImplementedError],
[1/sqrt(-8+6*x+9*x^2),	x,	2,	1//3*atanh((1+3*x)/sqrt(-8+6*x+9*x^2)), SI.NotImplementedError],
[x^2/sqrt(4*x-x^2),	x,	4,	-6*asin(1-1//2*x)-3*sqrt(4*x-x^2)-1//2*x*sqrt(4*x-x^2), SI.NotImplementedError],
[1/(2+2*x+x^2)^2,	x,	3,	1//2*(1+x)/(2+2*x+x^2)+1//2*atan(1+x)],
[1/(5-4*x-x^2)^(5//2),	x,	2,	1//27*(2+x)/(5-4*x-x^2)^(3//2)+2//243*(2+x)/sqrt(5-4*x-x^2), SI.NotImplementedError], #exponent 5//2
[exp(t)*sqrt(9-exp(2*t)),	t,	3,	9//2*asin(1//3*exp(t))+1//2*exp(t)*sqrt(9-exp(2*t)), SI.NotImplementedError],
[sqrt(-9+exp(2*t)),	t,	4,	-3*atan(1//3*sqrt(-9+exp(2*t)))+sqrt(-9+exp(2*t)), SI.NotImplementedError],

# Section 7.4 - Integration of Rational Functions by Partial Fractions
[1//sqrt(a^2+x^2),	x,	2,	atanh(x//sqrt(a^2+x^2)), SI.NotImplementedError],	# sqrt, a
[(5+x)//(-2+x+x^2),	x,	3,	2*log(1-x)-log(2+x)],
[(x+x^3)//(-1+x),	x,	3,	2*x+1//2*x^2+1//3*x^3+2*log(1-x)],
[(-1+2*x+x^2)//(-2*x+3*x^2+2*x^3),	x,	3,	1//10*log(1-2*x)+1//2*log(x)-1//10*log(2+x)],
[(1+4*x-2*x^2+x^4)//(1-x-x^2+x^3),	x,	2,	2//(1-x)+x+1//2*x^2+log(1-x)-log(1+x)],
[(4-x+2*x^2)//(4*x+x^3),	x,	6,	-1//2*atan(1//2*x)+log(x)+1//2*log(4+x^2)],
[(2-3*x+4*x^2)//(3-4*x+4*x^2),	x,	6,	x+1//8*log(3-4*x+4*x^2)+1//4*atan((1-2*x)/sqrt(2))/sqrt(2)],
[(1+x^2+x^3)//((-1+x)*x*(1+x^2)^3*(1+x+x^2)),	x,	14,	1//8*(1+x)//(1+x^2)^2-3//8*(1-x)//(1+x^2)+3//16*x//(1+x^2)+7//16*atan(x)+1//8*log(1-x)-log(x)+15//16*log(1+x^2)-1//2*log(1+x+x^2)-atan((1+2*x)/sqrt(3))/sqrt(3)],
[(1-3*x+2*x^2-x^3)//(x*(1+x^2)^2),	x,	6,	1//2*(-1-2*x)//(1+x^2)-2*atan(x)+log(x)-1//2*log(1+x^2)],
[1//(1+x^2)^2,	x,	2,	1//2*x//(1+x^2)+1//2*atan(x)],
[1//((-1+x)*(2+x)),	x,	3,	1//3*log(1-x)-1//3*log(2+x)],
[7//(-12+5*x+2*x^2),	x,	4,	7//11*log(3-2*x)-7//11*log(4+x)],
[(-4+3*x+x^2)//((-1+2*x)^2*(3+2*x)),	x,	2,	(-9//32)//(1-2*x)+41//128*log(1-2*x)-25//128*log(3+2*x)],
[(-x^2+x^3)//((-6+x)*(3+5*x)^3),	x,	3,	(-12//1375)//(3+5*x)^2+201//15125//(3+5*x)+20//3993*log(6-x)+1493//499125*log(3+5*x)],
[1//(-x^3+x^4),	x,	3,	1//2//x^2+1//x+log(1-x)-log(x)],
[(1-x-x^2+x^3+x^4)//(-x+x^3),	x,	4,	x+1//2*x^2-log(x)+1//2*log(1-x^2)],
[(-2+x^2)//(x*(2+x^2)),	x,	3,	-log(x)+log(2+x^2)],
[(2-4*x^2+x^3)//((1+x^2)*(2+x^2)),	x,	8,	6*atan(x)-1//2*log(1+x^2)+log(2+x^2)-5*atan(x/sqrt(2))*sqrt(2)],
[(1+x^2+x^4)//((1+x^2)*(4+x^2)^2),	x,	6,	-13//24*x//(4+x^2)+25//144*atan(1//2*x)+1//9*atan(x)],
[(1+16*x)//((5+x)^2*(-3+2*x)*(1+x+x^2)),	x,	6,	(-79//273)//(5+x)+200//3211*log(3-2*x)+2731//24843*log(5+x)-481//5586*log(1+x+x^2)+451//2793*atan((1+2*x)/sqrt(3))/sqrt(3)],
[x^4//(9+x^2)^3,	x,	3,	-1//4*x^3//(9+x^2)^2-3//8*x//(9+x^2)+1//8*atan(1//3*x)],
[19*x//((-1+x)^3*(3+5*x+4*x^2)^2),	x,	8,	(-399//736)//(1-x)^2+(-1843//4416)//(1-x)+19//276*(39+44*x)//((1-x)^2*(3+5*x+4*x^2))+209//2304*log(1-x)-209//4608*log(3+5*x+4*x^2)+114437//52992*atan((5+8*x)/sqrt(23))/sqrt(23)],
[(1+x^2+x^3)//(2*x^2+x^3+x^4),	x,	7,	(-1//2)//x-1//4*log(x)+5//8*log(2+x+x^2)+1//4*atan((1+2*x)/sqrt(7))/sqrt(7)],
[1//(-x^3+x^6),	x,	8,	1//2//x^2+1//3*log(1-x)-1//6*log(1+x+x^2)-atan((1+2*x)/sqrt(3))/sqrt(3)],
[x^2//(1+x),	x,	2,	-x+1//2*x^2+log(1+x)],
[x//(-5+x),	x,	2,	x+5*log(5-x)],
[(-1+4*x)//((-1+x)*(2+x)),	x,	2,	log(1-x)+3*log(2+x)],
[1//((1+x)*(2+x)),	x,	3,	log(1+x)-log(2+x)],
[(-5+6*x)//(3+2*x),	x,	2,	3*x-7*log(3+2*x)],
[1//((a+x)*(b+x)),	x,	3,	-log(a+x)/(a-b)+log(b+x)/(a-b)],
[(1+x^2)//(-x+x^2),	x,	3,	x+2*log(1-x)-log(x)],
[(1-12*x+x^2+x^3)//(-12+x+x^2),	x,	5,	1//2*x^2+1//7*log(3-x)-1//7*log(4+x)],
[(3+2*x)//(1+x)^2,	x,	2,	(-1)//(1+x)+2*log(1+x)],
[1//(x*(1+x)*(3+2*x)),	x,	2,	1//3*log(x)-log(1+x)+2//3*log(3+2*x)],
[(-3+5*x+6*x^2)//(-3*x+2*x^2+x^3),	x,	3,	2*log(1-x)+log(x)+3*log(3+x)],
[x//(4+4*x+x^2),	x,	3,	2//(2+x)+log(2+x)],
[1//((-1+x)^2*(4+x)),	x,	2,	1//5//(1-x)-1//25*log(1-x)+1//25*log(4+x)],
[x^2//((-3+x)*(2+x)^2),	x,	2,	4//5//(2+x)+9//25*log(3-x)+16//25*log(2+x)],
[(-2+3*x+5*x^2)//(2*x^2+x^3),	x,	3,	1//x+2*log(x)+3*log(2+x)],
[(18-2*x-4*x^2)//(-6+x+4*x^2+x^3),	x,	2,	log(1-x)-2*log(2+x)-3*log(3+x)],
[(2*x+x^2)//(4+3*x^2+x^3),	x,	1,	1//3*log(4+3*x^2+x^3)],
[1//((-1+x)^2*x^2),	x,	2,	1//(1-x)+(-1)//x-2*log(1-x)+2*log(x)],
[x^2//(1+x)^3,	x,	2,	(-1//2)//(1+x)^2+2//(1+x)+log(1+x)],
[1//(-x^2+x^4),	x,	3,	1//x-atanh(x)],
[(-x+2*x^3)//(1-x^2+x^4),	x,	1,	1//2*log(1-x^2+x^4)],
[x^3//(1+x^2),	x,	3,	1//2*x^2-1//2*log(1+x^2)],
[(-1+x)//(2+2*x+x^2),	x,	4,	-2*atan(1+x)+1//2*log(2+2*x+x^2)],
[x//(1+x+x^2),	x,	4,	1//2*log(1+x+x^2)-atan((1+2*x)/sqrt(3))/sqrt(3)],
[(7+5*x+4*x^2)//(5+4*x+4*x^2),	x,	6,	x+3//8*atan(1//2+x)+1//8*log(5+4*x+4*x^2)],
[(5-4*x+3*x^2)//((-1+x)*(1+x^2)),	x,	5,	-3*atan(x)+2*log(1-x)+1//2*log(1+x^2)],
[(3+2*x)//(3*x+x^3),	x,	6,	log(x)-1//2*log(3+x^2)+2*atan(x/sqrt(3))/sqrt(3)],
[1//(-1+x^3),	x,	6,	1//3*log(1-x)-1//6*log(1+x+x^2)-atan((1+2*x)/sqrt(3))/sqrt(3)],
[x^3//(1+x^3),	x,	7,	x-1//3*log(1+x)+1//6*log(1-x+x^2)+atan((1-2*x)/sqrt(3))/sqrt(3)],
[(-1-2*x+x^2)//((-1+x)^2*(1+x^2)),	x,	5,	1//(-1+x)+atan(x)+log(1-x)-1//2*log(1+x^2)],
[x^4//(-1+x^4),	x,	4,	x-1//2*atan(x)-1//2*atanh(x)],
[(-4+6*x-x^2+3*x^3)//((1+x^2)*(2+x^2)),	x,	6,	-3*atan(x)+3//2*log(1+x^2)+atan(x/sqrt(2))*sqrt(2)],
[(1+x-2*x^2+x^3)//(4+5*x^2+x^4),	x,	7,	-3//2*atan(1//2*x)+atan(x)+1//2*log(4+x^2)],
[(-3+x)//(4+2*x+x^2)^2,	x,	3,	1//6*(-7-4*x)//(4+2*x+x^2)-2//3*atan((1+x)/sqrt(3))/sqrt(3)],
[(1+x^4)//(x*(1+x^2)^2),	x,	3,	1//(1+x^2)+log(x)],
[cos(x)*(-3+2*sin(x))//(2-3*sin(x)+sin(x)^2),	x,	2,	log(2-3*sin(x)+sin(x)^2)],
[cos(x)^2*sin(x)//(5+cos(x)^2),	x,	3,	-cos(x)+atan(cos(x)/sqrt(5))*sqrt(5)],  # result contains algebraic numbers
[1//(-3+2*x+x^2),	x,	3,	1//4*log(1-x)-1//4*log(3+x)],
[1//(-2*x+x^2),	x,	1,	1//2*log(2-x)-1//2*log(x)],
[(1+2*x)//(-7+12*x+4*x^2),	x,	3,	1//8*log(1-2*x)+3//8*log(7+2*x)],
[x//(-1+x+x^2),	x,	3,	1//10*log(1+2*x-sqrt(5))*(5-sqrt(5))+1//10*log(1+2*x+sqrt(5))*(5+sqrt(5))],

# Section 7.5 - Rationalization Substitutions
[(-32+5*x-27*x^2+4*x^3)//(-70-299*x-286*x^2+50*x^3-13*x^4+30*x^5),	x,	6,	-3146//80155*log(7-3*x)-334//323*log(1+2*x)+4822//4879*log(2+5*x)+11049//260015*log(5+x+x^2)+3988//13685*atan((1+2*x)/sqrt(19))/sqrt(19)],
[(8-13*x^2-7*x^3+12*x^5)//(4-20*x+41*x^2-80*x^3+116*x^4-80*x^5+100*x^6),	x,	7,	5828//9075//(2-5*x)+1//1452*(-313-502*x)//(1+2*x^2)-59096//99825*log(2-5*x)+2843//7986*log(1+2*x^2)-251//726*atan(x*sqrt(2))/sqrt(2)+272//1331*atan(x*sqrt(2))*sqrt(2)],
[sqrt(4+x)//x,	x,	3,	-4*atanh(1//2*sqrt(4+x))+2*sqrt(4+x), SI.NotImplementedError],
[1//((-1)//x^(1//3)+sqrt(x)),	x,	9,	6//5*log(1-x^(1//6))-3//10*log(2+x^(1//6)+2*x^(1//3)+x^(1//6)*sqrt(5))*(1-sqrt(5))-3//10*log(2+x^(1//6)+2*x^(1//3)-x^(1//6)*sqrt(5))*(1+sqrt(5))+2*sqrt(x)+3//5*atan((1+4*x^(1//6)-sqrt(5))/sqrt(2*(5+sqrt(5))))*sqrt(2*(5-sqrt(5)))-3//5*atan(1//2*(1+4*x^(1//6)+sqrt(5))*sqrt(1//10*(5+sqrt(5))))*sqrt(2*(5+sqrt(5))), SI.NotImplementedError],
[1//(-4*cos(x)+3*sin(x)),	x,	2,	-1//5*atanh(1//5*(3*cos(x)+4*sin(x)))],
[1//(1+sqrt(x)),	x,	3,	-2*log(1+sqrt(x))+2*sqrt(x), SI.NotImplementedError],
[1//(1+1//x^(1//3)),	x,	3,	3*x^(1//3)-3//2*x^(2//3)+x-3*log(1+1//x^(1//3))-log(x), SI.NotImplementedError], #exponent 1//3
[sqrt(x)//(1+x),	x,	3,	-2*atan(sqrt(x))+2*sqrt(x), SI.NotImplementedError],
[1//(x*sqrt(1+x)),	x,	2,	-2*atanh(sqrt(1+x)), SI.NotImplementedError],
[1//(-x^(1//3)+x),	x,	2,	3//2*log(1-x^(2//3)), SI.NotImplementedError],	# exponent 1//3
[1//(x-sqrt(2+x)),	x,	4,	4//3*log(2-sqrt(2+x))+2//3*log(1+sqrt(2+x)), SI.NotImplementedError],
[x^2//sqrt(-1+x),	x,	2,	4//3*(-1+x)^(3//2)+2//5*(-1+x)^(5//2)+2*sqrt(-1+x), SI.NotImplementedError],
[sqrt(-1+x)//(1+x),	x,	3,	-2*atan(sqrt(-1+x)/sqrt(2))*sqrt(2)+2*sqrt(-1+x), SI.NotImplementedError],
[1//sqrt(1+sqrt(x)),	x,	3,	4//3*(1+sqrt(x))^(3//2)-4*sqrt(1+sqrt(x)), SI.NotImplementedError],
[sqrt(x)//(x+x^2),	x,	3,	2*atan(sqrt(x)), SI.NotImplementedError],
[(1+sqrt(x))//(-1+sqrt(x)),	x,	3,	x+4*log(1-sqrt(x))+4*sqrt(x), SI.NotImplementedError],
[(1+1//x^(1//3))//(-1+1//x^(1//3)),	x,	4,	-6*x^(1//3)-3*x^(2//3)-x-6*log(1-x^(1//3)), SI.NotImplementedError],	# exponent 1//3
[x^3//(1+x^2)^(1//3),	x,	3,	-3//4*(1+x^2)^(2//3)+3//10*(1+x^2)^(5//3), SI.NotImplementedError],	#exponent 1//3
[sqrt(x)//((-1)//x^(1//3)+sqrt(x)),	x,	10,	6*x^(1//6)+x+6//5*log(1-x^(1//6))-3//10*log(2+x^(1//6)+2*x^(1//3)-x^(1//6)*sqrt(5))*(1-sqrt(5))-3//10*log(2+x^(1//6)+2*x^(1//3)+x^(1//6)*sqrt(5))*(1+sqrt(5))-3//5*atan(1//2*(1+4*x^(1//6)+sqrt(5))*sqrt(1//10*(5+sqrt(5))))*sqrt(2*(5-sqrt(5)))-3//5*atan((1+4*x^(1//6)-sqrt(5))/sqrt(2*(5+sqrt(5))))*sqrt(2*(5+sqrt(5))), SI.NotImplementedError],
[1//(1//x^(1//4)+sqrt(x)),	x,	9,	4//3*log(1+x^(1//4))-2//3*log(1-x^(1//4)+sqrt(x))+4*atan((1-2*x^(1//4))/sqrt(3))/sqrt(3)+2*sqrt(x), SI.NotImplementedError],
[1//(1//x^(1//3)+1//x^(1//4)),	x,	4,	12*x^(1//12)-6*x^(1//6)+4*x^(1//4)-3*x^(1//3)+12//5*x^(5//12)+12//7*x^(7//12)-3//2*x^(2//3)+4//3*x^(3//4)-6//5*x^(5//6)+12//11*x^(11//12)-x+12//13*x^(13//12)-6//7*x^(7//6)+4//5*x^(5//4)-12*log(1+x^(1//12))-2*sqrt(x), SI.NotImplementedError],	# exponent 1//3, 1/4
[sqrt((1-x)//x),	x,	5,	-atan(sqrt(-1+1//x))+x*sqrt(-1+1//x), SI.NotImplementedError],
[cos(x)//(sin(x)+sin(x)^2),	x,	2,	log(sin(x))-log(1+sin(x))],
[exp(2*x)//(2+3*exp(x)+exp(2*x)),	x,	4,	-log(1+exp(x))+2*log(2+exp(x))],
[1//sqrt(1+exp(x)),	x,	3,	-2*atanh(sqrt(1+exp(x))), SI.NotImplementedError],
[sqrt(1-exp(x)),	x,	4,	-2*atanh(sqrt(1-exp(x)))+2*sqrt(1-exp(x)), SI.NotImplementedError],
[1//(3-5*sin(x)),	x,	4,	-1//4*log(cos(1//2*x)-3*sin(1//2*x))+1//4*log(3*cos(1//2*x)-sin(1//2*x))],
[1//(cos(x)+sin(x)),	x,	2,	-atanh((cos(x)-sin(x))/sqrt(2))/sqrt(2)],	# result contains algebraic numbers
[1//(1-cos(x)+sin(x)),	x,	2,	-log(1+cot(1//2*x))],
[1//(4*cos(x)+3*sin(x)),	x,	2,	-1//5*atanh(1//5*(3*cos(x)-4*sin(x)))],
[1//(sin(x)+tan(x)),	x,	6,	-1//2*atanh(cos(x))+1//2*cot(x)*csc(x)-1//2*csc(x)^2],
[1//(2*sin(x)+sin(2*x)),	x,	4,	1//4*log(tan(1//2*x))+1//8*tan(1//2*x)^2],
[sec(x)//(1+sin(x)),	x,	4,	1//2*atanh(sin(x))+(-1//2)//(1+sin(x))],
[1//(b*cos(x)+a*sin(x)),	x,	2,	-atanh((a*cos(x)-b*sin(x))/sqrt(a^2+b^2))/sqrt(a^2+b^2)],
[1//(b^2*cos(x)^2+a^2*sin(x)^2),	x,	2,	atan(a*tan(x)/b)/(a*b)],

# Section 7.6 - Strategy for Integration
[x//(-1+x^2),	x,	1,	1//2*log(1-x^2)],
[sqrt(x)*(1+sqrt(x)),	x,	2,	2//3*x^(3//2)+1//2*x^2, SI.NotImplementedError],
[1//(1-cos(x)),	x,	1,	-sin(x)//(1-cos(x))],
[sec(x)*tan(x)^2,	x,	2,	-1//2*atanh(sin(x))+1//2*sec(x)*tan(x)],
[sec(x)^3*tan(x)^3,	x,	3,	-1//3*sec(x)^3+1//5*sec(x)^5],
[exp(sqrt(x)),	x,	3,	-2*exp(sqrt(x))+2*exp(sqrt(x))*sqrt(x), SI.NotImplementedError],
[(1+x^5)//(-10*x-3*x^2+x^3),	x,	3,	19*x+3//2*x^2+1//3*x^3+3126//35*log(5-x)-1//10*log(x)-31//14*log(2+x)],
[1//(x*sqrt(log(x))),	x,	2,	2*sqrt(log(x)), SI.NotImplementedError],
[(5+2*x)//(-3+x),	x,	2,	2*x+11*log(3-x)],
[exp(exp(x)+x),	x,	2,	exp(exp(x))],
[cos(x)^2*sin(x)^2,	x,	3,	1//8*x+1//8*cos(x)*sin(x)-1//4*cos(x)^3*sin(x)],
[(-cos(x)+sin(x))//(cos(x)+sin(x)),	x,	1,	-log(cos(x)+sin(x))],
[x//sqrt(1-x^2),	x,	1,	-sqrt(1-x^2), SI.NotImplementedError],
[x^3*log(x),	x,	1,	-1//16*x^4+1//4*x^4*log(x)],
[sqrt(-2+x)//(2+x),	x,	3,	-4*atan(1//2*sqrt(-2+x))+2*sqrt(-2+x), SI.NotImplementedError],
[x//(2+x)^2,	x,	2,	2//(2+x)+log(2+x)],
[log(1+x^2),	x,	3,	-2*x+2*atan(x)+x*log(1+x^2)],
[sqrt(1+log(x))//(x*log(x)),	x,	4,	-2*atanh(sqrt(1+log(x)))+2*sqrt(1+log(x)), SI.NotImplementedError],
[(1+sqrt(x))^8,	x,	3,	-2//9*(1+sqrt(x))^9+1//5*(1+sqrt(x))^10, SI.NotImplementedError],
[sec(x)^4*tan(x)^3,	x,	3,	-1//4*sec(x)^4+1//6*sec(x)^6],
[x//(2-2*x+x^2),	x,	4,	-atan(1-x)+1//2*log(2-2*x+x^2)],
[x*asin(x),	x,	3,	-1//4*asin(x)+1//2*x^2*asin(x)+1//4*x*sqrt(1-x^2), SI.NotImplementedError], # asin
[sqrt(9-x^2)//x,	x,	4,	-3*atanh(1//3*sqrt(9-x^2))+sqrt(9-x^2), SI.NotImplementedError],
[x//(2+3*x+x^2),	x,	3,	-log(1+x)+2*log(2+x)],
[x^2*cosh(x),	x,	3,	-2*x*cosh(x)+2*sinh(x)+x^2*sinh(x)],
[(1+x+x^3)//(4*x+2*x^2+x^4),	x,	1,	1//4*log(4*x+2*x^2+x^4)],

[cos(x)//(1+sin(x)^2),	x,	2,	atan(sin(x))],
[cos(sqrt(x)),	x,	3,	2*cos(sqrt(x))+2*sin(sqrt(x))*sqrt(x), SI.NotImplementedError],
[sin(Pi*x),	x,	1,	-cos(Pi*x)//Pi, SI.NotImplementedError], #Pi
[exp(2*x)//(1+exp(x)),	x,	3,	exp(x)-log(1+exp(x))],
[exp(3*x)*cos(5*x),	x,	1,	3//34*exp(3*x)*cos(5*x)+5//34*exp(3*x)*sin(5*x)],
[cos(3*x)*cos(5*x),	x,	1,	1//4*sin(2*x)+1//16*sin(8*x)],
[1//(1+x+x^2+x^3),	x,	5,	1//2*atan(x)+1//2*log(1+x)-1//4*log(1+x^2)],
[x^2*log(1+x),	x,	3,	-1//3*x+1//6*x^2-1//9*x^3+1//3*log(1+x)+1//3*x^3*log(1+x)],
[x^5//exp(x^3),	x,	2,	(-1//3)//exp(x^3)-1//3*x^3//exp(x^3)],
[tan(4*x)^2,	x,	2,	-x+1//4*tan(4*x)],
[1//sqrt(-5+12*x+9*x^2),	x,	2,	1//3*atanh((2+3*x)//sqrt(-5+12*x+9*x^2)), SI.NotImplementedError],
[x^2*atan(x),	x,	4,	-1//6*x^2+1//3*x^3*atan(x)+1//6*log(1+x^2)],
[(1-sqrt(x))//x^(1//3),	x,	2,	3//2*x^(2//3)-6//7*x^(7//6), SI.NotImplementedError],
[1//((-1)//exp(x)+exp(x)),	x,	2,	-atanh(exp(x))],
[x//(10+2*x^2+x^4),	x,	3,	1//6*atan(1//3*(1+x^2))],
[1//(1//x^(1//3)+x),	x,	2,	3//4*log(1+x^(4//3)), SI.NotImplementedError],	# exponent 1//3
[cos(x)^4*sin(x)^2,	x,	4,	1//16*x+1//16*cos(x)*sin(x)+1//24*cos(x)^3*sin(x)-1//6*cos(x)^5*sin(x)],
[1//sqrt(5-4*x-x^2),	x,	2,	-asin(1//3*(-2-x)), SI.NotImplementedError],
[x//(1-x^2+sqrt(1-x^2)),	x,	3,	-log(1+sqrt(1-x^2)), SI.NotImplementedError],
[(1+cos(x))*csc(x),	x,	2,	log(1-cos(x))],
[exp(x)//(-1+exp(2*x)),	x,	2,	-atanh(exp(x))],
[1//(-8+x^3),	x,	6,	1//12*log(2-x)-1//24*log(4+2*x+x^2)-1//4*atan((1+x)/sqrt(3))/sqrt(3)],
[x^5*cosh(x),	x,	6,	-120*cosh(x)-60*x^2*cosh(x)-5*x^4*cosh(x)+120*x*sinh(x)+20*x^3*sinh(x)+x^5*sinh(x)],
[log(tan(x))//(cos(x)*sin(x)),	x,	1,	1//2*log(tan(x))^2],
[-2*x+x^2+x^3,	x,	1,	-x^2+1//3*x^3+1//4*x^4],
[(1+exp(x))//(1-exp(x)),	x,	3,	x-2*log(1-exp(x))],
[x//((1+x^2)*(4+x^2)),	x,	4,	1//6*log(1+x^2)-1//6*log(4+x^2)],
[1//(4-5*sin(x)),	x,	4,	-1//3*log(cos(1//2*x)-2*sin(1//2*x))+1//3*log(2*cos(1//2*x)-sin(1//2*x))],
[x*(c+x)^(1//3),	x,	2,	-3//4*c*(c+x)^(4//3)+3//7*(c+x)^(7//3), SI.NotImplementedError],	# exponent 1//3
[exp(x^(1//3)),	x,	4,	6*exp(x^(1//3))-6*exp(x^(1//3))*x^(1//3)+3*exp(x^(1//3))*x^(2//3), SI.NotImplementedError],	#exponent 1//3
[1//(4+x+sqrt(1+x)),	x,	5,	log(4+x+sqrt(1+x))-2*atan((1+2*sqrt(1+x))/sqrt(11))/sqrt(11), SI.NotImplementedError],
[(1+x^3)//(-x^2+x^3),	x,	3,	1//x+x+2*log(1-x)-log(x)],
[(-3+4*x+x^2)*sin(2*x),	x,	8,	7//4*cos(2*x)-2*x*cos(2*x)-1//2*x^2*cos(2*x)+sin(2*x)+1//2*x*sin(2*x)],
[cos(cos(x))*sin(x),	x,	2,	-sin(cos(x))],
[1//sqrt(16-x^2),	x,	1,	asin(1//4*x), SI.NotImplementedError],
[x^3//(1+x)^10,	x,	2,	1//9//(1+x)^9+(-3//8)//(1+x)^8+3//7//(1+x)^7+(-1//6)//(1+x)^6],
[cot(2*x)^3*csc(2*x)^3,	x,	3,	1//6*csc(2*x)^3-1//10*csc(2*x)^5],
[(x+sin(x))^2,	x,	6,	1//2*x+1//3*x^3-2*x*cos(x)+2*sin(x)-1//2*cos(x)*sin(x)],
[exp(atan(x))//(1+x^2),	x,	1,	exp(atan(x))],
[1//(x*(1+x^4)),	x,	4,	log(x)-1//4*log(1+x^4)],
[t^3//exp(2*t),	t,	4,	(-3//8)//exp(2*t)-3//4*t//exp(2*t)-3//4*t^2//exp(2*t)-1//2*t^3//exp(2*t)],
[sqrt(t)//(1+t^(1//3)),	t,	7,	-6*t^(1//6)-6//5*t^(5//6)+6//7*t^(7//6)+6*atan(t^(1//6))+2*sqrt(t), SI.NotImplementedError],
[sin(x)*sin(2*x)*sin(3*x),	x,	5,	-1//8*cos(2*x)-1//16*cos(4*x)+1//24*cos(6*x)],
[log(1//2*x),	x,	1,	-x+x*log(1//2*x)],
[sqrt((1+x)//(1-x)),	x,	3,	2*atan(sqrt((1+x)//(1-x)))-(1-x)*sqrt((1+x)//(1-x)), SI.NotImplementedError],
[x*log(x)//sqrt(-1+x^2),	x,	5,	atan(sqrt(-1+x^2))-sqrt(-1+x^2)+log(x)*sqrt(-1+x^2), SI.NotImplementedError],
[(a+x)//(a^2+x^2),	x,	3,	atan(x//a)+1//2*log(a^2+x^2)],
[sqrt(1+x-x^2),	x,	3,	-5//8*asin((1-2*x)/sqrt(5))-1//4*(1-2*x)*sqrt(1+x-x^2), SI.NotImplementedError],
[x^4//(16+x^10),	x,	2,	1//20*atan(1//4*x^5)],
[(2+x)//(2+x+x^2),	x,	4,	1//2*log(2+x+x^2)+3*atan((1+2*x)/sqrt(7))/sqrt(7)],
[x*sec(x)*tan(x),	x,	2,	-atanh(sin(x))+x*sec(x)],
[x//(-a^4+x^4),	x,	2,	-1//2*atanh(x^2//a^2)//a^2],
[1//(sqrt(x)+sqrt(1+x)),	x,	3,	-2//3*x^(3//2)+2//3*(1+x)^(3//2), SI.NotImplementedError],
[1//(1+(-1)//exp(x)+2*exp(x)),	x,	4,	1//3*log(1-2*exp(x))-1//3*log(1+exp(x))],
[atan(sqrt(x))//sqrt(x),	x,	2,	-log(1+x)+2*atan(sqrt(x))*sqrt(x), SI.NotImplementedError],
[log(1+x)//x^2,	x,	4,	log(x)-log(1+x)-log(1+x)//x],
[1//(-exp(x)+exp(3*x)),	x,	3,	exp(-x)-atanh(exp(x))],
[(1+cos(x)^2)//(1-cos(x)^2),	x,	4,	-x-2*cot(x)],

# Section 7.?
[1//(x*sqrt(-25+2*x)),	x,	2,	2//5*atan(1//5*sqrt(-25+2*x)), SI.NotImplementedError],
[sin(2*x)//sqrt(9-cos(x)^4),	x,	5,	-asin(1//3*cos(x)^2), SI.NotImplementedError],
[x^2//sqrt(5-4*x^2),	x,	2,	5//16*asin(2*x/sqrt(5))-1//8*x*sqrt(5-4*x^2), SI.NotImplementedError],
[x^3*sin(x),	x,	4,	6*x*cos(x)-x^3*cos(x)-6*sin(x)+3*x^2*sin(x)],
[x*sqrt(4+2*x+x^2),	x,	4,	1//3*(4+2*x+x^2)^(3//2)-3//2*asinh((1+x)/sqrt(3))-1//2*(1+x)*sqrt(4+2*x+x^2), SI.NotImplementedError],
[x*(5+x^2)^8,	x,	1,	1//18*(5+x^2)^9],
[cos(x)^2*sin(x)^5,	x,	3,	-1//3*cos(x)^3+2//5*cos(x)^5-1//7*cos(x)^7],
[cos(4*x)//exp(3*x),	x,	1,	-3//25*cos(4*x)//exp(3*x)+4//25*sin(4*x)//exp(3*x)],
[csc(1//2*x)^3,	x,	2,	-atanh(cos(1//2*x))-cot(1//2*x)*csc(1//2*x)],
[sqrt(-1+9*x^2)//x^2,	x,	3,	3*atanh(3*x//sqrt(-1+9*x^2))-sqrt(-1+9*x^2)//x, SI.NotImplementedError],
[sqrt(4-3*x^2)//x,	x,	4,	-2*atanh(1//2*sqrt(4-3*x^2))+sqrt(4-3*x^2), SI.NotImplementedError],
[exp(3*x)*x^2,	x,	3,	2//27*exp(3*x)-2//9*exp(3*x)*x+1//3*exp(3*x)*x^2],
[cos(x)*sin(x)//sqrt(1+sin(x)),	x,	3,	2//3*(1+sin(x))^(3//2)-2*sqrt(1+sin(x)), SI.NotImplementedError],
[x*asin(x^2),	x,	3,	1//2*x^2*asin(x^2)+1//2*sqrt(1-x^4), SI.NotImplementedError],	# asin
[x^3*asin(x^2),	x,	5,	-1//8*asin(x^2)+1//4*x^4*asin(x^2)+1//8*x^2*sqrt(1-x^4), SI.NotImplementedError],	# asin
[exp(x)*sech(exp(x)),	x,	2,	atan(sinh(exp(x)))],
[x^2*cos(3*x),	x,	3,	2//9*x*cos(3*x)-2//27*sin(3*x)+1//3*x^2*sin(3*x)],
[sqrt(5-4*x-x^2),	x,	3,	-9//2*asin(1//3*(-2-x))+1//2*(2+x)*sqrt(5-4*x-x^2), SI.NotImplementedError],
[x^5//(x^2+sqrt(2)),	x,	3,	1//4*x^4+log(x^2+sqrt(2))-x^2/sqrt(2), SI.NotImplementedError],	# integrand contains algebraic number
[sec(x)^5,	x,	3,	3//8*atanh(sin(x))+3//8*sec(x)*tan(x)+1//4*sec(x)^3*tan(x)],
[sin(2*x)^6,	x,	4,	5//16*x-5//32*cos(2*x)*sin(2*x)-5//48*cos(2*x)*sin(2*x)^3-1//12*cos(2*x)*sin(2*x)^5],
[cos(x)*log(sin(x))*sin(x)^2,	x,	4,	-1//9*sin(x)^3+1//3*log(sin(x))*sin(x)^3],
[1//(exp(x)*(1+2*exp(x))),	x,	3,	(-1)//exp(x)-2*x+2*log(1+2*exp(x))],
[sqrt(2+3*cos(x))*tan(x),	x,	4,	2*atanh(sqrt(2+3*cos(x))/sqrt(2))*sqrt(2)-2*sqrt(2+3*cos(x)), SI.NotImplementedError],
[x//sqrt(-4*x+x^2),	x,	3,	4*atanh(x//sqrt(-4*x+x^2))+sqrt(-4*x+x^2), SI.NotImplementedError],
[cos(x)^5,	x,	2,	sin(x)-2//3*sin(x)^3+1//5*sin(x)^5],
[x^4//exp(x),	x,	5,	(-24)//exp(x)-24*x//exp(x)-12*x^2//exp(x)-4*x^3//exp(x)-x^4//exp(x)],
[x^4//sqrt(-2+x^10),	x,	3,	1//5*atanh(x^5//sqrt(-2+x^10)), SI.NotImplementedError],
[exp(x)*cos(4+3*x),	x,	1,	1//10*exp(x)*cos(4+3*x)+3//10*exp(x)*sin(4+3*x)],
[exp(x)*log(1+exp(x)),	x,	4,	-exp(x)+(1+exp(x))*log(1+exp(x))],
[x^2*atan(x),	x,	4,	-1//6*x^2+1//3*x^3*atan(x)+1//6*log(1+x^2)],
[sqrt(-1+exp(2*x)),	x,	4,	-atan(sqrt(-1+exp(2*x)))+sqrt(-1+exp(2*x)), SI.NotImplementedError],
[exp(sin(x))*sin(2*x),	x,	4,	-2*exp(sin(x))+2*exp(sin(x))*sin(x)],
[x^2*sqrt(5-x^2),	x,	3,	25//8*asin(x/sqrt(5))-5//8*x*sqrt(5-x^2)+1//4*x^3*sqrt(5-x^2), SI.NotImplementedError],
[x^2*(1+x^3)^4,	x,	1,	1//15*(1+x^3)^5],
[cos(x)^3*sin(x)^3,	x,	3,	1//4*sin(x)^4-1//6*sin(x)^6],
[sec(x)^4*tan(x)^2,	x,	3,	1//3*tan(x)^3+1//5*tan(x)^5],
[x*sqrt(1+2*x),	x,	2,	-1//6*(1+2*x)^(3//2)+1//10*(1+2*x)^(5//2), SI.NotImplementedError],
[sin(x)^4,	x,	3,	3//8*x-3//8*cos(x)*sin(x)-1//4*cos(x)*sin(x)^3],
[tan(x)^3,	x,	2,	log(cos(x))+1//2*tan(x)^2],
[x^5*sqrt(1+x^2),	x,	3,	1//3*(1+x^2)^(3//2)-2//5*(1+x^2)^(5//2)+1//7*(1+x^2)^(7//2), SI.NotImplementedError],

#=
# David Jeffrey - Rectifying Transformations for Trig Integration (1997)
# Problem (1.2)
[3/(5-4*cos(x)),    x,  2,  x+2*atan(sin(x)/(2-cos(x)))],
# Problem (1.4)
[(1+cos(x)+2*sin(x))/(3+cos(x)^2+2*sin(x)-2*cos(x)*sin(x)), x,  -43,    -atan((2*cos(x)-sin(x))/(2+sin(x)))],
# Problem (1.5)
[(2+cos(x)+5*sin(x))/(4*cos(x)-2*sin(x)+cos(x)*sin(x)-2*sin(x)^2),  x,  -25,    -log(1-3*cos(x)+sin(x))+log(3+cos(x)+sin(x))],
# Problem (3.3)
[(3+7*cos(x)+2*sin(x))/(1+4*cos(x)+3*cos(x)^2-5*sin(x)-cos(x)*sin(x)),  x   ,   -32,    -log(1+cos(x)-2*sin(x))+log(3+cos(x)+sin(x))],
# Problem
[(-1+4*cos(x)+5*cos(x)^2)/(-1-4*cos(x)-3*cos(x)^2+4*cos(x)^3),  x,  -2, x-2*atan(sin(x)/(3+cos(x)))-2*atan((3*sin(x)+7*cos(x)*sin(x))/(1+2*cos(x)+5*cos(x)^2))],
# Problem
[(-5+2*cos(x)+7*cos(x)^2)/(-1+2*cos(x)-9*cos(x)^2+4*cos(x)^3),  x,  -2, x-2*atan(2*cos(x)*sin(x)/(1-cos(x)+2*cos(x)^2))],
# Problem (3.4)
[3/(5+4*sin(x)),    x,  2,  x+2*atan(cos(x)/(2+sin(x)))],
# Problem (3.6)
[2/(1+cos(x)^2),    x,  3,  x*sqrt(2)-atan(cos(x)*sin(x)/(1+cos(x)^2+sqrt(2)))*sqrt(2)],
# Problem (3.8)
[1/(p+q*cos(x)+r*sin(x)),   x,  3,  2*atan((r+(p-q)*tan(1/2*x))/sqrt(p^2-q^2-r^2))/sqrt(p^2-q^2-r^2), SI.NotImplementedError],

# Waldek Hebisch - email May 2013

# Problem #1
[(1-x^3+x^4-x^5+x^6)*exp(x),    x,  25, 871*exp(x)-870*exp(x)*x+435*exp(x)*x^2-145*exp(x)*x^3+36*exp(x)*x^4-7*exp(x)*x^5+exp(x)*x^6],
# Problem #2
#[(2-x^2)*exp(x/(2+x^2))/(2*x+x^3),  x,  -5,Ei(x/(2+x^2))],
#[(2+2*x+3*x^2-x^3+2*x^4)*exp(x/(2+x^2))/(2*x+x^3),  x,  -5, exp(x/(2+x^2))*(2+x^2)+Ei(x/(2+x^2))],
# Problem #3
#[(1+exp(x))*exp(x+exp(x))/(x+exp(x)),  x,   2, Ei(exp(x)+x)],
# Problem #4
[(1-3*x-x^2+x^3)*exp(1/(-1+x^2))/(1-x-x^2+x^3), x,  -6, exp(1/(-1+x^2))*(1+x)],
# Problem #5
[exp(1+1/log(x))*(-1+log(x)^2)/log(x)^2,    x,  1,  exp(1+1/log(x))*x],
[exp(x+1/log(x))*(-1+(1+x)*log(x)^2)/log(x)^2,  x,  -2, exp(x+1/log(x))*x]
=#
]


k = 0
expected_exceptions = 0
unexpected_exceptions = 0
failed = 0
passed = 0
for prob in problems
    global k, passed, failed, expected_exceptions, unexpected_exceptions
    k += 1
    println("--- #$k -----------------------------------------------------------------")
    print("∫", prob[1], "dx = ")
    if length(prob)<=4
        try
            result = SI.integrate(prob[1], prob[2], catchNotImplementedError=false, catchAlgorithmFailedError=false)
            println(result)
            arg = 1.123456789
            err = abs(SymbolicUtils.substitute(prob[1]-Symbolics.derivative(result, prob[2]), prob[2]=>arg))
            if !isa(err, Real) || err>1e-8
                if isa(err, Real)
                    println("FAILED: wrong result, err=$err")
                else
                    println("FAILED: wrong result, complete solution should exist")
                end
                failed += 1
            else
                passed += 1
            end
        catch e
            unexpected_exceptions += 1
            failed += 1
            println("\nFAILED: unexpected exception $e")
        end
        println("expected: ", prob[4])
    else
        try
            result = SI.integrate(prob[1], prob[2], catchNotImplementedError=false, catchAlgorithmFailedError=false)
        catch e
            if e isa prob[5]
                println(e.msg)
                expected_exceptions += 1
                passed += 1
            else
                println("\nFAILED: unexpected exception $e")
                unexpected_exceptions += 1
                failed += 1
            end
        end
        println("expected: ", prob[5])
    end
end

println("----------------------------------------------------------")
total = failed+passed
println("passed: $passed, of which expected exceptions: $expected_exceptions, failed: $failed, of which unexpected exceptions: $unexpected_exceptions, total: $total")
