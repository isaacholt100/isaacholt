#import "../../template.typ": template
#show: template

#let char = $op("char")$
#let cbrt(arg) = $root(3, #arg)$

= Introduction

== Cubic equations over $CC$

- For a polynomial equation, a *solution by radicals* is a formula for solutions using only addition, subtraction, multiplication, division and radicals $root(m, dot.op)$ for $m in NN$.
- For general cubic equation $x^3 + a_2 x^2 + a_1 x + a_0 = 0$:
    - *Tschirnhaus transformation* is substitution $t = x + a_2 / 3$, giving $ t^3 + p t + q = 0, quad p = (-a_2^2 + 3a_1) / 3, quad q = (2a_2^3 - 9a_1 a_2 + 27a_0)/27 $ This is a *reduced* cubic equation.
    - When $t = u + v$, $t^3 - (3u v)t - (u^3 + v^3) = 0$ which is in the reduced cubic form with $p = -3u v, q = -(u^3 + v^3)$.
    - We have $ (y - u^3)(y - v^3) = y^2 - (u^3 + v^3)y + u^3 v^3 = y^2 + q y - p^3/27 = 0 $ so $u^3, v^3 = -q/2 plus.minus sqrt(q^2/4 + p^3/27)$.
    - So a solution to $t^3 + p t + q = 0$ is $ t = u + v = cbrt(-q/2 + sqrt(q^2/4 + p^3 / 27)) + cbrt(-q/2 - sqrt(q^2/4 + p^3 / 27)) $ The other solutions are $omega u + omega^2 v$ and $omega^2 u + omega v$ where $omega = e^(2pi i \/ 3)$ is the 3rd root of unity. This is because $u$ and $v$ each have three solutions indepedently to $u^3, v^3 = -q/2 plus.minus sqrt(q^2/4 + p^3/27)$, but also $u v = -p/3$.
- *Remark*: the above method doesn't work for fields of characteristic $2$ or $3$ since the formulas involve division by $2$ or $3$ (which is dividing by zero in these respective fields).
- For general cubic equation $x^3 + a_3 x^3 + a_2 x^2 + a_1 x + a_0 = 0$:
    - Substitution $t = x + a_3/4$ gives *reduced* quartic equation $ t^4 + p t^2 + q t + r = 0 $
    - We then manipulate the polynomial so that it is the sum or difference of two squares and use $a^2 + b^2 = (a + i b)(a - i b)$ or $a^2 - b^2 = (a + b)(a - b)$: $ (t^2 + w)^2 + (p - 2w)t^2 + q t + (r - w^2) = 0 $
    - $(p - 2w)t^2 + q t + (r - w^2) = 0$ is a square iff its discriminant is zero: $ q^2 - 4(p - 2w)(r - w^2) = 0 <==> w^3 - 1/2 p w^2 - r w + 1/8 (4p r - q^2) = 0 $
    - This *cubic resolvent* is solvable by radicals. Taking any of the solutions and substituting for $w$ gives a sum or difference of two squares in $t$. The quadratic factors can then be solved.

== Galois theory for quadratic equations



= Fields and polynomials

== Basic properties of fields

- *Definition*: ring $R$ is *field* if every element of $R - {0}$ has mutliplicative inverse and $1 != 0 in R$.
- *Lemma*: every field is integral domain.
- *Definition*: field homomorphism is a ring homomorphism $phi: K -> L$ between fields:
    - $phi(a + b) = phi(a) + phi(b)$
    - $phi(a b) = phi(a) phi(b)$
    - $phi(1) = 1$
These imply $phi(0) = 0$, $phi(-a) = -phi(a)$, $phi(a^(-1)) = phi(a)^(-1)$.
- *Lemma*: let $phi: K -> L$ homomorphism.
    - $im(phi) = {phi(a): a in K}$ is a field.
    - $ker(phi) = {a in K: phi(a) = 0} = {0}$, i.e. $phi$ is injective.
- *Definition*: *subfield* $K$ of field $L$ is subring of $L$ where $K$ is a field. $L$ is a *field extension* of $K$.
- The above lemma shows the image of $phi: K -> L$ is a subfield of $L$.
- *Lemma*: intersections of subfields are subfields.
- *Prime subfield* of $L$: intersection of all subfields of field $L$.
- *Definition*: *characteristic* $char(K)$ of field $K$ is $ char(K) := min({0} union {n in NN: chi(n) = 0}) $ where $chi: ZZ -> K$, $chi(m) = 1 + dots.h.c + 1$ ($m$ times).
- *Example*: $char(QQ) = char(RR) = char(CC) = 0$, $char(FF_p) = p$ for $p$ prime.
- *Lemma*: for any field $K$, $char(K)$ is either $0$ or a prime.
- *Theorem*:
    - $char(K) = 0$ iff $QQ$ is the prime subfield of $K$.
    - $char(K) = p > 0$ iff $FF_p$ is the prime subfield of $K$.
- Note $p | binom(p, i)$ so $(a + b)^p = a^p + b^p$.

== Polynomials over fields

- *Degree* of $f(x) = a_0 + a_1 x + dots.h.c + a_n x_n$, $a_n != 0$ is $deg(f(x)) = n$.
- $deg(f(x)g(x)) = deg(f(x)) + deg(g(x))$ and $deg(f(x) + g(x)) = max{deg(f(x)), deg(g(x))}$ with equality if $deg(f(x)) != deg(g(x))$.
- Degree of zero polynomial is $deg(0) = -oo$.
- Only invertible elements in $K[x]$ are non-zero constants $f(x) = a_0 != 0$.
- Similarities between $ZZ$ and $K[x]$ for field $K$:
    - $K[x]$ is integral domain.
    - There is a division algorithm for $K[x]$: for $f(x), g(x) in K[x]$, $exists! q(x), r(x) in K[x]$ with $deg(r(x)) < deg(g(x))$ such that $ f(x) = q(x) g(x) + r(x) $
    - Every $f(x), g(x) in K[x]$ have greatest common divisor $gcd(f(x), g(x))$ unique up to multiplication by non-zero constants. By Euclidean algorithm for polynomials, $ exists a(x), b(x) in K[x]: a(x) f(x) + b(x) g(x) = gcd(f(x), g(x)) $
    - Can construct field from $K[x]$: *field of fractions* of $K[x]$ is $ K(x) = "Frac"(K[x]) = {f(x) / g(x): f(x), g(x) in K[x], g(x) != 0} $ (We can construct the field of fractions for any integral domain).
    - $K[x]$ is PID and UFD.
- *Definition*: $f(x) in K[x]$ *irreducible* in $K[x]$ if
    - $deg(f(x)) >= 1$ and
    - $f(x) = g(x) h(x) ==> g(x) "or" h(x) "is constant"$

== Tests for irreducibility

- If $f(x)$ has linear factor in $K[x]$, it has root in $K[x]$.
- *Rational root test*: if $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$ has rational root $b/c in QQ$ with $gcd(b, c) = 1$ then $b | a_0$ and $c | a_n$.