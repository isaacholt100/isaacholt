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
- *Rational root test*: if $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$ has rational root $b/c in QQ$ with $gcd(b, c) = 1$ then $b | a_0$ and $c | a_n$. This doesn't show $f$ is irreducible for $deg(f(x)) >= 4$.
- *Gauss's lemma*: let $f(x) in ZZ[x]$, $f(x) = g(x) h(x)$, $g(x), h(x) in QQ[x]$. Then $exists r in QQ: r g(x), r^(-1) h(x) in ZZ[x]$.
- *Example*: let $f(x) = x^4 - 3x^3 + 1 in QQ[x]$. Using the rational root test, $f(plus.minus 1) != 0$ so no linear factors in $QQ[x]$. Checking quadratic factors, let $ f(x) = (a x^2 + b x + c)(r x^2 + s x + t), quad a, b, c, r, s, t in ZZ "by Gauss's lemma" $ So $1 = a r => a = r = plus.minus 1$. $1 = c t => c = t = plus.minus 1$. $-3 = b + s$ and $0 = c(b + s)$: contradiction. So $f(x)$ irreducible in $QQ[x]$.
- *Example*: let $f(x) = x^4 - 3x^2 + 1 in QQ[x]$. The rational root test shows there are no linear factors. Checking quadratic factors, let $ f(x) = (a x^2 + b x + c)(r x^2 + s x + t), quad a, b, c, r, s, t in ZZ "by Gauss's lemma" $ As before, $a = r = plus.minus 1$, $c = t = plus.minus 1$. $0 = b + s => b = -s$, $-3 = a t + b s + c r = -b^2 plus.minus 2$. $b = 1$ works. So $f(x) = (x^2 - x - 1)(x^2 + x - 1)$.
- *Proposition*: let $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$. If exists prime $p divides.not a_n$ such that $overline(f)(x)$ is irreducible in $FF_p [x]$, then $f(x)$ irreducible in $QQ[x]$.
- *Example*: let $f(x) = 8x^3 + 14x - 9$. Reducing $mod 7$, $overline(f)(x) = x^3 - 2 in FF_7 [x]$. No roots exist for this, so $f(x)$ irreducible in $QQ[x]$. For polynomials, no $p$ is suitable, e.g. $f(x) = x^4 + 1$.
- Gauss's lemma works with any UFD $R$ instead of $ZZ$ and field of fractions $"Frac"(R)$ instead of $QQ$: let $F$ field, $R = F[t]$, $K = F(t)$, then $f(x) in R[x]$ irreducible in $K[x]$ iff $f(x)$ has no proper factors in $R[x]$.
- *Eisenstein's criterion*: let $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$, prime $p in ZZ$ such that $p | a_0, ..., p | a_(n - 1)$, $p divides.not a_n$, $p^2 divides.not a_0$. Then $f(x)$ irreducible in $QQ[x]$.
- Eisenstein's criterion generalises to UFD $R$ instead of $ZZ$, $"Frac"(R)$ instead of $QQ$.
- *Example*: let $f(x) = x^3 - 3x + 1$. Consider $f(x - 1) = x^3 - 3x^2 + 3$. Then by Eisenstein's criterion with $p = 3$, $f(x - 1)$ irreducible in $QQ[x]$ so $f(x)$ is as well, since factoring $f(x - 1)$ is equivalent to factoring $f(x)$.
- *Example*: *$p$-th cyclotomic polynomial* is $ f(x) = (x^p - 1)/(x - 1) = 1 + dots.h.c + x^(p - 1) $ Now $ f(x + 1) = ((1 + x)^p - 1)/(1 + x - 1) = x^(p - 1) + p x^(p - 2) + dots.h.c + binom(p, p - 2) x + p $ so can apply Eisenstein with $p$.
-

= Field extensions

== Definitions and examples

- *Definition*: *field extension* $L \/ K$ is field $L$ containing subfield $K$. Can specify homomorphism $iota: K -> L$ (which is injective)
- *Example*:
    - $CC \/ RR$, $CC \/ QQ$, $RR \/ QQ$.
    - $L = QQ(sqrt(2)) = {a + b sqrt(2): a, b in QQ}$ is field extension of $QQ$. $QQ(theta)$ is field extension of $QQ$ where $theta$ is root of $f(x) in Q[x]$.
    - $L = QQ\(root(3, 2)\) = {a + b root(3, 2) + c root(3, 4): a, b, c in QQ}$ is smallest subfield of $RR$ containing $QQ$ and $root(3, 2)$.
    - $L = K(t)$ is field extension of $K$.
- *Definition*: let $L \/ K$ field extension, $S subset.eq L$. Then *$K$ with $S$ adjoined*, $K(S)$, is minimal subfield of $L$ containing $K$ and $S$. If $|S| = 1$, $L \/ K$ is a *simple extension*.
- *Example*: $QQ(sqrt(2), sqrt(7)) = \{a + b sqrt(2) + c sqrt(7) + d sqrt(14): a, b, c, d, in QQ\}$ is $QQ$ with $S = \{sqrt(2), sqrt(7)\}$.
- *Example*: $RR \/ QQ$ is not simple extension.
- *Definition*: a *tower* if a chain of field extensions, e.g. $K subset M subset L$.

== Algebraic elements and minimal polynomials

- *Definition*: let $L \/ K$ field extension, $theta in L$. Then $theta$ is *algebraic over $K$* if $ exists 0 != f(x) in K[x]: f(theta) = 0 $ Otherwise, $theta$ is *transcendental over $K$*.
- *Example*: for $n >= 1$, $theta = e^(2pi i\/n)$ is algebraic over $QQ$ (root of $x^n - 1$).
- *Example*: $t in K(t)$ is transcendental over $K$.