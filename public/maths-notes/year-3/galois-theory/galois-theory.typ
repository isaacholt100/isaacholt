#import "../../template.typ": template
#show: template

#let char = $op("char")$
#let cbrt(arg) = $root(3, #arg)$
#let ideal(gens) = $angle.l gens angle.r$
#let Aut = $"Aut"$
#let Gal = $"Gal"$

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
- *Definition*: *characteristic* $char(K)$ of field $K$ is $ char(K) := min{n in NN: chi(n) = 0} $ (or $0$ if this does not exist) where $chi: ZZ -> K$, $chi(m) = 1 + dots.h.c + 1$ ($m$ times).
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
- *Lemma*: the algebraic elements in $K(t)\/K$ are precisely $K$.
- *Lemma*: let $L\/K$ field extension, $theta in L$. Define $I_K (theta) := {f(x) in K[x]: f(theta) = 0}$. Then $I_K (theta)$ is ideal in $K[x]$ and
    - If $theta$ transcendental over $K$, $I_K (theta) = {0}$
    - If $theta$ algebraic over $K$, then exists unique monic irreducible polynomial $m(x) in K[x]$ such that $I_K (theta) = angle.l m(x) angle.r$.
- *Definition*: for $theta in L$ algebraic over $K$, *minimal polynomial* of $theta$ over $K$ is the unique monic polynomial $m(x) in K[x]$ such that $I_K (theta) = angle.l m(x) angle.r$. The *degree* of $theta$ over $K$ is $deg(m(x))$.
- *Remark*: if $f(x) in K[x]$ irreducible over $K$, monic and $f(theta) = 0$ then $f(x) = m(x)$.
- *Example*:
    - Any $theta in K$ has minimal polynomial $x - theta$ over $K$.
    - $i in CC$ has minimal polynomial $x^2 + 1$ over $RR$.
    - $sqrt(2)$ has minimal polynomial $x^2 - 2$ over $QQ$. $root(3, 2)$ has minimal polynomial $x^3 - 2$ over $QQ$.

== Constructing field extensions

- *Lemma*: let $K$ field, $f(x) in K[x]$ non-zero. Then $ f(x) "irreducible over" K <==> K[x] \/ angle.l f(x) angle.r "is a field" $
- *Theorem*: let $m(x) in K[x]$ irreducible, monic, $K_m := K[x] \/ ideal(m(x))$. Then
    - $K_m \/ K$ is field extension.
    - Let $theta = pi(x)$ where $pi: K[x] -> K_m$ is canonical projection, then $theta$ has minimal polynomial $m(x)$ and $K_m = K(theta)$.
- *Definition*: let $L_1 \/ K$, $L_2 \/ K$ field extensions, $phi: L_1 -> L_2$ field homomorphism. $phi$ is *$K$-homomorphism* if $forall a in K, phi(a) = a$ ($phi$ fixes elements of $K$).
    - If $phi$ is isomorphism then it is *$K$-isomorphism*.
    - If $L_1 = L_2$ and $phi$ is bijective then $phi$ is *$K$-automorphism*.
- *Example*:
    - Complex conjugation $CC -> CC$ is $RR$-automorphism.
    - Let $K$ field, $char(K) != 2$, $sqrt(2) in.not K$, so $x^2 - 2$ is minimal polynomial of $sqrt(2)$ over $K$, then $K(sqrt(2)) tilde.equiv K[x] \/ ideal(x^2 - 2)$ is field extension of $K$ and $a + b sqrt(2) -> a - b sqrt(2)$ is $K$-automorphism.
- *Proposition*: let $L\/K$ field extension, $tau in L$ with $m(tau) = 0$ and $K_L (tau)$ be minimal subfield of $L$ containing $K$ and $tau$. Then exists unique $K$-isomorphism $phi: K_m -> K_L (tau)$ such that $phi(theta) = tau$.
- *Proposition*: let $theta$ transcendental over $K$, then exists unique $K$-isomorphism $phi: K(t) -> K(theta)$ such that $phi(t) = theta$: $ phi(f(g)/g(t)) = phi(f(theta)/g(theta)) $

== Explicit examples of simple extensions

- Let $r in K^times$ non-square in $K$, then $x^2 - r$ irreducible in $K[x]$. E.g. for $K = QQ(t)$, $x^2 - t in K[x]$ irreducible. Then $K\(sqrt(t)\) = QQ\(sqrt(t)\) = tilde.equiv K[x] \/ ideal(x^2 - t)$. Then for $s = sqrt(3)$, we have an extension $QQ(s) \/ QQ(s^2)$.
- Define $FF_9 = FF_3 [x] \/ ideal(x^2 - 2) tilde.equiv FF_3 (theta) = {a + b theta: a, b in FF_3}$ for $theta$ a root of $x^2 - 2$.
- *Proposition*: let $K(theta)\/K$ where $theta$ has minimal polynomial $m(x) in K[x]$ of degree $n$. Then $ K[x] \/ ideal(m(x)) tilde.equiv = K(theta) = {c_0 + c_1 theta + dots.h.c + c_(n - 1) theta^(n - 1): c_i in K} $ and its elements are written uniquely: $K(theta)$ is vector space over $K$ of dimension $n$ with basis ${1, theta, ..., theta^(n - 1)}$.
- *Example*: $QQ(cbrt(2)) = {a + b cbrt(2) + c cbrt(4): a, b, c in QQ} tilde.equiv QQ[x] \/ ideal(x^3 - 2)$. $QQ(omega cbrt(2))$ and $QQ(w^2 cbrt(2))$ where $omega = e^(2pi i \/ 3)$ are isomorphic to $QQ(cbrt(2))$ as $omega cbrt(2)$, $omega cbrt(4)$ have same minimal polynomial.

== Degrees of field extensions

- *Definition*: *degree* of field extension $L\/K$ is $ [L: K] := dim_L (F) $ Write $[L: K] < oo$ if degree is finite.
- *Example*:
  - When $theta$ algebraic over $K$ of degree $n$, $[K(theta): K] = n$.
  - Let $theta$ transcendental over $K$, then $[K(theta): K] = oo$, so $[K(t): K] = oo$, $[QQ(pi): QQ]$, $[RR: QQ] = oo$.
- *Proposition*: let $[L: K] < oo$, then every element in $L\/K$ is algebraic over $K$ (in this case, $L\/K$ is *algebraic extension*).
- *Tower theorem*: let $K subset.eq M subset.eq L$ *tower* of field extensions. Then
  - $[L: K] < oo <==> [L: M] < oo and [M: K] < oo$.
  - $[L: K] = [L: M] [M: K]$.
- *Example*:
    - $K = QQ subset M = QQ\(sqrt(2)\) subset L = QQ\(sqrt(2), sqrt(7)\)$. $M\/K$ has basis ${1, sqrt(2)}$ so $[M: K] = 2$. Let $sqrt(7) in QQ(sqrt(2))$, then $sqrt(7) = c + d sqrt(2)$, $c, d in QQ$ so $7 = (c^2 + 2d^2) + 2c d sqrt(2)$ so $7 = c^2 + 2d^2$, $0 = 2c d$ so $d^2 = 7/2$ or $c^2 = 7$, which are both contradictions. So $[L: K] = 4$ with basis $\{1, sqrt(2), sqrt(7), sqrt(14)\}$.
    - Let $K = QQ subset M = QQ(i) subset QQ\(i, sqrt(2)\)$. We know $[QQ(i): QQ] = 2$, and $\[QQ\(sqrt(2)\): QQ\] = 2$, $\[QQ\(i, sqrt(2)\): QQ\] = 2$ (since $i in.not RR$) so $\[QQ\(i, sqrt(2)\): QQ\(sqrt(2)\)\] = 2$.
    - Let $K = QQ subset M = QQ\(sqrt(2)\) subset L = QQ\(sqrt(2), cbrt(3)\)$. Then $\[QQ\(sqrt(2)\): QQ\] = 2$, $\[QQ\(cbrt(3)\): QQ\] = 3$ so $2 | [L: K]$ and $3 | [L: K]$ so $6 | [L: K]$ so $[L: K] >= 6$. But $[L: M] <= 3$ and $[M: K] <= 2$ so $[L: K] <= 6$ hence $[L: K] = 6$.
- More generally, we have $[K(alpha, beta): K] <= [K(alpha): K] [K(beta): K]$.
- *Example*:
    - Let $theta = cbrt(4) + 1$. $QQ(theta) = QQ\(cbrt(4)\)$ so minimal polynomial over $QQ$, $m$, has $deg(m) = 3$. $(theta - 1)^3 = 4$ so minimal polynomial is $x^3 - 3x^2 + 3x - 5$.
    - Let $theta = sqrt(2) + sqrt(3)$. $QQ\(sqrt(2), theta\) = QQ\(sqrt(2), sqrt(3)\)$ which has degree $2$ over $QQ\(sqrt(2)\)$ so minimal polynomial of $theta$ over $QQ\(sqrt(2)\)$ has degree $2$, $(theta - sqrt(2)) = sqrt(3)$ so minimal polynomial is $x^2 - 2 sqrt(2) x - 1$.
    - Let $theta = sqrt(2) + sqrt(3)$. $QQ subset QQ(theta) subset QQ\(sqrt(2), sqrt(7)\)$ so $[QQ(theta): QQ] | \[QQ\(sqrt(2), sqrt(3)\): QQ\] = 4$ so $[QQ(theta): QQ] in {1, 2, 4}$. Can't be $1$ as $theta in.not QQ$. If it was $2$ then $1, theta, theta^2$ are linearly dependent over $QQ$ which leads to a contradiction. So degree of minimal polynomial of $theta$ over $QQ$ is $4$. $theta^2 = 5 + 2 sqrt(6) => (theta^2 - 5)^2 = 24$ so minimal polynomial is $x^4 - 10x^2 + 1$.

= Galois extensions

== Splitting fields

- *Definition*: for field $K$, $0 != f(x) in K[x]$, $L\/K$ is *splitting field* of $f(x)$ over $K$ if
    - $exists c in K^times, theta_1, ..., theta_n in L: f(x) = c (x - theta_1) thin dots.h.c thin (x - theta_n)$ ($f(x)$ *splits over $L$*).
    - $L = K(theta_1, ..., theta_n)$.
- *Example*:
    - $CC$ is splitting field of $x^2 + 1$ over $RR$, since $x^2 + 1 = (x + i)(x - i)$ and $CC = RR(i, -i) = RR(i)$.
    - $CC$ is not splitting field of $x^2 + 1$ over $QQ$ as $CC != QQ(i, -i)$.
    - $QQ$ is splitting field of $x^2 - 36$ over $QQ$.
    - $CC$ is splitting of $x^4 + 1$ over $RR$.
    - $QQ\(i, sqrt(2)\)$ is splitting field of $x^4 - x^2 - 2$ over $QQ$.
    - $FF_2 (theta)$ where $theta^3 + theta + 1 = 0$ is splitting field of $x^3 + x + 1$ over $FF_2$.
    - Consider splitting field of $x^3 - 2$ over $QQ$. Let $omega = e^(2pi i\/3) = (-1 + sqrt(-3))\/2$ then $QQ\(cbrt(2), omega\)$ is splitting field since it must contain $cbrt(2)$, $omega cbrt(2)$, $omega^2 cbrt(2)$.
- *Theorem*: let $0 != f(x) in K[x]$, $deg(f) = n$. Then there exists a splitting field $L$ of $f(x)$ over $K$ with $ [L: K] <= n! $
- *Notation*: for field homomorphism $phi: K -> K'$ and $f(x) = a_0 + dots.h.c + a_n x^n in K[x]$, write $ phi_* (f(x)) := phi(a_0) + dots.h.c + phi(a_n) x^n in K'[x] $
- *Lemma*: let $sigma: K -> K'$ isomorphism and $K(theta)\/K$, $theta$ has minimal polynomial $m(x) in K[x]$, $theta'$ be root of $sigma_* (m(x))$. Then there exists unique field isomorphism $tau: K(theta) -> K'(theta')$ such that $tau(theta) = theta'$ and $forall a in K, tau(a) = sigma(a)$.
- *Theorem*: for field isomorphism $sigma: K -> K'$ and $0 != f(x) in K[x]$, let $L$ be splitting field of $f(x)$ over $K$, $L'$ be splitting field of $sigma_* (f(x))$ over $K'$. Then there exists a field isomorphism $tau: L -> L'$ such that $forall a in K, tau(a) = sigma(a)$.
- *Corollary*: setting $K = K'$ and $sigma = id$ implies that splitting fields are unique.

== Normal extensions

- *Definition*: $L\/K$ is *normal* if: for all $f(x) in K[x]$, if $f$ is irreducible and has a root in $L$ then all its roots are in $L$. In particular, $f(x)$ splits completely as product of linear factors in $L[x]$. So the minimal polynomial of $theta in L$ over $K$ has all its roots in $L$ and can be written as product of linear factors in $L[x]$.
- *Example*:
    - If $[L: K] = 1$ then $L\/K$ is normal.
    - If $[L: K] = 2$ then $L\/K$ is normal: let $theta in L$ have minimal polynomial $m(x) in K[x]$, then $K subset.eq K(theta) subset.eq L$ so $deg(m(x)) = [K(theta): K] in {1, 2}$:
        - If $deg(m(x)) = 1$ then $m(x)$ is already linear.
        - If $deg(m(x)) = 2$ then $m(x) = (x - theta) m_1 (x)$, $m_1 (x) in L[x]$ is linear so $m(x)$ splits completely in $L[x]$.
    - If $[L: K] = 3$ then $L\/K$ is not necessarily normal. Let $theta$ be root of $x^3 - 2 in QQ[x]$. Other two roots are $omega theta$, $omega^2 theta$ where $omega = e^(2pi i\/3)$. If $omega theta in QQ(theta)$ then $omega = (omega theta)/theta in L$ so $QQ subset QQ(omega) subset QQ(theta)$ but $[QQ(omega): QQ] = 2$ which doesn't divide $[QQ(theta): QQ] = 3$.
    - Let $theta in CC$ be root of irreducible $f(x) = x^3 - 3x - 1 in QQ[x]$. Let $theta = u + v$, then $(u + v)^3 - 3 u v(u + v) - (u^3 + v^3) equiv 0$ implies $u v = 1 = u^3 v^3$, $u^3 + v^3 = 1$. So $(y - u^3)(y - v^3) = y^2 - y + 1$ has roots $u^3$ and $v^3$. So the three roots of $f$ are $ u + v = e^(pi i\/9) + e^(-pi i\/9) & = 2 cos(pi\/9) \ omega u + omega^2 v = e^(7pi i\/9) + e^(-7 pi i\/9) & = 2 cos(7 pi \/ 9) \ omega^2 u + omega v = e^(13 pi i\/9) + e^(-13pi i\/9) & = 2 cos(13pi\/9) $ Furthermore, for each $i, j$, $theta_i in QQ(theta_j)$, e.g. $ theta_2 = 2 cos(pi - (2pi)/9) = -2cos((2pi)/9) = -2(2cos(pi/9)^2 - 1) = 2 - theta_1^2 $ So $QQ(theta)$ contains all roots of $f(x)$.
- *Theorem (normality criterion)*: $L\/K$ is finite and normal iff $L$ is splitting field for some $0 != f(x) in K[x]$ over $K$.
- *Example*:
    - $QQ\(sqrt(2), sqrt(3), sqrt(5), sqrt(7)\)\/Q$ is normal as it is the splitting field of $f(x) = (x^2 - 2)(x^2 - 3)(x^2 - 5)(x^2 - 7) in QQ[x]$.
    - $QQ\(cbrt(2)\)\/QQ$ is not normal but $QQ\(cbrt(2), omega\)\/QQ$ is normal as it is the splitting field of $x^3 - 2 in QQ$.
    - $QQ\(root(4, 2)\)\/QQ$ is not normal but $QQ\(root(4, 2), i\)\/QQ$ is normal.
    - Let $theta$ root of $f(x) = x^3 - 3x - 1 in QQ[x]$. Then $QQ(theta)\/QQ$ is normal as is splitting field of $f(x)$ over $QQ$.
    - $FF_2 (theta)\/FF_2$ where $theta^3 + theta^2 + 1 = 0$ is normal.
    - $FF_p (theta)\/FF_p (t)$ where $theta^p = t$ is normal as it is the splitting field of $x^p - t = x^p - theta^p = (x - theta)^p$ so $f(x)$ splits into linear factors in $L[x]$.
- *Definition*: field $N$ is *normal closure* of $L\/K$ if $K subset.eq L subset.eq N$, $N\/K$ is normal, and if $K subset.eq L subset.eq N' subset.eq N$ with $N'\/K$ normal then $N = N'$.
- *Theorem*: every finite extension $L\/K$ has normal closure $N$.
- *Definition*: $Aut(L\/K)$ is group of $K$-automorphisms of $L\/K$ with composition the group operation.
- *Example*:
    - $Aut(CC\/RR)$ contains at least two elements: complex conjugation: $sigma(a + b i) = a - b i$ and the identity map $id = sigma^2$. If $tau in Aut(CC\/RR)$ then $tau(a + b i) = a + b tau(i)$. But $tau(i)^2 = tau(i^2) = tau(-1) = -1$ hence $tau(i) = plus.minus i$. So there are only two choices for $tau$. So $Aut(CC\/RR) = {id, sigma}$.
    - Let $f(x) = x^2 + p x + q in QQ[x]$ irreducible with roots $theta, theta'$. Then $Aut(QQ(theta)\/QQ) = {id, sigma} tilde.equiv ZZ\/2$ where $sigma(a + b theta) = a + b theta'$.
    - Let $theta$ root of $x^3 - 2$, let $sigma in Aut(QQ(theta)\/QQ)$. Now $sigma(theta)^3 = sigma(theta^3) = sigma(2) = 2$ so $sigma(theta) in {theta, omega theta, omega^2 theta}$ but $omega theta, omega^2 theta in.not QQ(theta)$ so $sigma(theta) = theta ==> sigma = id$.
    - Let $theta^p = t$, $sigma in Aut(FF_p (theta)\/ FF_p (t))$. Then $ sigma(theta)^p = sigma(theta^p) = sigma(t) = t = theta^p $ so $(sigma(theta) - theta))^p = sigma(theta)^p - theta^p = 0 ==> sigma(theta) = theta ==> sigma = id$.
    - Let $sigma in Aut(RR\/QQ)$. Then $alpha <= beta in RR ==> beta - alpha = gamma^2$, $gamma in RR$, so $sigma(beta) - sigma(a) = sigma(gamma)^2 >= 0$ so $sigma(alpha) <= sigma(beta)$. Given $alpha in RR$, there exist sequences $(r_n), (s_n) subset QQ$ with $r_n <= alpha <= s_n$ and $r_n -> alpha$, $s_n -> alpha$ as $n -> oo$. Hence $r_n = sigma(r_n) <= sigma(alpha) <= sigma(s_n) = s_n$ so $sigma(alpha) = alpha$ by squeezing. Hence $Aut(RR\/QQ) = {id}$.
- *Theorem*: let $L = K(theta)$, $theta$ root of irreducible $f(x) in K[x]$, $deg(f) = n$. Then $|Aut(L\/K)| <= n$, with equality iff $f(x)$ has $n$ distinct rotos in $L$.
- *Theorem*: let $L\/K$ be finite extension. Then $|Aut(L\/K)| <= [L: K]$, with equality iff $L\/K$ is normal and minimal polynomial of every $theta in L$ over $K$ has no repeated roots (in a splitting field).

== Separable extensions

- *Definition*: let $L\/K$ finite extension.
    - $theta in L$ is *separable over $K$* if its minimal polynomial over $K$ has no repeated roots (in its splitting field).
    - $L\/K$ is *separable* if every $theta in L$ is separable over $K$.
- *Example*:
    - Let $theta^3 = 2$, the minimal polynomial of $theta$ over $QQ$ is $x^3 - 2 = (x - theta)(x - omega theta)(x - omega^2 theta)$, so $QQ(theta)\/QQ$ is not normal.
    - Let $theta^3 = t$, so minimal polynomial of $theta$ over $FF_3 (t)$ is $x^3 - t = (x - theta)^3$, so $FF_3 (theta)\/FF_3 (t)$ is not separable but is normal.
- *Definition*: let $f(x) = sum_(i = 0)^n a_i x^i in K[x]$. *Formal derivative* of $f(x)$ is $ D f(x) = D(f) := sum_(i = 1)^n i a_i x^(i - 1) in K[x] $
- Formal derivative satisfies: $ D(f + g) = D(f) + D(g), quad D(f g) = f dot.op D(g) + D(f) dot.op g, quad forall a in K, D(a) = 0 $ Also $deg(D(f)) < deg(f)$. But if $char(K) = p$, then $D(x^p) = p x^(p - 1) = 0$ so it is not always true that $deg(D(f)) = deg(f) - 1$.
- *Theorem (sufficient conditions for separability)*: finite extension $L\/K$ is separable if any of the following hold:
    - $char(K) = 0$,
    - $char(K) = p$ and $K = {b^p: b in K}$ for prime $p$,
    - $char(K) = p$ and $p divides.not [L: K]$.
- *Definition*: $K$ is a *perfect field* if the first two of the above properties hold.
- *Remark*: all finite extensions of any perfect extension (e.g. $QQ, FF_p$) are separable (recall Fermat's little theorem: $forall a in FF_p, a = a^p$). So to find a non-separable extension $L\/K$, we need $char(K) = p > 0$, $K$ infinite and $p | [L: K]$. For example, $L = FF_p (theta)$, $K = FF_p (t)$ where $theta^p = t$.
- *Theorem*: let $alpha_1, ..., alpha_n$ algebraic over $K$, then $K(alpha_1, ..., alpha_n)\/K$ is separable iff every $alpha_i$ is separable over $K$.
- *Remark*: for tower $K subset.eq M subset.eq L$, $L\/K$ is separable iff $L\/M$ and $M\/K$ are separable. However, the same statement for normality does not hold.
- *Theorem of the Primitive Element*: let $L\/K$ finite and separable. Then $L\/K$ is simple, i.e. $exists alpha in L: L = K(alpha)$.

== The fundamental theorem of Galois theory

- *Definition*: finite extension $L\/K$ is *Galois extension* if it is normal and separable. Equivalently, $|Aut(L\/K)| = [L: K]$. When $L\/K$ is Galois, the *Galois group* is $Gal(L\/K) := Aut(L\/K)$.
- *Definition*: let $cal(F) := {"intermediate fields of" L\/K}$ and $cal(G) := {"subgroups of" Gal(L\/K)}$. Define the map $Gamma: cal(F) -> cal(G)$, $Gamma(M) = Gal(L\/M)$.
- *Definition*: let $L$ field, $G$ a group of automorphisms of $L$. *Fixed field* $L^G$ of $G$ is set of elements in $L$ which are invariant under all automorphisms in $G$: $ L^G := {alpha in L: forall alpha in G, thick sigma(alpha) = alpha} $
- *Theorem*: if $G$ is fintie group of automorphisms of $L$ then $L^G$ is subfield of $L$ and $[L: L^G] = |G|$.
- *Corollary*: if $L\/K$ is Galois then
    - $L^(Gal(L\/K)) = K$.
    - If $L^G = K$ for some group $G$ of $K$-automorphisms of $L$, then $G = Gal(L\/K)$.
- *Remark*: if $L\/K$ is Galois and $alpha in L$ but $alpha in.not K$, then there exists an automorphism $sigma in Gal(L\/K)$ such that $sigma(alpha) != alpha$.
- *Definition*: for $H$ subgroup of $Gal(L\/K)$, set $L^H := {alpha in L: forall sigma in H, thick sigma(alpha) = alpha}$, then $K subset.eq L^H subset.eq L$. Define $Phi: cal(G) -> cal(F)$, $Phi(H) = L^H$.
- $Gamma$ and $Phi$ are inclusion-reversing: $M_1 subset.eq M_2 ==> Gamma(M_2) subset.eq Gamma(M_1)$, and $H_1 subset.eq H_2 ==> Phi(H_2) subset.eq Phi(H_1)$.
- *Theorem A*: for finite Galois extension $L\/K$,
    - $Gamma: cal(F) -> cal(G)$ and $Phi: cal(F) -> cal(F)$ are mutually inverse bijections (the *Galois correspondence*).
    - For $M in cal(F)$, $L\/M$ is Galois and $|Gal(L\/M)| = [L: M]$.
    - For $H in cal(G)$, $L\/L^H$ is Galois and $Gal(L\/L^H) = H$.
- *Remark*: $Gal(L\/K)$ acts on $cal(F)$: given $sigma in Gal(L\/K)$ and $K subset.eq M subset.eq L$, consider $sigma(M) = {sigma(alpha): alpha in M}$ which is a subfield of $L$ and contains $K$, since $sigma$ fixes elements of $K$. Given another automorphism $tau: L -> L$, $ tau in Gal(L\/sigma(M)) & <==> forall alpha in M, tau(sigma(alpha)) = sigma(alpha) \ & <==> forall alpha in M, sigma^(-1) (tau (sigma(alpha))) = alpha \ & <==> sigma^(-1) tau sigma in Gal(L\/M) \ & <==> tau in sigma Gal(L\/M) sigma^(-1) $ Hence $sigma Gal(L\/M) sigma^(-1)$ and $Gal(L\/M)$ are conjugate subgroups of $Gal(L\/K)$. Now $ [M: K] = ([L: K]) / ([L: M]) = abs(Gal(L\/K)) / abs(Gal(L\/M)) $
- *Theorem B*: for finite Galois extension $L\/K$, $G = Gal(L\/K)$ and $K subset.eq M subset.eq L$. Then the following are equivalent:
    - $M\/K$ is Galois.
    - $forall sigma in G, quad sigma(M) = M$.
    - $H = Gal(L\/M)$ is normal subgroup of $G = Gal(L\/K)$.
    When these conditions hold, we have $Gal(M\/K) tilde.equiv G\/H$.