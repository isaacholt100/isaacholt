#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

// FIND: - \*(\w+)\*: ([\s\S]*?)(?=\n-|\n\n)\n
// REPLACE: #$1[\n    $2\n]\n

#let char = $op("char")$
#let cbrt(arg) = $root(3, #arg)$
#let ideal(..gens) = $angle.l #gens.pos().join(",") angle.r$
#let Aut = $"Aut"$
#let Gal = $"Gal"$
#let gtlex = $scripts(>)_"lex"$

= Introduction

#definition[
    *Epimorphism* is surjective homomorphism.
]
#definition[
    *Embedding* or *monomorphism* is injective homomorphism.
]

== Cubic equations over $CC$

- For a polynomial equation, a *solution by radicals* is a formula for solutions using only addition, subtraction, multiplication, division and radicals $root(m, dot.op)$ for $m in NN$.
- For general cubic equation $x^3 + a_2 x^2 + a_1 x + a_0 = 0$:
    - *Tschirnhaus transformation* is substitution $t = x + a_2 / 3$, giving $ t^3 + p t + q = 0, quad p := (-a_2^2 + 3a_1) / 3, quad q := (2a_2^3 - 9a_1 a_2 + 27a_0)/27 $ This is a *reduced* (or *depressed*) cubic equation.
    - When $t = u + v$, $t^3 - (3u v)t - (u^3 + v^3) = 0$ which is in the reduced cubic form with $p = -3u v, q = -(u^3 + v^3)$.
    - We have $ (y - u^3)(y - v^3) = y^2 - (u^3 + v^3)y + u^3 v^3 = y^2 + q y - p^3/27 = 0 $ so $u^3, v^3 = -q/2 plus.minus sqrt(q^2/4 + p^3/27)$.
    - So a solution to $t^3 + p t + q = 0$ is $ t = u + v = cbrt(-q/2 + sqrt(q^2/4 + p^3 / 27)) + cbrt(-q/2 - sqrt(q^2/4 + p^3 / 27)) $ The other solutions are $omega u + omega^2 v$ and $omega^2 u + omega v$ where $omega = e^(2pi i \/ 3)$ is the 3rd root of unity. This is because $u$ and $v$ each have three solutions independently to $u^3, v^3 = -q/2 plus.minus sqrt(q^2/4 + p^3/27)$, but also $u v = -p/3$.
#remark[
    The above method doesn't work for fields of characteristic $2$ or $3$ since the formulas involve division by $2$ or $3$ (which is dividing by zero in these respective fields).
]

== Quartic equations over $CC$

- For general quartic equation $x^4 + a_3 x^3 + a_2 x^2 + a_1 x + a_0 = 0$:
    - Substitution $t = x + a_3/4$ gives *reduced* quartic equation $ t^4 + p t^2 + q t + r = 0 $
    - We then manipulate the polynomial so that it is the sum or difference of two squares and use $a^2 + b^2 = (a + i b)(a - i b)$ or $a^2 - b^2 = (a + b)(a - b)$: $ (t^2 + w)^2 + (p - 2w)t^2 + q t + (r - w^2) = 0 $
    - $(p - 2w)t^2 + q t + (r - w^2) = 0$ is a square iff its discriminant is zero: $ q^2 - 4(p - 2w)(r - w^2) = 0 <==> w^3 - 1/2 p w^2 - r w + 1/8 (4p r - q^2) = 0 $
    - This *cubic resolvent* is solvable by radicals. Taking any of the solutions and substituting for $w$ gives a sum or difference of two squares in $t$. The quadratic factors can then be solved.

= Fields and polynomials

== Basic properties of fields

#definition[
    Ring $R$ is *field* if every element of $R - {0}$ has mutliplicative inverse and $1 != 0 in R$.
]
#lemma[
    Every field is integral domain.
]
#definition[
    *Field homomorphism* is ring homomorphism $phi: K -> L$ between fields:
    - $phi(a + b) = phi(a) + phi(b)$
    - $phi(a b) = phi(a) phi(b)$
    - $phi(1) = 1$
    These imply $phi(0) = 0$, $phi(-a) = -phi(a)$, $phi(a^(-1)) = phi(a)^(-1)$.
]
#lemma[
    Let $phi: K -> L$ field homomorphism.
    - $im(phi) = {phi(a): a in K}$ is field.
    - $ker(phi) = {a in K: phi(a) = 0} = {0}$, i.e. $phi$ is injective.
]
#definition[
    *Subfield* $K$ of field $L$ is subring of $L$ where $K$ is field. $L$ is *field extension* of $K$.
]
- The above lemma shows image of $phi: K -> L$ is subfield of $L$.
#lemma[
    Intersections of subfields are subfields.
]
#definition[
    *Prime subfield* of $L$ is intersection of all subfields of $L$.
]
#definition[
    *Characteristic* $char(K)$ of field $K$ is $ char(K) := min{n in NN: chi(n) = 0} $ (or $0$ if this does not exist) where $chi: ZZ -> K$, $chi(m) = 1 + dots.h.c + 1$ ($m$ times).
]
#example[
    $char(QQ) = char(RR) = char(CC) = 0$, $char\(FF_p\) = p$ for $p$ prime.
]
#lemma[
    For any field $K$, $char(K)$ is either $0$ or prime.
]
#theorem[
    - If $char(K) = 0$ then prime subfield of $K$ is $tilde.equiv QQ$.
    - If $char(K) = p > 0$ then prime subfield of $K$ is $tilde.equiv FF_p$.
]
#corollary[
    - If $QQ$ is subfield of $K$ then $char(K) = 0$.
    - If $FF_p$ is subfield of $K$ for prime $p$ then $char(K) = p$.
]
#remark[
    Let $char(K) = p$, then $p | binom(p, i)$ so $(a + b)^p = a^p + b^p$ in $K$. Also in $K[x]$ for $p$ prime, $x^p - 1 = (x - 1)^p$.
]
#theorem("Fermat's little theorem")[
    $forall a in FF_p, a^p = a$.
]

== Polynomials over fields

#definition[
    *Degree* of $f(x) = a_0 + a_1 x + dots.h.c + a_n x^n$, $a_n != 0$, is $deg(f(x)) = n$.
    - Degree of zero polynomial is $deg(0) = -oo$.
    - $deg(f(x)g(x)) = deg(f(x)) + deg(g(x))$.
    - $deg(f(x) + g(x)) <= max{deg(f(x)), deg(g(x))}$ with equality if $deg(f(x)) != deg(g(x))$.
]
- Only invertible elements in $K[x]$ are non-zero constants $f(x) = a_0 != 0$.
- Similarities between $ZZ$ and $K[x]$ for field $K$:
    - $K[x]$ is integral domain.
    - There is a division algorithm for $K[x]$: for $f(x), g(x) in K[x]$, $exists! q(x), r(x) in K[x]$ with $deg(r(x)) < deg(g(x))$ such that $ f(x) = q(x) g(x) + r(x) $
    - Every $f(x), g(x) in K[x]$ have greatest common divisor $gcd(f(x), g(x))$ unique up to multiplication by non-zero constants. By Euclidean algorithm for polynomials, $ exists a(x), b(x) in K[x]: a(x) f(x) + b(x) g(x) = gcd(f(x), g(x)) $
    - Can construct field from $K[x]$: *field of fractions* of $K[x]$ is $ K(x) := "Frac"(K[x]) = {f(x) / g(x): f(x), g(x) in K[x], g(x) != 0} $ where $f_1 (x) \/ g_1 (x) = f_2 (x) \/ g_2 (x) <==> f_1 (x) g_2 (x) = f_2 (x) g_1 (x)$. (We can construct the field of fractions for any integral domain).
    - $K[x]$ is PID and so UFD.
#definition[
    For field $K$, $f(x) in K[x]$ *irreducible in $K[x]$* (or $f(x)$ is *irreducible over $K$*) if
    - $deg(f(x)) >= 1$ and
    - $f(x) = g(x) h(x) ==> g(x) "or" h(x) "is constant"$
]

== Tests for irreducibility

#proposition[
    If $f(x)$ has linear factor in $K[x]$, it has root in $K[x]$.
]
#proposition("Rational root test")[
    If $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$ has rational root $b/c in QQ$ with $gcd(b, c) = 1$ then $b | a_0$ and $c | a_n$. *Note*: this can't be used to show $f$ is irreducible for $deg(f(x)) >= 4$.
]
#theorem("Gauss's lemma")[
    Let $f(x) in ZZ[x]$, $f(x) = g(x) h(x)$, $g(x), h(x) in QQ[x]$. Then $exists r in QQ: r g(x), r^(-1) h(x) in ZZ[x]$. i.e. if $f(x)$ can be factored in $QQ[x]$ it can be factored in $ZZ[x]$.
]
#example[
    Let $f(x) = x^4 - 3x^3 + 1 in QQ[x]$. Using the rational root test, $f(plus.minus 1) != 0$ so no linear factors in $QQ[x]$. Checking quadratic factors, let $ f(x) = (a x^2 + b x + c)(r x^2 + s x + t), quad a, b, c, r, s, t in ZZ "by Gauss's lemma" $ So $1 = a r => a = r = plus.minus 1$. $1 = c t => c = t = plus.minus 1$. $-3 = b + s$ and $0 = c(b + s)$: contradiction. So $f(x)$ irreducible in $QQ[x]$.
]
#example[
    Let $f(x) = x^4 - 3x^2 + 1 in QQ[x]$. The rational root test shows there are no linear factors. Checking quadratic factors, let $ f(x) = (a x^2 + b x + c)(r x^2 + s x + t), quad a, b, c, r, s, t in ZZ "by Gauss's lemma" $ As before, $a = r = plus.minus 1$, $c = t = plus.minus 1$. $0 = b + s => b = -s$, $-3 = a t + b s + c r = -b^2 plus.minus 2$. $b = 1$ works. So $f(x) = (x^2 - x - 1)(x^2 + x - 1)$.
]
#proposition[
    Let $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$. If exists prime $p divides.not a_n$ such that $overline(f)(x)$ is irreducible in $FF_p [x]$, then $f(x)$ irreducible in $QQ[x]$.
]
#example[
    Let $f(x) = 8x^3 + 14x - 9$. Reducing $mod 7$, $overline(f)(x) = x^3 - 2 in FF_7 [x]$. No roots exist for this, so $f(x)$ irreducible in $QQ[x]$. For some polynomials, no $p$ is suitable, e.g. $f(x) = x^4 + 1$.
]
- Gauss's lemma works with any UFD $R$ instead of $ZZ$ and field of fractions $"Frac"(R)$ instead of $QQ$: e.g. let $F$ field, $R = F[t]$, $K = F(t)$, then $f(x) in R[x]$ irreducible in $K[x]$ if $f(x)$ is irreducible in $R[x]$.
#proposition("Eisenstein's criterion")[
    Let $f(x) = a_0 + dots.h.c + a_n x^n in ZZ[x]$, prime $p in ZZ$ such that $p | a_0, ..., p | a_(n - 1)$, $p divides.not a_n$, $p^2 divides.not a_0$. Then $f(x)$ irreducible in $QQ[x]$.
]
#example[
    Let $f(x) = x^3 - 3x + 1$. Consider $f(x - 1) = x^3 - 3x^2 + 3$. Then by Eisenstein's criterion with $p = 3$, $f(x - 1)$ irreducible in $QQ[x]$ so $f(x)$ is as well, since factoring $f(x - 1)$ is equivalent to factoring $f(x)$.
]
#example[
    *$p$-th cyclotomic polynomial* is $ f(x) = (x^p - 1)/(x - 1) = 1 + dots.h.c + x^(p - 1) $ Now $ f(x + 1) = ((1 + x)^p - 1)/(1 + x - 1) = x^(p - 1) + p x^(p - 2) + dots.h.c + binom(p, p - 2) x + p $ so can apply Eisenstein with $p = p$.
]
#proposition("Generalised Eisenstein's criterion")[
    Let $R$ be integral domain, $K = "Frac"(R)$, $ f(x) = a_0 + dots.h.c + a_n x^n in R[x] $ If there is irreducible $p in R$ with $ p | a_0, ..., p | a_(n - 1), p divides.not a_n, p^2 divides.not a_0 $ then $f(x)$ is irreducible in $K[x]$.
]

= Field extensions

== Definitions and examples

#definition[
    *Field extension* $L \/ K$ is field $L$ containing subfield $K$. Can specify homomorphism $iota: K -> L$ (which is injective).
]
#example[
    - $CC \/ RR$, $CC \/ QQ$, $RR \/ QQ$.
    - $L = QQ\(sqrt(2)\) = \{a + b sqrt(2): a, b in QQ\}$ is field extension of $QQ$. $QQ(theta)$ is field extension of $QQ$ where $theta$ is root of $f(x) in QQ[x]$.
    - $L = QQ\(root(3, 2)\) = \{a + b root(3, 2) + c root(3, 4): a, b, c in QQ\}$ is smallest subfield of $RR$ containing $QQ$ and $root(3, 2)$.
    - $K(t)$ is field extension of $K$.
]
#definition[
    Let $L \/ K$ field extension, $S subset.eq L$. Then *$K$ with $S$ adjoined*, $K(S)$, is minimal subfield of $L$ containing $K$ and $S$. If $|S| = 1$, $L \/ K$ is a *simple extension*.
]
#example[
    $QQ\(sqrt(2), sqrt(7)\) = \{a + b sqrt(2) + c sqrt(7) + d sqrt(14): a, b, c, d, in QQ\}$ is $QQ$ with $S = \{sqrt(2), sqrt(7)\}$.
]
#example[
    $RR \/ QQ$ is not simple extension.
]
#definition[
    *Tower* is chain of field extensions, e.g. $K subset M subset L$.
]

== Algebraic elements and minimal polynomials

#definition[
    Let $L \/ K$ field extension, $theta in L$. Then $theta$ is *algebraic over $K$* if $ exists 0 != f(x) in K[x]: f(theta) = 0 $ Otherwise, $theta$ is *transcendental over $K$*.
]
#example[
    For $n >= 1$, $theta = e^(2pi i\/n)$ is algebraic over $QQ$ (root of $x^n - 1$).
]
#example[
    $t in K(t)$ is transcendental over $K$.
]
#lemma[
    The algebraic elements in $K(t)\/K$ are precisely $K$.
]
#lemma[
    Let $L\/K$ field extension, $theta in L$. Define $I_K (theta) := {f(x) in K[x]: f(theta) = 0}$. Then $I_K (theta)$ is ideal in $K[x]$ and
    - If $theta$ transcendental over $K$, $I_K (theta) = {0}$
    - If $theta$ algebraic over $K$, then exists unique monic irreducible polynomial $m(x) in K[x]$ such that $I_K (theta) = angle.l m(x) angle.r$.
]
#definition[
    For $theta in L$ algebraic over $K$, *minimal polynomial of $theta$ over $K$* is the unique monic polynomial $m(x) in K[x]$ such that $I_K (theta) = angle.l m(x) angle.r$. The *degree* of $theta$ over $K$ is $deg(m(x))$.
]
#remark[
    If $f(x) in K[x]$ irreducible over $K$, monic and $f(theta) = 0$ then $f(x) = m(x)$.
]
#example[
    - Any $theta in K$ has minimal polynomial $x - theta$ over $K$.
    - $i in CC$ has minimal polynomial $x^2 + 1$ over $RR$.
    - $sqrt(2)$ has minimal polynomial $x^2 - 2$ over $QQ$. $root(3, 2)$ has minimal polynomial $x^3 - 2$ over $QQ$.
]

== Constructing field extensions

#lemma[
    Let $K$ field, $f(x) in K[x]$ non-zero. Then $ f(x) "irreducible over" K <==> K[x] \/ angle.l f(x) angle.r "is a field" $
]
#definition[
    Let $L_1 \/ K$, $L_2 \/ K$ field extensions, $phi: L_1 -> L_2$ field homomorphism. $phi$ is *$K$-homomorphism* if $forall a in K, phi(a) = a$ ($phi$ fixes elements of $K$).
    - If $phi$ is isomorphism then it is *$K$-isomorphism*.
    - If $L_1 = L_2$ and $phi$ is bijective then $phi$ is *$K$-automorphism*.
]
#theorem[
    Let $m(x) in K[x]$ irreducible, monic, $K_m := K[x] \/ ideal(m(x))$. Then
    - $K_m \/ K$ is field extension.
    - Let $theta = pi(x)$ where $pi: K[x] -> K_m$ is canonical projection, then $theta$ has minimal polynomial $m(x)$ and $K_m tilde.equiv K(theta)$.
]
#proposition("Universal property of simple extension")[
    Let $L\/K$ field extension, $tau in L$ with $m(tau) = 0$ and $K_L (tau)$ be minimal subfield of $L$ containing $K$ and $tau$. Then exists unique $K$-isomorphism $phi: K_m -> K_L (tau)$ such that $phi(theta) = tau$.
]
#example[
    - Complex conjugation $CC -> CC$ is $RR$-automorphism.
    - Let $K$ field, $char(K) != 2$, $sqrt(2) in.not K$, so $x^2 - 2$ is minimal polynomial of $sqrt(2)$ over $K$, then $K\(sqrt(2)\) tilde.equiv K[x] \/ ideal(x^2 - 2)$ is field extension of $K$ and $a + b sqrt(2) |-> a - b sqrt(2)$ is $K$-automorphism.
]
#proposition[
    Let $theta$ transcendental over $K$, then exists unique $K$-isomorphism $phi: K(t) -> K(theta)$ such that $phi(t) = theta$: $ phi(f(t)/g(t)) = phi(f(theta)/g(theta)) $
]

== Explicit examples of simple extensions

#example[
    - Let $r in K^times$ non-square in $K$, $char(K) != 2$, then $x^2 - r$ irreducible in $K[x]$. E.g. for $K = QQ(t)$, $x^2 - t in K[x]$ is irreducible. Then $K\(sqrt(t)\) = QQ\(sqrt(t)\) tilde.equiv K[x] \/ ideal(x^2 - t)$.
    - Define $FF_9 = FF_3 [x] \/ ideal(x^2 - 2) tilde.equiv FF_3 (theta) = {a + b theta: a, b in FF_3}$ for $theta$ a root of $x^2 - 2$.
]
#proposition[
    Let $K(theta)\/K$ where $theta$ has minimal polynomial $m(x) in K[x]$ of degree $n$. Then $ K[x] \/ ideal(m(x)) tilde.equiv K(theta) = {c_0 + c_1 theta + dots.h.c + c_(n - 1) theta^(n - 1): c_i in K} $ and its elements are written uniquely: $K(theta)$ is vector space over $K$ of dimension $n$ with basis ${1, theta, ..., theta^(n - 1)}$.
]
#example[
    $QQ\(cbrt(2)\) = \{a + b cbrt(2) + c cbrt(4): a, b, c in QQ\} tilde.equiv QQ[x] \/ ideal(x^3 - 2)$. $QQ\(omega cbrt(2)\)$ and $QQ\(w^2 cbrt(2)\)$ where $omega = e^(2pi i \/ 3)$ are isomorphic to $QQ\(cbrt(2)\)$ as $omega cbrt(2)$, $omega cbrt(4)$ have same minimal polynomial.
]

== Degrees of field extensions

#definition[
    *Degree* of field extension $L\/K$ is $ [L: K] := dim_K (L) $
]
#example[
  - When $theta$ algebraic over $K$ of degree $n$, $[K(theta): K] = n$.
  - Let $theta$ transcendental over $K$, then $[K(theta): K] = oo$, so $[K(t): K] = oo$, $[QQ(pi): QQ]$, $[RR: QQ] = oo$.
]
#definition[
    $L\/K$ is *algebraic extension* if every element in $L$ is algebraic over $K$.
]
#proposition[
    Let $[L: K] < oo$, then $L\/K$ is algebraic extension and $L = K(alpha_1, ..., alpha_n)$ for some $alpha_1, ..., alpha_n in L$. The converse also holds.
]
#theorem("Tower law")[
    Let $K subset.eq M subset.eq L$ tower of field extensions. Then
  - $[L: K] < oo <==> [L: M] < oo and [M: K] < oo$.
  - $[L: K] = [L: M] [M: K]$.
]
#example[
    - $K = QQ subset M = QQ\(sqrt(2)\) subset L = QQ\(sqrt(2), sqrt(7)\)$. $M\/K$ has basis $\{1, sqrt(2)\}$ so $[M: K] = 2$. Let $sqrt(7) in QQ\(sqrt(2)\)$, then $sqrt(7) = c + d sqrt(2)$, $c, d in QQ$ so $7 = (c^2 + 2d^2) + 2c d sqrt(2)$ so $7 = c^2 + 2d^2$, $0 = 2c d$ so $d^2 = 7/2$ or $c^2 = 7$, which are both contradictions. So $[L: K] = 4$ with basis $\{1, sqrt(2), sqrt(7), sqrt(14)\}$.
    - Let $K = QQ subset M = QQ(i) subset QQ\(i, sqrt(2)\)$. We know $[QQ(i): QQ] = 2$, and $\[QQ\(sqrt(2)\): QQ\] = 2$, $\[QQ\(i, sqrt(2)\): QQ\] = 4$ (since $i in.not RR$) so $\[QQ\(i, sqrt(2)\): QQ\(sqrt(2)\)\] = 2$.
    - Let $K = QQ subset M = QQ\(sqrt(2)\) subset L = QQ\(sqrt(2), cbrt(3)\)$. Then $\[QQ\(sqrt(2)\): QQ\] = 2$, $\[QQ\(cbrt(3)\): QQ\] = 3$ so $2 | [L: K]$ and $3 | [L: K]$ so $6 | [L: K]$ so $[L: K] >= 6$. But $[L: M] <= 3$ and $[M: K] <= 2$ so $[L: K] <= 6$ hence $[L: K] = 6$.
]
- More generally, we have $[K(alpha, beta): K] <= [K(alpha): K] [K(beta): K]$.
#example[
    - Let $theta = cbrt(4) + 1$. $QQ(theta) = QQ\(cbrt(4)\)$ so minimal polynomial over $QQ$, $m$, has $deg(m) = 3$. $(theta - 1)^3 = 4$ so minimal polynomial is $x^3 - 3x^2 + 3x - 5$.
    - Let $theta = sqrt(2) + sqrt(3)$. $QQ\(sqrt(2), theta\) = QQ\(sqrt(2), sqrt(3)\)$ which has degree $2$ over $QQ\(sqrt(2)\)$ so minimal polynomial of $theta$ over $QQ\(sqrt(2)\)$ has degree $2$, $theta - sqrt(2) = sqrt(3)$ so minimal polynomial is $x^2 - 2 sqrt(2) x - 1$.
    - Let $theta = sqrt(2) + sqrt(3)$. $QQ subset QQ(theta) subset QQ\(sqrt(2), sqrt(3)\)$ so $[QQ(theta): QQ] | \[QQ\(sqrt(2), sqrt(3)\): QQ\] = 4$ so $[QQ(theta): QQ] in {1, 2, 4}$. Can't be $1$ as $theta in.not QQ$. If it was $2$ then $1, theta, theta^2$ are linearly dependent over $QQ$ which leads to a contradiction. So degree of minimal polynomial of $theta$ over $QQ$ is $4$. $theta^2 = 5 + 2 sqrt(6) => (theta^2 - 5)^2 = 24$ so minimal polynomial is $x^4 - 10x^2 + 1$.
]

= Galois extensions

== Splitting fields

#definition[
    For field $K$, $0 != f(x) in K[x]$, $L\/K$ is *splitting field* of $f(x)$ over $K$ if
    - $exists c in K^times, theta_1, ..., theta_n in L: f(x) = c (x - theta_1) thin dots.h.c thin (x - theta_n)$ ($f(x)$ *splits over $L$*).
    - $L = K(theta_1, ..., theta_n)$.
]
#example[
    - $CC$ is splitting field of $x^2 + 1$ over $RR$, since $x^2 + 1 = (x + i)(x - i)$ and $CC = RR(i, -i) = RR(i)$.
    - $CC$ is not splitting field of $x^2 + 1$ over $QQ$ as $CC != QQ(i, -i)$.
    - $QQ$ is splitting field of $x^2 - 36$ over $QQ$.
    - $CC$ is splitting of $x^4 + 1$ over $RR$.
    - $QQ\(i, sqrt(2)\)$ is splitting field of $x^4 - x^2 - 2 = (x^2 + 1)(x^2 - 2) = (x + i)(x - i)\(x + sqrt(2)\)\(x - sqrt(2)\)$ over $QQ$.
    - $FF_2 (theta)$ where $theta^3 + theta + 1 = 0$ is splitting field of $x^3 + x + 1$ over $FF_2$.
    - Consider splitting field of $x^3 - 2$ over $QQ$. Let $omega = e^(2pi i\/3) = \(-1 + sqrt(-3)\)\/2$ then $QQ\(cbrt(2), omega\)$ is splitting field since it must contain $cbrt(2)$, $omega cbrt(2)$, $omega^2 cbrt(2)$.
]
#theorem[
    Let $0 != f(x) in K[x]$, $deg(f) = n$. Then there exists a splitting field $L$ of $f(x)$ over $K$ with $ [L: K] <= n! $
]
#notation[
    For field homomorphism $phi: K -> K'$ and $f(x) = a_0 + dots.h.c + a_n x^n in K[x]$, write $ phi_* (f(x)) := phi(a_0) + dots.h.c + phi(a_n) x^n in K'[x] $
]
#lemma[
    Let $sigma: K -> K'$ isomorphism and $K(theta)\/K$, $theta$ has minimal polynomial $m(x) in K[x]$, $theta'$ be root of $sigma_* (m(x))$. Then there exists unique $K$-isomorphism $tau: K(theta) -> K'(theta')$ such that $tau(theta) = theta'$.
]
#theorem[
    For field isomorphism $sigma: K -> K'$ and $0 != f(x) in K[x]$, let $L$ be splitting field of $f(x)$ over $K$, $L'$ be splitting field of $sigma_* (f(x))$ over $K'$. Then there exists a field isomorphism $tau: L -> L'$ such that $forall a in K, tau(a) = sigma(a)$.
]
#corollary[
    Setting $K = K'$ and $sigma = id$ implies that splitting fields are unique.
]

== Normal extensions

#definition[
    $L\/K$ is *normal* if: for all $f(x) in K[x]$, if $f$ is irreducible and has a root in $L$ then all its roots are in $L$. In particular, $f(x)$ splits completely as product of linear factors in $L[x]$. So the minimal polynomial of $theta in L$ over $K$ has all its roots in $L$ and can be written as product of linear factors in $L[x]$.
]
#example[
    - If $[L: K] = 1$ then $L\/K$ is normal.
    - If $[L: K] = 2$ then $L\/K$ is normal: let $theta in L$ have minimal polynomial $m(x) in K[x]$, then $K subset.eq K(theta) subset.eq L$ so $deg(m(x)) = [K(theta): K] in {1, 2}$:
        - If $deg(m(x)) = 1$ then $m(x)$ is already linear.
        - If $deg(m(x)) = 2$ then $m(x) = (x - theta) m_1 (x)$, $m_1 (x) in L[x]$ is linear so $m(x)$ splits completely in $L[x]$.
    - If $[L: K] = 3$ then $L\/K$ is not necessarily normal. Let $theta$ be root of $x^3 - 2 in QQ[x]$. Other two roots are $omega theta$, $omega^2 theta$ where $omega = e^(2pi i\/3)$. If $omega theta in QQ(theta)$ then $omega = (omega theta)/theta in L$ so $QQ subset QQ(omega) subset QQ(theta)$ but $[QQ(omega): QQ] = 2$ which doesn't divide $[QQ(theta): QQ] = 3$.
    - Let $theta in CC$ be root of irreducible $f(x) = x^3 - 3x - 1 in QQ[x]$. Let $theta = u + v$, then $(u + v)^3 - 3 u v(u + v) - (u^3 + v^3) equiv 0$ implies $u v = 1 = u^3 v^3$, $u^3 + v^3 = 1$. So $(y - u^3)(y - v^3) = y^2 - y + 1$ has roots $u^3$ and $v^3$. So the three roots of $f$ are $ theta_1 = u + v = e^(pi i\/9) + e^(-pi i\/9) & = 2 cos(pi\/9) \ theta_2 = omega u + omega^2 v = e^(7pi i\/9) + e^(-7 pi i\/9) & = 2 cos(7 pi \/ 9) \ theta_3 = omega^2 u + omega v = e^(13 pi i\/9) + e^(-13pi i\/9) & = 2 cos(13pi\/9) $ Furthermore, for each $i, j$, $theta_i in QQ(theta_j)$, e.g. $ theta_2 = 2 cos(pi - (2pi)/9) = -2cos((2pi)/9) = -2(2cos(pi/9)^2 - 1) = 2 - theta_1^2 $ Also $theta_1 + theta_2 + theta_3 = 0$ so $theta_3 in QQ(theta_1)$. So $QQ(theta_1)$ contains all roots of $f(x)$.
]
#theorem("normality criterion")[
    $L\/K$ is finite and normal iff $L$ is splitting field for some $0 != f(x) in K[x]$ over $K$.
]
#example[
    - $QQ\(sqrt(2), sqrt(3), sqrt(5), sqrt(7)\)\/QQ$ is normal as it is the splitting field of $f(x) = (x^2 - 2)(x^2 - 3)(x^2 - 5)(x^2 - 7) in QQ[x]$.
    - $QQ\(cbrt(2)\)\/QQ$ is not normal but $QQ\(cbrt(2), omega\)\/QQ$ is normal as it is the splitting field of $x^3 - 2 in QQ$.
    - $QQ\(root(4, 2)\)\/QQ$ is not normal but $QQ\(root(4, 2), i\)\/QQ$ is normal.
    - Let $theta$ root of $f(x) = x^3 - 3x - 1 in QQ[x]$. Then $QQ(theta)\/QQ$ is normal as is splitting field of $f(x)$ over $QQ$.
    - $FF_2 (theta)\/FF_2$ where $theta^3 + theta^2 + 1 = 0$ is normal, as $FF_2 (theta)$ contains all roots of $x^3 + x^2 + 1$.
    - $FF_p (theta)\/FF_p (t)$ where $theta^p = t$ is normal as it is the splitting field of $x^p - t = x^p - theta^p = (x - theta)^p$ so $f(x)$ splits into linear factors in $L[x]$.
]
#definition[
    Field $N$ is *normal closure* of $L\/K$ if $K subset.eq L subset.eq N$, $N\/K$ is normal, and if $K subset.eq L subset.eq N' subset.eq N$ with $N'\/K$ normal then $N = N'$.
]
#theorem[
    Every finite extension $L\/K$ has normal closure, unique up to a $K$-isomorphism.
]
#definition[
    $Aut(L\/K)$ is group of $K$-automorphisms of $L\/K$ with composition as the group operation.
]
#example[
    - $Aut(CC\/RR)$ contains at least two elements: complex conjugation: $sigma(a + b i) = a - b i$ and the identity map $id = sigma^2$. If $tau in Aut(CC\/RR)$ then $tau(a + b i) = a + b tau(i)$. But $tau(i)^2 = tau(i^2) = tau(-1) = -1$ hence $tau(i) = plus.minus i$. So there are only two choices for $tau$. So $Aut(CC\/RR) = {id, sigma}$.
    - Let $f(x) = x^2 + p x + q in QQ[x]$ irreducible with distinct roots $theta, theta'$. Then $Aut(QQ(theta)\/QQ) = {id, sigma} tilde.equiv ZZ\/2$ where $sigma(a + b theta) = a + b theta'$.
    - Let $theta$ root of $x^3 - 2$, let $sigma in Aut(QQ(theta)\/QQ)$. Now $sigma(theta)^3 = sigma(theta^3) = sigma(2) = 2$ so $sigma(theta) in {theta, omega theta, omega^2 theta}$ but $omega theta, omega^2 theta in.not QQ(theta)$ so $sigma(theta) = theta ==> sigma = id$.
    - Let $theta^p = t$, $sigma in Aut(FF_p (theta)\/ FF_p (t))$. Then $ sigma(theta)^p = sigma(theta^p) = sigma(t) = t = theta^p $ so $(sigma(theta) - theta))^p = sigma(theta)^p - theta^p = 0 ==> sigma(theta) = theta ==> sigma = id$.
    - Let $sigma in Aut(RR\/QQ)$. Then $alpha <= beta in RR ==> beta - alpha = gamma^2$, $gamma in RR$, so $sigma(beta) - sigma(a) = sigma(gamma)^2 >= 0$ so $sigma(alpha) <= sigma(beta)$. Given $alpha in RR$, there exist sequences $(r_n), (s_n) subset QQ$ with $r_n <= alpha <= s_n$ and $r_n -> alpha$, $s_n -> alpha$ as $n -> oo$. Hence $r_n = sigma(r_n) <= sigma(alpha) <= sigma(s_n) = s_n$ so $sigma(alpha) = alpha$ by squeezing. Hence $Aut(RR\/QQ) = {id}$.
]
#theorem[
    Let $L = K(theta)$, $theta$ root of irreducible $f(x) in K[x]$, $deg(f) = n$. Then $|Aut(L\/K)| <= n$, with equality iff $f(x)$ has $n$ distinct roots in $L$.
]
#theorem[
    Let $L\/K$ be finite extension. Then $|Aut(L\/K)| <= [L: K]$, with equality iff $L\/K$ is normal and minimal polynomial of every $theta in L$ over $K$ has no repeated roots (in a splitting field).
]

== Separable extensions

#definition[
    Let $L\/K$ finite extension.
    - $theta in L$ is *separable over $K$* if its minimal polynomial over $K$ has no repeated roots (in its splitting field).
    - $L\/K$ is *separable* if every $theta in L$ is separable over $K$.
]
#example[
    Let $K = FF_p (t)$, then $f(x) = x^p - t in K[x]$ is irreducible by Eisenstein's criterion with $p = t$, and $f(x) = x^p - theta^p = (x - theta)^p$ so $theta$ is root of multiplicity $p >= 2$. So $FF_p (theta)\/FF_p (t)$ is normal but not separable.
]
#definition[
    Let $f(x) = sum_(i = 0)^n a_i x^i in K[x]$. *Formal derivative* of $f(x)$ is $ D f(x) = D(f) := sum_(i = 1)^n i a_i x^(i - 1) in K[x] $
]
#note[
    Formal derivative satisfies: $ D(f + g) = D(f) + D(g), quad D(f g) = f dot.op D(g) + D(f) dot.op g, quad forall a in K, D(a) = 0 $ Also $deg(D(f)) < deg(f)$. But if $char(K) = p$, then $D(x^p) = p x^(p - 1) = 0$ so it is not always true that $deg(D(f)) = deg(f) - 1$.
]
#note[
    If $f(x)$ has a repeated root $alpha$, then $D f(alpha) = 0$.
]
#theorem("sufficient conditions for separability")[
    Finite extension $L\/K$ is separable if any of the following hold:
    - $char(K) = 0$,
    - $char(K) = p$ and $K = {b^p: b in K} = K^p$ for prime $p$,
    - $char(K) = p$ and $p divides.not [L: K]$
]
#definition[
    $K$ is *perfect field* if either of first two of above properties hold.
]
#remark[
    All finite extensions of any perfect extension (e.g. $QQ, FF_p$) are separable (recall Fermat's little theorem: $forall a in FF_p, a = a^p$). So to find a non-separable extension $L\/K$, we need $char(K) = p > 0$, $K$ infinite and $p | [L: K]$. For example, $L = FF_p (theta)$, $K = FF_p (t)$ where $theta^p = t$.
]
#theorem[
    Let $alpha_1, ..., alpha_n$ algebraic over $K$, then $K(alpha_1, ..., alpha_n)\/K$ is separable iff every $alpha_i$ is separable over $K$.
]
#remark[
    For tower $K subset.eq M subset.eq L$, $L\/K$ is separable iff $L\/M$ and $M\/K$ are separable. However, the same statement for normality does not hold.
]
#theorem("Theorem of the Primitive Element")[
    Let $L\/K$ finite and separable. Then $L\/K$ is simple, i.e. $exists alpha in L: L = K(alpha)$.
]

== The fundamental theorem of Galois theory

#definition[
    Finite extension $L\/K$ is *Galois extension* if it is normal and separable. Equivalently, $|Aut(L\/K)| = [L: K]$. When $L\/K$ is Galois, the *Galois group* is $Gal(L\/K) := Aut(L\/K)$.
]
#definition[
    Let $cal(F) := {"intermediate fields of" L\/K}$ and $cal(G) := {"subgroups of" Gal(L\/K)}$. Define the map $Gamma: cal(F) -> cal(G)$, $Gamma(M) = Gal(L\/M)$.
]
#definition[
    Let $L$ field, $G$ a group of automorphisms of $L$. *Fixed field* $L^G$ of $G$ is set of elements in $L$ which are invariant under all automorphisms in $G$: $ L^G := {alpha in L: forall alpha in G, thick sigma(alpha) = alpha} $
]
#theorem[
    If $G$ is finite group of automorphisms of $L$ then $L^G$ is subfield of $L$ and $[L: L^G] = |G|$.
]
#corollary[
    If $L\/K$ is Galois then
    - $L^(Gal(L\/K)) = K$.
    - If $L^G = K$ for some group $G$ of $K$-automorphisms of $L$, then $G = Gal(L\/K)$.
]
#note[
    Let $sigma in Gal(L\/K)$. If $alpha in L$ has minimal polynomial $f(x) in K[x]$ over $K$, then $f(alpha) = 0$, and $ f(sigma(alpha)) = sigma(f(alpha)) $ by properties of field homomorphisms. Hence $sigma(alpha)$ is also a root of $f(x)$ for any $sigma in Gal(L\/K)$, i.e. $sigma$ permutes the roots of $f(x)$.
]
#remark[
    If $L\/K$ is Galois and $alpha in L$ but $alpha in.not K$, then there exists an automorphism $sigma in Gal(L\/K)$ such that $sigma(alpha) != alpha$.
]
#definition[
    For $H$ subgroup of $Gal(L\/K)$, set $L^H := {alpha in L: forall sigma in H, thick sigma(alpha) = alpha}$, then $K subset.eq L^H subset.eq L$. Define $Phi: cal(G) -> cal(F)$, $Phi(H) = L^H$.
]
- $Gamma$ and $Phi$ are inclusion-reversing: $M_1 subset.eq M_2 ==> Gamma(M_2) subset.eq Gamma(M_1)$, and $H_1 subset.eq H_2 ==> Phi(H_2) subset.eq Phi(H_1)$.
#theorem("Fundamental theorem of Galois theory - Theorem A")[
    For finite Galois extension $L\/K$,
    - $Gamma: cal(F) -> cal(G)$ and $Phi: cal(G) -> cal(F)$ are mutually inverse bijections (the *Galois correspondence*).
    - For $M in cal(F)$, $L\/M$ is Galois and $|Gal(L\/M)| = [L: M]$.
    - For $H in cal(G)$, $L\/L^H$ is Galois and $Gal(L\/L^H) = H$.
]
#remark[
    $Gal(L\/K)$ acts on $cal(F)$: given $sigma in Gal(L\/K)$ and $K subset.eq M subset.eq L$, consider $sigma(M) = {sigma(alpha): alpha in M}$ which is a subfield of $L$ and contains $K$, since $sigma$ fixes elements of $K$. Given another automorphism $tau: L -> L$, $ tau in Gal(L\/sigma(M)) & <==> forall alpha in M, tau(sigma(alpha)) = sigma(alpha) \ & <==> forall alpha in M, sigma^(-1) (tau (sigma(alpha))) = alpha \ & <==> sigma^(-1) tau sigma in Gal(L\/M) \ & <==> tau in sigma Gal(L\/M) sigma^(-1) $ Hence $sigma Gal(L\/M) sigma^(-1)$ and $Gal(L\/M)$ are conjugate subgroups of $Gal(L\/K)$. Now $ [M: K] = ([L: K]) / ([L: M]) = abs(Gal(L\/K)) / abs(Gal(L\/M)) $
]
#theorem("Fundamental theorem of Galois theory - Theorem B")[
    Let $L\/K$ be finite Galois extension, $G = Gal(L\/K)$ and $K subset.eq M subset.eq L$. Then the following are equivalent:
    - $M\/K$ is Galois.
    - $forall sigma in G, quad sigma(M) = M$.
    - $H = Gal(L\/M)$ is normal subgroup of $G = Gal(L\/K)$.
    When these conditions hold, we have $Gal(M\/K) tilde.equiv G\/H$.
]
#example[
    Let $L\/K$ be Galois, $[L: K] = p$ prime.
    - By the tower law, any $K subset.eq M subset.eq L$ has $[L: M] in {1, p}$, $[M: K] in {p, 1}$, so $M = L$ or $K$. In both cases, $M\/K$ is normal.
    - $|Gal(L\/K)| = [L: K] = p$ so $Gal(L\/M) tilde.equiv ZZ\/p$, so the only subgroups are $Gal(L\/K)$ and ${id}$. In both cases, $H$ is normal subgroup of $Gal(L\/K)$.
]

== Computations with Galois groups

#example("quadratic extension")[
    $QQ\(sqrt(2)\)\/QQ$ is normal (since degree is $2$) and separable (since characteristic is zero). Any element of $phi in G = Gal\(QQ\(sqrt(2)\)\/QQ\)$ is determined by the image of $sqrt(2)$. But $phi\(sqrt(2)\)^2 = phi(2) = 2$ so $phi\(sqrt(2)\) = plus.minus sqrt(2)$. This gives two automorphisms $id\(sqrt(2)\) = sqrt(2)$ and $sigma\(sqrt(2)\) = -sqrt(2)$. So $G = {id, sigma} = ideal(sigma) tilde.equiv ZZ\/2$. Subgroup ${id}$ corresponds to $QQ\(sqrt(2)\)$, $G$ corresponds to $QQ$.
]
#example("biquadratic extension")[
    $L = QQ\(sqrt(2), sqrt(3)\)$ over $QQ$ is normal (as splitting field of $(x^2 - 2)(x^2 - 3)$ over $QQ$) and separable (as $char(QQ) = 0$), so is Galois extension. Let $sigma$ be given as before.
    - Suppose $sqrt(3) in QQ\(sqrt(2)\)$, then $sigma\(sqrt(3)\)^2 = sigma(3) = 3$, so $sigma\(sqrt(3)\) = plus.minus sqrt(3)$.
    - If $sigma\(sqrt(3)\) = sqrt(3)$, then $sqrt(3) in QQ\(sqrt(2)\)^({id, sigma}) = QQ$: contradiction.
    - If $sigma\(sqrt(3)\) = -sqrt(3)$, then $sigma\(sqrt(2)\) sigma\(sqrt(3)\) = sigma\(sqrt(6)\) = \(-sqrt(2)\)\(-sqrt(3)\) = sqrt(6)$, so $sqrt(6) in QQ\(sqrt(2)\)^({id, sigma}) = QQ$: contradiction.
    - So $sqrt(3) in.not QQ\(sqrt(2)\)$, hence $[L: QQ] = \[L: QQ\(sqrt(2)\)\] \[QQ\(sqrt(2)): QQ\] = 4$.
    - Now $G = Gal(L\/QQ)$ has order $[L: QQ] = 4$, so $G tilde.equiv ZZ\/4$ or $ZZ\/2 times ZZ\/2$.
    - For $phi in G$, $phi\(sqrt(2)\)^2 = 2 ==> phi\(sqrt(2)\) = plus.minus sqrt(2)$, $phi\(sqrt(3)\)^2 = 3 ==> phi\(sqrt(3)\) = plus.minus sqrt(3)$. So there are four choices, corresponding to choices of $plus.minus$ signs.
    - Define $sigma, tau$ by $sigma\(sqrt(2)\) = -sqrt(2)$, $sigma\(sqrt(3)\) = sqrt(3)$, $tau\(sqrt(2)\) = sqrt(2)$, $tau\(sqrt(3)\) = -sqrt(3)$. Now $sigma^2 = tau^2 = id$, $sigma tau \(sqrt(2)\) = - sqrt(2)$, $sigma tau \(sqrt(3)\) = -sqrt(3)$ and $sigma tau = tau sigma$.
    - So $G = angle.l sigma, tau: sigma^2 = tau^2 = id, sigma tau = tau sigma angle.r = ideal(sigma) times ideal(tau) tilde.equiv ZZ\/2 times ZZ\/2$.
    - $G$ has proper subgroups $H_1 = ideal(sigma)$, $H_2 = ideal(tau)$, $H_3 = ideal(sigma tau)$.
    - So the intermediate fields are $L^(H_1), L^(H_2), L^(H_3)$.
    - $sigma\(sqrt(3)\) = sqrt(3) ==> sqrt(3) in L^(H_1)$ so $QQ\(sqrt(3)\) subset.eq L^(H_1)$, but $\[L: QQ\(sqrt(3)\)\] = 2 = |H_1| = [L: L^(H_1)]$. Hence $L^(H_1) = QQ\(sqrt(3)\)$. Similarly $L^(H_2) = QQ\(sqrt(2)\)$.
    - $sigma tau \(sqrt(6)\) = sqrt(6) ==> sqrt(6) in L^(H_3)$, so $L^(H_3) = QQ\(sqrt(6)\)$.
]
#remark[
    It is not generally true that $\[K\(sqrt(a), sqrt(b)\): K\] = 4$, e.g. $QQ\(sqrt(2), sqrt(8)\) = QQ\(sqrt(2)\)$.
]
#remark[
    Can generalise above example to arbitrary $K\(sqrt(a), sqrt(b)\)\/K$ where $char(K) != 2$, and $a, b in K$, $a, b, a b in.not (K^times)^2$ where $(K^times)^2$ is set of squares of $K^times$.
]
#example([degree $8$ extension])[
    - Consider $L = QQ\(sqrt(2), sqrt(3), sqrt(5)\)$ over $QQ$. $L$ is splitting field of $(x^2 - 2)(x^2 - 3)(x^2 - 5)$, so is normal, and $char(QQ) = 0$, so is separable, so is Galois.
    - Let $M = QQ\(sqrt(2), sqrt(3)\)$. By above, $Gal(M\/Q) = ideal(sigma) times ideal(tau) tilde.equiv ZZ\/2 times ZZ\/2$.
    - Suppose $sqrt(5) in M$. Then $sigma\(sqrt(5)\)^2 = tau\(sqrt(5)\)^2 = 5$, so $sigma\(sqrt(5)\) = plus.minus sqrt(5)$, $tau\(sqrt(5)\) = plus.minus sqrt(5)$.
    - If $sigma\(sqrt(5)\) = sqrt(5)$, then $sqrt(5) in M^(ideal(sigma)) = QQ\(sqrt(3)\)$.
        - If $tau\(sqrt(5)\) = sqrt(5)$, $sqrt(5) in M^(ideal(sigma, tau)) = QQ$: contradiction.
        - If $tau\(sqrt(5)\) = -sqrt(5)$, then since $sqrt(15) in M^(ideal(sigma))$, $tau\(sqrt(15)\) = sqrt(15)$, so $sqrt(15) in M^(ideal(sigma, tau)) = QQ$: contradiction.
    - If $sigma\(sqrt(5)\) = -sqrt(5)$, then $sigma\(sqrt(10)\) = sigma\(sqrt(2)\) sigma\(sqrt(5)\) = \(-sqrt(2)\)\(-sqrt(5)\) = sqrt(10)$, so $sqrt(10) in M^(ideal(sigma)) = QQ\(sqrt(3)\)$.
        - If $tau\(sqrt(5)\) = sqrt(5)$, $tau\(sqrt(10)\) = sqrt(10) in M^(ideal(sigma, tau)) = QQ$: contradiction.
        - If $tau\(sqrt(5)\) = -sqrt(5)$, $tau\(sqrt(30)\) = tau\(sqrt(5)\) tau\(sqrt(3)\) tau\(sqrt(2)\) = sqrt(30) in M^(ideal(sigma, tau)) = QQ$: contradiction.
    - So $sqrt(5) in.not M$, so $[L: QQ] = [L: M][M: QQ] = 8$. The $8$ elements in $Gal(L\/QQ)$ are determined by choices of $sqrt(a) |-> plus.minus sqrt(a)$ where $a in {2, 3, 5}$.
    - $Gal(L\/QQ) = ideal(sigma_1, sigma_2, sigma_3) tilde.equiv ZZ\/2 times ZZ\/2 times ZZ\/2$ where $sigma_1 \(sqrt(2)\) = -sqrt(2)$, $sigma_2 \(sqrt(3)\) = -sqrt(3)$, $sigma_1 \(sqrt(5)\) = -sqrt(5)$ and the $sigma_i$ fix all other square roots.
    - More generally, write $sigma\(sqrt(5)\) = (-1)^j sqrt(5)$, $tau\(sqrt(5)\) = (-1)^k sqrt(5)$, $j, k in {0, 1}$. Define $m = 2^j 3^k$, then $sigma\(sqrt(m)\) = (-1)^j sqrt(m) => sigma\(sqrt(5 m)\) = sqrt(5m)$ and $tau\(sqrt(m)\) = (-1)^k sqrt(m) => tau\(sqrt(5m)\) = sqrt(5m)$, so $sqrt(5 m) in M^ideal(sigma, tau) = QQ$: contradiction.
]
#example("cubic extension and its normal closure")[
    - Let $L = QQ(theta)$, $theta^3 - 2 = 0$. $L\/QQ$ isn't Galois since not normal. Take the normal closure $N = QQ(theta, omega) = QQ\(theta, sqrt(-3)\)$.
    - Let $M = QQ(omega)$ so $[M: QQ] = 2$, $[L: QQ] = 3$ and $[N: QQ] = 6$. Let $G = Gal(N\/QQ)$.
    - Since $|G| = [N: QQ] = 6$, $G tilde.equiv ZZ\/6$ or $G tilde.equiv D_3 tilde.equiv S_3$.
    - $G$ contains $Gal(N\/L)$. Since $N = L(omega)$, $ Gal(N\/L) = {id, tau} = ideal(tau) tilde.equiv ZZ\/2 $ where $tau\(sqrt(-3)\) = -sqrt(-3)$ (i.e. $tau(w) = omega^2$) and $tau(theta) = theta$ as $theta in L$.
    - $G$ contains $H = Gal(N\/M)$. $N = M(theta)$, $|H| = [N: M] = 3$ so $Gal(N\/M)$ is cyclic so $ H = {id, sigma, sigma^2} = ideal(sigma) tilde.equiv ZZ\/3 $ where $sigma(theta) = omega theta$, also $sigma(omega) = omega$ as $omega in M$ and $sigma^2 (theta) = omega^2 theta$, so $H$ permutes the three roots of $x^3 - 2$.
    - $tau in.not H$ so $H = {id, sigma, sigma^2}$ and $tau H = {tau, tau sigma, tau sigma^2}$ are disjoint cosets. So $G = H union tau H = ideal(tau, sigma)$ so $|G| = 6$. $tau^2 = sigma^3 = id$ and $sigma tau = tau sigma^2$. So $G tilde.equiv S_3 tilde.equiv D_3$.
    - $G$ has one subgroup of order $3$, $H = ideal(sigma)$. Fixed field is $N^H = M$. $H$ is only proper normal subgroup of $G$. Correspondingly, $M$ is only normal extension of $Q$ in $N$.
    - There are $3$ order $2$ subgroups: $ideal(tau)$, $ideal(tau sigma)$, $ideal(tau sigma^2)$. $N^ideal(tau) = QQ(theta) = L$, $N^ideal(tau sigma) = QQ(omega theta) = sigma(L)$, $N^ideal(tau sigma^2) = QQ(omega^2 theta) = sigma^2 (L)$.
]
#example[
    Show $cbrt(3) in.not QQ\(cbrt(2)\)$.
    - Assume $cbrt(3) in QQ\(cbrt(2)\)$. Then $cbrt(3) in N = QQ\(omega, cbrt(2)\)$, the normal closure.
    - As above, let $sigma in Gal(N\/QQ)$, $sigma\(cbrt(2)\) = omega cbrt(2)$ and $N^ideal(sigma) = QQ(omega)$. Also, $ sigma\(cbrt(3)\)^3 = sigma(3) = 3 ==> sigma\(cbrt(3)\) in \{cbrt(3), omega cbrt(3), omega^2 cbrt(3)\} $
    - If $sigma\(cbrt(3)\) = cbrt(3)$, then $cbrt(3) in N^ideal(sigma) = QQ(omega)$, so $QQ\(cbrt(3)\) subset.eq QQ(omega)$: contradiction.
    - If $sigma\(cbrt(3)\) = omega cbrt(3)$, then $sigma\(cbrt(3)\/cbrt(2)\) = cbrt(3)\/cbrt(2)$ hence $cbrt(3\/2) in N^ideal(sigma) = QQ(omega)$, so $QQ\(cbrt(3\/2)\) = QQ\(cbrt(12)\) subset.eq QQ(omega)$: contradiction.
    - If $sigma\(cbrt(3)\) = omega^2 cbrt(3)$, $QQ\(cbrt(3\/4)\) = QQ\(cbrt(6)\) subset.eq QQ(omega)$: contradiction.
]
#remark[
    In the above example, $N = QQ(theta_1, theta_2, theta_3) = QQ\(cbrt(2), omega\)$ where $theta_i$ are the roots of $x^3 - 2$. Plotting these roots on Argand diagram gives the symmetry group $S_3 tilde.equiv D_3$ of an equilateral triangle. $tau$ reflects the $theta_i$ (complex conjugation), $sigma$ rotates the roots (but *doesn't* rotate all of $N$, as it fixes $QQ$). For $g in G$, $g(theta_j) = theta_(pi(j))$ where $pi$ is permutation of ${1, 2, 3}$. So there is a group homomorphism $phi: G -> S_3$, $phi(g) = pi$. $ker(phi) = {id}$, so $phi$ is injective and also surjective, since $|G| = |S_3| = 6$, so $phi$ is isomorphism.
]
#definition[
    For $f(x) in K[x]$, $deg(f) = n >= 1$, with $n$ distinct roots, the *Galois group* of $f(x)$, $G_f$, is Galois group of splitting field of $f(x)$ over $K$ (provided it is separable).
]
#remark[
    Elements of $G_f$ permute roots of $f$, so $G_f$ is subgroup of $S_n$. If $f(x)$ irreducible over $K$, then $G_f$ is *transitive* subgroup, i.e. given $2$ roots $alpha, beta$ of $f$, there is a $g in G_f$ with $g(alpha) = beta$. This gives a general pattern $ "polynomial" --> "field extension" --> "permutation group" $
]
#example[
    Consider $QQ subset L = QQ(theta) subset N = QQ(theta, i)$ where $theta = root(4, 2)$. $N$ is normal closure of $QQ(theta)$, $[N: QQ] = 8$ so $|Gal(N\/QQ)| = 8$.
    - Define $sigma(theta) = i theta$, $sigma(i) = i$, $tau(theta) = theta$, $tau(i) = -i$. Then $tau^2 = sigma^4 = id$. We have $
    #table(
    columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto),
    inset: 10pt,
    align: horizon,
    [], $id$, $sigma$, $sigma^2$, $sigma^3$, $tau$, $tau sigma$, $tau sigma^2$, $tau sigma^3$,
    $theta$, $theta$, $i theta$, $-theta$, $-i theta$, $theta$, $-i theta$, $-theta$, $i theta$,
    $i$, $i$, $i$, $i$, $i$, $-i$, $-i$, $-i$, $-i$
    ) $ so $G = Gal(N\/QQ) = angle.l sigma, tau: sigma^4 = tau^2 = id, sigma tau = tau sigma^3 angle.r tilde.equiv D_4$.
    - Order $2$ subgroups are $ideal(tau)$, $ideal(tau sigma)$, $ideal(tau sigma^2)$, $ideal(tau sigma^3)$, $ideal(sigma^2)$.
    - Order $4$ subgroups are $ideal(sigma^2, tau) tilde.equiv (ZZ\/2)^2$, $ideal(sigma) tilde.equiv ZZ\/4$, $ideal(sigma^2, tau sigma) tilde.equiv (ZZ\/2)^2$.
    - Respectively, intermediate field extensions of degree $4$ are $QQ\(root(4, 2)\)$, $QQ\(i root(4, 2)\)$, $QQ\(sqrt(2), i\)$, $QQ\((1 - i) root(4, 2)\)$, $QQ\((1 + i) root(4, 2)\)$.
    - Respectively, intermediate field extensions of degree $2$ are $QQ\(sqrt(2)\)$, $QQ(i)$, $QQ\(i sqrt(2)\)$.
]

= Cyclotomic field extensions

== Roots of unity

#definition[
    $zeta in K^*$ is *$n$-th primitive root of unity* if $zeta^n = 1$ and $forall 0 < m < n$, $zeta^m != 1$, i.e. order of $zeta$ in $K^*$ is $n$.
]
#example[
    - $zeta$ is primitive $1$-st root of unity iff $zeta = 1$.
    - $-1$ is primitive $2$-nd root of unity iff $char(K) != 2$.
    - If $char(K) = p$ prime, then $K$ contains no $p$-th primitive roots of unity (since $zeta^p = 1 <==> (zeta - 1)^p = 0 <==> zeta = 1$).
    - If $K = CC$, $exp(2pi i\/n)$ is $n$-th primitive root of unity.
]
#proposition[
    Let $zeta in K^*$ primitive $n$-th root of unity, let $d = gcd(m, n)$. Then $zeta^m$ is primitive $(n\/d)$-th root of unity.
]
#corollary[
    Let $zeta in K^*$ primitive $n$-th root of unity.
    - $zeta^m = 1 <==> m equiv 0 mod n$.
    - $zeta^m$ is primitive $n$-th root of unity iff $gcd(m, n) = 1$.
]
#definition[
    Let $mu(K)$ denote subgroup of all roots of unity in $K^*$.
]
#theorem[
    Let $K$ field, $H$ finite subgroup of $K^*$, then $H$ is cyclic.
]
#remark[
    This implies that any finite field $FF_q$ can be written $FF_q = FF_(p^n) = FF_p (alpha)$ where $alpha$ is generator of $FF_q^times$.
]
#corollary[
    Let $K$ field, $n in NN$ be largest such that $K$ contains primitive $n$-th root of unity $zeta$. Then $mu(K)$ is cyclic subgroup in $K^*$ generated by $zeta$.
]

== $n$-th cyclotomic field extensions

#notation[
    Let $zeta_n = exp(2pi i \/ n) in CC$.
]
#definition[
    $QQ\(zeta_n\)\/QQ$ is *$n$-th cyclotomic field extension*.
]
#proposition[
    $QQ\(zeta_n\)\/QQ$ is Galois.
]
#definition[
    $Phi_n (x) := product_(a in A) (x - zeta_n^a)$ where $A = {a in NN: 0 < a < n, gcd(a, n) = 1}$.
]
#proposition[
    $Phi_n (x) in QQ[x]$ is irreducible and so is minimal polynomial of a primitive $n$-th root of unity over $QQ$. In particular, $[QQ\(zeta_n\): QQ] = phi(n)$, where $phi(n) = |(ZZ\/n)^times|$ is Euler function.
]
#proposition[
    Properties of $phi$ function:
    - For prime $p$, $phi(p) = p - 1$.
    - For prime $p$, $phi(p^k) = p^k - p^(k - 1)$.
    - If $gcd(n, m) = 1$, then $phi(n m) = phi(n) phi(m)$.
    - If $n = product_(i = 1)^r p_i^(k_i)$ is prime factorisation of $n$, then $ phi(n) = n product_(i = 1)^r (1 - 1/p_i) $
]
#proposition[
    $forall n in NN, x^n - 1 = product_(n_1 divides n) Phi_(n_1)(x)$.
]
#example[
    - $Phi_1 (x) = x - 1$.
    - $Phi_1 (x) Phi_2 (x) = x^2 - 1 ==> Phi_2 (x) = x + 1$.
    - $Phi_1 (x) Phi_3 (x) = x^3 - 1 ==> Phi_3 (x) = x^2 + x + 1$.
]
#proposition[
    - For $p$ prime, $Phi_p (x) = x^(p - 1) + dots.h.c + x + 1$.
    - For $p$ prime, $Phi_(p^k)(x) = Phi_p \(x^(p^(k - 1))\)$.
    - For every $n in NN$, $Phi_n (x)$ has integer coefficients.
]

== Galois properties of cyclotomic extensions

#theorem[
    $Gal(QQ\(zeta_n\)\/QQ) tilde.equiv (ZZ\/n)^times$.
]
#remark[
    To compute $(ZZ\/n)^times$, note that for $m, n$ coprime, $(ZZ\/m n)^times tilde.equiv (ZZ\/m)^times times (ZZ\/n)^times$ and
    - If $p != 2$ prime, then $(ZZ\/p^r)^times$ is cyclic of order $phi(p^r)$.
    - $(ZZ\/4)^times tilde.equiv ZZ\/2$ and for $r >= 3$, $(ZZ\/2^r)^times tilde.equiv ZZ\/2 times ZZ\/2^(r - 2)$.
]
#corollary[
    $Gal(QQ\(zeta_n\)\/QQ)$ is abelian so every subgroup is normal, so any subfield of $QQ\(zeta_n\)$ is Galois over $QQ$.
]
#corollary[
    For $p$ prime, $G = Gal(QQ\(zeta_p\)\/QQ) tilde.equiv (ZZ\/p)^times tilde.equiv ZZ\/(p - 1)$. In particular, for $d | (p - 1)$, $QQ\(zeta_p\)$ contains exactly one subfield of degree $d$ and there are no other subfields.
]
#remark[
    For $d = 2$ in above corollary, $QQ\(zeta_p\)$ contains unique quadratic subfield $QQ\(sqrt(D_p)\)$, where $D_p = (-1)^((p - 1)\/2) p$
]
#example[
    $Gal(QQ\(zeta_n\)\/QQ)$ not always cyclic, e.g. $Gal(QQ(zeta_8)\/QQ) tilde.equiv ZZ\/2 times ZZ\/2$.
]
#proposition[
    - If $n$ odd, $mu(QQ\(zeta_n\))$ is cyclic of order $2n$ and is generated by $-zeta_n$.
    - If $n$ even, $mu(QQ\(zeta_n\))$ is cyclic of order $n$ and is generated by $zeta_n$.
    - If $gcd(m, n) = d$, then $QQ(zeta_m, zeta_n) = QQ(zeta_(m n \/ d))$.
]

== Special properties of $QQ\(zeta_p\)$, where $p > 2$ is prime

#example[
    $Gal(QQ(zeta_5)\/QQ) tilde.equiv (ZZ\/5)^times$ has generator $tau: zeta_5 |-> zeta_5^2$. $QQ$-basis ${1, zeta_5, zeta_5^2, zeta_5^3}$ is not invariant under action of $tau$ or any power of $tau$ (since $tau(zeta_5^2) = zeta_5^4$) but ${zeta, zeta_5^2, zeta_5^3, zeta_5^4}$ is invariant. The same holds for general $p > 2$ prime. For $alpha_i in QQ$, $alpha_1 zeta_p + dots.h.c + alpha_(p - 1) zeta_p^(p - 1) in QQ$ iff $alpha_1 = dots.h.c = alpha_(p - 1)$.
]
#example[
    If $x in QQ\(zeta_p\)$, $[QQ(x): QQ] = |\{sigma(x): sigma in Gal\(QQ\(zeta_p\)\/QQ\)\}|$ In particular, if $tau$ is generator of $G = Gal\(QQ\(zeta_p\)\/QQ\)$ and $x = alpha_1 zeta_p + dots.h.c + alpha_(p - 1) zeta_p^(p - 1)$ then set of all conjugates of $x$ is equal to (note not all elements are distinct) $ {tau^a (x): a in [p - 1]} = {sum_(i = 1)^(p - 1) alpha_i zeta_p^(a i): a in [p - 1]} $
]
#example[
    Let $x = zeta_5 + zeta_5^4$, $tau: zeta_5 |-> zeta_5^2$ is a generator of $Gal(QQ\(zeta_5\)\/QQ)$. $tau(x) = zeta_5^2 + zeta_5^3 != x$ but $tau^2 (x) = x$, so $[QQ(x): QQ] = 2$, i.e. $QQ(zeta_5 + zeta_5^4)$ is unique quadratic subfield in $QQ(zeta_5)$.
]
#definition[
    Let $x in QQ\(zeta_p\)$, let minimal polynomial of $x$ over $QQ$ be $m(t) = (t - x^((1))) dots.h.c (t - x^((d)))$. *Conjugates* of $x$ over $QQ$ are $x^((1)) = x, ..., x^((d))$.
]
#example[
    Minimal polynomial of $zeta_5 + zeta_5^4 = 2 cos(2pi\/5)$ over $QQ$ is $m(x) = (x - zeta_5 - zeta_5^4)(x - zeta_5^2 - zeta_5^3) = x^2 + x - 1$, with roots $(-1 plus.minus sqrt(5))\/2$. So $cos(2pi\/5) = (-1 + sqrt(5))\/4$, and unique quadratic subfield of $QQ(zeta_5)$ over $QQ$ is $QQ\(sqrt(5)\)$.
]
#example[
    Let $tau in G$ be generator of $G = Gal(QQ\(zeta_p\)\/QQ)$, i.e. $tau(zeta_p) = zeta_p^a$, $a mod p$ generates $(ZZ\/p)^times$. Let $ Theta_p = zeta_p - tau(zeta_p) + tau^2 (zeta_p) - dots.h.c + tau^(p - 3) (zeta_p) - tau^(p - 2) (zeta_p) $ $Theta_p$ behaves like $sqrt(D_p)$: $tau\(Theta_p\) = -Theta_p$, $tau^2 \(Theta_p\) = Theta_p$. So $Theta_p in QQ\(zeta_p\)^ideal(tau^2)$. Also, $tau\(Theta_p^2\) = Theta_p^2$ so $Theta_p^2 in QQ\(zeta_p\)^ideal(tau) = QQ$. In fact, $Theta_p^2 = D_p$. Therefore $ Theta_p^2 = A + B (zeta_p + dots.h.c + zeta_p^(p - 1)) = A - B $ So when computing $Theta_p^2$, only need to consider coefficients for $1$ and $zeta_p$.
]

= Cyclic field extensions

== Cyclic extensions of degree $2$

#example[
    Let $L\/K$ cyclic of degree $2$, so $Gal(L\/K) = {e, tau}$, $tau^2 = e$. Let $theta in L - K$, then $tau(theta) != theta$ (as otherwise $theta in L^ideal(tau) = K$). Let $theta_1 = tau(theta) - theta$, so $tau(theta_1) = tau^2 (theta) - tau(theta) = -theta_1$. If $char(K) != 2$, then $theta_1 != -theta_1$ and so $theta_1 in.not K$, $L = K(theta_1)$. $theta_1$ is "better" than $theta$, since $tau(theta_1) = -theta_1$. Now if $a = theta_1^2$, then $tau(a) = a$, so $L = K\(sqrt(a)\)$.
]
#theorem[
    If $char(K) != 2$ and $L\/K$ is cyclic quadratic extension, then $ exists a in K^times - K^times^2: quad L = K\(sqrt(a)\) $
]
#definition[
    $a_1, ..., a_n$ are *independent modulo $K^times^2$ (independent modulo squares)* if $ a_1^(epsilon_1) dots.h.c a_n^(epsilon_n) in K^times^2 <==> "all" epsilon_i "are even" $
]
#proposition[
    If $char(K) != 2$:
    - $K\(sqrt(a_1)\) = K\(sqrt(a_2)\) <==> a_1 equiv a_2 mod K^times^2$, i.e. $a_1 = a_2 dot.op b^2$, $b in K^times$.
    - If $a_1, ..., a_n in K^times$ are independent modulo $K^times^2$ then $K\(sqrt(a_1), ..., sqrt(a_n)\)$ has degree $2^n$ over $K$ with Galois group $tilde.equiv (ZZ\/2)^n$.
    - If $L\/K$ Galois with Galois group $(ZZ\/2)^n$, then $ exists a_1, ..., a_n in K^times: quad L = K\(sqrt(a_1), ..., sqrt(a_n)\) $
]
#remark[
    Let $char(K) = 2$, then $forall a in K^times$, $L = K\(sqrt(a)\)$ is normal but not separable (since minimal polynomial of e.g. $sqrt(a)$ is $x^2 - a = (x + sqrt(a))(x - sqrt(a)) = (x - sqrt(a))^2$ so has repeated roots).
]

== Cyclic extensions of degree $n$ (the Kummer theory)

#definition[
    $L\/K$ is *cyclic of degree $n$* if it is Galois and $Gal(L\/K)$ is cyclic of order $n$.
]
#theorem[
    If $K$ contains primitive $n$-th root of unity and for all divisors $d > 1$ of $n$, $a in K^times$ is not $d$-th power in $K$, then $L = K\(root(n, a)\)$ is cyclic extension of $K$ of degree $n$. In particular, $x^n - a in K[x]$ is irreducible.
]
#proposition[
    If $zeta_p in K$, $a in K^times - K^times^p$, then $K(root(p, a))\/K$ is cyclic of degree $p$. In particular, $x^p - a in K[x]$ is irreducible.
]
#theorem[
    Let $K$ contain primitive $n$-th root of unity $zeta_n$, $L\/K$ is cyclic extension of degree $n$, $Gal(L\/K) = ideal(sigma)$. Then $ exists a in K^times: L = K\(root(n, a)\) $ Such an $a$ is given by $theta_b^n$ for some $b in L$, where $ theta_b = b + zeta_n^(-1) sigma(b) + dots.h.c + zeta_n^(-(n - 1)) sigma^(n - 1)(b) $ is *Lagrange resolvent* for $b$, i.e. $L = K(theta_b)$.
]<lagrange-resolvent>
#lemma("Artin's lemma")[
    There exists $b in L$ such that $theta_b != 0$.
]

= Finite fields

== Existence and uniqueness

#lemma[
    Let $K$ finite field, then $K$ is field extension of $FF_p$ for some prime $p$ and $|K| = p^n$ where $n = \[K: FF_p\]$.
]
#theorem[
    Let $p$ prime. Then $forall n in NN$, there is field $K$ with $|K| = p^n$.
]
#theorem[
    Let $K$ finite field with $|K| = q = p^n$. Then
    - $forall alpha in K, alpha^q = alpha$.
    - $x^q - x = product_(alpha in K) (x - alpha)$
    - $K$ is splitting field of $x^q - x$ over $FF_p$.
]
#corollary[
    If $K_1$, $K_2$ finite fields, $|K_1| = |K_2|$, then $K_1 tilde.equiv K_2$.
]
#definition[
    Let $q = p^n$, then $FF_q$ is the unique (up to isomorphism) field containing $q$ elements.
]
#definition[
    For $q = p^n$, the *Frobenius automorphism* is $ sigma: FF_q -> FF_q, quad sigma(alpha) = alpha^p $ which is an $FF_p$-automorphism by Fermat's little theorem.
]
#theorem[
    Let $q = p^n$, $p$ prime.
    - $FF_q \/ FF_p$ is Galois of degree $n$.
    - Frobenius automorphism generates $Gal(FF_q \/ FF_p)$ and there is group isomorphism $ Gal(FF_q \/ FF_p) <-> ZZ\/n, quad sigma <--> 1 mod n $
]

== Counting irreducible polynomials over finite fields

#notation[
    Let $"Irr"_(FF_p) (m)$ denote set of all irreducible polynomials in $FF_p [x]$ of degree $m$. Let $N_p (m) = |"Irr"_(FF_p)(m)|$.
]
#theorem[
    Let $q = p^m$, then $m N_p (m) = |\{alpha in FF_q: FF_p (alpha) = FF_q\}|$.
]
#remark[
    To use above theorem, note that $FF_p (alpha) != FF_(p^m)$ iff $alpha$ belongs to proper subfield of $FF_(p^m)$.
]
#example[
     - If $m$ is prime, then $FF_(p^m)$ has only one proper subfield $FF_p$, so $m N_p (m) = |FF_(p^m)| - |FF_p| = p^m - p$.
     - The proper subfields of $FF_(p^4)$ are $FF_p$ and $FF_(p^2)$, but $FF_p subset FF_(p^2)$, so $4 N_p (4) = |FF_(p^4)| - |FF_(p^2)|$.
     - $FF_p (alpha) != FF_(p^6)$ iff $alpha in FF_(p^3) union FF_(p^2)$. Since $FF_(p^3) sect FF_(p^2) = FF_p$, we have $6 N_p (6) = |FF_(p^6)| - |FF_(p^3)| - |FF_(p^2)| + |FF_p| = p^6 - p^3 - p^2 + p$.
]
#proposition[
    We have $ p^n = sum_(m | n) m N_p (m) $ which we can use recursively to compute any $N_p (m)$.
]
#example[
    We construct $L = FF_(3^16)$ by finding irreducible polynomial of degree $16$ in $FF_3 [x]$.
    - $FF_9 = FF_3 (theta)$ where $theta^2 + 1 = 0$, $FF_9 = {a + b theta: a, b in FF_3}$. $K := FF_9$ contains primitive $8$-th root of unity since $FF_9^times tilde.equiv ZZ\/8$.
    - $L\/K$ is cyclic extension of degree $8$, so by Kummer theory there exists $alpha in K$ such that $L = K\(root(8, alpha)\)$. $alpha$ must be element that is not square or fourth power in $FF_9$, so we can look for elements that have order $8$.
    - $alpha = theta$ doesn't work since $theta^2 = -1 ==> theta^4 = 1$. $alpha = 1 + theta$ works since $ (1 + theta)^2 = theta^2 + theta + 1 = -theta, quad (1 + theta)^4 = theta^2 = -1, (1 + theta)^8 = 1 $ so $alpha = 1 + theta$ has order $8$ in $FF_9$.
    - So $L = K\(root(8, a)\) = FF_9 \(root(8, 1 + theta)\) = FF_3 \(theta, root(8, 1 + theta)\) = FF_3 (eta)$ where $eta^8 = 1 + theta$. Now $[L: FF_3] = 16$ by tower law, so $L = FF_(3^16)$ by uniqueness of finite fields.
    - $eta^8 = 1 + theta ==> (eta^8 - 1)^2 = theta^2 = -1 ==> eta^16 + eta^8 + 2 = 0$ so $f(x) = x^16 + x^8 + 2 in FF_3 [x]$ is irreducible.
]

= Galois groups of polynomials

== Symmetric functions

#definition[
    Define action of $S_n$ on $L = k(x_1, ..., x_n)$ by $tau: x_j |-> x_(pi(j))$ where $pi in S_n$, which gives $k$-automorphism $
        tau: L -> L, quad f(x_1, ..., x_n) / g(x_1, ..., x_n) |-> (f\(x_(pi(1)), ..., x_(pi(n))\)) / (g\(x_(pi(1)), ..., x_(pi(n))\))
    $ The *symmetric functions* in $L$ are elements of fixed field $L^(S_n)$.
]
#definition[
    The *elementary symmetric polynomials* $e_r in L$ for $r in [n]$ are $ e_1 & = sum_(1 <= i <= n) x_i \ e_2 & = sum_(1 <= i < j <= n) x_i x_j \ & dots.v \ e_r & = sum_(1 <= i_1 < dots.h.c < i_r <= n) x_(i_1) dots.h.c x_(i_r) \ & dots.v \ e_n & = x_1 dots.h.c x_n $ Define $K = k(e_1, ..., e_n)$.
]
#theorem[
    $K = L^(S_n)$ and $L\/K$ is Galois with $Gal(L\/K) tilde.equiv S_n$.
]<symmetric-polynomial-extension-galois-group-is-symmetric-group>
#proof[
    - Note that $f(x) = (x - x_1) dots.h.c (x - x_n) = x^n - e_1 x^(n - 1) + dots.h.c + (-1)^n e_n$.
    - Show $L$ splitting field of $f(x)$ over $K$ and $[L: K] <= n!$.
    - Show $[L: K] >= n!$.
]
#remark[
    Every finite group $G$ is subgroup of $S_n$ for some $n$, so there is always Galois extension with Galois group $G$: let $L = k(x_1, ... x_n)$, let $G subset.eq S_n$ act on $L$ as above, then $Gal(L\/L^G) = G$.
]
#definition[
    For $f(x) in K[x]$, *Galois group* of $f(x)$, $G_f$, is Galois group of splitting field of $f(x)$ over $K$ (provided this extension is separable). If $deg(f) = n$, $G_f$ acts by permuting roots $theta_1, ..., theta_n$ of $f$, so is subgroup of $S_n$. There can be non-trivial relationships between roots, so $G_f$ may be proper subgroup.
]
#corollary[
    Any symmetric polynomial in $k[x_1, ..., x_n]$ can be expressed as polynomial in elementary symmetric polynomials, i.e. $ k[x_1, ..., x_n]^(S_n) = k[e_1, ..., e_n] $ where LHS is set of symmetric polynomials, RHS is set of polynomials in elementary symmetric polynomials.
]
#example[
    - When $n = 2$, $x_1^2 + x_2^2 = e_1^2 - 2e_2$ and $x_1^3 + x_2^3 = e_1^3 - 3e_1 e_2$.
    - When $n = 3$, $x_1^2 x_2 + x_1 x_2^2 + x_2^2 x_3 + x_2 x_3^2 + x_3^2 x_1 + x_3 x_1^2 = e_1 e_2 - 3e_3$.
]
#definition[
    *Lexicographic ordering of monomials*, $gtlex$ (or $scripts(gt.curly)_L$), is $ x_1^(a_1) dots.h.c x_n^(a_n) gtlex x_1^(b_1) dots.h.c x_n^(b_n) $ iff $exists 0 <= j <= n - 1$ such that $a_1 = b_1, ..., a_j = b_j$ and $a_(j + 1) > b_(j + 1)$.
]
#example[
    $x_1^2 x_2^3 x_3 gtlex x_1^2 x_2^2 x_3^4$.
]
#definition[
    *Leading term* of $f(x_1, ..., x_n) in k[x_1, ..., x_n]$ is largest monomial $c x_1^(a_1) dots.h.c x_n^(a_n)$ with $c != 0$, $a_i != 0$ for some $i$, appearing in $f$ with respect to lexicographic ordering.
]
#note[
    If $f$ is symmetric, then $a_1 >= dots.h.c >= a_n$.
]
#algorithm[
    Given $f(x_1, ..., x_n) in k[x_1, ..., x_n]^(S_n)$, express $f$ as polynomial in elementary symmetric polynomials:
    + Find leading term $c x_1^(a_1) dots.h.c x_n^(a_n)$ of $f$, compute $ f_1 = f - c e_1^(a_1 - a_2) dots.h.c e_(n - 1)^(a_(n - 1) - a_n) e_n^(a_n) $ Note leading term of $c e_1^(a_1 - a_2) dots.h.c e_(n - 1)^(a_(n - 1) - a_n) e_n^(a_n)$ is also $c x_1^(a_1) dots.h.c x_n^(a_n)$ so leading term of $f_1$ is strictly smaller than leading term of $f$. Also, $f_1$ is symmetric.
    + If $f_1 != 0$, apply step $1$ to get $f_2$, $f_3$, .... Since leading term of $f_1, f_2, ...$ is strictly decreasing, eventually $f_i = 0$.
]
#example[
    Express $f(x_1, x_2) = x_1^3 + x_2^3$ in elementary symmetric polynomials:
    - Leading term of $f$ is $x_1^3 = x_1^3 x_2^0$, so $ f_1 = f - e_1^(3 - 0) e_2^0 = -3x_1^2 x_2 - 3x_1 x_2^2 $
    - Leading term of $f_1$ is $-3x_1^2 x_2$, so $ f_2 = f_1 - (-3) e_1^(2 - 1) e_2^1 = -3x_1^2 x_2 - 3x_1 x_2^2 + 3(x_1 + x_2) x_1 x_2 = 0 $
    - So $f_1 = f_2 + (-3) e_1^(2 - 1) e_2^1 = -3e_1 e_2$ and $f = e_1^3 + f_1 = e_1^3 - 3e_1 e_2$.
]
#example[
    - Let $theta_1 = 1/3(x_1 + omega x_2 + omega^2 x_3)$, $theta_2 = 1/3(x_1 + omega^2 x_2 + omega x_3)$, where $omega = zeta_3$.
    - Let $sigma = (1 thick 2 thick 3) in S_3$, then $sigma (theta_1) = omega^2 theta_1$, $sigma (theta_2) = omega theta_2$, hence $ sigma(theta_1^3 + theta_2^3) = omega^6 theta_1^3 + omega^3 theta_2^3 = theta_1^3 + theta_2^3 $
    - Let $tau = (2 thick 3) in S_3$, then $tau(theta_1) = theta_2$, $tau(theta_2) = theta_1$ so $tau(theta_1^3 + theta_2^3) = theta_1^3 + theta_2^3$.
    - Since $S_3 = ideal(sigma, tau)$, $f(x_1, x_2, x_3) = 27(theta_1^3 + theta_2^3) in QQ[x_1, x_2, x_3]^(S_3)$. Applying the algorithm:
        - $f_1 = f - 2 e_1^3 = 9 (x_1^2 x_2 + dots.h.c)$.
        - $f_2 = f_1 - (-9) e_1 e_2 = 27 x_1 x_2 x_3$.
        - $f_3 = f_2 - 27 e_3 = 0$.
        - So $f = 2 e_1^3 - 9 e_1 e_2 + 27 e_3$.
    - By a similar process, $9 theta_1 theta_2 = e_1^2 - 3 e_2$.
]<example:theta_i-for-cubic>

== Galois theory for cubic polynomials

#example("Solving quadratic")[
    Let $char(k) != 2$. General quadratic polynomial can be written as $ f(x) = x^2 - e_1 x + e_2 = (x - x_1)(x - x_2) in K[x] $ where $e_1 = x_1 + x_2, e_2 = x_1 x_2 in K = k(e_1, e_2)$. Let $L = k(x_1, x_2) = K(x_1)$, then $L\/K$ is Galois and $Gal(L\/K) = {id, sigma} tilde.equiv S_2 tilde.equiv ZZ\/2$ where $sigma(x_1) = x_2$, $sigma(x_2) = x_1$. Since $L\/K$ cyclic and $zeta_2 = -1 in K$, by @lagrange-resolvent, Lagrange resolvent of $x_1$ is $ theta = theta_(x_1) = x_1 + zeta_2^(-1) sigma(x_1) = x_1 - x_2 $ So $sigma(theta) = -theta$ and $theta^2 = e_1^2 - 4e_2$. $Delta = theta^2$ is *discriminant* of $f(x)$. So we have $x_1 = \(e_1 + sqrt(Delta)\)\/2$, $x_2 = \(e_1 - sqrt(Delta)\)\/2$. If $f(x)$ is irreducible, it has distinct roots, and so Galois group $G_f tilde.equiv ZZ\/2$.
]
#example("Solving cubic")[
    - Let $char(k) != 2, 3$, let $ f(x) = x^3 - e_1 x^2 + e_2 x - e_3 = (x - x_1)(x - x_2)(x - x_3) in K[x] $ where $e_1 = x_1 + x_2 + x_3$, $e_2 = x_1 x_2 + x_1 x_3 + x_2 x_3$, $e_3 = x_1 x_2 x_3 in K = k(e_1, e_2, e_3) subset L = K(x_1, x_2, x_3)$.
    - By @symmetric-polynomial-extension-galois-group-is-symmetric-group, $Gal(L\/K) = S_3$ with normal subgroup $A_3 tilde.equiv ZZ\/3$. We have tower $K subset M = L^(A_3) subset L$. So $Gal(L\/M) tilde.equiv A_3 tilde.equiv ZZ\/3$, $Gal(M\/K) tilde.equiv S_3 \/ A_3 tilde.equiv ZZ\/2$.
    - Assume $k$ contains primitive $3$rd root of unity $omega$, so $w^2$ is also primitive $3$rd root of unity. Define $
        theta_1 & = 1/3(x_1 + omega x_2 + omega^2 x_3), quad t_1 = theta_1^3, \
        theta_2 & = 1/3(x_1 + omega^2 x_2 + omega x_3), quad t_2 = theta_2^3
    $ then $t_1, t_2 in M$ and $L = M(theta_1) = M(theta_2)$. By @example:theta_i-for-cubic, $27(theta_1^3 + theta_2^3) = 2e_1^3 - 9e_1 e_2 + 27e_3$, $9 theta_1 theta_2 = e_1^2 - 3e_2$, so $t_1, t_2$ are roots of *quadratic resolvent* of $f(x)$: $ (t - t_1)(t - t_2) = t^2 - ((2e_1^3 - 9e_1 e_2 + 27e_3)/27) t + ((e_1^2 - 3e_2)/9)^3 $
    - To find roots $x_1, x_2, x_3$ of $f$:
        - Solve quadratic resolvent to find $t_1, t_2$.
        - Choose $theta_1 = cbrt(t_1)$, find $theta_2$ from $9 theta_1 theta_2 = e_1^2 - 3e_2$.
        - Solve the linear system $
            cases(x_1 + x_2 + x_3 = e_1, x_1 + omega x_2 + omega^2 x_3 = 3 theta_1, x_1 + omega^2 x_2 + omega x_3 = 3 theta_2) quad ==> quad cases(x_1 = e_1\/3 + theta_1 + theta_2, x_2 = e_1\/3 + omega^2 theta_1 + omega theta_2, x_3 = e_1\/3 + omega theta_1 + omega^2 theta_2)
        $
]
#remark[
    To solve general cubic $f(x) = x^3 + a x^2 + b x + c$, first perform shift: $ f(x - a\/3) = x^3 + p x + q $ then quadratic resolvent is  (_memorise_) *$ t^2 + q t - p^3 / 27 $* with roots $t_1 = theta_1^3$, $t_2 = theta_2^3$, choose $theta_1, theta_2$ such that $theta_1 theta_2 = -p/3$, then roots of $f(x - a\/3)$ are $x_1 = theta_1 + theta_2$, $x_2 = omega^2 theta_1 + omega theta_2$, $omega theta_1 + omega^2 theta_2$.
]
#example("Galois groups of cubic polynomials")[
    Let $char(K) != 2, 3$, $f(x) = x^3 + a x^2 + b x + c in K[x]$, let $L$ be splitting field for $f(x)$ over $K$, then $G_f = Gal(L\/K)$. Let $alpha_1, alpha_2, alpha_3$ be roots of $f(x)$ in $L$.
    - If $alpha_1, alpha_2, alpha_3 in K$, then $L = K$, $G_f = {id}$.
    - If $f(x) = (x - alpha_j) g(x)$ where $alpha_j in K$, $g(x) in K[x]$ irreducible quadratic, then $[L: K] = 2$, $G_f tilde.equiv ZZ\/2$.
    - If $f(x)$ irreducible in $K[x]$, then $K subset K(alpha_1) subset.eq K(alpha_1, alpha_2, alpha_3) = L$, then either $[L: K(alpha_1)] = 1$, so $[L: K] = 3$ and $G_f tilde.equiv A_3 tilde.equiv ZZ\/3$, or $[L: K(alpha_1)] = 2$, so $[L: K] = 6$ and $G_f tilde.equiv S_3$.
]
#definition[
    *Discriminant* of $f(x) = (x - alpha_1)(x - alpha_2)(x - alpha_3)$ is $Delta = delta^2$ where $ delta = (alpha_1 - alpha_2)(alpha_2 - alpha_3)(alpha_3 - alpha_1) $ Note $Delta != 0$ if $f$ has distinct roots.
]
#note[
    If $G_f tilde.equiv A_3$, then $G_f = ideal(tau)$ where $tau: alpha_1 |-> alpha_2$, $alpha_2 |-> alpha_3$, $alpha_3 |-> alpha_1$, then $tau(delta) = delta$ so $delta in L^(G_f) = K$ and $Delta in K^times^2$. But if $G_f tilde.equiv S_3$, then if $tau in A_3$, $tau(delta) = delta$ and if $tau in S_3 - A_3$, then $tau(delta) = -delta$ so $delta in.not K$ but $Delta in K$.
]
#theorem[
    Let $f(x) in K[x]$ irreducible, $deg(f) = 3$. Then
    - $G_f tilde.equiv A_3 <==> Delta in K^times^2$,
    - $G_f tilde.equiv S_3 <==> Delta in K^times - K^times^2$.
]
#theorem[
    Let $f(x) = x^3 + a x^2 + b x + c in K[x]$, then $ Delta = 18 a b c - 4a^3 c + a^2 b^2 - 4b^3 - 27c^2 $ For reduced cubic $f(x) = x^3 + p x + q$,  (_memorise_) *$ Delta = -4p^3 - 27q^2 $*
]
#note[
    The reduced form of $f(x)$ has same discriminant as $f(x)$.
]

== Galois theory for quartic polynomials

#example[
    Let $char(k) != 2, 3$, $K = k(e_1, e_2, e_3, e_4) subset.eq L = k(x_1, x_2, x_3, x_4)$, so $L$ is splitting field over $K$ of $f(x) = x^4 - e_1 x^3 + e_2 x^2 - e_3 x + x_4$ and $Gal(L\/K) tilde.equiv S_4$.
]
#remark[
    $S_4$ can be visualised as symmetries of regular tetrahedron with vertices labelled ${1, 2, 3, 4}$. Consider three pairs of opposite edges $ P_1 = {(1, 2), (3, 4)}, quad P_2 = {(1, 3), (2, 4)}, quad P_3 = {(1, 4), (2, 3)} $ Any permutation in $S_4$ of the four vertices permutes $P_1$, $P_2$, $P_3$, which gives map $pi: S_4 -> S_3$.
    - $pi$ is surjective group homomorphism.
    - $pi$ has kernel $ker(pi) = {id, (1 thick 2)(3 thick 4), (1 thick 3)(2 thick 4), (1 thick 4)(2 thick 3)} = V_4 tilde.equiv ZZ\/2 times ZZ\/2$.
    - $A_4 subset S_4$ is subgroup of even permutations (orientation-preserving symmetries). Restriction of $pi$ to $A_4$ gives another surjective homomorphism $A_4 -> A_3$ (and $pi^(-1) (A_3) = A_4$) also with kernel $V_4$.
    - $V_4$ is kernel so is normal subgroup of $S_4$ and of $A_4$. Note that $V_4$ is only subgroup of $A_4$ isomorphic to $ZZ\/2 times ZZ\/2$, but there are four subgroups of $S_4$, isomorphic to $ZZ\/2 times ZZ\/2$, with $V_4$ the only normal one.
    - This gives increasing sequence of subgroups in $S_4$ $ {id} subset ZZ\/2 subset V_4 subset A_4 subset S_4 $ and $V_4 tilde.equiv ZZ\/2 times ZZ\/2$, $A_4 \/ V_4 tilde.equiv A_3 tilde.equiv ZZ\/3$, $S_4 \/ A_4 tilde.equiv ZZ\/2$.
    - Each $G_i$ in this sequence is normal subgroup of $G_(i + 1)$ and $G_(i + 1)\/G_i$ is cyclic, meaning that $S_4$ is *solvable (soluble) group*.
    - We have tower $ K = L^(S_4) subset L^(V_4) subset L = L^({e}) $ By fundamental theorem, $Gal(L\/L^(V_4)) = V_4 tilde.equiv ZZ\/2 times ZZ\/2$, so $L\/L^(V_4)$ appears as biquadratic extension.
    - $V_4$ is normal in $S_4$ so by fundamental theorem, $Gal(L^(V_4)\/K) tilde.equiv S_4 \/ V_4 tilde.equiv S_3$ by first isomorphism theorem. Hence $L^(V_4)$ appears as splitting field of a cubic polynomial over $K$.
]
#example("Solving quartic equations")[
    Define $ theta_1 & = 1/2 (x_1 + x_2 - x_3 - x_4), \ theta_2 & = 1/2 (x_1 - x_2 + x_3 - x_4), \ theta_3 & = 1/2 (x_1 - x_2 - x_3 + x_4) $ Then $forall j in [3], forall sigma in V_4$, $sigma (theta_j) = plus.minus theta_j$. The $theta_j$ arise from Lagrange resolvents for the three quadratic subextensions of $L^(V_4)$ in $L$. They behave like $sqrt(2)$, $sqrt(3)$, $sqrt(6)$ in $QQ\(sqrt(2), sqrt(3)\)$. Each $t_i = theta_i^2$ is fixed by $V_4$ and are permuted by $S_4 \/ V_4 tilde.equiv S_3$. They are roots of *cubic resolvent* of $f(x)$: $ (t - t_1)(t - t_2)(t - t_3) = t^3 + s_1 t^2 + s_2 t + s_3 $ which has coefficients in $\(L^(V_4)\)^(S_3) = L^(S_4) = K$. To find roots $x_1, x_2, x_3, x_4$ of $f(x)$:
    - Solve cubic resolvent to find $t_1$, $t_2$, $t_3$.
    - Set $theta_j = plus.minus sqrt(t_j)$ where signs are chosen so that $theta_1 theta_2 theta_3 = (e_1^3 - 4e_1 e_2 + 8 e_3)\/8$.
    - Solve the linear system $
        cases(x_1 + x_2 + x_3 + x_4 & = e_1, x_1 + x_2 - x_3 + x_4 & = 2theta_1, x_1 - x_2 + x_3 - x_4 & = 2theta_2, x_1 - x_2 - x_3 + x_4 & = 2theta_3) quad ==> quad cases(x_1 & = e_1\/4 + (theta_1 + theta_2 + theta_3)\/2, x_2 & = e_1\/4 + (theta_1 - theta_2 - theta_3)\/4, x_3 & = e_1\/4 + (-theta_1 + theta_2 - theta_3)\/2, x_4 & = e_1\/4 + (-theta_1 - theta_2 + theta_3)\/2)
    $
]
#remark[
    In practice, perform shift to kill $x^3$ coefficient to obtain *reduced quartic*: $ f(x - a\/4) = x^4 + p x^2 + q x + r $
    - Cubic resolvent is _(memorise)_ *$ t^3 + 2 p t^2 + (p^2 - 4r)t - q^2 $*
    - Choose $theta_1, theta_2, theta_3$ such that _(memorise)_ *$ theta_1 theta_2 theta_3 = -q $*
    - Roots of $f(x - a\/4)$ are _(memorise)_ *$ x_1 & = 1/2 (theta_1 + theta_2 + theta_3), \ x_2 & = 1/2 (theta_1 - theta_2 - theta_3), \ x_3 & = 1/2 (-theta_1 + theta_2 - theta_3), \ x_4 & = 1/2 (-theta_1 - theta_2 + theta_3) $*
    - Recover roots of $f(x)$ by subtracting $a\/4$.
]
#example[
    Find all complex roots of $f(x) = x^4 + 6x^3 + 18x^2 + 30x + 25$.
    - Eliminate $x^3$ term: $ f(x - 6\/4) = x^4 + 9/2 x^2 + 3x + 85/16 $
    - $p = 9\/2$, $q = 3$, $r = 85\/16$, so cubic resolvent is $ t^3 + 2p t^2 + (p^2 - 4r)t - q^2 = t^3 + 9t^2 - t - 9 = (t - 1)(t + 1)(t + 9) $ So roots are $t_1 = 1$, $t_2 = -1$, $t_3 = -9$. Set $theta_1 = sqrt(t_1) = 1$, $theta_2 = sqrt(t_2) = i$, $theta_3 = plus.minus sqrt(t_3) = plus.minus 3i$ so that $theta_1 theta_2 theta_3 = -q = -3$, i.e. $theta_3 = 3i$.
    - So roots of $f(x - 3\/2)$ are $ x_1 & = 1/2 (theta_1 + theta_2 + theta_3) = 1/2 (1 + 4i), \ x_2 & = 1/2 (theta_1 - theta_2 - theta_3) = 1/2 (1 - 4i), \ x_3 & = 1/2 (-theta_1 + theta_3 - theta_3) = 1/2 (-1 - 2i), \ x_4 & = 1/2 (-theta_1 - theta_2 + theta_3) = 1/2 (-1 + 2i) $
    - So roots of $f(x)$ are $-1 plus.minus 2i$, $-2 plus.minus i$.
]
#example("Galois groups of quartic polynomials")[
    - Let $char(K) != 2, 3$, $f(x) = x^4 + a x^3 + b x^2 + c x + d in K[x]$. Galois group is $G_f = Gal(L\/K)$ where $L$ is splitting field for $f(x)$ over $K$, and $G_f$ is subgroup of $S_4$.
    - Assume that $f(x)$ irreducible in $K[x]$. It can be shown there are five possible isomorphism classes of Galois groups: $S_4, A_4, V_4, ZZ\/4$ or $D_4$.
    - Let $R(t) in K[t]$ be cubic resolvent of $f(x)$ with roots $t_1 = theta_1^2$, $t_2 = theta_2^2$, $t_3 = theta_3^2$. Let $M$ be splitting field of $R(t)$ over $K$, so $ K subset K(t_1, t_2, t_3) subset M subset L = M(theta_1, theta_2, theta_3) $
]
#theorem[
    Let $f(x) in K[x]$ irreducible and have irreducible cubic resolvent $R(t) in K[t]$ with roots $t_1 = theta_1^2$, $t_2 = theta_2^2$, $t_3 = theta_2^3$. Let $L$ be splitting field of $f(x)$ over $K$ (so $G_f = Gal(L\/K)$) and let $M$ be splitting field of $R(t)$ over $K$ (so $G_R = Gal(M\/K)$).
    - If $Delta_R in K^times^2$ (i.e. $G_R tilde.equiv A_3$ and $[M: K] = 3$), then $G_f tilde.equiv A_4$.
    - If $Delta_R in K^times - K^times^2$ (i.e. $G_R tilde.equiv S_3$ and $[M: K] = 6$), then $G_f tilde.equiv S_4$.
]
#proof[
    - Sufficient to prove $[L: M] = 4$ since then $[L: K] = 12$ or $24$ by Tower Law.
    - Show $M$ does not contain $theta_1, theta_2$ or $theta_3$.
        - Suppose it does, so WLOG $theta_1 in M$. $Gal(M\/K) tilde.equiv A_3$ or $S_3$, so must be order 3 element $sigma in Gal(M\/K)$. $sigma(theta_1)$ and $sigma^2 (theta_1)$ are the other two roots $theta_2$ and $theta_3$ since $R(t)$ is irreducible and $theta_1, theta_2, theta_3 in M$. But this implies $M = L$ so $[L: K] = 3$ or $6$, but $4 | [L: K]$ since $L$ contains roots of irreducible quartic.
    - $M(theta_1)\/M$ is degree $2$. Assume $theta_2 in M(theta_1)$. $Gal(M(theta_1)\/M) = {id, tau}$ for some $tau: theta_1 |-> -theta_1$. Also $theta_2^2 in M$ so $tau(theta_2) = plus.minus theta_2$.
        - If $tau(theta_2) = theta_2$, then $theta_2 in M$: contradiction.
        - If $tau(theta_2) = -theta_2$, then $tau(theta_1 theta_2) = (-theta_1)(-theta_2) = theta_1 theta_2$ hence $theta_1 theta_2 in M$. But $theta_1 theta_2 theta_3 in K$ and $theta_1 theta_2 != 0$ since $R(t)$ irreducible. But then $theta_3 in M$: contradiction.
    - Hence $[M(theta_1, theta_2): M] >= 4$, and $theta_1 theta_2 theta_3 in M$ so $L = M(theta_1, theta_2)$ and $[L: M] = 4$.
]
#example[
    - If $f(x) in K[x]$ but cubic resolvent $R(t) in K[t]$ is reducible, it is possible that all roots $t_1 = theta_1^2$, $t_2 = theta_2^2$, $t_3 = theta_3^2$ are in $K$. Then $M = K$ and $L = K(theta_1, theta_2, theta_3)$. Since $theta_1 theta_2 theta_3 in K$, $L\/K$ is obtained by adjoining only two square roots to $K$. Since $f(x)$ irreducible of degree $4$, we have $[L: K] >= 4$, hence only option is biquadratic extension $G_f = Gal(L\/K) = V_4 tilde.equiv ZZ\/2 times ZZ\/2$.
    - If only one root $t_1, t_2, t_3$ is in $K$ (say it is $t_1$):
        - $M$ is splitting field of irreducible quadratic over $K$. Hence $M = K\(sqrt(d)\)$ for some $d in K^times - K^times^2$ and $Gal(M\/K) = {id, phi} tilde.equiv ZZ\/2$ where $phi\(sqrt(d)\) = -sqrt(d)$.
        - We have $ K subset M = K\(sqrt(d)\) = K(alpha, overline(alpha)) subset L = M\(sqrt(alpha), sqrt(overline(alpha))\) $ where $alpha$ and $overline(alpha) = phi(alpha)$ are conjugate elements in $M^times - M^times^2$ (corresponding to $t_2$ and $t_3$).
        - In this case, $L\/K$ is normal extension, since if $alpha, overline(alpha)$ are roots of $x^2 + a x + b in K[x]$, then $plus.minus sqrt(alpha), plus.minus sqrt(overline(alpha))$ are roots of $x^4 + a x^2 + b in K[x]$. So $L$ is splitting field of $x^4 + a x^2 + b$ over $K$. For above tower of fields, we have Galois groups $ {id} subset Gal(L\/M) = H subset Gal(L\/K) = G $ and $G\/H tilde.equiv Gal(M\/K) = {id, phi} tilde.equiv ZZ\/2$.
]
#theorem[
    Let $M = K\(sqrt(d)\)$, $d in.not K^times^2$, $Gal(M\/K) = {id, phi}$. Let $alpha$, $overline(alpha) = phi(alpha) in M^times - M^times^2$, and let $L = M\(sqrt(alpha), sqrt(overline(alpha))\)$, $G = Gal(L\/K)$.
    - If $alpha overline(alpha) in K^times^2$, then $[L: K] = 4$ and $G tilde.equiv ZZ\/2 times ZZ\/2$.
    - If $alpha overline(alpha) in M^times^2 - K^times^2$ then $[L: K] = 4$ and $G tilde.equiv ZZ\/4$.
    - If $alpha overline(alpha) in.not M^times^2$, then $[L: K] = 8$ and $G tilde.equiv D_4$.
]
#note[
    In the case that $C := alpha overline(alpha) in.not M^times^2$ and so $G tilde.equiv D_4$:
    - We have $Gal(M\/K) = {id, phi}$, $phi: sqrt(d) |-> -sqrt(d)$.
    - There are two lifts of $phi$ to $L$: $ tau: \(sqrt(d), sqrt(C), sqrt(alpha)\) & |-> \(-sqrt(d), sqrt(C), sqrt(overline(alpha))\), \ sigma: \(sqrt(d), sqrt(C), sqrt(alpha)\) & |-> \(-sqrt(d), -sqrt(C), sqrt(overline(alpha))) $ (so $tau\(sqrt(overline(alpha))\) = sqrt(alpha)$, $sigma\(sqrt(overline(alpha))\) = -sqrt(alpha)$)
    - Then $G = Gal(L\/K) = ideal(tau, sigma | tau^2 = sigma^4 = e, tau sigma = sigma^3 tau)$.
]

== A criterion for solvability by radicals

#note[
    Assume all fields in this section have characteristic $0$.
]
#definition[
    $L\/K$ is *radical extension* if there is tower of field extensions $ K = K_0 subset dots.h.c subset K_m = L $ where for each $1 <= i <= m$, $K_i = K_(i - 1)(root(n_i, alpha_i))$ with $alpha_i in K_(i - 1)$ and $n_i in NN$.
]
#example[
    Let $alpha = cbrt(2 + root(5, 3 - sqrt(7)))$. We have $ K_0 = QQ subset K_1 = QQ\(sqrt(7)\) subset K_2 = K_1 (root(5, 3 - sqrt(7))) subset K_3 = K_2 (alpha) $
]
#definition[
    $f(x) in K[x]$ is *solvable in radicals* over $K$ if there is a radical extension $L$ of $K$ containing at least one root of $f(x)$.
]
#lemma[
    If $f(x)$ irreducible and solvable in radicals, then all its roots belong to the radical field extension $L$.
]
#definition[
    A finite group $G$ is *solvable (soluble)* if there exists decreasing sequence of subgroups $ G = G_0 supset dots.c supset G_m = {id} $ where for each $1 <= i <= m$, $G_i$ is normal subgroup of $G_(i - 1)$ and $G_(i - 1)\/G_i$ is cyclic.
]
#lemma("Properties of solvable groups")[
    - Every subgroup of finite solvable group is solvable.
    - Abelian groups are solvable.
    - $S_n$ is solvable iff $n <= 4$.
    - Let $G$ finite group with normal subgroup $H$. Then $G$ is solvable iff both $H$ and $G\/H$ are solvable.
]
#theorem("Galois' Theorem: Criterion for solvability in radicals")[
    Let $f(x) in K[x]$ irreducible. Then $f(x)$ is solvable in radicals over $K$ iff Galois group $G_f$ is solvable.
]

== Polynomials not solvable by radicals

#lemma[
    $A_n$ is generated by $3$-cycles $(i med j med k)$.
]
#proof[
    - $A_1 = A_2 = {id}$.
    - For $n >= 3$, any element in $A_n$ is product of even number of transpositions.
    - Combine pairs of transpositions as follows:
        - $(i j)(i j) = id$.
        - $(i j)(i k) = (i k j)$.
        - $(i j)(k l) = (i k)(j k)(j k)(k l) = (i j k)(j k l)$.
]
#theorem[
    For $n >= 5$, $A_n$ and $S_n$ are not solvable.
]
#proof[
    - Assume $A_n$ solvable, so there is decreasing sequence of subgroups $ A_n = G_0 supset dots.c supset G_m = {id} $ with $G_i$ normal in $G_(i - 1)$, $G_(i - 1)\/G_i$ cyclic and so abelian. So we have canonical projection homomorphism $pi: A_n -> Q = A_n\/G_1$, $Q$ is abelian and non-trivial.
    - Let $g = (i_1 i_2 i_3) in A_n$. There are $i_4, i_5 in [n]$ (since $n >= 5$) such that $i_1, i_2, i_3, i_4, i_5$ distinct. Let $g_1 = (i_1 i_2 i_4)$, $g_2 = (i_1 i_3 i_5)$, then $g_1 g_2 g_1^(-1) g_2^(-1) = g$.
    - Since $Q$ abelian, $pi(g) = pi(g_1) pi(g_2) pi(g_1)^(-1) pi(g_2)^(-1) = id$.
    - So $pi$ sends $3$-cycles to $id$, and $A_n$ is generated by $3$-cycles, so $pi(A_n) = {id}$ which is the trivial group: contradiction.
]
#theorem[
    Let $f(x) in QQ[x]$ irreducible polynomial of degree $5$ with exactly $3$ real roots. Then $f(x)$ has Galois group $G_f tilde.equiv S_5$ (and so $f(x)$ is not solvable by radicals over $QQ$).
]