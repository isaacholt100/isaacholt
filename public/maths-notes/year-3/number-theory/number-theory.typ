#import "../../template.typ": template
#show: template

#let ideal(gens) = $angle.l #gens angle.r$

== Prerequisites

- $I subset R$ is an ideal if $forall (a, b) in RR^2, a b in I ==> a in I or b in I$.
- $I$ is maximal if $I != R$ and there is no ideal $J subset R$ such that $I subset J$.
- $p in ZZ$ is prime iff $ideal(p) = ideal(p)_ZZ$ is a prime ideal.
- For commutative ring $R$:
    - $I subset R$ is prime ideal iff $R \/ I$ is an integral domain.
    - $I$ is maximal iff $R \/ I$ is a field.
- Let $R$ be PID and $a in R$ irreducible. Then $ideal(a) = ideal(a)_R$ is maximal.
- *Theorem*: let $F$ be field, $f(x) in F[x]$ irreducible. Then $F[x] \/ ideal(f(x))$ is a field and a vector space over $F$ with basis $B = {1, overline(x), ..., overline(x)^(n - 1)}$ where $n = deg(f)$. That is, every element in $F[x] \/ ideal(f(x))$ can be uniquely written as a linear combination $ a_0 + a_1 overline(x) + dots.h.c + a_(n - 1) overline(x)^(n - 1) $

= Divisibility in rings

== Every ED is a PID

- *Definition*: let $R$ integral domain. $phi: R - {0} -> NN_0$ is *Euclidean function (norm)* on $R$ if:
    - $forall x, y in R - {0}, phi(x) <= phi(x y)$.
    - $forall x in R, y in R - {0}, exists q, r in R: x = q y + r$ with either $r = 0$ or $phi(r) < phi(y)$.
- $R$ is *Euclidan domain (ED)* if a Euclidean function is defined on it.
- Examples of EDs:
    - $ZZ$ with $phi(n) = |n|$.
    - $F[x]$ for field $F$ with $phi(f) = deg(f)$.
- *Lemma*: $ZZ[-sqrt(2)]$ is an ED with Euclidean function with $ phi(a + b sqrt(-2)) = N(a + b sqrt(-2)) =: a^2 + 2b^2. $
- *Proposition*: every ED is a PID.

== Every PID is a UFD

- *Definition*: Integral domain $R$ is *unique factorisation domain (UFD)* if every non-zero non-unit in $R$ can be written uniquely (up to order of factors and multiplication by units) as product of irreducible elements in $R$.
- *Example*: let $R = {f(x) in QQ[x]: f(0) in ZZ}$. Its units are $plus.minus 1$. Any factorisation of $x in R$ must be of the form $f(x) g(x)$ where $deg f = 1, deg g = 0$, so $x = (a x + b)c$, $a in QQ$, $b, c in ZZ$. We have $b c = 0$ and $a c = 1$ hence $x = x / c dot.op c$. So $x$ irreducible if $c != plus.minus 1$. Also, any factorisation of $x / c$ in $R$ is of the form $x / c = x / (c d) dot.op d$, $d in ZZ$, $d != 0$. Again, neither factor is a unit when $d != plus.minus 1$. So $x = x / c dot.op c = x / (c d) dot.op c dot.op c = dots.h.c$ can never be decomposed into irreducibles (the first factor is never irreducible).
- *Lemma*: let $R$ be PID. Then every irreducible element is prime in $R$.
- *Theorem*: every PID is a UFD.