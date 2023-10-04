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