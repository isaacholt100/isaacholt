#import "../../template.typ": template
#show: template

#let ideal(gens) = $angle.l #gens angle.r$
#let pm = $plus.minus$

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
- *Example*: let $R = {f(x) in QQ[x]: f(0) in ZZ}$. Its units are $pm 1$. Any factorisation of $x in R$ must be of the form $f(x) g(x)$ where $deg f = 1, deg g = 0$, so $x = (a x + b)c$, $a in QQ$, $b, c in ZZ$. We have $b c = 0$ and $a c = 1$ hence $x = x / c dot.op c$. So $x$ irreducible if $c != pm 1$. Also, any factorisation of $x / c$ in $R$ is of the form $x / c = x / (c d) dot.op d$, $d in ZZ$, $d != 0$. Again, neither factor is a unit when $d != pm 1$. So $x = x / c dot.op c = x / (c d) dot.op c dot.op c = dots.h.c$ can never be decomposed into irreducibles (the first factor is never irreducible).
- *Lemma*: let $R$ be PID. Then every irreducible element is prime in $R$.
- *Theorem*: every PID is a UFD.
- *Example*: $ZZ[sqrt(-2)]$ so by the above theorem it is a UFD. Let $x, y in ZZ$ such that $y^2 + 2 = x^3$.
    - $y$ must be odd, since if $y = 2a, a in ZZ$ then $x = 2b, b in ZZ$ but then $2a^2 + 1 = 4b^3$.
    - $y pm sqrt(-2)$ are relatively prime: if $a + b sqrt(-2)$ divides both, then it divides their difference $2 sqrt(-2)$, so norm $a^2 + 2b^2 | N(2 sqrt(-2)) = 8$. Only possible case is $a = pm 1, b = 0$ so $a + b sqrt(-2)$ is unit. Other cases $a = 0, b = pm 1$, $a = pm 2, b = 0$ and $a = 0, b = pm 2$ are impossible since $y$ not even.
    - If $a + b sqrt(-2)$ is unit, $exists x, y in ZZ: (a + b sqrt(-2)) (x + y sqrt(-2)) = 1$. If $b != 0$ then $(-a^2 - 2b^2)y = 1 ==> b = 0$: contradiction. If $b = 0$, $a = pm 1$.

= Finite field extensions

- *Definition*: let $F$, $L$ fields. If $F subset.eq L$ and $F$ and $L$ share the same operations then $F$ is a *subfield* of $L$ and $L$ is *field extension* of $F$ (denoted $L \/ F$), and $L$ is vector space over $F$ with
    - $0 in L$ (zero vector).
    - $u, v in L ==> u + v in L$ (additivity).
    - $a in F, u in L ==> a u in L$ (scalar multiplication).
- *Definition*: let $L \/ F$ field extension. *Degree* of $L$ over $F$ is dimension of $L$ as vector space over $F$: $ [L: F] := dim_F (L) $ If $[L: F]$ finite, $L \/ F$ is *finite field extension*.
- *Example*: $QQ(sqrt(-2)) = {a + b sqrt(-2): a, b in QQ}$ is isomorphic as a vector space to $QQ^2$ so is $2$-dimensional vector space over $QQ$. Isomorphism is $a + b sqrt(-2) <--> (a, b)$. Standard basis ${e_1, e_2}$ in $QQ^2$ corresponds to the basis ${1, sqrt(-2)}$ in $QQ(sqrt(-2))$. $[QQ(sqrt(-2)): QQ] = 2$.
- *Example*: $[CC: RR] = 2$ (a basis is ${1, i}$). $[RR: QQ]$ is not finite, due to the existence of transcendental numbers (if $alpha$ transcendental, then ${1, alpha, alpha^2, ...}$ is linearly independent).
- *Definition*: let $L \/ F$ field extension. $alpha in L$ is *algebraic* over $F$ if $ exists f(x) in F[x]: f(alpha) = 0 $ If all elements in $L$ are algebraic, then $L \/ F$ is *algebraic field extension*.
- *Example*: $i in CC$ is algebraic over $RR$ since $i$ is root of $x^2 + 1$. $CC \/ RR$ is algebraic since $z = a + b i$ is root of $(x - z)(x - overline(z))$.
- *Proposition*: if $L \/ F$ is finite field extension then it is algebraic.
- *Definition*: let $L \/ F$ field extension, $alpha in L$ algebraic. *Minimal polynomial* $p_alpha (x) = p_(alpha, F) (x)$ of $alpha$ over $F$ is the monic polynomial $f$ of smallest degree such that $f(alpha) = 0$.
- *Proposition*: $p_alpha (x)$ is unique and irreducible. Also, if $f(x) in F[x]$ is monic, irreducible and $f(alpha) = 0$, then $f = p_alpha$.
- *Example*:
    - $p_(i, RR)(x) = p_(i, QQ)(x) = x^2 + 1$, $p_(i, QQ(i))(x) = x - i$.
    - Let $alpha = root(7, 5)$. $f(x) = x^7 - 5$ is minimal polynomial of $alpha$ over $QQ$, as it is irreducible by Eisenstein's criterion with $p = 5$ and the above proposition.
    - Let $alpha = e^(2pi i\/p)$, $p$ prime. $alpha$ is algebraic as root of $x^p - 1$ which isn't irreducible as $x^p - 1 = (x - 1) Phi(x)$ where $Phi(x) = (x^(p - 1) + dots.h.c + 1)$. $Phi(alpha) = 0$ since $alpha != 1$, $Phi(x)$ is monic and $Phi(x + 1) = ((x + 1)^p - 1)\/x$ irreducible by Eisenstein's criterion with $p = p$, hence $Phi(x)$ irreducible. So $p_alpha (x) = Phi(x)$.

== Fields generated by elements

- *Definition*: let $L\/F$ field extension, $alpha in L$. The *field generated by $alpha$ over $F$* is the smallest subfield of $L$ containing $F$ and $alpha$: $ F(alpha) = sect.big_(K "field", \ F subset.eq K subset.eq L, \ alpha in K) K $ Generally, $F(alpha_1, ..., alpha_n)$ is smallest field extension of $F$ containing $alpha_1, ..., alpha_n$
- We have $F(alpha_1, ..., alpha_n) = F(alpha_1) dots.h.c (alpha_n)$ (show $F(alpha, beta) subset.eq F(alpha)(beta)$ and $F(alpha)(beta) subset.eq F(alpha, beta)$ by minimality and use induction).
- *Definition*: $F[alpha] = \{sum_(i = 0)^n a_i alpha^i: a_i in F, n in NN\} = {f(alpha): f(x) in F[x]}$.
- *Lemma*: let $L\/F$ field extension, $alpha in L$ algebraic over $F$. Then $F[alpha]$ is field, hence $F(alpha) = F[alpha]$.
- *Lemma*: let $alpha$ algebraic over $F$. Then $[F(alpha): F] = deg(p_alpha)$.
- *Definition*: let $K\/F$ and $L\/K$ field extensions, then $F subset.eq K subset.eq L$ are *tower of fields*.\
- *Tower theorem*: let $F subset.eq K subset.eq L$ tower of fields. Then $ [L: F] = [L: K] dot.op [K: F] $