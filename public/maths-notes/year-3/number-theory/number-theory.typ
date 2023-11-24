#import "../../template.typ": template
#show: template

#let ideal(..gens) = $angle.l #gens.pos().join(",") angle.r$
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
- *Lemma*: $ZZ[-sqrt(2)]$ is an ED with Euclidean function with $ phi(a + b sqrt(-2)) = N(a + b sqrt(-2)) =: a^2 + 2b^2 $
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
- *Example*: let $L = QQ(sqrt(2), sqrt(3))$. Show $[L: QQ] = 4$.
    - Let $K = QQ(sqrt(2))$. Let $sqrt(3) = a + b sqrt(2)$, $a, b in QQ$ so $3 = a^2 + 2b^2 + 2a b sqrt(2)$. So $0 in {a, b}$, otherwise $sqrt(2) in QQ$. But if $a = 0$, then $sqrt(6) = 2b in QQ$, if $b = 0$ then $sqrt(3) = a in QQ$: contradiction. So $x^2 - 3$ has no roots in $K$ so is irreducible over $K$ so $p_(sqrt(3), K)(x) = x^2 - 3$.
    - So $[L: K] = 2$ so by the tower theorem, $[L: QQ] = [L: K] dot.op [K: QQ] = 4$.

== Norm and trace

- Let $L\/F$ finite field extension, $n = [L: F]$. For any $alpha in L$, there is $F$-linear map $ hat(alpha): L -> L, quad x -> alpha x $
- With basis ${alpha_1, ..., alpha_n}$ of $L$ over $F$, then let $T_alpha = T_(alpha, L\/F) in M_n (F)$ be the corresponding matrix of the linear map $alpha$ with respect to the basis ${a_i}$: $ hat(alpha)(alpha_1) & = alpha alpha_1 = a_(1, 1) alpha_1 + dots.h.c + a_(1, n) alpha_n, \ & dots.v \ hat(alpha)(alpha_n) & = alpha alpha_n = a_(n, 1) alpha_1 + dots.h.c + alpha_(n, n) alpha_n $ with $a_(i, j) in F$, $T_alpha = (a_(i, j))$, i.e. $ alpha vec(alpha_1, dots.v, alpha_n) = T_alpha vec(alpha_1, dots.v, alpha_n) $
- *Definition*: *norm* of $alpha$ is $ N_(L\/F)(alpha) := det(T_alpha) $
- *Definition*: *trace* of $alpha$ is $ tr_(L\/F)(alpha) := tr(T_alpha) $
- *Remark*: norm and trace are independent of choice of basis so are well-defined (uniquely determined by $alpha$).
- *Example*: let $L = QQ(sqrt(m))$, $m in ZZ$ non-square, let $alpha = a + b sqrt(m)$, $a, b in QQ$. Fix basis ${1, sqrt(m)}$. Now $ hat(alpha)(1) & = alpha dot.op 1 = a + b sqrt(m), \ hat(alpha)(sqrt(m)) & = alpha sqrt(m) = b m + a sqrt(m), \ T_alpha & = mat(a, b; b m, a) $ So $N_(L\/F)(alpha) = a^2 - b^2 m$, $tr_(L\/F)(alpha) = 2a$.
- *Lemma*: the map $L -> M_n (F)$ given by $alpha -> T_alpha$ is injective ring homomorphism. So if $f(x) in F[x]$, $T_(f(alpha)) = f(T_alpha)$ ($f(T_alpha)$ is a polynomial in $T_alpha$, not $f$ applied to each entry).
- *Proposition*: let $L\/F$ finite field extension. $forall alpha, beta in L$,
  - $N_(L\/F)(alpha) = 0 <==> alpha = 0$.
  - $N_(L\/F)(alpha beta) = N_(L\/F)(alpha) N_(L\/F)(beta)$.
  - $forall a in F, N_(L\/F)(a) = a^([L: F])$ and $tr_(L\/F)(a) = [L: F] alpha$.
  - $forall a, b in F, tr_(L\/F)(a alpha + b beta) = a tr_(L\/F)(alpha) + b tr_(L\/F)(beta)$ (hence $tr_(L\/F)$ is $F$-linear map).

== Characteristic polynomials

- Let $A in M_n (F)$, then characteristic polynomial is $chi_A (x) = det(x I - A) in F[x]$ and is monic, $deg(chi_A) = n$. If $chi_A (x) = x^n + sum_(i = 0)^(n = 1) c_i x^i$ then $det(A) = (-1)^n det(0 - A) = (-1)^n chi_A (0) = (-1)^n c_0$ and $tr(A) = -c_(n - 1)$, since if $alpha_1, ..., alpha_n$ are eigenvalues of $A$ (in some field extension of $F$), then $tr(A) = alpha_1 + dots.h.c + alpha_n$, $chi_A (x) = (x - alpha_1) dots.h.c (x - alpha_n) = x^n - (alpha_1 + dots.h.c alpha_n) x^(n - 1) + dots.h.c$.
- For finite field extension $L\/F$, $n = [L: F]$, $alpha in L$, *characteristic polynomial* $chi_alpha (x) = chi_(alpha, L\/F)(x)$ is characterstic polynomial of $T_alpha$. So $N_(L\/F)(alpha) = (-1)^n c_0$, $tr_(L\/F)(alpha) = -c_(n - 1)$. By the Cayley-Hamilton theorem, $chi_alpha (T_alpha) = 0$ so $T_(chi_alpha (alpha)) = chi_alpha (T_alpha) = 0$. Since $alpha -> T_alpha$ is injective, $chi_alpha (alpha) = 0$.
- *Lemma*: let $L\/F$ finite field extension, $alpha in L$ with $L = F(alpha)$. Then $chi_alpha (x) = p_alpha (x)$.
- *Proposition*: consider tower $F subset.eq F(alpha) subset.eq L$, let $m = [L: F(alpha)]$. Then $chi_alpha (x) = p_alpha (x)^m$.
- *Corollary*: let $L\/F$, $alpha in L$ as above, $p_alpha (x) = x^d + a_(d - 1) x^(d - 1) + dots.h.c + a_0$, $a_i in F$. Then $ N_(L\/F)(alpha) = (-1)^(m d) a_0^m, quad tr_(L\/F)(alpha) = -m a_(d - 1) $

= Algebraic number fields and algebraic integers

== Algebraic numbers

- *Definition*: $alpha in CC$ is *algebraic number* if algebraic over $QQ$.
- *Definition*: $K$ is *(algebraic) number field* if $Q subset.eq K subset.eq CC$ and $[K: QQ] < oo$.
- Every element of an algebraic number field is an algebraic number.
- *Example*: let $theta = sqrt(2) + sqrt(3)$, then $QQ(theta) subset.eq QQ\(sqrt(2), sqrt(3)\)$ but also $theta^3 = 11 sqrt(2) + 9 sqrt(3)$ so $ sqrt(2) = (theta^3 - 9 theta)/2, quad sqrt(3) = (-theta^3 + 11 theta)/2 $ so $QQ\(sqrt(2), sqrt(3)\) subset.eq QQ(theta)$ hence $QQ\(sqrt(2), sqrt(3)\) = QQ(theta)$.
- *Simple extension theorem*: every number field $K$ has form $K = QQ(theta)$ for some $theta in K$.
- Set of all algebraic numbers (union of all number fields) is denoted $overline(QQ)$ and is a field, since if $alpha != 0$ algebraic over $QQ$, $[QQ(alpha): QQ] = deg(p_alpha) < oo$ so $QQ(alpha)\/QQ$ algebraic, so $-alpha, alpha^(-1) in QQ(alpha)$ algebraic, so $alpha^(-1), -alpha in overline(QQ)$, and if $alpha, beta in overline(QQ)$ then $QQ(alpha, beta) = QQ(alpha)(beta)$ is finite extension of $QQ$ by tower theorem so $alpha + beta$, $alpha beta in QQ(alpha, beta)$ so are algebraic.
- $[overline(QQ): QQ] = oo$ since if $[overline(QQ): QQ] = d in NN$ then every algebraic number would have degree $<= d$, but $root(d + 1, 2)$ has degree $d + 1$ since it is a root of $x^(d + 1) - 2$ which is irreducible by Eisenstein's criterion with $p = 2$.
- *Definition*: let $alpha in overline(QQ)$. *Conjugates* of $alpha$ are roots of $p_alpha (x)$ in $CC$.
- *Example*:
    - Conjugate of $a + b i in QQ(i)$ is $a - b i$.
    - Conjugate of $a + b sqrt(2) in QQ\(sqrt(2)\)$ is $a - b sqrt(2)$.
    - Conjugates of $theta$ do not always lie in $QQ(theta)$, e.g. for $theta = root(3, 2)$, $p_theta (x) = x^3 - 2$ has two non-real roots not in $QQ(theta) subset RR$.
- *Notation*: when base field is $QQ$, $N_K$ and $tr_K$ denote $N_(K\/QQ)$ and $tr_(K\/QQ)$.
- *Lemma*: let $K\/QQ$ number field, $alpha in K$, $alpha_1, ..., alpha_n$ conjugates of $alpha$. Then $ N_K (alpha) = (alpha_1 thin dots.h.c thin alpha_n)^([K: QQ(alpha)]), quad tr_K (alpha) = (alpha_1 + dots.h.c + alpha_n) [K: QQ(alpha)] $

== Algebraic integers

- *Definition*: $alpha in overline(QQ)$ is *algebraic integer* if it is root of a monic polynomial in $ZZ[x]$. The set of algebraic integers is denoted $overline(ZZ)$. If $K\/QQ$ is number field, set of algebraic integers in $K$ is denoted $cal(O)_K$.
- *Example*: $i, (1 + sqrt(3))\/2 in overline(ZZ)$ since they are roots of $x^2 + 1$ and $x^2 - x + 1$ respectively.
- *Theorem*: let $alpha in overline(QQ)$. The following are equivalent:
    - $alpha in overline(ZZ)$.
    - $p_alpha (x) in ZZ[x]$.
    - $ZZ[alpha] = {sum_(i = 0)^(d - 1) a_i alpha^i: a_i in ZZ}$ where $d = deg(p_alpha)$.
    - There exists non-trivial finitely generated abelian additive subgroup $G subset CC$ such that $ alpha G subset.eq G "i.e." forall g in G, alpha g in G $ ($alpha g$ is complex multiplication).
- *Remark*:
    - For third statement, generally we have $ZZ[alpha] = {f(alpha: f(x) in ZZ[x])}$ and in this case, $ZZ[alpha] = {f(alpha): f(x) in ZZ[x], deg(f) < d}$.
    - Fourth statement means that $ G = {a_1 gamma_1 + dots.h.c + a_r gamma_r: a_i in ZZ} = gamma_1 ZZ + dots.h.c + gamma_r ZZ = ideal(gamma_1, ..., gamma_r)_ZZ $ $G$ is typically $ZZ[alpha]$. E.g. if $alpha = sqrt(2)$, $ZZ\[sqrt(2)\]$ is generated by $1, sqrt(2)$ and $sqrt(2) dot.op ZZ\[sqrt(2)\] subset.eq ZZ\[sqrt(2)\]$.
- *Proposition*: $overline(ZZ)$ is a ring. Also, for every number field $K$, $cal(O)_K$ is a ring.
- *Lemma*: let $alpha in overline(ZZ)$. For every number field $K$ with $alpha in K$, $ N_K (alpha) in ZZ, quad tr_K (alpha) in ZZ $
- *Lemma*: let $K$ number field. Then $ K = {alpha / m: alpha in cal(O)_K, m in ZZ, m != 0} $
- *Lemma*: let $alpha in overline(ZZ)$, $K$ number field, $alpha in K$. Then $ alpha in cal(O)_K^times <==> N_K (alpha) = plus.minus 1. $

== Quadratic fields and their integers

- *Definition*: $d in ZZ$ is *squarefree* if $d in.not {0, 1}$ and there is no prime $p$ such that $p^2 | d$.
- *Definition*: $K = QQ\(sqrt(d)\)$ is a *quadratic field* if $d$ is squarefree. If $d > 0$ then it is *real quadratic*. If $d < 0$ it is *imaginary quadratic*.
- *Proposition*: let $K\/QQ$ have degree $2$. Then $K = QQ\(sqrt(d)\)$ for some squarefree $d in ZZ$.
- *Lemma*: let $K = QQ\(sqrt(d)\)$, $d equiv 1 thick (mod 4)$. Then $ ZZ\[ (1 + sqrt(d))/2 \] = {(r + s sqrt(d))/2: r, s in ZZ, r equiv s thick (mod 2)} $
- *Theorem*: let $K = QQ\(sqrt(d)\)$ quadratic field, then $ cal(O)_K = cases(ZZ\[sqrt(d)\] & "if" d equiv.not 1 thick (mod 4), ZZ\[ (1 + sqrt(d))/2\] & "if" d equiv 1 thick (mod 4)) $

= Units in quadratic rings

- *Notation*: in this section, let $K = QQ\(sqrt(d)\)$ be quadratic number field, $d in ZZ - {0}$, $|d|$ is not a square. Let $cal(O)_d = cal(O)_K$. Let $overline(a + b sqrt(d)) = a - b sqrt(d)$. The map $x -> overline(x)$ is a $QQ$-automorphism from $K$ to $K$.
- *Definition*: $S$ is *quadratic number ring of $K$* if $S = cal(O)_d$ or $S = ZZ\[sqrt(d)\]$.
- We have $ alpha in S^times ==> exists x in S: alpha x = 1 ==> N_K (alpha) N_K (x) = 1 ==> N_K (alpha) = plus.minus 1 $ and for $alpha in S - ZZ$, since $[QQ(alpha): QQ] = 2$ and so $[K: QQ(alpha)] = 1$ by the Tower Theorem, $ N_K (alpha) = plus.minus 1 ==> alpha overline(alpha) = plus.minus 1 ==> alpha in S^times $
- *Theorem*: to determine the group of units for imaginary quadratic fields:
    - \
        - For $d < -1$, $ZZ\[sqrt(d)\]^times = {plus.minus 1}$.
        - $cal(O)_(-1)^times = ZZ[i]^times = {plus.minus 1, plus.minus i}$.
    - \
        - For $d equiv 1 thick (mod 4)$ and $d < -3$, $ZZ\[ (1 + sqrt(d))/2\]^times = {plus.minus 1}$.
        - $ZZ\[ (1 + sqrt(-3))/2\]^times = {plus.minus 1, plus.minus omega, plus.minus omega^2}$ where $omega = (1 + sqrt(-3))/2 = e^(pi i\/3)$.
- *Main theorem*: let $d > 1$, $d$ non-square, $S$ be quadratic number ring of $K = QQ\(sqrt(d)\)$ (i.e. $S = cal(O)_d$ or $S = ZZ\[sqrt(d)\]$). Then
    - $S$ has a smallest unit $u > 1$ (smaller than all units except $1$).
    - $S^times = {plus.minus u^r: r in ZZ} = ideal(-1, u)$.
- *Definition*: the smallest unit $u > 1$ above is the *fundamental unit* of $S$ (or of $K$, in the case $S = cal(O)_d$).

== Proof of the main theorem

- *Remark*: if $alpha = a + b sqrt(d)$ is unit in $ZZ\[sqrt(d)\]$, $a, b > 0$, then $N_K (alpha) = alpha overline(alpha) = plus.minus 1$, so $ |overline(alpha)| = |a - b sqrt(d)| = (|N_K (alpha)|)/(|alpha|) = 1/(|alpha|) < 1/(b sqrt(d)) < 1/b $ Define $ A = {alpha = a + b sqrt(d): a, b in NN_0, |overline(alpha)| < 1/b} $ If $alpha$ is a unit, then one of $plus.minus alpha, plus.minus overline(alpha)$ has $a, b >= 0$, so $A$ is non-empty.
- *Lemma*: $|A| = oo$.
- *Lemma*: if $alpha in A$, then $|N_K (alpha)| < 1 + 2 sqrt(d)$.
- *Lemma*: $exists alpha = a + b sqrt(d), alpha' = a' + b' sqrt(d) in A: alpha > alpha'$, $|N_K (alpha)| = |N_K (alpha')| =: n$ and $ alpha equiv alpha' thick (mod n), quad b equiv b' thick (mod n) $
