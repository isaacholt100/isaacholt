#import "../../template.typ": *
#show: template

#let ideal(..gens) = $angle.l #gens.pos().join(",") angle.r$
#let pm = $plus.minus$

== Prerequisites

- *Definition*: $I subset R$ is *prime ideal* if $forall a, b in R, a b in I ==> a in I or b in I$.
- *Definition*: ideal $I$ is *maximal* if $I != R$ and there is no ideal $J subset R$ such that $I subset J$.
- *Example*:
    - $p in ZZ$ is prime iff $ideal(p) = p ZZ$ is prime ideal.
    - $ideal(0)$ is prime ideal iff $R$ is integral domain.
- *Lemma*: if $I$ is maximal ideal, then it is prime.
- *Proposition*: for commutative ring $R$, ideal $I$:
    - $I subset R$ is prime ideal iff $R \/ I$ is an integral domain.
    - $I$ is maximal iff $R \/ I$ is field.
- *Proposition*: let $R$ be PID and $a in R$ irreducible. Then $ideal(a) = ideal(a)_R$ is maximal.
- *Theorem*: let $F$ be field, $f(x) in F[x]$ irreducible. Then $F[x] \/ ideal(f(x))$ is a field and a vector space over $F$ with basis $B = \{1, overline(x), ..., overline(x)^(n - 1)\}$ where $n = deg(f)$. That is, every element in $F[x] \/ ideal(f(x))$ can be uniquely written as linear combination $ overline(a_0 + a_1 x + hdots + a_(n - 1) x^(n - 1)), quad a_i in F $

= Divisibility in rings

== Every ED is a PID

- *Definition*: let $R$ integral domain. $phi: R - {0} -> NN_0$ is *Euclidean function (norm)* on $R$ if:
    - $forall x, y in R - {0}, phi(x) <= phi(x y)$.
    - $forall x in R, y in R - {0}, exists q, r in R: x = q y + r$ with either $r = 0$ or $phi(r) < phi(y)$.
    $R$ is *Euclidan domain (ED)* if Euclidean function is defined on it.
- *Example*:
    - $ZZ$ is ED with $phi(n) = |n|$.
    - $F[x]$ is ED for field $F$ with $phi(f) = deg(f)$.
- *Lemma*: $ZZ\[-sqrt(2)\]$ is ED with Euclidean function $ phi\(a + b sqrt(-2)\) = N\(a + b sqrt(-2)\) =: a^2 + 2b^2 $
- *Proposition*: every ED is a PID.

== Every PID is a UFD

- *Definition*: Integral domain $R$ is *unique factorisation domain (UFD)* if every non-zero non-unit in $R$ can be written uniquely (up to order of factors and multiplication by units) as product of irreducible elements in $R$.
- *Example*: let $R = {f(x) in QQ[x]: f(0) in ZZ}$. Its units are $pm 1$. Any factorisation of $x in R$ must be of the form $f(x) g(x)$ where $deg f = 1, deg g = 0$, so $x = (a x + b)c$, $a in QQ$, $b, c in ZZ$. We have $b c = 0$ and $a c = 1$ hence $x = x / c dot.op c$. So $x$ irreducible if $c != pm 1$. Also, any factorisation of $x / c$ in $R$ is of the form $x / c = x / (c d) dot.op d$, $d in ZZ$, $d != 0$. Again, neither factor is a unit when $d != pm 1$. So $x = x / c dot.op c = x / (c d) dot.op c dot.op c = hdots$ can never be decomposed into irreducibles (the first factor is never irreducible).
- *Lemma*: let $R$ be PID. Then every irreducible element is prime in $R$.
- *Theorem*: every PID is a UFD.
- *Example*: $ZZ[sqrt(-2)]$ so by the above theorem it is a UFD. Let $x, y in ZZ$ such that $y^2 + 2 = x^3$.
    - $y$ must be odd, since if $y = 2a, a in ZZ$ then $x = 2b, b in ZZ$ but then $2a^2 + 1 = 4b^3$.
    - $y pm sqrt(-2)$ are relatively prime: if $a + b sqrt(-2)$ divides both, then it divides their difference $2 sqrt(-2)$, so norm $a^2 + 2b^2 | N(2 sqrt(-2)) = 8$. Only possible case is $a = pm 1, b = 0$ so $a + b sqrt(-2)$ is unit. Other cases $a = 0, b = pm 1$, $a = pm 2, b = 0$ and $a = 0, b = pm 2$ are impossible since $y$ not even.
    - If $a + b sqrt(-2)$ is unit, $exists x, y in ZZ: (a + b sqrt(-2)) (x + y sqrt(-2)) = 1$. If $b != 0$ then $(-a^2 - 2b^2)y = 1 ==> b = 0$: contradiction. If $b = 0$, $a = pm 1$.

= Finite field extensions

- *Definition*: let $F$, $L$ fields. If $F subset.eq L$ and $F$ and $L$ share the same operations then $F$ is a *subfield* of $L$ and $L$ is *field extension* of $F$ (denoted $L \/ F$). $L$ is vector space over $F$:
    - $0 in L$ (zero vector).
    - $u, v in L ==> u + v in L$ (additivity).
    - $a in F, u in L ==> a u in L$ (scalar multiplication).
- *Definition*: let $L \/ F$ field extension. *Degree* of $L$ over $F$ is dimension of $L$ as vector space over $F$: $ [L: F] := dim_F (L) $ If $[L: F]$ finite, $L \/ F$ is *finite field extension*.
- *Example*: $QQ\(sqrt(-2)\) = \{a + b sqrt(-2): a, b in QQ\}$ is isomorphic as a vector space to $QQ^2$ so is $2$-dimensional vector space over $QQ$. Isomorphism is $a + b sqrt(-2) <--> (a, b)$. Standard basis $\{e_1, e_2\}$ in $QQ^2$ corresponds to the basis $\{1, sqrt(-2)\}$ in $QQ\(sqrt(-2)\)$. $\[QQ\(sqrt(-2)\): QQ\] = 2$.
- *Example*: $[CC: RR] = 2$ (a basis is ${1, i}$). $[RR: QQ]$ is not finite, due to the existence of transcendental numbers (if $alpha$ transcendental, then $\{1, alpha, alpha^2, ...\}$ is linearly independent).
- *Definition*: let $L \/ F$ field extension. $alpha in L$ is *algebraic* over $F$ if $ exists f(x) in F[x]: f(alpha) = 0 $ If all elements in $L$ are algebraic, then $L \/ F$ is *algebraic field extension*.
- *Example*: $i in CC$ is algebraic over $RR$ since $i$ is root of $x^2 + 1$. $CC \/ RR$ is algebraic since $z = a + b i$ is root of $(x - z)(x - overline(z)) = x^2 - 2a x + a^2 + b^2$.
- *Proposition*: if $L \/ F$ is finite field extension then it is algebraic.
- *Definition*: let $L \/ F$ field extension, $alpha in L$ algebraic over $F$. *Minimal polynomial* $p_alpha (x) = p_(alpha, F) (x)$ of $alpha$ over $F$ is the monic polynomial $f$ of smallest degree such that $f(alpha) = 0$. *Degree* of $alpha$ over $F$ is $deg(p_alpha)$.
- *Proposition*: $p_alpha (x)$ is unique and irreducible. Also, if $f(x) in F[x]$ is monic, irreducible and $f(alpha) = 0$, then $f = p_alpha$.
- *Example*:
    - $p_(i, RR)(x) = p_(i, QQ)(x) = x^2 + 1$, $p_(i, QQ(i))(x) = x - i$.
    - Let $alpha = root(7, 5)$. $f(x) = x^7 - 5$ is minimal polynomial of $alpha$ over $QQ$, as it is irreducible by Eisenstein's criterion with $p = 5$ and the above proposition.
    - Let $alpha = e^(2pi i\/p)$, $p$ prime. $alpha$ is algebraic as root of $x^p - 1$ which isn't irreducible as $x^p - 1 = (x - 1) Phi(x)$ where $Phi(x) = (x^(p - 1) + hdots + 1)$. $Phi(alpha) = 0$ since $alpha != 1$, $Phi(x)$ is monic and $Phi(x + 1) = ((x + 1)^p - 1)\/x$ irreducible by Eisenstein's criterion with $p = p$, hence $Phi(x)$ irreducible. So $p_alpha (x) = Phi(x)$.

== Fields generated by elements

- *Definition*: let $L\/F$ field extension, $alpha in L$. The *field generated by $alpha$ over $F$* is the smallest subfield of $L$ containing $F$ and $alpha$: $ F(alpha) := sect.big_(K "field", \ F subset.eq K subset.eq L, \ alpha in K) K $ Generally, $F(alpha_1, ..., alpha_n)$ is smallest field extension of $F$ containing $alpha_1, ..., alpha_n$.
- We have $F(alpha_1, ..., alpha_n) = F(alpha_1) hdots (alpha_n)$ (show $F(alpha, beta) subset.eq F(alpha)(beta)$ and $F(alpha)(beta) subset.eq F(alpha, beta)$ by minimality and use induction).
- *Definition*: $F[alpha] = \{sum_(i = 0)^n a_i alpha^i: a_i in F, n in NN\} = {f(alpha): f(x) in F[x]}$.
- *Lemma*: let $L\/F$ field extension, $alpha in L$ algebraic over $F$. Then $F[alpha]$ is field, hence $F(alpha) = F[alpha]$.
- *Lemma*: let $alpha$ algebraic over $F$. Then $[F(alpha): F] = deg(p_alpha)$.
- *Definition*: let $K\/F$ and $L\/K$ field extensions, then $F subset.eq K subset.eq L$ is *tower of fields*.\
- *Tower theorem*: let $F subset.eq K subset.eq L$ tower of fields. Then $ [L: F] = [L: K] dot.op [K: F] $
- *Example*: let $L = QQ\(sqrt(2), sqrt(3)\)$. Show $[L: QQ] = 4$.
    - Let $K = QQ\(sqrt(2)\)$. Let $sqrt(3) = a + b sqrt(2)$, $a, b in QQ$ so $3 = a^2 + 2b^2 + 2a b sqrt(2)$. So $0 in {a, b}$, otherwise $sqrt(2) in QQ$. But if $a = 0$, then $sqrt(6) = 2b in QQ$, if $b = 0$ then $sqrt(3) = a in QQ$: contradiction. So $x^2 - 3$ has no roots in $K$ so is irreducible over $K$ so $p_(sqrt(3), K)(x) = x^2 - 3$.
    - So $[L: K] = 2$ so by the tower theorem, $[L: QQ] = [L: K] dot.op [K: QQ] = 4$.

== Norm and trace

- Let $L\/F$ finite field extension, $n = [L: F]$. For any $alpha in L$, there is $F$-linear map $ hat(alpha): L --> L, quad x |-> alpha x $
- With basis $\{alpha_1, ..., alpha_n\}$ of $L$ over $F$, let $T_alpha = T_(alpha, L\/F) in M_n (F)$ be the corresponding matrix of the linear map $alpha$ with respect to the basis $\{alpha_i\}$: $ hat(alpha)(alpha_1) & = alpha alpha_1 = a_(1, 1) alpha_1 + hdots + a_(1, n) alpha_n, \ & thick dots.v \ hat(alpha)(alpha_n) & = alpha alpha_n = a_(n, 1) alpha_1 + hdots + alpha_(n, n) alpha_n $ with $a_(i, j) in F$, $T_alpha = (a_(i, j))$, so $alpha$ is eigenvalue of $T_alpha$: $ alpha vec(alpha_1, dots.v, alpha_n) = T_alpha vec(alpha_1, dots.v, alpha_n) $
- *Definition*: *norm* of $alpha$ is $ N_(L\/F)(alpha) := det(T_alpha) $
- *Definition*: *trace* of $alpha$ is $ tr_(L\/F)(alpha) := tr(T_alpha) $
- *Remark*: norm and trace are independent of choice of basis so are well-defined (uniquely determined by $alpha$).
- *Example*: let $L = QQ(sqrt(m))$, $m in ZZ$ non-square, let $alpha = a + b sqrt(m) in L$. Fix basis $\{1, sqrt(m)\}$. Now $ hat(alpha)(1) & = alpha dot.op 1 = a + b sqrt(m), \ hat(alpha)(sqrt(m)) & = alpha sqrt(m) = b m + a sqrt(m), \ T_alpha & = mat(a, b; b m, a) $ So $N_(L\/F)(alpha) = a^2 - b^2 m$, $tr_(L\/F)(alpha) = 2a$.
- *Lemma*: the map $L -> M_n (F)$ given by $alpha |-> T_alpha$ is injective ring homomorphism. So if $f(x) in F[x]$, $ T_(f(alpha)) = f(T_alpha) $ ($f(T_alpha)$ is a polynomial in $T_alpha$, not $f$ applied to each entry).
- *Proposition*: let $L\/F$ finite field extension. $forall alpha, beta in L$,
  - $N_(L\/F)(alpha) = 0 <==> alpha = 0$.
  - $N_(L\/F)(alpha beta) = N_(L\/F)(alpha) N_(L\/F)(beta)$.
  - $forall a in F, N_(L\/F)(a) = a^([L: F])$ and $tr_(L\/F)(a) = [L: F] alpha$.
  - $forall a, b in F, tr_(L\/F)(a alpha + b beta) = a tr_(L\/F)(alpha) + b tr_(L\/F)(beta)$ (so $tr_(L\/F)$ is $F$-linear map).

== Characteristic polynomials

- Let $A in M_n (F)$, then characteristic polynomial is $chi_A (x) = det(x I - A) in F[x]$ and is monic, $deg(chi_A) = n$. If $chi_A (x) = x^n + sum_(i = 0)^(n = 1) c_i x^i$ then $det(A) = (-1)^n det(0 - A) = (-1)^n chi_A (0) = (-1)^n c_0$ and $tr(A) = -c_(n - 1)$, since if $alpha_1, ..., alpha_n$ are eigenvalues of $A$ (in some field extension of $F$), then $tr(A) = alpha_1 + hdots + alpha_n$, $chi_A (x) = (x - alpha_1) hdots (x - alpha_n) = x^n - (alpha_1 + hdots alpha_n) x^(n - 1) + hdots$.
- For finite extension $L\/F$, $n = [L: F]$, $alpha in L$, *characteristic polynomial* $chi_alpha (x) = chi_(alpha, L\/F)(x)$ is characteristic polynomial of $T_alpha$. So $N_(L\/F)(alpha) = (-1)^n c_0$, $tr_(L\/F)(alpha) = -c_(n - 1)$. By the Cayley-Hamilton theorem, $chi_alpha (T_alpha) = 0$ so $T_(chi_alpha (alpha)) = chi_alpha (T_alpha) = 0$, where $chi_alpha (x) = x^n + c_(n - 1) x^(n - 1) + hdots + c_0$. Since $alpha -> T_alpha$ is injective, $chi_alpha (alpha) = 0$.
- *Lemma*: let $L\/F$ finite extension, $alpha in L$ with $L = F(alpha)$. Then $chi_alpha (x) = p_alpha (x)$.
- *Proposition*: let $F subset.eq F(alpha) subset.eq L$, let $m = [L: F(alpha)]$. Then $chi_alpha (x) = p_alpha (x)^m$.
- *Corollary*: let $L\/F$, $alpha in L$ as above, $p_alpha (x) = x^d + a_(d - 1) x^(d - 1) + hdots + a_0$, $a_i in F$. Then $ N_(L\/F)(alpha) = (-1)^(m d) a_0^m, quad tr_(L\/F)(alpha) = -m a_(d - 1) $

= Algebraic number fields and algebraic integers

== Algebraic numbers

- *Definition*: $alpha in CC$ is *algebraic number* if algebraic over $QQ$.
- *Definition*: $K$ is *(algebraic) number field* if $QQ subset.eq K subset.eq CC$ and $[K: QQ] < oo$.
- Every element of an algebraic number field is an algebraic number.
- *Example*: let $theta = sqrt(2) + sqrt(3)$, then $QQ(theta) subset.eq QQ\(sqrt(2), sqrt(3)\)$ but also $theta^3 = 11 sqrt(2) + 9 sqrt(3)$ so $ sqrt(2) = (theta^3 - 9 theta)/2, quad sqrt(3) = (-theta^3 + 11 theta)/2 $ so $QQ\(sqrt(2), sqrt(3)\) subset.eq QQ(theta)$ hence $QQ\(sqrt(2), sqrt(3)\) = QQ(theta)$.
- *Simple extension theorem*: every number field $K$ has form $K = QQ(theta)$ for some $theta in K$.
- Set of all algebraic numbers (union of all number fields) is denoted $overline(QQ)$ and is a field, since if $alpha != 0$ algebraic over $QQ$, $[QQ(alpha): QQ] = deg(p_alpha) < oo$ so $QQ(alpha)\/QQ$ algebraic, so $-alpha, alpha^(-1) in QQ(alpha)$ algebraic, so $alpha^(-1), -alpha in overline(QQ)$, and if $alpha, beta in overline(QQ)$ then $QQ(alpha, beta) = QQ(alpha)(beta)$ is finite extension of $QQ$ by tower theorem so $alpha + beta$, $alpha beta in QQ(alpha, beta)$ so are algebraic.
- $\[overline(QQ): QQ\] = oo$ since if $\[overline(QQ): QQ\] = d in NN$ then every algebraic number would have degree $<= d$, but $root(d + 1, 2)$ has degree $d + 1$ since it is a root of $x^(d + 1) - 2$ which is irreducible by Eisenstein's criterion with $p = 2$.
- *Definition*: let $alpha in overline(QQ)$. *Conjugates* of $alpha$ are roots of $p_alpha (x)$ in $CC$.
- *Example*:
    - Conjugate of $a + b i in QQ(i)$ is $a - b i$.
    - Conjugate of $a + b sqrt(2) in QQ\(sqrt(2)\)$ is $a - b sqrt(2)$.
    - Conjugates of $theta$ do not always lie in $QQ(theta)$, e.g. for $theta = root(3, 2)$, $p_theta (x) = x^3 - 2$ has two non-real roots not in $QQ(theta) subset RR$.
- *Notation*: when base field is $QQ$, $N_K$ and $tr_K$ denote $N_(K\/QQ)$ and $tr_(K\/QQ)$.
- *Lemma*: let $K\/QQ$ number field, $alpha in K$, $alpha_1, ..., alpha_n$ conjugates of $alpha$. Then $ N_K (alpha) = (alpha_1 thin hdots thin alpha_n)^([K: QQ(alpha)]), quad tr_K (alpha) = (alpha_1 + hdots + alpha_n) [K: QQ(alpha)] $

== Algebraic integers

- *Definition*: $alpha in overline(QQ)$ is *algebraic integer* if it is root of a monic polynomial in $ZZ[x]$. The set of algebraic integers is denoted $overline(ZZ)$. If $K\/QQ$ is number field, set of algebraic integers in $K$ is denoted $cal(O)_K$, $alpha in cal(O)_K$ is called *integer in $K$*.
- *Example*: $i, (1 + sqrt(3))\/2 in overline(ZZ)$ since they are roots of $x^2 + 1$ and $x^2 - x + 1$ respectively.
- *Theorem*: let $alpha in overline(QQ)$. The following are equivalent:
    - $alpha in overline(ZZ)$.
    - $p_alpha (x) in ZZ[x]$.
    - $ZZ[alpha] = \{sum_(i = 0)^(d - 1) a_i alpha^i: a_i in ZZ\}$ where $d = deg(p_alpha)$.
    - There exists non-trivial finitely generated abelian additive subgroup $G subset CC$ such that $ alpha G subset.eq G "i.e." forall g in G, alpha g in G $ ($alpha g$ is complex multiplication).
- *Remark*:
    - For third statement, generally we have $ZZ[alpha] = {f(alpha: f(x) in ZZ[x])}$ and in this case, $ZZ[alpha] = {f(alpha): f(x) in ZZ[x], deg(f) < d}$.
    - Fourth statement means that $ G = {a_1 gamma_1 + hdots + a_r gamma_r: a_i in ZZ} = gamma_1 ZZ + hdots + gamma_r ZZ = ideal(gamma_1, ..., gamma_r)_ZZ $ $G$ is typically $ZZ[alpha]$. E.g. if $alpha = sqrt(2)$, $ZZ\[sqrt(2)\]$ is generated by $1, sqrt(2)$ and $sqrt(2) dot.op ZZ\[sqrt(2)\] subset.eq ZZ\[sqrt(2)\]$.
- *Proposition*: $overline(ZZ)$ is a ring. Also, for every number field $K$, $cal(O)_K$ is a ring.
- *Lemma*: let $alpha in overline(ZZ)$. For every number field $K$ with $alpha in K$, $ N_K (alpha) in ZZ, quad tr_K (alpha) in ZZ $
- *Lemma*: let $K$ number field. Then $ K = {alpha / m: alpha in cal(O)_K, m in ZZ, m != 0} $
- *Lemma*: let $alpha in overline(ZZ)$, $K$ number field, $alpha in K$. Then $ alpha in cal(O)_K^times <==> N_K (alpha) = plus.minus 1 $

== Quadratic fields and their integers

- *Definition*: $d in ZZ$ is *squarefree* if $d in.not {0, 1}$ and there is no prime $p$ such that $p^2 | d$.
- *Definition*: $K = QQ\(sqrt(d)\)$ is a *quadratic field* if $d$ is squarefree. If $d > 0$ then it is *real quadratic*. If $d < 0$ it is *imaginary quadratic*.
- *Proposition*: let $K\/QQ$ have degree $2$. Then $K = QQ\(sqrt(d)\)$ for some squarefree $d in ZZ$.
- *Lemma*: let $K = QQ\(sqrt(d)\)$, $d equiv 1 thick (mod 4)$. Then $ ZZ\[ (1 + sqrt(d))/2 \] = {(r + s sqrt(d))/2: r, s in ZZ, r equiv s thick (mod 2)} $
- *Theorem*: let $K = QQ\(sqrt(d)\)$ quadratic field, then $ cal(O)_K = cases(ZZ\[sqrt(d)\] & "if" d equiv.not 1 thick (mod 4), ZZ\[ (1 + sqrt(d))/2\] & "if" d equiv 1 thick (mod 4)) $

= Units in quadratic rings

- *Notation*: in this section, let $K = QQ\(sqrt(d)\)$ be quadratic number field, $d in ZZ - {0}$, $|d|$ is not a square. Let $cal(O)_d = cal(O)_K$. Let $overline(a + b sqrt(d)) = a - b sqrt(d)$. The map $x -> overline(x)$ is a $QQ$-automorphism from $K$ to $K$.
- *Definition*: $S$ is *quadratic number ring of $K$* if $S = cal(O)_d$ or $S = ZZ\[sqrt(d)\]$.
- We have $ alpha in S^times ==> exists x in S: alpha x = 1 ==> N_K (alpha) N_K (x) = 1 ==> N_K (alpha) = plus.minus 1 $ and for $alpha in S - ZZ$, since $[QQ(alpha): QQ] = 2$ and so $[K: QQ(alpha)] = 1$ by the Tower Theorem, $ N_K (alpha) = plus.minus 1 ==> alpha overline(alpha) = plus.minus 1 ==> alpha in S^times $ So $alpha in S^times <==> N_K (alpha) = plus.minus 1$.
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

- *Remark*: if $alpha = a + b sqrt(d)$ is unit in $ZZ\[sqrt(d)\]$, $a, b > 0$, then $N_K (alpha) = alpha overline(alpha) = plus.minus 1$, so $ |overline(alpha)| = |a - b sqrt(d)| = (|N_K (alpha)|)/(|alpha|) = 1/(|alpha|) < 1/(b sqrt(d)) < 1/b $ Define $ A = {alpha = a + b sqrt(d): a, b in NN_0, |overline(alpha)| < 1/b} $
- *Lemma*: $|A| = oo$.
- *Lemma*: if $alpha in A$, then $|N_K (alpha)| < 1 + 2 sqrt(d)$.
- *Lemma*: $exists alpha = a + b sqrt(d), alpha' = a' + b' sqrt(d) in A: alpha > alpha'$, $|N_K (alpha)| = |N_K (alpha')| =: n$ and $ alpha equiv alpha' thick (mod n), quad b equiv b' thick (mod n) $
- *Lemma*: there exists a unit $u$ in $ZZ\[sqrt(d)\]$ such that $u > 1$.
- *Lemma*: let $0 != alpha = a + b sqrt(d) in QQ\(sqrt(d)\)$. Then $alpha > sqrt(|N_K (alpha)|)$ iff $a, b > 0$.

== Computing fundamental units

- *Theorem*: let $d > 1$ non-square.
    - If $S = ZZ\[sqrt(d)\]$ and $a + b sqrt(d) in S^times$, $a, b > 0$ such that $b$ is minimal, then $a + b sqrt(d)$ is the fundamental unit in $S$.
    - If $S = ZZ\[ (1 + sqrt(d))/2 \]$ (so $d equiv 1 thick (mod 4)$), then
        - $(1 + sqrt(5))/2$ is the fundamental unit in $cal(O)_5$.
        - If $d > 5$ and $(s + t sqrt(d))/2 in cal(O)_d^times$ with $s, t > 0$ such that $t$ is minimal, then $(s + t sqrt(d))/2$ is the fundamental unit in $cal(O)_d$.
- *Remark*: both $u = (1 + sqrt(5))/2$ and $u^2 = (3 + sqrt(5))/2$ have $t$ minimal (equal to $1$), which is why a separate case is needed for $d = 5$.
- *Example*:
    - $1 + sqrt(2)$ is fundamental unit in $ZZ\[sqrt(2)\] = cal(O)_2$, since $N_K (1 + sqrt(2)) = -1$ so is a unit, and here $b = 1$, so is minimal (as $b > 0$).
    - $2 + sqrt(5)$ is the fundamental unit in $ZZ\[sqrt(5)\]$ (since $b = 1$ is minimal) but is not the fundamental unit in $cal(O)_5$.
- *Example*: find fundamental unit in $cal(O)_7$. $7 equiv.not 1 thick (mod 4)$ so $cal(O)_7 = ZZ\[sqrt(7)\]$. $a + b sqrt(7)$ is a unit iff $a^2 - 7b^2 = plus.minus 1$. Also, by the above theorem, it is the fundamental unit if $a, b > 0$ and $b$ is minimal. We use trial and error: for each $b = 1, 2, ..., $ check whether $7b^2 plus.minus 1$ is a square #align(center)[#table(
  columns: (auto, auto, auto, auto),
  inset: 6pt,
  align: center,
  [$b$], [$7b^2 - 1$], [$7b^2 + 1$], [$a^2$],
  $1$, $6$, $8$, $-$,
  $2$, $27$, $29$, $-$,
  $3$, $62$, $64$, $64 = 8^2$,
)] So the unit with minimal $b$ such that $a, b > 0$ is $8 + 3 sqrt(7)$, so is the fundamental unit.

== Pell's equation and norm equations

- *Definition*: *Pell's equation* is $x^2 - d y^2 = 1$ for nonsquare $d$, where solutions are $x, y in ZZ$. Since LHS is norm of $x + y sqrt(d)$, solutions are given by $x + y sqrt(d) in ZZ\[sqrt(d)\]$ with norm $1$.
- *Example*: consider $x^2 - 2y^2 = plus.minus 1$. Fundamental unit in $ZZ\[sqrt(2)\]$ is $u = 1 + sqrt(2)$, with norm $-1$. So if $x + y sqrt(2) in ZZ\[sqrt(2)\]$ is such that $N_(ZZ\(sqrt(2)\))(x + y sqrt(2)) = 1$, then $x + y sqrt(2)$ is an even power of $u$. Thus elements of norm $plus.minus 1$ are $ plus.minus u^(2n) thick ("RHS" = 1), quad plus.minus u^(2n + 1) thick ("RHS" = -1) $ To extract solutions $x, y$, note that if $x + y sqrt(2) = plus.minus u^r$, then $x - y sqrt(2) = plus.minus overline(u)^r$, hence $ x = plus.minus (u^r + overline(u)^r)/2, quad y = plus.minus (u^r - overline(u)^r)/(2 sqrt(2)) $ Solutions when RHS $= 1$ are given by even $r$, solutions when RHS $= -1$ are given by odd $r$.
- *Example*: consider $x^2 - 75 y^2 = 1$. $75 = 3 dot.op 5^2$ is not square-free, so rewrite as $ x^2 - 3z^2 = 1 $ where $z = 5y$. Fundamental unit in $ZZ\[sqrt(3)\]$ is $u = 2 + sqrt(3)$ of norm $1$ so solutions are $ x = plus.minus (u^n + overline(u)^n)/2, quad z = plus.minus (u^n - overline(u)^n)/(2 sqrt(3)), quad n in ZZ $ To get solution for $(x, y)$, we need $5 | z$ (which doesn't always hold). Note that $ u^2 = 7 + 4 sqrt(3) in.not ZZ\[sqrt(75)\] = ZZ\[5 sqrt(3)\], quad u^3 = 26 + 3 sqrt(75) in ZZ\[sqrt(75)\] $ Thus when $n = 2$, $(x, z)$ is not solution, but is when $n = 3$, and hence when $n = 3k$ for $k in ZZ$: $ x = plus.minus (u^(3k) + overline(u)^(3k))/2, quad y = plus.minus (u^(3k) - overline(u)^(3k))/(5 dot.op 2 sqrt(3)), quad k in ZZ $ $u^(3k + 1)$ and $u^(3k + 2)$ never give solutions, since if $u^(3k + 1) in ZZ\[sqrt(75)\]$, then $u in ZZ\[sqrt(75)\]$ (since $u^(-3k) in ZZ\[sqrt(75)\]$). Similarly, if $u^(3k + 2) in ZZ\[sqrt(75)\]$, then $u^2 in ZZ\[sqrt(75)\]$: contradiction. Note $ZZ\[sqrt(75)\] subset ZZ\[sqrt(3)\]$ and any unit in $ZZ\[sqrt(75)\]$ is unit in $ZZ\[sqrt(3)\]$, so is $plus.minus u^r$ for some $r in ZZ$. So by taking powers of $u$, eventually we find the fundamental unit in $ZZ\[sqrt(75)\]$ (as it will be smallest unit $> 1$ assuming we increment powers from $1$).


#let jack = false

#show: a => if jack { smallcaps(a) } else { a }

= Discriminants and integral bases

== Discriminant of an $n$-tuple


- *Definition*: let $K$ number field of degree $n$. *Discriminant* of $gamma = (gamma_1, ..., gamma_n) in K^n$ is $ Delta_K (gamma) := det(Q(gamma)) $ where $Q(gamma) = \(tr_K \(gamma_i gamma_j\)\)_(1 <= i, j <= n) in M_n (QQ)$.
- *Example*: let $K = QQ\(sqrt(d)\)$, $d != 1$ squarefree. $
gamma & = \(1, sqrt(d)\) ==> Q(gamma) = mat(2, 0; 0, 2d) ==> Delta_K (gamma) = 4d \
gamma & = \(1, (1 + sqrt(d))/2) ==> Q(gamma) = mat(2, 1; 1, (1 + d)/2) ==> Delta_K (gamma) = d
$
- *Proposition*:
    - $Delta_K (gamma) in QQ$ and if every $gamma_i in cal(O)_K$, then $Delta_K (gamma) in ZZ$.
    - Let $M in M_n (QQ)$, then $Delta_K (M gamma) = det(M)^2 Delta_K (gamma)$.
    - $Delta_K (gamma)$ is invariant under permutations of $gamma_1, ..., gamma_n$.
- *Lemma*: let $theta_1, ..., theta_n in CC$, let $ D = mat(1, theta_1, ..., theta_1^(n - 1); dots.v, dots.v, dots.down, dots.v; 1, theta_n, ..., theta_n^(n - 1)) $ then $ det(D) = (-1)^binom(n, 2) product_(1 <= r < s <= n) (theta_r - theta_s) $
- *Theorem*: let $K = QQ(theta)$ be number field. Let $theta_1, ..., theta_n$ be roots of $p_theta (x)$, let $gamma = (1, ..., theta^(n - 1))$. Then $
Delta_K (gamma) = product_(1 <= i < j <= n) \(theta_i - theta_j\)^2 = (-1)^binom(n, 2) product_(i = 1)^n p'_theta (theta_i) = (-1)^binom(n, 2) N_K (p'_theta (theta))
$
- *Example*:
    - Let $K = QQ\(sqrt(d)\)$, $d$ square-free, $theta = (1 + sqrt(d))/2$, then $ Delta_K ((1, theta)) = ((1 + sqrt(d))/2 - (1 - sqrt(d))/2)^2 = d $
    - Let $theta = sqrt(d)$, so $p_theta (x) = x^2 - d$, $p'_theta (x) = 2x$, so $ Delta_K (1, theta) = (-1)^binom(2, 2) N_K (2 theta) = -4 N_k (theta) = 4d $
    - Let $theta = root(d, 3)$, so $p_theta (x) = x^3 - d$, $p'_theta (x) = 3x^2$ so $ Delta_K (1, theta, theta^2) = (-1)^binom(3, 2) N_K (3 theta^2) = -27 d^2 $
    - Let $theta$ be root of $p_theta (x) = x^3 - x + 2$, so $p'_theta (x) = 3x^2 - 1$. $ Delta_K (1, theta, theta^2) = (-1)^binom(3, 2) N_K (3 theta^2 - 1) $ Now $theta^3 = theta - 2$ so $ N_K (3 theta^2 - 1) = (N_K (2) N_K (theta - 3))/(N_K (theta)) = 8/2 N_K (3 - theta) = 4(3 - theta_1)(3 - theta_2)(3 - theta_3) = 4 p_theta (3) = 104 $ so $Delta_K (1, theta, theta^2) = -104$. Note: in general, this method doesn't work, and generally we have to compute matrix $T_theta$ and $det(f(T_theta))$. *As a generalisation*, $ N_(QQ(theta)) (a - b theta) = b^n p_theta (a\/b) $
- *Lemma*:
    - Roots $theta_1, ..., theta_n$ of $p_theta (x)$ are distinct.
    - $forall f in QQ[x], tr_K (f(theta)) = sum_(i = 1)^n f(theta_i)$.
    - $forall f in QQ[x], N_K (f(theta)) = product_(i = 1)^n f(theta_i)$.
- *Proposition*: let $K = QQ(theta)$ number field. Then $Delta_K (gamma) != 0$ iff $gamma$ is $QQ$-basis of $K$.

== Full lattices and integral bases

- *Definition*: let $A$ subgroup of $QQ$-vector space $V$. $A$ is *full lattice* in $V$ if there are $gamma_1, ..., gamma_n in V$ such that
    - ${gamma_1, ..., gamma_n}$ is basis for $V$.
    - $A = {a_1 gamma_i + dots.h.c + a_n gamma_n: a_i in ZZ}$ (i.e. $gamma_1, ..., gamma_n$ generate $A$ as a group). Note $a_1, ..., a_n$ are uniquely determined for each $a in A$.
    ${gamma_1, ..., gamma_n}$ is *generating basis* for $A$.
- *Example*: let $K = QQ(theta)$, $theta in cal(O)_K$, $[K: QQ] = n$, then $ZZ[theta]$ has generating basis ${1, ..., theta^(n - 1)}$ and is full lattice in $K$.
- *Example*: $ZZ$, $ZZ\[sqrt(2)\/2\]$ are not full lattices in $QQ\(sqrt(2)\)$.
- *Proposition*: let $K$ number field. Every non-zero ideal $I subset.eq cal(O)_K$ is full lattice in $K$.
- *Definition*: generating basis for $cal(O)_K$ is *integral basis* for $K$.
- *Example*: let $K = QQ\(sqrt(d)\)$, then an integral basis for $K$ is $\{1, sqrt(d)\}$ if $d equiv.not 1 mod 4$, $\{1, \(1 + sqrt(d)\)\/2\}$ if $d equiv 1 mod 4$.
- *Theorem*: if $V$ is $QQ$-vector space, $dim(V) = n$, and $B subset A subset V$, $A$ and $B$ full lattices, ${beta_1, ..., beta_n}$ is generating basis for $B$, ${alpha_1, ..., alpha_n}$ is generating basis for $A$, where $beta = M alpha$, $M in M_n (ZZ)$, then
    - $|A\/B| = |det(M)|$ (in particular, $A\/B$ is finite)
    - If $V = K$ is number field, these satisfy *index-discriminant formula*: $Delta_K (B) = |A\/B|^2 Delta_K (A)$.
    (Note $M$ exists since $alpha$ is generating basis for $A$ so spans $B$ over $ZZ$).
- *Lemma*: if $A subset K$ is full lattice and ${gamma_1, ..., gamma_n}$, ${delta_1, ..., delta_n}$ are generating bases for $A$, then $Delta_K (gamma_1, ..., gamma_n) = Delta_K (delta_1, ..., delta_n)$. We define discriminant of $A$ to be $Delta_K (A) = Delta_K (gamma_1, ..., gamma_n)$ for any generating basis ${gamma_1, ..., gamma_n}$.
- *Definition*: *disciminant* of number field $K$ is $ Delta_K = Delta_K (cal(O)_K) = Delta_K (gamma_1, ..., gamma_n) $ for any integral basis ${gamma_1, ..., gamma_n}$.

== When is $R = ZZ[theta]$?

- *Proposition*: if $S subset.eq cal(O)_K$ is full lattice in $K = QQ(theta)$, ${gamma_1, ..., gamma_n}$ is generating basis for $S$, and $p$ prime, $p | |cal(O)_K\/S|$, then
    - $p^2 | Delta_K (S)$
    - There exists $alpha = m_1 gamma_1 + dots.h.c + m_n gamma_n in S$, $m_i in ZZ$, such that $alpha\/p in cal(O)_K - S$ and $ cases(0 <= |m_i| < p\/2 & "if" p "is odd", m_i in {0, 1} & "if" p = 2) $
- *Example*: if $K = QQ\(sqrt(d)\)$, $ Delta_K = cases(4d & "if" d equiv.not 1 mod 4, d & "if" d equiv 1 mod 4) $
- *Example*: let $theta$ be root of $x^3 + 4x + 1$, $K = QQ\(theta\)$. We have $ZZ[theta] subset.eq cal(O)_K$ and $Delta_K (ZZ[theta]) = Delta_K (1, theta, theta^2) = 281 = |cal(O)_K \/ ZZ[theta]|^2 Delta_K (cal(O)_K)$. As 281 is squarefree, $|cal(O)_K \/ ZZ[theta]| = 1$ so $cal(O)_K = ZZ[theta]$.
- *Example*: let $K = QQ(theta)$, $theta = root(3, 5)$. let $R = cal(O)_K$, $S = ZZ[theta]$. $Delta_K (S) = -3^3 dot.op 5^2$. If $p$ prime and $p | |R\/S|$, then $p in {3, 5}$ and there is $alpha = a + b theta + c theta^2$ such that $alpha\/p in R - S$, $|a|, |b|, |c| < p\/2$. Note $alpha != 0$, as otherwise $alpha in S$.
    - If $5 | |R\/S|$, then $|a|, |b|, |c| in {0, 1, 2}$. Then $tr_(K\/QQ)(alpha\/5) = 3a\/5 in ZZ$ so $5 | a$ so $a = 0$. $theta alpha = c + (b theta^2)\/5 in cal(O)_K$ so $(b theta^2)\/5 in cal(O)_K$ so $ N_K ((b theta^2)\/5) = (N_K (b) N_K (theta)^2)/(N_K (5)) = b^3 / 5 in ZZ $ so $5 | b$, so $b = 0$. Finally, $ N_K (alpha/5) = N_K ((c theta^2)/5) = (c^3 (-5)^2)/5^3 = c^3/5 in ZZ ==> c = 0 $ Contradiction.
    - If $3 | |R\/S|$, then $|a|, |b|, |c| in {0, 1}$ and can assume $a >= 0$ (by possibly multiplying by $-1$). Then $ N_K ((a + b theta + c theta^2) / 3) in ZZ ==> a^3 + 5b^3 + 25c^3 - 15a b c equiv 0 (mod 3^3) $ If $a = 0$, then $5b^3 + 25c^3 equiv 2b + c equiv 0 (mod 3)$ (as $b, c in {0, 1, -1}$), so if $b = 0$, then $c equiv 0 (mod 3) ==> c = 0$: contradiction. So $b = 1$ (by possibly multiplying by $-1$) hence $c = 1$. But then $ N_K (alpha\/3) = N_K ((theta + theta^2)/3) = (N_K (theta) N_K (1 + theta))/3^3 = (5 dot.op 6)/27 in.not ZZ $ Contradiction. If $a = 1$, then $ 1 + 5b^3 + 25c^3 equiv 1 + 2b + c equiv 0 (mod 3) $ which also leads to a contradiction.
    - So $5 divides.not |R\/S|$, $3 divides.not |R\/S|$, so $|R\/S| = 1$, so $ZZ[theta] = cal(O)_K$.

= Unique factorisation of ideals

- *Definition*: *product* of ideals $I, J subset.eq R$ is $ I J := {sum_(i = 1)^k x_i y_i: k in NN, x_i in I, y_i in J} $ If $I = ideal(a_1, ..., a_m)$, $J = (b_1, ..., b_n)$ then $ I J = ideal(a_i b_j | i in [m], j in [n]) $
- *Definition*: $I$ *divides* $J$, $I | J$, if there is ideal $K$ such that that $I K = J$.
- *Note*: _to divide is to contain_: $I | J ==> J subset.eq I$.
- *Example*: let $R = ZZ\[sqrt(-6)\]$, $I = ideal(5, 1 + 3 sqrt(-6))$, $J = (5, 1 - 3 sqrt(-6))$, then $ I J = ideal(25, 5\(1 + 3 sqrt(-6)\), 5\(1 - 3 sqrt(-6)\), 55) subset.eq ideal(5) $ But also $5 = 55 - 2 dot.op 25 in I$, $ideal(5) subset.eq I J$, so $I J = ideal(5)$.
- *Lemma*: let $I, J$ ideals, $P$ prime ideal. Then $ I J subset.eq P <==> (I subset.eq P or J subset.eq P) $
- *Example*: $ideal(5, 1 + 3 sqrt(-6)) subset ZZ\[sqrt(-6)\]$ is prime: define $phi: ZZ\[sqrt(-6)\] -> FF_5$, $phi\(a + b sqrt(-6)\) = a - 2b$. $phi$ is surjective homomorphism. Also, $5, 1 + 3 sqrt(-6) in ker(phi)$, and $ a + b sqrt(-6) in ker(phi) & ==> b equiv 3a mod 5 \ & ==> \(a + b sqrt(-6)\) - a\(1 + 3 sqrt(-6)\) = (b - 3a) sqrt(-6) in ideal(5) $ so $ker(phi) = \(5, 1 + 3 sqrt(-6)\)$. So by first isomorphism theorem, $R\/ideal(5, 1 + sqrt(-6)) tilde.equiv FF_5$ which is field, so $ideal(5, 3 + sqrt(-6))$ is maximal, so prime.
- *Definition*: let $K$ number field, $R = cal(O)_K$. *Fractional ideal* of $R$ is subset of $K$ of the form $ lambda I = {lambda x: x in I} $ where $ideal(0) != I subset.eq R$ and $lambda in K^times$. If $I = R$, $lambda I$ is *principal fractional ideal*. Set of fractional ideals in $R$ is denoted $cal(I)(R)$, set of principal fractional ideals is dented $cal(P)(R)$.
- *Example*:
    - $n/m ZZ$ is fractional ideal in $QQ$ for all $m, n in ZZ - {0}$.
    - Every non-zero ideal is fractional ideal (take $lambda = 1$).
    - If $lambda I$ is fractional ideal, then $lambda^(-1) lambda I = I$ is ideal.
- *Definition*: a fractional ideal $A$ is *invertible* if there is fractional ideal $B$ such that $A B = cal(O)_K$. $B$ is the *inverse* of $A$. The invertible fractional ideals form a group.
- *Example*: in $ZZ\[sqrt(-6)\] = cal(O)_K$, $ideal(5, 1 + 3 sqrt(-6)) ideal(5, 1 - 3 sqrt(-6)) = ideal(5)$ so $ ideal(5, 1 + 3 sqrt(-6)) dot.op 1/5 ideal(5, 1 - 3 sqrt(-6)) = cal(O)_K $ so inverse of $ideal(5, 1 + 3 sqrt(-6))$ is $1/5 ideal(5, 1 - 3 sqrt(-6))$.
- *Definition*: the *class group* of $K$ is the quotient group $F\/P$ where $F$ is abelian group of fractional ideals of $K$, $P$ is subgroup of principal fractional ideals of $K$.