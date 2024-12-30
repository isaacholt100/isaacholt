#import "../../template.typ": *
#show: doc => template(doc, hidden: ("proof",), slides: false)

// FIND: - \*(\w+)\*: ([\s\S]*?)(?=\n-|\n\n)\n
// REPLACE: #$1[\n    $2\n]\n

#let ideal(..gens) = $angle.l #gens.pos().join(",") angle.r$
#let pm = $plus.minus$
#let Cl = $op("Cl")$

== Prerequisites

#definition[
    $I subset R$ is *prime ideal* if $forall a, b in R, a b in I ==> a in I or b in I$.
]
#definition[
    Ideal $I$ is *maximal* if $I != R$ and there is no ideal $J subset R$ such that $I subset J$.
]
#example[
    - $p in ZZ$ is prime iff $ideal(p) = p ZZ$ is prime ideal.
    - $ideal(0)$ is prime ideal iff $R$ is integral domain.
]
#lemma[
    If $I$ is maximal ideal, then it is prime.
]
#proposition[
    For commutative ring $R$, ideal $I$:
    - $I subset R$ is prime ideal iff $R \/ I$ is an integral domain.
    - $I$ is maximal iff $R \/ I$ is field.
]
#proposition[
    Let $R$ be PID and $a in R$ irreducible. Then $ideal(a) = ideal(a)_R$ is maximal.
]<ideals-generated-by-irreducible-elements-in-PIDs-are-maximal>
#theorem[
    Let $F$ be field, $f(x) in F[x]$ irreducible. Then $F[x] \/ ideal(f(x))$ is a field and a vector space over $F$ with basis $B = \{1, overline(x), ..., overline(x)^(n - 1)\}$ where $n = deg(f)$. That is, every element in $F[x] \/ ideal(f(x))$ can be uniquely written as linear combination $ overline(a_0 + a_1 x + cdots + a_(n - 1) x^(n - 1)), quad a_i in F $
]

= Divisibility in rings

== Every ED is a PID

#definition[
    Let $R$ integral domain. $phi: R - {0} -> NN_0$ is *Euclidean function (norm)* on $R$ if:
    - $forall x, y in R - {0}, phi(x) <= phi(x y)$.
    - $forall x in R, y in R - {0}, exists q, r in R: x = q y + r$ with either $r = 0$ or $phi(r) < phi(y)$.
    $R$ is *Euclidean domain (ED)* if Euclidean function is defined on it.
]
#example[
    - $ZZ$ is ED with $phi(n) = |n|$.
    - $F[x]$ is ED for field $F$ with $phi(f) = deg(f)$.
]
#lemma[
    $ZZ\[-sqrt(2)\]$ is ED with Euclidean function $ phi\(a + b sqrt(-2)\) = N\(a + b sqrt(-2)\) := a^2 + 2b^2 $
]
#proposition[
    Every ED is a PID.
]

== Every PID is a UFD

#definition[
    Integral domain $R$ is *unique factorisation domain (UFD)* if every non-zero non-unit in $R$ can be written uniquely (up to order of factors and multiplication by units) as product of irreducible elements in $R$.
]
#example[
    Let $R = {f(x) in QQ[x]: f(0) in ZZ}$. Its units are $pm 1$. Any factorisation of $x in R$ must be of the form $f(x) g(x)$ where $deg f = 1, deg g = 0$, so $x = (a x + b)c$, $a in QQ$, $b, c in ZZ$. We have $b c = 0$ and $a c = 1$ hence $x = x / c dot.op c$. So $x$ is not irreducible if $c != pm 1$. Also, any factorisation of $x / c$ in $R$ is of the form $x / c = x / (c d) dot.op d$, $d in ZZ$, $d != 0$. Again, neither factor is a unit when $d != pm 1$. So $x = x / c dot.op c = x / (c d) dot.op d dot.op c = cdots$ can never be decomposed into irreducibles (the first factor is never irreducible).
]
#lemma[
    Let $R$ be PID. Then every irreducible element is prime in $R$.
]<irreducible-elements-in-PIDs-are-prime>
#theorem[
    Every PID is a UFD.
]
#example[
    $ZZ\[sqrt(-2)\]$ is ED so by the above theorem it is a UFD. Let $x, y in ZZ$ such that $y^2 + 2 = x^3$.
    - $y$ must be odd, since if $y = 2a, a in ZZ$ then $x = 2b, b in ZZ$ but then $2a^2 + 1 = 4b^3$.
    - $y pm sqrt(-2)$ are relatively prime: if $a + b sqrt(-2)$ divides both, then it divides their difference $2 sqrt(-2)$, so norm $a^2 + 2b^2 | N(2 sqrt(-2)) = 8$. Only possible case is $a = pm 1, b = 0$ so $a + b sqrt(-2)$ is unit. Other cases $a = 0, b = pm 1$, $a = pm 2, b = 0$ and $a = 0, b = pm 2$ are impossible since $y$ not even.
    - If $a + b sqrt(-2)$ is unit, $exists x, y in ZZ: (a + b sqrt(-2)) (x + y sqrt(-2)) = 1$. If $b != 0$ then $(-a^2 - 2b^2)y = 1 ==> b = 0$: contradiction. If $b = 0$, $a = pm 1$. So only units in $ZZ\[sqrt(-2)\]$ are $plus.minus 1$.
]

= Finite field extensions

#definition[
    Let $F$, $L$ fields. If $F subset.eq L$ and $F$ and $L$ share the same operations then $F$ is a *subfield* of $L$ and $L$ is *field extension* of $F$ (denoted $L \/ F$). $L$ is vector space over $F$:
    - $0 in L$ (zero vector).
    - $u, v in L ==> u + v in L$ (additivity).
    - $a in F, u in L ==> a u in L$ (scalar multiplication).
]
#definition[
    Let $L \/ F$ field extension. *Degree* of $L$ over $F$ is dimension of $L$ as vector space over $F$: $ [L: F] := dim_F (L) $ If $[L: F]$ finite, $L \/ F$ is *finite field extension*.
]
#example[
    $QQ\(sqrt(-2)\) = \{a + b sqrt(-2): a, b in QQ\}$ is isomorphic as a vector space to $QQ^2$ so is $2$-dimensional vector space over $QQ$. Isomorphism is $a + b sqrt(-2) <--> (a, b)$. Standard basis $\{e_1, e_2\}$ in $QQ^2$ corresponds to the basis $\{1, sqrt(-2)\}$ in $QQ\(sqrt(-2)\)$. $\[QQ\(sqrt(-2)\): QQ\] = 2$.
]
#example[
    $[CC: RR] = 2$ (a basis is ${1, i}$). $[RR: QQ]$ is not finite, due to the existence of transcendental numbers (if $alpha$ transcendental, then $\{1, alpha, alpha^2, ...\}$ is linearly independent).
]
#definition[
    Let $L \/ F$ field extension. $alpha in L$ is *algebraic* over $F$ if $ exists 0 != f(x) in F[x]: f(alpha) = 0 $ If all elements in $L$ are algebraic, then $L \/ F$ is *algebraic field extension*.
]
#example[
    $i in CC$ is algebraic over $RR$ since $i$ is root of $x^2 + 1$. $CC \/ RR$ is algebraic since $z = a + b i$ is root of $(x - z)(x - overline(z)) = x^2 - 2a x + a^2 + b^2$.
]
#proposition[
    If $L \/ F$ is finite field extension then it is algebraic.
]
#definition[
    Let $L \/ F$ field extension, $alpha in L$ algebraic over $F$. *Minimal polynomial* $p_alpha (x) = p_(alpha, F) (x)$ of $alpha$ over $F$ is the monic polynomial $f$ of smallest degree such that $f(alpha) = 0$. *Degree* of $alpha$ over $F$ is $deg(p_alpha)$.
]
#proposition[
    $p_alpha (x)$ is unique and irreducible. Also, if $f(x) in F[x]$ is monic, irreducible and $f(alpha) = 0$, then $f = p_alpha$.
]
#example[
    - $p_(i, RR)(x) = p_(i, QQ)(x) = x^2 + 1$, $p_(i, QQ(i))(x) = x - i$.
    - Let $alpha = root(7, 5)$. $f(x) = x^7 - 5$ is minimal polynomial of $alpha$ over $QQ$ by above proposition, as it is irreducible by Eisenstein's criterion with $p = 5$.
    - Let $alpha = e^(2pi i\/p)$, $p$ prime. $alpha$ is algebraic as root of $x^p - 1$ which isn't irreducible as $x^p - 1 = (x - 1) Phi(x)$ where $Phi(x) = (x^(p - 1) + cdots + 1)$. $Phi(alpha) = 0$ since $alpha != 1$, $Phi(x)$ is monic and $Phi(x + 1) = ((x + 1)^p - 1)\/x$ irreducible by Eisenstein's criterion with $p = p$, hence $Phi(x)$ irreducible. So $p_alpha (x) = Phi(x)$.
]

== Fields generated by elements

#definition[
    Let $L\/F$ field extension, $alpha in L$. The *field generated by $alpha$ over $F$* is the smallest subfield of $L$ containing $F$ and $alpha$: $ F(alpha) := sect.big_(K "field", \ F subset.eq K subset.eq L, \ alpha in K) K $ Generally, $F(alpha_1, ..., alpha_n)$ is smallest field extension of $F$ containing $alpha_1, ..., alpha_n$.
]
- We have $F(alpha_1, ..., alpha_n) = F(alpha_1) cdots (alpha_n)$ (show $F(alpha, beta) subset.eq F(alpha)(beta)$ and $F(alpha)(beta) subset.eq F(alpha, beta)$ by minimality and use induction).
#definition[
    $F[alpha] = \{sum_(i = 0)^n a_i alpha^i: a_i in F, n in NN\} = {f(alpha): f(x) in F[x]}$.
]
#lemma[
    Let $L\/F$ field extension, $alpha in L$ algebraic over $F$. Then $F[alpha]$ is field, hence $F(alpha) = F[alpha]$.
]
#lemma[
    Let $alpha$ algebraic over $F$. Then $[F(alpha): F] = deg(p_alpha)$.
]
#definition[
    Let $K\/F$ and $L\/K$ field extensions, then $F subset.eq K subset.eq L$ is *tower of fields*.\
]
#theorem("Tower theorem")[
    Let $F subset.eq K subset.eq L$ tower of fields. Then $ [L: F] = [L: K] dot.op [K: F] $
]
#example[
    Let $L = QQ\(sqrt(2), sqrt(3)\)$. Show $[L: QQ] = 4$.
    - Let $K = QQ\(sqrt(2)\)$. Let $sqrt(3) = a + b sqrt(2)$, $a, b in QQ$ so $3 = a^2 + 2b^2 + 2a b sqrt(2)$. So $0 in {a, b}$, otherwise $sqrt(2) in QQ$. But if $a = 0$, then $sqrt(6) = 2b in QQ$, if $b = 0$ then $sqrt(3) = a in QQ$: contradiction. So $x^2 - 3$ has no roots in $K$ so is irreducible over $K$ so $p_(sqrt(3), K)(x) = x^2 - 3$.
    - So $[L: K] = 2$ so by the tower theorem, $[L: QQ] = [L: K] dot.op [K: QQ] = 4$.
]

== Norm and trace

- Let $L\/F$ finite field extension, $n = [L: F]$. For any $alpha in L$, there is $F$-linear map $ hat(alpha): L --> L, quad x |-> alpha x $
- With basis $\{alpha_1, ..., alpha_n\}$ of $L$ over $F$, let $T_alpha = T_(alpha, L\/F) in M_n (F)$ be the corresponding matrix of the linear map $alpha$ with respect to the basis $\{alpha_i\}$: $ hat(alpha)(alpha_1) & = alpha alpha_1 = a_(1, 1) alpha_1 + cdots + a_(1, n) alpha_n, \ & thick dots.v \ hat(alpha)(alpha_n) & = alpha alpha_n = a_(n, 1) alpha_1 + cdots + alpha_(n, n) alpha_n $ with $a_(i, j) in F$, $T_alpha = (a_(i, j))$, so $alpha$ is eigenvalue of $T_alpha$: $ alpha vec(alpha_1, dots.v, alpha_n) = T_alpha vec(alpha_1, dots.v, alpha_n) $
#definition[
    *Norm* of $alpha$ is $ N_(L\/F)(alpha) := det(T_alpha) $
]
#definition[
    *Trace* of $alpha$ is $ tr_(L\/F)(alpha) := tr(T_alpha) $
]
#remark[
    Norm and trace are independent of choice of basis so are well-defined (uniquely determined by $alpha$).
]
#example[
    Let $L = QQ(sqrt(m))$, $m in ZZ$ non-square, let $alpha = a + b sqrt(m) in L$. Fix basis $\{1, sqrt(m)\}$. Now $ hat(alpha)(1) & = alpha dot.op 1 = a + b sqrt(m), \ hat(alpha)(sqrt(m)) & = alpha sqrt(m) = b m + a sqrt(m), \ T_alpha & = mat(a, b; b m, a) $ So $N_(L\/F)(alpha) = a^2 - b^2 m$, $tr_(L\/F)(alpha) = 2a$.
]
#lemma[
    The map $L -> M_n (F)$ given by $alpha |-> T_alpha$ is injective ring homomorphism. So if $f(x) in F[x]$, $ T_(f(alpha)) = f(T_alpha) $ ($f(T_alpha)$ is a polynomial in $T_alpha$, not $f$ applied to each entry).
]
#proposition[
    Let $L\/F$ finite field extension. $forall alpha, beta in L$,
  - $N_(L\/F)(alpha) = 0 <==> alpha = 0$.
  - $N_(L\/F)(alpha beta) = N_(L\/F)(alpha) N_(L\/F)(beta)$.
  - $forall a in F, N_(L\/F)(a) = a^([L: F])$ and $tr_(L\/F)(a) = [L: F] a$.
  - $forall a, b in F, tr_(L\/F)(a alpha + b beta) = a tr_(L\/F)(alpha) + b tr_(L\/F)(beta)$ (so $tr_(L\/F)$ is $F$-linear map).
]

== Characteristic polynomials

- Let $A in M_n (F)$, then characteristic polynomial is $chi_A (x) = det(x I - A) in F[x]$ and is monic, $deg(chi_A) = n$. If $chi_A (x) = x^n + sum_(i = 0)^(n - 1) c_i x^i$ then $det(A) = (-1)^n det(0 - A) = (-1)^n chi_A (0) = (-1)^n c_0$ and $tr(A) = -c_(n - 1)$, since if $alpha_1, ..., alpha_n$ are eigenvalues of $A$ (in some field extension of $F$), then $tr(A) = alpha_1 + cdots + alpha_n$, $chi_A (x) = (x - alpha_1) cdots (x - alpha_n) = x^n - (alpha_1 + cdots alpha_n) x^(n - 1) + cdots$.
- For finite extension $L\/F$, $n = [L: F]$, $alpha in L$, *characteristic polynomial* $chi_alpha (x) = chi_(alpha, L\/F)(x)$ is characteristic polynomial of $T_alpha$. So $N_(L\/F)(alpha) = (-1)^n c_0$, $tr_(L\/F)(alpha) = -c_(n - 1)$. By the Cayley-Hamilton theorem, $chi_alpha (T_alpha) = 0$ so $T_(chi_alpha (alpha)) = chi_alpha (T_alpha) = 0$, where $chi_alpha (x) = x^n + c_(n - 1) x^(n - 1) + cdots + c_0$. Since $alpha -> T_alpha$ is injective, $chi_alpha (alpha) = 0$.
#lemma[
    Let $L\/F$ finite extension, $alpha in L$ with $L = F(alpha)$. Then $chi_alpha (x) = p_alpha (x)$.
]
#proposition[
    Let $F subset.eq F(alpha) subset.eq L$, let $m = [L: F(alpha)]$. Then $chi_alpha (x) = p_alpha (x)^m$.
]
#corollary[
    Let $L\/F$, $alpha in L$, $m = [L: F(alpha)]$, $p_alpha (x) = x^d + a_(d - 1) x^(d - 1) + cdots + a_0$, $a_i in F$. Then $ N_(L\/F)(alpha) = (-1)^(m d) a_0^m, quad tr_(L\/F)(alpha) = -m a_(d - 1) $
]

= Algebraic number fields and algebraic integers

== Algebraic numbers

#definition[
    $alpha in CC$ is *algebraic number* if algebraic over $QQ$.
]
#definition[
    $K$ is *(algebraic) number field* if $QQ subset.eq K subset.eq CC$ and $[K: QQ] < oo$.
]
- Every element of an algebraic number field is an algebraic number.
#example[
    Let $theta = sqrt(2) + sqrt(3)$, then $QQ(theta) subset.eq QQ\(sqrt(2), sqrt(3)\)$ but also $theta^3 = 11 sqrt(2) + 9 sqrt(3)$ so $ sqrt(2) = (theta^3 - 9 theta)/2, quad sqrt(3) = (-theta^3 + 11 theta)/2 $ so $QQ\(sqrt(2), sqrt(3)\) subset.eq QQ(theta)$ hence $QQ\(sqrt(2), sqrt(3)\) = QQ(theta)$.
]
#theorem("Simple extension theorem")[
    Every number field $K$ has form $K = QQ(theta)$ for some $theta in K$.
]
- Set of all algebraic numbers (union of all number fields) is denoted $overline(QQ)$ and is a field, since if $alpha != 0$ algebraic over $QQ$, $[QQ(alpha): QQ] = deg(p_alpha) < oo$ so $QQ(alpha)\/QQ$ algebraic, so $-alpha, alpha^(-1) in QQ(alpha)$ algebraic, so $alpha^(-1), -alpha in overline(QQ)$, and if $alpha, beta in overline(QQ)$ then $QQ(alpha, beta) = QQ(alpha)(beta)$ is finite extension of $QQ$ by tower theorem so $alpha + beta$, $alpha beta in QQ(alpha, beta)$ so are algebraic.
- $\[overline(QQ): QQ\] = oo$ since if $\[overline(QQ): QQ\] = d in NN$ then every algebraic number would have degree $<= d$, but $root(d + 1, 2)$ has degree $d + 1$ since it is a root of $x^(d + 1) - 2$ which is irreducible by Eisenstein's criterion with $p = 2$.
#definition[
    Let $alpha in overline(QQ)$. *Conjugates* of $alpha$ are roots of $p_alpha (x)$ in $CC$.
]
#example[
    
    - Conjugate of $a + b i in QQ(i)$ is $a - b i$.
    - Conjugate of $a + b sqrt(2) in QQ\(sqrt(2)\)$ is $a - b sqrt(2)$.
    - Conjugates of $theta$ do not always lie in $QQ(theta)$, e.g. for $theta = root(3, 2)$, $p_theta (x) = x^3 - 2$ has two non-real roots not in $QQ(theta) subset RR$.
]
#notation[
    When base field is $QQ$, $N_K$ and $tr_K$ denote $N_(K\/QQ)$ and $tr_(K\/QQ)$.
]
#lemma[
    Let $K\/QQ$ number field, $alpha in K$, $alpha_1, ..., alpha_n$ conjugates of $alpha$. Then $ N_K (alpha) = (alpha_1 thin cdots thin alpha_n)^([K: QQ(alpha)]), quad tr_K (alpha) = (alpha_1 + cdots + alpha_n) [K: QQ(alpha)] $
]

== Algebraic integers

#definition[
    $alpha in overline(QQ)$ is *algebraic integer* if it is root of a monic polynomial in $ZZ[x]$. The set of algebraic integers is denoted $overline(ZZ)$. If $K\/QQ$ is number field, set of algebraic integers in $K$ is denoted $cal(O)_K$, $alpha in cal(O)_K$ is called *integer in $K$*.
]
#example[
    $i, (1 + sqrt(3))\/2 in overline(ZZ)$ since they are roots of $x^2 + 1$ and $x^2 - x + 1$ respectively.
]
#theorem[
    Let $alpha in overline(QQ)$. The following are equivalent:
    - $alpha in overline(ZZ)$.
    - $p_alpha (x) in ZZ[x]$.
    - $ZZ[alpha] = \{sum_(i = 0)^(d - 1) a_i alpha^i: a_i in ZZ\}$ where $d = deg(p_alpha)$.
    - There exists non-trivial finitely generated abelian additive subgroup $G subset CC$ such that $ alpha G subset.eq G "i.e." forall g in G, alpha g in G $ ($alpha g$ is complex multiplication).
]
#remark[
    - For third statement, generally we have $ZZ[alpha] = {f(alpha): f(x) in ZZ[x]}$ and in this case, $ZZ[alpha] = {f(alpha): f(x) in ZZ[x], deg(f) < d}$.
    - Fourth statement means that $ G = {a_1 gamma_1 + cdots + a_r gamma_r: a_i in ZZ} = gamma_1 ZZ + cdots + gamma_r ZZ = ideal(gamma_1, ..., gamma_r)_ZZ $ $G$ is typically $ZZ[alpha]$. E.g. if $alpha = sqrt(2)$, $ZZ\[sqrt(2)\]$ is generated by $1, sqrt(2)$ and $sqrt(2) dot.op ZZ\[sqrt(2)\] subset.eq ZZ\[sqrt(2)\]$.
]
#proposition[
    $overline(ZZ)$ is a ring. Also, for every number field $K$, $cal(O)_K$ is a ring.
]
#lemma[
    Let $alpha in overline(ZZ)$. For every number field $K$ with $alpha in K$, $ N_K (alpha) in ZZ, quad tr_K (alpha) in ZZ $
]
#lemma[
    Let $K$ number field. Then $ K = {alpha / m: alpha in cal(O)_K, m in ZZ, m != 0} $
]
#lemma[
    Let $alpha in overline(ZZ)$, $K$ number field, $alpha in K$. Then $ alpha in cal(O)_K^times <==> N_K (alpha) = plus.minus 1 $
]

== Quadratic fields and their integers

#definition[
    $d in ZZ$ is *squarefree* if $d in.not {0, 1}$ and there is no prime $p$ such that $p^2 | d$.
]
#definition[
    $K = QQ\(sqrt(d)\)$ is a *quadratic field* if $d$ is squarefree. If $d > 0$ then it is *real quadratic*. If $d < 0$ it is *imaginary quadratic*.
]
#proposition[
    Let $K\/QQ$ have degree $2$. Then $K = QQ\(sqrt(d)\)$ for some squarefree $d in ZZ$.
]
#lemma[
    Let $K = QQ\(sqrt(d)\)$, $d equiv 1 thick (mod 4)$. Then $ ZZ\[ (1 + sqrt(d))/2 \] = {(r + s sqrt(d))/2: r, s in ZZ, r equiv s thick (mod 2)} $
]
#theorem[
    Let $K = QQ\(sqrt(d)\)$ quadratic field, then $ cal(O)_K = cases(ZZ\[sqrt(d)\] & "if" d equiv.not 1 thick (mod 4), ZZ\[ (1 + sqrt(d))/2\] & "if" d equiv 1 thick (mod 4)) $
]

= Units in quadratic rings

#notation[
    In this section, let $K = QQ\(sqrt(d)\)$ be quadratic number field, $d in ZZ - {0}$, $|d|$ is not a square. Let $cal(O)_d = cal(O)_K$. Let $overline(a + b sqrt(d)) = a - b sqrt(d)$. The map $x -> overline(x)$ is a $QQ$-automorphism from $K$ to $K$.
]
#definition[
    $S$ is *quadratic number ring of $K$* if $S = cal(O)_d$ or $S = ZZ\[sqrt(d)\]$.
]
- We have $ alpha in S^times ==> exists x in S: alpha x = 1 ==> N_K (alpha) N_K (x) = 1 ==> N_K (alpha) = plus.minus 1 $ and for $alpha in S - ZZ$, since $[QQ(alpha): QQ] = 2$ and so $[K: QQ(alpha)] = 1$ by the Tower Theorem, $ N_K (alpha) = plus.minus 1 ==> alpha overline(alpha) = plus.minus 1 ==> alpha in S^times $ So $alpha in S^times <==> N_K (alpha) = plus.minus 1$.
#theorem[
    To determine the group of units for imaginary quadratic fields:
    - \
        - For $d < -1$, $ZZ\[sqrt(d)\]^times = {plus.minus 1}$.
        - $cal(O)_(-1)^times = ZZ[i]^times = {plus.minus 1, plus.minus i}$.
    - \
        - For $d equiv 1 thick (mod 4)$ and $d < -3$, $ZZ\[ (1 + sqrt(d))/2\]^times = {plus.minus 1}$.
        - $ZZ\[ (1 + sqrt(-3))/2\]^times = {plus.minus 1, plus.minus omega, plus.minus omega^2}$ where $omega = (1 + sqrt(-3))/2 = e^(pi i\/3)$.
]
#theorem("Main theorem")[
    Let $d > 1$, $d$ non-square, $S$ be quadratic number ring of $K = QQ\(sqrt(d)\)$ (i.e. $S = cal(O)_d$ or $S = ZZ\[sqrt(d)\]$). Then
    - $S$ has a smallest unit $u > 1$ (smaller than all units except $1$).
    - $S^times = {plus.minus u^r: r in ZZ} = ideal(-1, u)$.
]<main-theorem-for-units>
#definition[
    The smallest unit $u > 1$ above is the *fundamental unit* of $S$ (or of $K$, in the case $S = cal(O)_d$).
]

== Proof of the main theorem

#remark[
    If $alpha = a + b sqrt(d)$ is unit in $ZZ\[sqrt(d)\]$, $a, b > 0$, then $N_K (alpha) = alpha overline(alpha) = plus.minus 1$, so $ |overline(alpha)| = |a - b sqrt(d)| = (|N_K (alpha)|)/(|alpha|) = 1/(|alpha|) < 1/(b sqrt(d)) < 1/b $ Define $ A = {alpha = a + b sqrt(d): a, b in NN_0, |overline(alpha)| < 1/b} $
]
#lemma[
    $|A| = oo$.
]
#lemma[
    If $alpha in A$, then $|N_K (alpha)| < 1 + 2 sqrt(d)$.
]
#lemma[
    $exists alpha = a + b sqrt(d), alpha' = a' + b' sqrt(d) in A: alpha > alpha'$, $|N_K (alpha)| = |N_K (alpha')| =: n$ and $ alpha equiv alpha' thick (mod n), quad b equiv b' thick (mod n) $
]
#lemma[
    There exists a unit $u$ in $ZZ\[sqrt(d)\]$ such that $u > 1$.
]
#lemma[
    Let $0 != alpha = a + b sqrt(d) in QQ\(sqrt(d)\)$. Then $alpha > sqrt(|N_K (alpha)|)$ iff $a, b > 0$.
]

== Computing fundamental units

#theorem[
    Let $d > 1$ non-square.
    - If $S = ZZ\[sqrt(d)\]$ and $a + b sqrt(d) in S^times$, $a, b > 0$ such that $b$ is minimal, then $a + b sqrt(d)$ is the fundamental unit in $S$.
    - If $S = ZZ\[ (1 + sqrt(d))/2 \]$ (so $d equiv 1 thick (mod 4)$), then
        - $(1 + sqrt(5))/2$ is the fundamental unit in $cal(O)_5$.
        - If $d > 5$ and $(s + t sqrt(d))/2 in cal(O)_d^times$ with $s, t > 0$ such that $t$ is minimal, then $(s + t sqrt(d))/2$ is the fundamental unit in $cal(O)_d$.
]
#remark[
    Both $u = (1 + sqrt(5))/2$ and $u^2 = (3 + sqrt(5))/2$ have $t$ minimal (equal to $1$), which is why a separate case is needed for $d = 5$.
]
#example[
    
    - $1 + sqrt(2)$ is fundamental unit in $ZZ\[sqrt(2)\] = cal(O)_2$, since $N_K (1 + sqrt(2)) = -1$ so is a unit, and here $b = 1$, so is minimal (as $b > 0$).
    - $2 + sqrt(5)$ is the fundamental unit in $ZZ\[sqrt(5)\]$ (since $b = 1$ is minimal) but is not the fundamental unit in $cal(O)_5$.
]
#example[
    Find fundamental unit in $cal(O)_7$. $7 equiv.not 1 thick (mod 4)$ so $cal(O)_7 = ZZ\[sqrt(7)\]$. $a + b sqrt(7)$ is a unit iff $a^2 - 7b^2 = plus.minus 1$. Also, by the above theorem, it is the fundamental unit if $a, b > 0$ and $b$ is minimal. We use trial and error: for each $b = 1, 2, ..., $ check whether $7b^2 plus.minus 1$ is a square #align(center)[#table(
  columns: (auto, auto, auto, auto),
  inset: 6pt,
  align: center,
  [$b$], [$7b^2 - 1$], [$7b^2 + 1$], [$a^2$],
  $1$, $6$, $8$, $-$,
  $2$, $27$, $29$, $-$,
  $3$, $62$, $64$, $64 = 8^2$,
)] So the unit with minimal $b$ such that $a, b > 0$ is $8 + 3 sqrt(7)$, so is the fundamental unit.
]

== Pell's equation and norm equations

#definition[
    *Pell's equation* is $x^2 - d y^2 = 1$ for nonsquare $d$, where solutions are $x, y in ZZ$. Since LHS is norm of $x + y sqrt(d)$, solutions are given by $x + y sqrt(d) in ZZ\[sqrt(d)\]$ with norm $1$.
]
#example[
    Consider $x^2 - 2y^2 = plus.minus 1$. Fundamental unit in $ZZ\[sqrt(2)\]$ is $u = 1 + sqrt(2)$, with norm $-1$. So if $x + y sqrt(2) in ZZ\[sqrt(2)\]$ is such that $N_(ZZ\(sqrt(2)\))(x + y sqrt(2)) = 1$, then $x + y sqrt(2)$ is an even power of $u$. Thus elements of norm $plus.minus 1$ are $ plus.minus u^(2n) thick ("RHS" = 1), quad plus.minus u^(2n + 1) thick ("RHS" = -1) $ To extract solutions $x, y$, note that if $x + y sqrt(2) = plus.minus u^r$, then $x - y sqrt(2) = plus.minus overline(u)^r$, hence $ x = plus.minus (u^r + overline(u)^r)/2, quad y = plus.minus (u^r - overline(u)^r)/(2 sqrt(2)) $ Solutions when RHS $= 1$ are given by even $r$, solutions when RHS $= -1$ are given by odd $r$.
]
#example[
    Consider $x^2 - 75 y^2 = 1$. $75 = 3 dot.op 5^2$ is not square-free, so rewrite as $ x^2 - 3z^2 = 1 $ where $z = 5y$. Fundamental unit in $ZZ\[sqrt(3)\]$ is $u = 2 + sqrt(3)$ of norm $1$ so solutions are $ x = plus.minus (u^n + overline(u)^n)/2, quad z = plus.minus (u^n - overline(u)^n)/(2 sqrt(3)), quad n in ZZ $ To get solution for $(x, y)$, we need $5 | z$ (which doesn't always hold). Note that $ u^2 = 7 + 4 sqrt(3) in.not ZZ\[sqrt(75)\] = ZZ\[5 sqrt(3)\], quad u^3 = 26 + 3 sqrt(75) in ZZ\[sqrt(75)\] $ Thus when $n = 2$, $(x, z)$ is not solution, but is when $n = 3$, and hence when $n = 3k$ for $k in ZZ$: $ x = plus.minus (u^(3k) + overline(u)^(3k))/2, quad y = plus.minus (u^(3k) - overline(u)^(3k))/(5 dot.op 2 sqrt(3)), quad k in ZZ $ $u^(3k + 1)$ and $u^(3k + 2)$ never give solutions, since if $u^(3k + 1) in ZZ\[sqrt(75)\]$, then $u in ZZ\[sqrt(75)\]$ (since $u^(-3k) in ZZ\[sqrt(75)\]$). Similarly, if $u^(3k + 2) in ZZ\[sqrt(75)\]$, then $u^2 in ZZ\[sqrt(75)\]$: contradiction. Note $ZZ\[sqrt(75)\] subset ZZ\[sqrt(3)\]$ and any unit in $ZZ\[sqrt(75)\]$ is unit in $ZZ\[sqrt(3)\]$, so is $plus.minus u^r$ for some $r in ZZ$. So by taking powers of $u$, eventually we find the fundamental unit in $ZZ\[sqrt(75)\]$ (as it will be smallest unit $> 1$ assuming we increment powers from $1$).
]


#let jack = false

#show: a => if jack { smallcaps(a) } else { a }

= Discriminants and integral bases

== Discriminant of an $n$-tuple


#definition[
    Let $K$ number field of degree $n$. *Discriminant* of $gamma = (gamma_1, ..., gamma_n) in K^n$ is $ Delta_K (gamma) := det(Q(gamma)) $ where $Q(gamma) = \(tr_K \(gamma_i gamma_j\)\)_(1 <= i, j <= n) in M_n (QQ)$.
]
#example[
    Let $K = QQ\(sqrt(d)\)$, $d != 1$ squarefree. $
gamma & = \(1, sqrt(d)\) ==> Q(gamma) = mat(2, 0; 0, 2d) ==> Delta_K (gamma) = 4d \
gamma & = \(1, (1 + sqrt(d))/2) ==> Q(gamma) = mat(2, 1; 1, (1 + d)/2) ==> Delta_K (gamma) = d
$
]
#proposition[
    
    - $Delta_K (gamma) in QQ$ and if every $gamma_i in cal(O)_K$, then $Delta_K (gamma) in ZZ$.
    - Let $M in M_n (QQ)$, then $Delta_K (M gamma) = det(M)^2 Delta_K (gamma)$.
    - $Delta_K (gamma)$ is invariant under permutations of $gamma_1, ..., gamma_n$.
]
#lemma[
    Let $theta_1, ..., theta_n in CC$, let $ D = mat(1, theta_1, ..., theta_1^(n - 1); dots.v, dots.v, dots.down, dots.v; 1, theta_n, ..., theta_n^(n - 1)) $ then $ det(D) = (-1)^binom(n, 2) product_(1 <= r < s <= n) (theta_r - theta_s) $
]
#theorem[
    Let $K = QQ(theta)$ be number field. Let $theta_1, ..., theta_n$ be roots of $p_theta (x)$, let $gamma = (1, ..., theta^(n - 1))$. Then $
Delta_K (gamma) = product_(1 <= i < j <= n) \(theta_i - theta_j\)^2 = (-1)^binom(n, 2) product_(i = 1)^n p'_theta (theta_i) = (-1)^binom(n, 2) N_K (p'_theta (theta))
$
]
#example[
    
    - Let $K = QQ\(sqrt(d)\)$, $d$ square-free, $theta = (1 + sqrt(d))/2$, then $ Delta_K ((1, theta)) = ((1 + sqrt(d))/2 - (1 - sqrt(d))/2)^2 = d $
    - Let $theta = sqrt(d)$, so $p_theta (x) = x^2 - d$, $p'_theta (x) = 2x$, so $ Delta_K (1, theta) = (-1)^binom(2, 2) N_K (2 theta) = -4 N_k (theta) = 4d $
    - Let $theta = root(3, d)$, so $p_theta (x) = x^3 - d$, $p'_theta (x) = 3x^2$ so $ Delta_K (1, theta, theta^2) = (-1)^binom(3, 2) N_K (3 theta^2) = -27 d^2 $
    - Let $theta$ be root of $p_theta (x) = x^3 - x + 2$, so $p'_theta (x) = 3x^2 - 1$. $ Delta_K (1, theta, theta^2) = (-1)^binom(3, 2) N_K (3 theta^2 - 1) $ Now $theta^3 = theta - 2$ so $ N_K (3 theta^2 - 1) = (N_K (2) N_K (theta - 3))/(N_K (theta)) = 8/2 N_K (3 - theta) = 4(3 - theta_1)(3 - theta_2)(3 - theta_3) = 4 p_theta (3) = 104 $ so $Delta_K (1, theta, theta^2) = -104$. Note: in general, this method doesn't work, and generally we have to compute matrix $T_theta$ and $det(f(T_theta))$. *As a generalisation*, $ N_(QQ(theta)) (a - b theta) = b^n p_theta (a\/b) $
]
#lemma[
    
    - Roots $theta_1, ..., theta_n$ of $p_theta (x)$ are distinct.
    - $forall f(x) in QQ[x], tr_K (f(theta)) = sum_(i = 1)^n f(theta_i)$.
    - $forall f(x) in QQ[x], N_K (f(theta)) = product_(i = 1)^n f(theta_i)$.
]
#proposition[
    Let $K = QQ(theta)$ number field. Then $Delta_K (gamma) != 0$ iff $gamma$ is $QQ$-basis of $K$.
]

== Full lattices and integral bases

#definition[
    Let $A$ subgroup of $QQ$-vector space $V$. $A$ is *full lattice* in $V$ if there are $gamma_1, ..., gamma_n in V$ such that
    - ${gamma_1, ..., gamma_n}$ is basis for $V$.
    - $A = {a_1 gamma_i + dots.h.c + a_n gamma_n: a_i in ZZ}$ (i.e. $gamma_1, ..., gamma_n$ generate $A$ as a group). Note $a_1, ..., a_n$ are uniquely determined for each $a in A$.
    ${gamma_1, ..., gamma_n}$ is *generating basis* for $A$.
]
#example[
    Let $K = QQ(theta)$, $theta in cal(O)_K$, $[K: QQ] = n$, then $ZZ[theta]$ has generating basis ${1, ..., theta^(n - 1)}$ and is full lattice in $K$.
]
#example[
    $ZZ$, $ZZ\[sqrt(2)\/2\]$ are not full lattices in $QQ\(sqrt(2)\)$.
]
#proposition[
    Let $K$ number field. Every non-zero ideal $I subset.eq cal(O)_K$ is full lattice in $K$.
]
#definition[
    Generating basis for $cal(O)_K$ is *integral basis* for $K$.
]
#example[
    Let $K = QQ\(sqrt(d)\)$, then an integral basis for $K$ is $\{1, sqrt(d)\}$ if $d equiv.not 1 mod 4$, $\{1, \(1 + sqrt(d)\)\/2\}$ if $d equiv 1 mod 4$.
]
#theorem[
    If $V$ is $QQ$-vector space, $dim(V) = n$, and $B subset A subset V$, $A$ and $B$ full lattices, ${beta_1, ..., beta_n}$ is generating basis for $B$, ${alpha_1, ..., alpha_n}$ is generating basis for $A$, where $beta = M alpha$, $M in M_n (ZZ)$, then
    - $|A\/B| = |det(M)|$ (in particular, $A\/B$ is finite)
    - If $V = K$ is number field, these satisfy *index-discriminant formula*: $Delta_K (B) = |A\/B|^2 Delta_K (A)$.
    (Note $M$ exists since $alpha$ is generating basis for $A$ so spans $B$ over $ZZ$).
]
#lemma[
    If $A subset K$ is full lattice and ${gamma_1, ..., gamma_n}$, ${delta_1, ..., delta_n}$ are generating bases for $A$, then $Delta_K (gamma_1, ..., gamma_n) = Delta_K (delta_1, ..., delta_n)$. We define discriminant of $A$ to be $Delta_K (A) = Delta_K (gamma_1, ..., gamma_n)$ for any generating basis ${gamma_1, ..., gamma_n}$.
]
#definition[
    *Disciminant* of number field $K$ is $ Delta_K = Delta_K (cal(O)_K) = Delta_K (gamma_1, ..., gamma_n) $ for any integral basis ${gamma_1, ..., gamma_n}$.
]

== When is $R = ZZ[theta]$?

#proposition[
    If $S subset.eq cal(O)_K$ is full lattice in $K = QQ(theta)$, ${gamma_1, ..., gamma_n}$ is generating basis for $S$, and $p$ prime, $p | |cal(O)_K\/S|$, then
    - $p^2 | Delta_K (S)$
    - There exists $alpha = m_1 gamma_1 + dots.h.c + m_n gamma_n in S$, $m_i in ZZ$, such that $alpha\/p in cal(O)_K - S$ and $ cases(0 <= |m_i| < p\/2 & "if" p "is odd", m_i in {0, 1} & "if" p = 2) $
]
#example[
    If $K = QQ\(sqrt(d)\)$, $ Delta_K = cases(4d & "if" d equiv.not 1 mod 4, d & "if" d equiv 1 mod 4) $
]
#example[
    Let $theta$ be root of $x^3 + 4x + 1$, $K = QQ\(theta\)$. We have $ZZ[theta] subset.eq cal(O)_K$ and $Delta_K (ZZ[theta]) = Delta_K (1, theta, theta^2) = 281 = |cal(O)_K \/ ZZ[theta]|^2 Delta_K (cal(O)_K)$. As 281 is squarefree, $|cal(O)_K \/ ZZ[theta]| = 1$ so $cal(O)_K = ZZ[theta]$.
]
#example[
    Let $K = QQ(theta)$, $theta = root(3, 5)$. let $R = cal(O)_K$, $S = ZZ[theta]$. $Delta_K (S) = -3^3 dot.op 5^2$. If $p$ prime and $p | |R\/S|$, then $p in {3, 5}$ and there is $alpha = a + b theta + c theta^2$ such that $alpha\/p in R - S$, $|a|, |b|, |c| < p\/2$. Note $alpha != 0$, as otherwise $alpha in S$.
    - If $5 | |R\/S|$, then $|a|, |b|, |c| in {0, 1, 2}$. Then $tr_(K\/QQ)(alpha\/5) = 3a\/5 in ZZ$ so $5 | a$ so $a = 0$. $theta alpha \/ 5 = c + (b theta^2)\/5 in cal(O)_K$ so $(b theta^2)\/5 in cal(O)_K$ so $ N_K ((b theta^2)\/5) = (N_K (b) N_K (theta)^2)/(N_K (5)) = b^3 / 5 in ZZ $ so $5 | b$, so $b = 0$. Finally, $ N_K (alpha/5) = N_K ((c theta^2)/5) = (c^3 (-5)^2)/5^3 = c^3/5 in ZZ ==> c = 0 $ Contradiction.
    - If $3 | |R\/S|$, then $|a|, |b|, |c| in {0, 1}$ and can assume $a >= 0$ (by possibly multiplying by $-1$). Then $ N_K ((a + b theta + c theta^2) / 3) in ZZ ==> a^3 + 5b^3 + 25c^3 - 15a b c equiv 0 (mod 3^3) $ If $a = 0$, then $5b^3 + 25c^3 equiv 2b + c equiv 0 (mod 3)$ (as $b, c in {0, 1, -1}$), so if $b = 0$, then $c equiv 0 (mod 3) ==> c = 0$: contradiction. So $b = 1$ (by possibly multiplying by $-1$) hence $c = 1$. But then $ N_K (alpha\/3) = N_K ((theta + theta^2)/3) = (N_K (theta) N_K (1 + theta))/3^3 = (5 dot.op 6)/27 in.not ZZ $ Contradiction. If $a = 1$, then $ 1 + 5b^3 + 25c^3 equiv 1 + 2b + c equiv 0 (mod 3) $ which also leads to a contradiction.
    - So $5 divides.not |R\/S|$, $3 divides.not |R\/S|$, so $|R\/S| = 1$, so $ZZ[theta] = cal(O)_K$.
]

= Unique factorisation of ideals

#definition[
    *Product* of ideals $I, J subset.eq R$ is $ I J := {sum_(i = 1)^k x_i y_i: k in NN, x_i in I, y_i in J} $ If $I = ideal(a_1, ..., a_m)$, $J = (b_1, ..., b_n)$ then $ I J = ideal(a_i b_j | i in [m], j in [n]) $
]
#definition[
    $I$ *divides* $J$, $I | J$, if there is ideal $K$ such that that $I K = J$.
]
#note[
    _to divide is to contain_: $I | J ==> J subset.eq I$.
]
#example[
    Let $R = ZZ\[sqrt(-6)\]$, $I = ideal(5, 1 + 3 sqrt(-6))$, $J = ideal(5, 1 - 3 sqrt(-6))$, then $ I J = ideal(25, 5\(1 + 3 sqrt(-6)\), 5\(1 - 3 sqrt(-6)\), 55) subset.eq ideal(5) $ But also $5 = 55 - 2 dot.op 25 in I$, $ideal(5) subset.eq I J$, so $I J = ideal(5)$.
]
#lemma[
    Let $I, J$ ideals, $P$ prime ideal. Then $ I J subset.eq P <==> (I subset.eq P or J subset.eq P) $
]
#example[
    $ideal(5, 1 + 3 sqrt(-6)) subset ZZ\[sqrt(-6)\]$ is prime: define $phi: ZZ\[sqrt(-6)\] -> FF_5$, $phi\(a + b sqrt(-6)\) = a - 2b$. $phi$ is surjective homomorphism. Also, $5, 1 + 3 sqrt(-6) in ker(phi)$, and $ a + b sqrt(-6) in ker(phi) & ==> b equiv 3a mod 5 \ & ==> \(a + b sqrt(-6)\) - a\(1 + 3 sqrt(-6)\) = (b - 3a) sqrt(-6) in ideal(5) $ so $ker(phi) = \(5, 1 + 3 sqrt(-6)\)$. So by first isomorphism theorem, $R\/ideal(5, 1 + sqrt(-6)) tilde.equiv FF_5$ which is field, so $ideal(5, 3 + sqrt(-6))$ is maximal, so prime.
]
#definition[
    Let $K$ number field, $R = cal(O)_K$. *Fractional ideal* of $R$ is subset of $K$ of the form $ lambda I = {lambda x: x in I} $ where $ideal(0) != I subset.eq R$ and $lambda in K^times$. If $I = R$, $lambda I$ is *principal fractional ideal*. Set of fractional ideals in $R$ is denoted $cal(I)(R)$, set of principal fractional ideals is denoted $cal(P)(R)$. Multiplication of fractional ideals is defined similarly to that of ideals.
]
#example[
    - $n/m ZZ$ is fractional ideal in $QQ$ for all $m, n in ZZ - {0}$.
    - Every non-zero ideal is fractional ideal (take $lambda = 1$).
    - If $lambda I$ is fractional ideal, then $lambda^(-1) lambda I = I$ is ideal.
]
#definition[
    A fractional ideal $A$ is *invertible* if there is fractional ideal $B$ such that $A B = cal(O)_K$. $B$ is the *inverse* of $A$. The invertible fractional ideals form a group.
]
#example[
    In $ZZ\[sqrt(-6)\] = cal(O)_K$, $ideal(5, 1 + 3 sqrt(-6)) ideal(5, 1 - 3 sqrt(-6)) = ideal(5)$ so $ ideal(5, 1 + 3 sqrt(-6)) dot.op 1/5 ideal(5, 1 - 3 sqrt(-6)) = cal(O)_K $ so inverse of $ideal(5, 1 + 3 sqrt(-6))$ is $1/5 ideal(5, 1 - 3 sqrt(-6))$.
]

== The norm of an ideal

#definition[
    Let $ideal(0) != I$ ideal of $cal(O)_K$. *Norm* of $I$ is $ N(I) := |cal(O)_K\/I| $ We have $N(I) in NN$, $N(R) = 1$, and $I subset.neq J ==> N(I) > N(J)$ (in fact, $N(I) = N(J) |J\/I|$).
]
#proposition[
    Every non-zero prime ideal in $cal(O)_K$ is maximal.
]
#lemma[
    Every nonzero ideal in $cal(O)_K$ contains product of one or more non-zero prime ideals.
]
#proof[
    Consider $I$ for which statement does not hold, with $N(I)$ minimal, then there are $b, b' in.not I$ but $b b' in I$.
]

== Ideals are invertible

#theorem[
    Every non-zero prime ideal in $cal(O)_K$ is invertible.
]
#proof[
    - Define $A = {x in K: x P subset.eq cal(O)_K}$, show $A$ is fractional ideal and $R subset.eq A$
    - Show $A != cal(O)_K$:
        - Choose $0 != alpha in P$, choose prime ideals such that $P_1 dots.h.c P_t subset.eq (alpha)$ and $t$ is minimal.
        - Choose $beta in P_2 dots.h.c P_t$ and $beta in.not (alpha)$, show that $beta/alpha in A - R$.
    - Show that $P != A P$, using Theorem 4.6.
    - Use fact that $P$ is maximal to conclude $A P = R$.
]
#lemma[
    If $lambda I$ is fractional ideal and $lambda I subset.eq cal(O)_K$, then $lambda I$ is ideal in $cal(O)_K$.
]
#lemma[
    Let $J subset.eq I$ ideals in $cal(O)_K$ with $I$ invertible. Then
    - $I^(-1) J$ is ideal in $cal(O)_K$ and so $I | J$.
    - $J subset.eq I^(-1) J$ with equality iff $I = R$.
]
#theorem[
    Let $I subset.neq cal(O)_K$ be non-zero ideal. Then $I$ is unique (up to reordering) product of prime ideals.
]
#definition[
    A ring where every proper non-zero ideal can be uniquely factorised into prime ideals is a *Dedekind domain*. So rings of integers are Dedekind domains.
]
#example[
    In $ZZ\[sqrt(-6)\]$, $\(1 + 3 sqrt(-6)\) \(1 - 3 sqrt(-6)\) = 55 = 5 dot.op 11$. $P_5 = ideal(5, 1 + 3 sqrt(-6))$ and $overline(P_5) = ideal(5, 1 - 3 sqrt(-6))$ are prime, as are $P_11 = ideal(11, 1 + 3 sqrt(-6))$ and $overline(P_11) = ideal(11, 1 - sqrt(-6))$. $P_5 overline(P_5) = ideal(5)$, $P_11 overline(P_11) = ideal(11)$, $P_5 P_11 = ideal(1 + 3 sqrt(-6))$, $overline(P_5) thick overline(P_11) = ideal(1 - 3 sqrt(-6))$ so $ \(P_5 P_11\) \(overline(P_5) thick overline(P_11)\) = \(P_5 overline(P_5)\) \(P_11 overline(P_11)\) $
]
#corollary[
    Let $R = cal(O)_K$.
    - Every fractional ideal (and hence every nonzero ideal) in $R$ is invertible.
    - $cal(I)(R)$ is abelian group under multiplication, with identity element $R$.
]
#corollary("to divide is to contain and to contain is to divide")[
    $I | J <==> J subset.eq I$.
]
#theorem[
    If $cal(O)_K$ is UFD, then it is also PID.
]

== Arithmetic with ideals

#definition[
    Let $I, J$ be non-zero ideals of $R$, $ I & = P_1^(a_1) dots.c P_r^(a_r), \ J & = P_1^(b_1) dots.c P_r^(b_r) $ with $P_1, ..., P_r$ distinct prime ideals of $R$ and $a_i, b_i >= 0$. *gcd* and *lcm* of $I$ and $J$ are $ gcd(I, J) & := P_1^(min{a_1, b_1}) dots.c P_r^(min{a_r, b_r}), \ "lcm"(I, J) & := P_1^(max{a_1, b_1}) dots.c P_r^(max{a_r, b_r}) $
]
#definition[
    $I$ and $J$ are *coprime* if $gcd(I, J) = ideal(1) = R$.
]
#proposition[
    - For $m, n in ZZ$, $gcd\(ideal(m)_ZZ, ideal(n)_ZZ\) = ideal(gcd(m, n))_ZZ$ and $"lcm"\(ideal(m)_ZZ, ideal(n)_ZZ\) = ideal("lcm"(m, n))_ZZ$.
    - $gcd(I, J)$ divides $I$ and $J$, and if any $K$ divides $I$ and $J$, then $K | gcd(I, J)$.
    - $I, J | "lcm"(I, J)$ and for any ideal $K$, if $I, J | K$ then $"lcm"(I, J) | K$.
]
#proposition[
    - In any ring, the smallest ideal containing ideals $I$ and $J$ is $I + J$. So if $I = ideal(a_1, ..., a_n)$ and $J = (b_1, ..., b_m)$ then smallest ideal containing $I$ and $J$ is $ideal(a_1, ..., a_n, b_1, ..., b_m)$.
    - In any ring, the largest ideal contained in both $I$ and $J$ is $I sect J$.
]
#proposition[
    If $I$ and $J$ are non-zero ideals in $cal(O)_K$ then $ gcd(I, J) = I + J, quad "lcm"(I, J) = I sect J $
]
#theorem("Chinese remainder theorem for ideals")[
    Let $I_1, ..., I_k$ be pairwise coprime ideals of $cal(O)_K$, then there is an isomorphism $ R \/ (I_1 dots.c I_k) & -> R\/I_1 times dots.c times R\/I_k, \ x + (I_1 dots.c I_k) & |-> (x + I_1, ..., x + I_k) $
]

= Splitting of primes and the Kummer-Dedekind theorem

== Properties of the ideal norm

#lemma[
    For every non-zero ideal $I$ of $cal(O)_K$, $N(I) in I$, hence $I sect ZZ != ideal(0)$.
]<ideal-contains-its-norm>
#notation[
    For $0 != alpha in cal(O)_K$, define $N(alpha) := N\(ideal(alpha)_(cal(O)_K)\)$.
]
#lemma[
    $forall 0 != alpha in cal(O)_K$, $N(alpha) = |N_K (alpha)|$.
]
#lemma[
    Ideal norm is multiplicative: for any non-zero ideals $I$, $J$ in $cal(O)_K$, $ N(I J) = N(I) N(J) $
]
#proof[
    - Clear when $I$ or $J$ is $cal(O)_K$ so assume both are proper.
    - Sufficient to show for when $J$ is prime (why?)
    - Use that $N(I P) = |R\/ (I P)| = |R\/I| dot.op |I\/(I P)|$.
    - Show that $|I\/(I P)| = |R\/P|$:
        - Show $I\/(I P)$ is one-dimensional vector space over $R\/P$:
            - Show $I != I P$ and choose $x in I - (I P)$.
            - Show $(x, I P) = I$ using unique factorisation.
]

== The Kummer-Dedekind theorem

#definition[
    If $p in ZZ$ prime, and $ideal(p)_(O_K) = P_1^(e_1) dots.h.c P_r^(e_r)$ then $P_1, ..., P_r$ are the prime ideals *lying above* $p$. Equivalently, $P$ *lies above* $p$ if $P sect ZZ = ideal(p)_ZZ$.
]
#remark[
    If $P subset cal(O)_K$ nonzero prime ideal, then $N(P) in P sect ZZ$ so $P sect ZZ != ideal(0)$. But $P sect ZZ$ is prime ideal of $ZZ$ so $P sect ZZ = ideal(p)_ZZ$ for some prime $p in ZZ$. Hence $p in P$, $ideal(p)_(cal(O)_K) subset.eq P$ so $P | ideal(p)_(cal(O)_K)$. Hence every $P$ lies over some prime $p$.
]
#lemma[
    Prime ideal $P$ of $cal(O)_K$ lies above $p$ iff $N(P) = p^r$ for some $1 <= r <= n = [K: QQ]$.
]
#proof[
    For "if" direction, use that $N(I) in I$.
]
#theorem("Kummer Dedekind")[
    Let $p$ prime. Suppose $cal(O)_K = ZZ[theta]$ for some $theta in cal(O)_K$ with minimal polynomial $p_theta$. Let $overline(f)(x)$ be reduction of $f(x) in ZZ[x]$ $mod p$, so $overline(f)(x) in FF_p [x]$. Let $ overline(p_theta)(x) = overline(f_1)(x)^(e_1) dots.h.c overline(f_r)(x)^(e_r) $ be factorisation of $overline(p_theta)$ where $overline(f_i)$ are distinct, monic, irreducible. For each $i$, let $f_i (x) in ZZ[x]$ be monic polynomial whose reduction $mod p$ is $overline(f_i)(x)$. Let $P_i = (p, f_i (theta))_(cal(O)_K)$. Then $P_i$ are distinct prime ideals, $N(P_i) = p^(deg(f_i))$ and $ ideal(p)_(cal(O)_K) = P_1^(e_1) dots.h.c P_r^(e_r) $
]
#proof[
    - Let $phi: ZZ[x] -> cal(O)_K \/ P_i$ be composition of evaluation map $ZZ[x] -> cal(O)_K$, $g(x) |-> g(theta)$, and canonical map $cal(O)_K -> cal(O)_K \/ P_i$. Show that $ ZZ[x] \/ ideal(p_theta (x), p, f_i (x)) tilde.equiv cal(O)_K\/P_i $
    - Deduce another isomorphism given by reduction mod $p$ map $g(x) + ideal(p_theta (x), p, f_i (x)) |-> overline(g)(x) + ideal(overline(p_theta)(x), overline(f_i)(x))$.
    - To show $P_i$ prime, deduce that $cal(O)_K\/P_i tilde.equiv FF_p [x] \/ ideal(overline(f_i)(x))$.
    - Deduce that $N(P_i) = p^(deg(f_i))$.
    - Use that $P_1^(e_1) dots.h.c P_r^(e_r) subset.eq ideal(p, f_1 (theta)^(e_1) dots.h.c f_r (theta)^(e_r))$ and $f_1 (theta)^(e_1) dots.h.c f_r (theta)^(e_r) equiv p_theta (theta) mod p$ and $N(P_1^(e_1) dots.h.c P_r^(e_r)) = N(p)$ to show $P_1^(e_1) dots.h.c P_r^(e_r) = ideal(p)_(cal(O)_K)$.
]
#theorem("Strong Kummer-Dedekind")[
    Let $K = QQ(theta)$, $theta in R = cal(O)_K$, $p divides.not |R\/ZZ[theta]|$ then $ideal(p)_R$ can be factorised by considering $overline(p_theta)(x) in FF_p [x]$ as in usual Kummer-Dedekind when $|R\/ZZ[theta]| = 1$.
]
#example[
    Let $K = QQ\(sqrt(6)\)$, so $cal(O)_K = ZZ\[sqrt(6)\]$. $p_theta (x) = x^2 - 6$ factorises modulo small primes as: $
        overline(x^2 - 6) & = x^2 quad & "in" FF_2 [x] \
        overline(x^2 - 6) & = x^2 quad & "in" FF_3 [x] \
        overline(x^2 - 6) & = x^2 - 1 = (x - 1)(x + 1) quad & "in" FF_5 [x] \
        overline(x^2 - 6) & "irreducible" quad & "in" FF_7 [x] \
        overline(x^2 - 6) & "irreducible" quad & "in" FF_11 [x]
    $ Since $6$ is not square $mod 7$ or $11$. By Kummer-Dedekind, $
        ideal(2)_(cal(O)_K) & = ideal(2, sqrt(6))^2, quad ideal(3)_(cal(O)_K) = ideal(3, sqrt(6))^2, \
        ideal(5)_(cal(O)_K) & = ideal(5, sqrt(6) + 1) ideal(5, sqrt(6) - 1), \
        ideal(7)_(cal(O)_K) & = ideal(7, sqrt(6)^2 - 6) = ideal(7, 0) = ideal(7), \
        ideal(11)_(cal(O)_K) & = ideal(11, sqrt(6)^2 - 6) = ideal(11, 0) = ideal(11)
    $
]
#definition[
    When $K$ is quadratic, Kummer-Dedekind implies there are 3 mutually exclusive possibilities for prime $p in ZZ$:
    - If $ideal(p)_(cal(O)_K)$ is prime ideal, $p$ is *inert*.
    - If $ideal(p)_(cal(O)_K) = P^2$ for prime ideal $P$, then $p$ *ramifies* (or *is ramified*) (otherwise, it is *unramified*).
    - If $ideal(p)_(cal(O)_K) = P_1 P_2$ for distinct prime ideals $P_1, P_2$, then $p$ *splits* (or *is split*).
]
#remark[
    If $K\/QQ$ is quadratic, $K = QQ\(sqrt(d)\)$, then Kummer-Dedekind always applies since $R = ZZ\[theta\]$ for some $theta in K$.
]
#notation[
    Let $K$ quadratic extension. If $I subset.eq cal(O)_K$ ideal, let $overline(I) = {overline(x): x in I}$ where $overline(a + b sqrt(d)) = a - b sqrt(d)$. We have $I$ prime iff $overline(I)$ prime and $N\(overline(I)\) = N(I)$.
]
#lemma[
    Let $K$ quadratic number field, $p in ZZ$ prime, $P$ non-zero prime ideal in $cal(O)_K$ lying above $p$. Then $overline(P)$ is prime ideal lying above $p$ and:
    - If $p$ inert, then $P = overline(P)$ and $N(P) = p^2$.
    - If $p$ ramifies, then $P = overline(P)$ and $N(P) = p$.
    - If $p$ splits, then $ideal(p)_(cal(O)_K) = P overline(P)$, $P != overline(P)$ and $N(P) = N\(overline(P)\) = p$.
    In all cases, $P overline(P) = ideal(N(P))_(cal(O)_K)$.
]<quadratic-field-kd-cases>
#example[
    Let $theta^3 + 3 theta - 1 = 0$, $K = QQ(theta)$. We have $cal(O)_K = ZZ[theta]$. To factorise $ideal(5)_(cal(O)_K)$ and $ideal(11)_(cal(O)_K)$: $-1$ and $2$ are roots of $x^3 + 3x - 1 mod 5$, so we get $x^3 + 3x - 1 equiv (x + 1)(x + 2)^2 mod 5$. So by Kummer-Dedekind, $ ideal(5)_(cal(O)_K) = ideal(5, theta + 1) ideal(5, theta + 2)^2 $ Only root in $overline(p_theta)$ in $FF_11$ is $-4$, so $overline(p_theta)(x) = (x + 4)(x^2 - 4x + 8) mod 11$ and $x^2 - 4x + 8 = (x - 2)^2 + 4$ is irreducible as $-4$ is not square $mod 11$. So by Kummer-Dedekind, $ ideal(11)_(cal(O)_K) = ideal(11, theta + 4) ideal(11, theta^2 - 4 theta + 8) $ To factorise $ideal(2 theta - 3)_(cal(O)_K)$: $ N_K (2 theta - 3) = -N_K (2) N_K (3/2 - theta) = -8 dot.op p_theta (3/2) = -8(27/8 + 9/2 - 1) = -55 $ So $ideal(2 theta - 3) = P_5 P_11$ where $N(P_5) = 5$, $N(P_11) = 11$, $P_5, P_11$ prime. So $P_5 | ideal(5)$, so $P_5 = ideal(5, theta + 1)$ or $ideal(5, theta + 2)$. Now $2 theta - 3 = 2(theta + 1) - 5 in ideal(5, theta + 1)$, so $ideal(5, theta + 1) | ideal(2 theta - 3)$, hence $P_5 = ideal(5, theta + 1)$. Now $P_11 | ideal(11)$ so $P_11 = ideal(11, theta + 4)$ or $ideal(11, theta^2 - 4theta + 8)$. But by Kummer-Dedekind, the latter has norm $11^2$ which is a contradiction (since $11^2 divides.not N(ideal(2 theta - 3)) = 55$). So $P_11 = ideal(11, theta + 4)$.
]

= The ideal class group

#notation[
    Let $R = cal(O)_K$ for number field $K$.
]
#definition[
    *(Ideal) class group* of $R$ (or of $K$) is $"Cl"(R) := cal(I)(R)\/cal(P)(R)$. For fractional ideal $I in cal(I)(R)$, let $[I] = I dot.op cal(P)(R) = {ideal(lambda)_R I: lambda in K^times} = {lambda I: lambda in K^times}$ denote *class* of $I$ in $"Cl"(R)$.
]
#proposition[
    - $[I] = e$ iff $I in cal(P)(R)$ iff $I$ is principal.
    - $[I] = [J]$ iff $I = ideal(lambda)_R J$ for some $lambda in K^times$ iff $alpha I = beta J$ for some $alpha, beta in R - {0}$.
    - $[I] dot.op [J] = I J dot.op cal(P)(R) = [I J]$.
    - $[I]^(-1) = [I^(-1)]$.
]
#proposition[
    $Cl(R)$ is the trivial group ($Cl(R) = e$) iff $R$ is a UFD iff $R$ is a PID.
]
#proof[
    - To show PID $==>$ UFD, enough to show every prime ideal is principal.
    - Use that prime ideal $P$ lies over some prime $p in ZZ$.
    - Use that in $R$, $p = pi_1 dots.h.c pi_r$ is factorisation into irreducibles.
]
#remark[
    If $ideal(alpha)_R = P Q$ then $e = [ideal(alpha)_R] = [P Q] = [P] [Q]$ so $[P] = [Q]^(-1)$.
]
#proposition[
    If $K$ is quadratic number field, $I$, $J$ ideals, then $\[overline(I)\] = [I]^(-1)$ and $I overline(J)$ is principal iff $[I] = [J]$.
]
#proof[
    Use @quadratic-field-kd-cases for first part.
]
#example[
    - Let $K = QQ\(sqrt(-29)\)$ so $cal(O)_K = ZZ\[sqrt(-29)\] = R$. $p_(sqrt(-29))(x) = x^2 + 29$ so by Kummer-Dedekind and @quadratic-field-kd-cases, $
        ideal(2)_R & = P_2^2, quad P_2 = ideal(2, 1 + sqrt(-29))_R, quad N(P_2) = 2, \
        ideal(3)_R & = P_3 overline(P_3), quad P_3 = ideal(3, 1 - sqrt(-29))_R, quad N(P_3) = 3, \
        ideal(5)_R & = P_5 overline(P_5), quad P_5 = ideal(5, 1 - sqrt(-29))_R, quad N(P_5) = 5
    $
    - If $P_2$ were principal, then $P_2 = ideal(a + b sqrt(-29))$ but $N(P_2) = 2 = a^2 + 29b^2$: contradiction. So $[P_2] != e$ but $[P_2]^2 = e$ as $P_2^2 = ideal(2)_R$ is principal.
    - Similarly, $P_5$ is not principal, but also $P_5^2$ is not principal, as if it was, then $P_5^2 = ideal(a + b sqrt(-29))$ so $25 = a^2 + 29b^2 ==> a = plus.minus 5$, but then $P_5^2 = ideal(5) = P_5 overline(P_5)$, but $P_5 != overline(P_5)$.
    - But $N\(3 + 2 sqrt(-29)\) = 5^3$, so $ideal(3 + 2 sqrt(-29))_R | (5^3)_R$ by @ideal-contains-its-norm, so $ideal(3 + 2 sqrt(-29)) = P_5^a overline(P_5)^(3 - a)$; but $5 divides.not 3 + 2 sqrt(-29)$, so we can't have $P_5 overline(P_5) | ideal(3 + 2 sqrt(-29))$. So $ideal(3 + 2 sqrt(-29)) = P_5^3$ or $overline(P_5)^3$, and $3 + 2 sqrt(-29) in P_5$ so $ideal(3 + 2 sqrt(-29)) = P_5^3$, hence $[P_5]^3 = e$, so $[P_5]$ has order $3$.
    - Again, $[P_3] != e$. As $N\(1 + sqrt(-29)\) = 30$, $ideal(1 + sqrt(-29)) | ideal(30) = ideal(2) ideal(3) ideal(5)$, so we see $ideal(1 + sqrt(-29)) = P_2 overline(P_3)overline(P_5)$, hence $e = [P_2] [P_3]^(-1) [P_5]^(-1)$ and so $[P_3] = [P_2] [P_5]^(-1)$. Since product of two elements of coprime orders $m, n$ in abelian group has order $m n$, we have $ "ord"([P_3]) = "ord"([P_2] \[overline(P_5)\]) = 2 dot.op 3 = 6 $ Also, $[P_3]^2 = \[overline(P_5)\]^2 = [P_5]$ so $[P_3]^3 = [P_2]$ and $[P_3]^4 = [P_5]^(-1)$. Hence $Cl(R)$ contains a cyclic subgroup of order $6$ generated by $[P_3]$.
]

== Finiteness of the class group

#lemma[
    Let $C > 0$, then there are finitely many ideals of $R$ of norm $<= C$.
]
#proof[
    Show if $N(I) = m$, then $I divides ideal(m)_R$, consider prime factorisation of $ideal(m)_R$.
]
#lemma[
    For any number field $K$, there is $C_K in NN$ such that for any nonzero ideal $J subset.eq R$, $ exists 0 != s in J: N(s) <= C_K dot.op N(J) $
]
#proof[
    - Let ${x_1, ..., x_n}$ be integral basis, define $f(c_1, ..., c_n) = N_K (c_1 x_1 + dots.h.c + c_n x_n)$ which is homogenous polynomial in $c_1, ..., c_n$ of degree $n$.
    - Let $C_K = max\{|f(c_1, ..., c_n)|: |c_1|, ..., |c_n| <= 1\}$, then $|f(c_1, ..., c_n)| <= max(|c_1|, ..., |c_n|)^n C_K$.
    - Let $c_i$ run through $0, ..., floor(N(I)^(1\/n))$, then there are $ (1 + floor(N(I)^(1\/n)))^n > N(I) = |R\/I| $ possibilities for $c_1, ..., c_n$.
    - By pigeonhole principle, there are $c_1, ..., c_n$ and $c'_1, ..., c'_n$ such that $ c_1 x_1 + dots.h.c + c_n x_n + I = c'_1 x_1 + dots.h.c + c'_n x_n + I $
    - Set $s = (c_1 - c'_1) x_1 + dots.h.c + (c_n - c'_n) x_n in I$, then $N(s) <= C_K N(I)$.
]
#corollary[
    Let $underline(c) in Cl(R)$, then there is ideal $I subset.eq R$ with $[I] = underline(c)$ and $N(I) <= C_K$.
]
#proof[
    Let $J subset.eq R$ such that $[J] = underline(c)^(-1)$, then there is $s in J$ with $N(s) <= C_K N_J$, so $ideal(s) = I J$ for some $I subset.eq R$, then use multiplicativity of norm.
]
#theorem[
    Let $K$ number field, $R = cal(O)_K$, then $Cl(R)$ is finite.
]
#definition[
    *Class number* of $K$ is $h_K := abs(Cl(R))$.
]

== The Minkowski bound

#theorem("Minkowski bound")[
    If $K = QQ(theta)$ and $p_theta$ has $s$ real roots, $2t$ complex roots, $n := s + 2t$, then for every $underline(c) in Cl(R)$, we can find a (non-fractional) ideal $I$ with $[I] = underline(c)$ and $ N(I) <= B_K := (4/pi)^t (n!)/(n^n) sqrt(abs(Delta_K)) $ i.e. we can take $C_K = B_K$.
]
#example[
    Let $K = QQ\(sqrt(-29)\)$, so $R = ZZ\[sqrt(-29)\]$, then every ideal class has representative of norm $<= (4\/pi) sqrt(29) < 7$ so of norm $1, 2, ..., 6$, so is product of $P_2$, $P_3$, $overline(P_3)$, $P_5$, $overline(P_5)$, so $Cl(R) = ideal([P_3])$ is cyclic of order $6$.
]
#example[
    Let $K = QQ\(sqrt(-19)\)$, so $R = cal(O)_K = ZZ\[ (1 + sqrt(-19))/2\]$, $Delta_K = -19$, then $ B_K = (4/pi) (2!)/(2^2) sqrt(19) = (2 sqrt(19))/pi < 3 $ So every element in $Cl(cal(O)_K)$ is represented by an ideal of norm $1$ or $2$. Let $N(I) = 2$, then $I$ is prime and $I | ideal(2)_R$. But minimal polynomial of $(1 + sqrt(-19))/2$ is $x^2 - x + 5$ and $x^2 - x + 4 = x^2 + x + 1 quad "irreducible in" FF_2 [x]$ so $2$ is inert in $R$, hence $I = ideal(2)_R$ and $N(ideal(2)_R) = 4$: contradiction. So $Cl(cal(O)_K) = {e}$, i.e. $cal(O)_K$ is PID, and in particular a UFD. Note that it is not an ED though.
]
#example[
    Let $K = QQ\(sqrt(-14)\)$, so $R = cal(O)_K = ZZ\[sqrt(-14)\]$. $Delta_K = 4 dot.op -14 = -56$, so $ B_K = (4/pi)^1 (2!)/2^2 sqrt(56) = (4 sqrt(14))/pi < 5 $ In general, $Cl(cal(O)_K)$ is generated by classes of prime ideals of norm $<= B_K$. By Kummer-Dedekind, $(2)_R = (2, sqrt(-14))^2 = P_2^2$ and $(3)_R = \(3, sqrt(-14) - 1\)\(3, sqrt(-14) + 1\)$. Hence if $N(I) = 4$, then $I | (2)_R^2 = P_2^4$ so $I = P_2^2 = (2)_R$. So as a set, $ Cl(R) = {e, [P_2], [P_3], [overline(P_3)] = [P_3]^(-1), [P_2^2] = e} $ The norm of a principal ideal is $N(ideal(a + b sqrt(-14))) = a^2 + 14b^2 != 2, 3, 6$ hence $P_2$, $P_3$, $overline(P_3)$, $P_2 P_3$, $P_2 overline(P_3)$ are not principal. We have $[P_2] [overline(P_3)] != e ==> [P_2] != [P_3]$, similarly $[P_2] != [overline(P_3)]$. We have $[P_3] != [overline(P_3)]$, since otherwise $[P_3]^2 = e$, so $P_3^2$ is principal and so $P_3^2 = ideal(3)$ but then $P_3 = overline(P_3)$. Thus $e, [P_2], [P_3], [overline(P_3)]$ are distinct, so $|Cl(R)| = 4$, so $Cl(R) tilde.equiv ZZ\/2 times ZZ\/2$ or $ZZ\/4$. But $[P_3]^2 != e$ so $[P_3]$ has order $4$, hence $Cl(R) tilde.equiv ZZ\/4$ is generated by $[P_3]$. Note $[overline(P_3)]^2$ and $[P_2]$ have order $2$, so $[overline(P_3)]^2 = [P_2]$, so $[P_2 P_3^2] = e$, hence $P_2 P_3^2$ is principal and there exists element in $cal(O)_K$ of norm $2 dot.op 3^2 = 18$.
]
#example[
    Let $K = QQ\(sqrt(79)\)$. Prove that $Cl(R) tilde.equiv ZZ\/3$.
    - $79 equiv.not 1 (mod 4)$ so $Delta_K = 4 dot.op 79$ so by the Minkowski bound, any element in $Cl(R)$ contains an ideal of norm at most $ B_K = (4/pi)^0 (2!)/2^2 sqrt(|Delta_K|) = sqrt(79) in (8, 9) $ Hence $Cl(R)$ is generated by the ideal classes of prime ideals dividing $2$, $3$, $5$ and $7$. By Kummer-Dedekind,
    #figure(table(
        columns: (auto, auto, auto, auto),
        inset: 8pt,
        $p$, $x^2 - 79 in FF_p [x]$, $ideal(p)_R$, $"norm of prime ideals above" p$,
        $2$, $x^2 - 1 = (x + 1)^2$, $P_2^2$, $2$,
        $3$, $x^2 - 1 = (x + 1)(x - 1)$, $P_3 overline(P_3)$, $3$,
        $5$, $x^2 - 4 = (x + 2)(x - 2)$, $P_5 overline(P_5)$, $5$,
        $7$, $x^2 - 9 = (x + 3)(x - 3)$, $P_7 overline(P_7)$, $7$
    ))
    Thus $Cl(R)$, as a set, is $ Cl(R) = & {e, [P_2], [P_3], [P_5], [P_7], [P_2]^2 = e, [P_2]^3 = [P_2], [P_2 P_3]} \ union & {[overline(P_3)], [overline(P_5)], [overline(P_7)], [P_2 overline(P_3)]} $ (since the ideals representing these classes have norm $<= 8$). Computing norms of some principal ideals $ideal(a + sqrt(79))$, letting $a$ increase up to $sqrt(79) approx 9$ to find mimimal value and other small values of the norm:
    #figure(table(
        columns: (auto, auto),
        $a$, $N(ideal(a + sqrt(79))_R) = |a^2 - 79|$,
        $0$, $79$,
        $1$, $2 dot.op 3 dot.op 13$,
        $2$, $3 dot.op 5^2$,
        $3$, $2 dot.op 5 dot.op 7$,
        $4$, $3^2 dot.op 7$,
        $5$, $2 dot.op 3^3$,
        $6$, $43$,
        $7$, $2 dot.op 3 dot.op 5$,
        $8$, $3 dot.op 5$,
        $9$, $2$,
        $10$, $3 dot.op 7$
    ))
    - So $N\(ideal(9 + sqrt(79))\) = 2 ==> ideal(7 + sqrt(79)) = P_2$ so $[P_2] = e$.
    - $N\(ideal(8 + sqrt(79))\) = 3 dot.op 5$ so $[P_3] [P_5] = e$ ($<=> [overline(P_3)] [overline(P_5)] = e$) or $[P_3] [overline(P_5)] = e$ ($<=> [overline(P_3)] [P_5] = e$). In both cases, $ {[P_5], [overline(P_5)]} = {[P_3], [overline(P_3)]} $
    - Similarly, since $N(ideal(10 + sqrt(79))) = 3 dot.op 7$, we have $ {[P_7], [overline(P_7)]} = {[P_3], [overline(P_3)]} $
    - Thus $Cl(R)$ is generated by $[P_3]$ and as a set, $Cl(R) = \{e, [P_3], [P_3]^(-1)\}$.
    - Since $N\(ideal(5 + sqrt(79))\) = 2 dot.op 27$, we have $ ideal(5 + sqrt(79)) = P_2 P_3^a overline(P_3)^(3 - a) quad "for some" a in {0, 1, 2, 3} $
    - If $a in {1, 2}$, then $P_3 overline(P_3) = ideal(3)_R | ideal(5 + sqrt(79))$: contradiction, since $3 divides.not 5 + sqrt(79)$. So WLOG assume $a = 3$ (if $a = 0$, swap $P_3$ and $overline(P_3)$. So $ideal(5 + sqrt(79)) = P_2 P_3^3$, hence $e = [P_3]^3$, so $[P_3]$ has order $1$ or $3$.
    - Assume that $P_3 = ideal(alpha)_R$, then $ P_2 P_3^3 = ideal(9 + sqrt(79)) ideal(alpha^3) = ideal(5 + sqrt(79)) $ and so $ alpha^3 = (5 + sqrt(79))/(9 + sqrt(79)) u = (-17 + 2 sqrt(79)) u quad "for some" u in R^times $
    - For any $a in R^times$, $ideal(plus.minus a alpha)_R = ideal(alpha)_R$ and $(plus.minus a alpha)^3 = \(-17 + 2 sqrt(79)\) u (plus.minus a)^3$. So without changing $P_3$, we can rescale $alpha$ by a unit and so rescale $u$ by a unit cube.
    - The fundamental unit of $R$ (by trial and error) is $v = 80 + 9 sqrt(79)$. By @main-theorem-for-units, $ R^times \/ ideal(plus.minus v^3) tilde.equiv ZZ\/3 $ (consider the map $R^times -> ZZ\/3$, $plus.minus v^r = r mod 3$ and use FIT). Thus, up to multiplication by unit cubes, there are only three possible units $1, v, v^2$ (can take $v^(-1)$ instead of $v^2$). So we can choose $alpha$ such that $u$ is $1$, $v$ or $v^(-1)$.
    - So $alpha^3$ is one of $ -17 + 2 sqrt(79), quad \(-17 + 2 sqrt(79)\)v = 62 + 7 sqrt(79), quad \(-17 + 2 sqrt(79)\) v^(-1) = -2782 + 313 sqrt(79) $
    - Let $alpha = a + b sqrt(79)$, $a, b in ZZ$, then $alpha^3 = a(a^2 + 3 dot 79b^2) + b(3a^2 + 79b^2) sqrt(79)$. We have $3 = N(P_3) = |N(alpha)| = |a^2 - 79b^2|$ so $a, b != 0$ so coefficient in $sqrt(79)$ in $alpha^3$ satisfies $|b(3a^2 + 79b^2)| >= 3 + 79 = 82$, hence $alpha^3 = -2782 + 313 sqrt(79)$. So $b(3a^2 + 79b^2) = 313$ which is prime, hence $b = 1$ and so $a^2 = 78$: contradiction.
    - So $P_3$ is not principal so has order $3$, so $Cl(R) tilde.equiv ZZ\/3$.
]

= Diophantine applications

== Mordell equations

#definition[
    A *Mordell equation* is of the form $x^2 + d = y^3$, $d in ZZ$, with solutions $x, y in ZZ$ sought.
]
#example[
    Find all solutions to the Mordell equation $y^3 = x^2 + 5$.

    - Let $K = QQ\(sqrt(-5)\)$, then $R = cal(O)_K = ZZ\[sqrt(-5)\]$. By the Minkowski bound, every element in $Cl(R)$ has representative ideal of norm at most $ (4/pi) sqrt(5) < 3 $ so as a set, $Cl(R) = {e, [P_2]}$ where $P_2 = ideal(2, 1 + sqrt(-5))$ by Kummer-Dedekind.
    - $P_2$ is not principal as $a^2 + 5b^2 = 2$ has no solutions, hence $Cl(R) tilde.equiv ZZ\/2$.
    - Let $ideal(alpha) = ideal(x + sqrt(-5))$, so $ideal(overline(alpha)) = ideal(x - sqrt(-5))$. If a prime ideal $P$ divides $ideal(alpha)$ and $ideal(overline(alpha))$, then $P | ideal(alpha - overline(alpha)) = ideal(2 sqrt(-5)) = ideal(2)_R ideal(sqrt(-5))_R = P_2^2 P_5$. $2$ and $5$ ramify, so $P_2 = overline(P_2)$ and $overline(P_5) = P_5$.
    - Hence $ ideal(alpha) & = P_2^a P_5^b Q_1^(r_1) dots.c Q_n^(r_n), \ ideal(overline(alpha))_R & = P_2^a P_5^b overline(Q_1)^(r_1) dots.c overline(Q_n)^(r_n) $ where $a, b, r_i >= 0$, all $Q_i, overline(Q_i)$ are distinct and different from $P_2$, $P_5$.
    - Then $ ideal(y)^3 = ideal(y^3) = ideal(alpha overline(alpha)) = ideal(alpha) ideal(overline(alpha)) = P_2^(2a) P_5^(2b) (Q_1 overline(Q_1))^(r_1) dots.c (Q_n overline(Q_n))^(r_n) $ By uniqueness of prime ideal factorisation, all exponents in RHS are divisible by $3$, so let $I = P_2^(a\/3) P_5^(b\/3) Q_1^(r_1\/3) dots.c Q_n^(r_n\/3)$, so that $I^3 = ideal(alpha)_R$.
    - Since $h_K = 2$, the square of any fractional ideal of $R$ is principal, so $(I^(-1))^2$ is principal, hence $I = I^3 (I^(-1))^2 = alpha (I^(-1))^2$ is principal, so let $I = ideal(beta)_R$, for $beta = s + t sqrt(-5) in R$.
    - Now $ideal(beta^3) = I^3 = ideal(alpha)$ so $beta^3 = u alpha$ for some $u in R^times$. But only units in $R$ are $plus.minus 1$. Since $I = ideal(-beta)$, can assume that $beta^3 = alpha$. Then $ s^3 + 3s t^2 (-5) + (3s^2 t + t^3(-5))sqrt(-5) = x + sqrt(-5) $
    - So $s^3 - 15s t^2 = x$, $3s^2 t - 5t^3 = 1$. Hence $t = plus.minus 1$, and both possibilities yield no integer solutions to the second equation, so $x^2 + 5 = y^3$ has no integer solutions.
]
#example[
    Let $K = QQ\(sqrt(-31)\)$, it can be shown with Minkowski bound that $h_K = 3$ so $Cl(R) = ideal([P_2]) tilde.equiv ZZ\/3$ where $P_2 = ideal(2, (1 + sqrt(-31))\/2)$. Show that $ x^2 + 31 = y^3 $ has no solutions $x, y in ZZ$.
    - Assume $x, y$ is a solution. $31 divides.not x$, as otherwise $31^2 | (y^3 - x^2) = 31$ (since $31$ is prime): contradiction.
    - $x$ is odd and $y$ is even:
        - If $x$ even, $y$ is odd and $y^3 equiv 31 equiv -1 mod 4$ so $y equiv -1 mod 4$. Now $x^2 + 4 = y^3 - 27 = (y - 3)(y^2 + 3y + 9)$.
        - $y^2 + 3y + 9 equiv -1 mod 4$. Hence $y^2 + 3y + 9$ is divisible by prime $p equiv 3 mod 4$ (since product two numbers of form $4n + 1$ is also of this form). So $x^2 + 4 equiv 0 mod p$. Hence $(x\/2)^2 equiv -1 mod p$ so $(x\/2)^(p - 1) equiv (-1)^((p - 1)/2) equiv -1$ as $p equiv 3 mod 4$ which contradicts Fermat's little theorem. Hence $x$ is odd so $y$ is even.
    - Now $\(x + sqrt(-31)\)\(x - sqrt(-31)\) = y^3$. $x$ is odd, so $alpha := (x + sqrt(-31))\/2 in R$. Let $y = 2z$, $z in ZZ$, then $alpha overline(alpha) = 2z^3$ and $ideal(alpha) ideal(overline(alpha)) = ideal(2) ideal(z)^3$.
    - If $P | ideal(alpha), ideal(overline(alpha))$, then $alpha, overline(alpha) in P$, so $sqrt(-31) = alpha - overline(alpha) in P$, hence $P = ideal(sqrt(-31))$ (this is prime since norm is $31$, a prime).
    - But then $x = alpha + overline(alpha) in P sect ZZ = ideal(31)_ZZ$, but $31 divides.not x$, so we have a contradiction. So $ideal(alpha)$, $ideal(overline(alpha))$ are coprime ideals.
    - WLOG, $ideal(alpha) = P_2^a Q_1^(r_1) dots.c Q_n^(r_n)$ and $ideal(overline(alpha)) = overline(P_2)^a overline(Q_1)^(r_1) dots.c overline(Q_n)^(r_n)$ with $P_2$, $overline(P_2)$, all $Q_i, overline(Q_i)$ distinct.
    - Then $ideal(alpha) ideal(overline(alpha)) = ideal(2)^a (Q_1 overline(Q_1))^(r_1) dots.c (Q_n overline(Q_n))^(r_n) = ideal(2) ideal(z)^3$.
    - Hence $a equiv 1 mod 3$ and for all $i$, $3 | r_i$. So $ideal(alpha) = P_2 I^3$ for some ideal $I$.
    - Now $[ideal(alpha)] = e$ and $[I^3] = [I]^3 = e$ as $h_K = 3$. Hence $[P_2] = e$ so $P_2$ is principal.
    - So $P_2 = ideal(\(u + v sqrt(-31)\)\/2)$, $u, v in ZZ$, $u equiv v mod 2$.
    - Then $2 = N(P_2) = (u^2 + 31v^2)\/4$ hence $8 = u^2 + 31v^2$: contradiction.
]

== Generalised Pell equations

#definition[
    A *generalised Pell equation* is of the form $ x^2 - d y^2 = n, quad n in ZZ, d in NN "square-free" $ i.e. determine whether $n$ is a norm from $ZZ\[sqrt(d)\]$.
]
#definition[
    Let $K = QQ\(sqrt(14)\)$. Solve $x^2 - 14y^2 = plus.minus 5$. We can assume $R = ZZ\[sqrt(14)\]$ is PID and so a UFD (can be proven using Minkowski bound by showing $h_K = 1$).
    - By trial and error, fundamental unit is $u = 15 + 4 sqrt(14)$ and $N(u) = 15^2 - 14 dot 16 = 1$.
    - We have $N\(3 - sqrt(14)\) = -5$ so $ideal(5) = ideal(3 + sqrt(14)) ideal(3 - sqrt(14))$ by Kummer-Dedekind.
    - Now $ideal(x + y sqrt(14)) ideal(x - y sqrt(14)) = ideal(3 + sqrt(14)) ideal(3 - sqrt(14))$. The ideals on the LHS are conjugate, and ideals on RHS are prime so $ideal(x + y sqrt(14)) = ideal(3 plus.minus sqrt(14))$.
    - Hence $x + y sqrt(14) = plus.minus \(15 + 4 sqrt(14)\)^n \(3 plus.minus sqrt(14)\)$ for some $n in ZZ$ and $x - y sqrt(14) = plus.minus \(15 - 4 sqrt(14)\)^n \(3 minus.plus sqrt(14)\)$ which gives all solutions $x, y in ZZ$.
    - *Note*: $N\(x + y sqrt(14)\) = x^2 - 14y^2 = N(u)^n N\(3 plus.minus sqrt(14)\) = 1^n dot -5 = -5$ so all solutions must have $-5$ on RHS.
]
#example[
    Solve $x^2 - 79y^2 = plus.minus 15$ for $x, y in ZZ$.

    - Let $K = QQ\(sqrt(79)\)$, so $R = cal(O)_K = ZZ\[sqrt(79)\]$. We have that $Cl(R) tilde.equiv ZZ\/3$, generated by $[P_3]$.
    - $x^2 - 79 equiv (x + 1)(x - 1) mod 3$ so $ideal(3)_R = P_3 overline(P_3) = ideal(3, 1 + sqrt(79)) ideal(3, 1 - sqrt(79))$ by Kummer-Dedekind.
    - $x^2 - 79 equiv (x + 2)(x - 2) mod 5$ so $ideal(5)_R = P_5 overline(P_5) = ideal(2 + sqrt(79)) ideal(2 - sqrt(79))$ by Kummer-Dedekind.
    - We have $ideal(x + y sqrt(79)) ideal(x - sqrt(79)) = ideal(15)_R = P_3 overline(P_3) P_5 overline(P_5)$. Since $overline(ideal(x + y sqrt(79))) = ideal(x - y sqrt(79))$, we have $x plus.minus y sqrt(79) = P_3 P_5$ or $P_3 overline(P_5)$.
    - Note $8^2 - 79 = -15$, thus $ideal(8 + sqrt(79)) = overline(P_3) overline(P_5)$ as $8 + sqrt(79) = 9 - \(1 - sqrt(79)\) = 10 - \(2 - sqrt(79)\)$. Hence $[overline(P_3)] [overline(P_5)] = e$ so $[P_5] = [P_3]^(-1) != [P_3]$.
    - So $P_3 P_5$ is principal and $P_3 overline(P_5)$ isn't. Hence $ideal(x plus.minus y sqrt(79)) = P_3 P_5 = ideal(8 - sqrt(79))$.
    - Therefore, $x plus.minus y sqrt(79) = plus.minus u^n \(8 - sqrt(79)\)$ where $u = 80 + 9 sqrt(79)$ is fundamental unit in $R$, $n in ZZ$ and this gives all solutions to $x, y in ZZ$.
    - Since $N(u) = 1$, $x^2 - 79y^2 = N("LHS") = N\(8 - sqrt(79)\) = -15$ so the only solutions are for $-15$, there are none for $15$.
]