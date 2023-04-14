#import "../template.typ": template
#show: template

= Rings, subrings and fields

- *Ring $R$*: set with binary operations addition and subtraction, where $(R, +)$ is an abelian group and:
	- *Identity*: exists $1 in R$ such that $forall x in R, 1 dot.op x = x dot.op 1 = x$
	- *Associativity*: for every $x, y, z in R, x(y z) = (x y)z$
	- *Distributivity*: for every $x, y, z in R, x(y + z) = x y + x z$ and $(y + z)x = y x + z x$
- *Set of remainders modulo $n$* (*residue classes*): $ZZ \/ n = {overline(0), overline(1), ..., overline(n - 1)}$
- $ZZ \/ n$ is a ring: $overline(a) + overline(b) = overline(a + b), overline(a) - overline(b) = overline(a - b), overline(a) dot.op overline(b) = overline(a dot.op b)$
- *Subring $S$* of ring $R$: a set $S subset.eq R$ that contains $0$ and $1$ and is closed under addition, multiplication and negation:
	- $0 in S$, $1 in S$
	- $forall a, b in S, a + b in S$
	- $forall a, b in S, a b in S$
	- $forall a in S, -a in S$
- *Field $F$* is a ring with:
	- $F$ is commutative
	- $0 != 1 in F$ ($F$ has at least two elements)
	- $forall 0 != a in R$, $exists b in R$, $a b = 1$. $b$ is the *inverse* of $a$
- $a$ is a *zero divisor* if $a b = 0$ for some $b != 0$

= Integral domains

- *Integral domain $R$*: ring which is commutative, has at least two elements ($0 != 1$), and has no zero divisors apart from $0$
- Any subring of a field is an integral domain
- If $R$ is an integral domain, then $R[x] = {a_0 + a_1 x + ... + a_n x^n : a_i in R}$ is also an integral domain.
- $a$ is a *unit* if $a b = b a = 1$ for some $b in R$. $b = a^(-1)$ is the *inverse* of $a$
- Inverses are unique
- $R^times$, set of all units in $R$, is a group under multiplication of $R$
- For field $F$, $F^times = F - {0}$
- $a in ZZ \/ n$ is a unit iff $gcd(a, n) = 1$
- $ZZ \/ p$ is a field iff $p$ is prime
- $ZZ \/ n$ is an integral domain iff $n$ is prime (iff $ZZ \/ n$ is a field)

= Polynomials over a field

- *Degree* of $f(x) = a_0 + a_1 x + ... + a_n x^n$:
$ deg(f) = cases(
	max{i: a_i != 0} & "if" f != 0,
	-oo & "if" f = 0
) $
- $deg(f g) = deg(f) + deg(g)$
- $deg(f + g) <= max{deg(f), deg(g)}$
- If $deg(f) != deg(g)$ then $deg(f + g) = max{deg(f), deg(g)}$
- Let $f(x), g(x) in F[x]$, $g(x) != 0$, then $exists q(x), r(x) in F[x]$ with $deg(r) < deg(g)$ such that $f(x) = q(x) g(x) + r(x)$

= Divisibility and greatest common divisor in a ring

- $a$ *divides* $b$, $a | b$, if $exists r in R$ such that $b = r a$
- $d$ is a *greatest common divisor* of $a$ and $b$, $gcd(a, b)$, if:
	- $d | a$ and $d | b$ and
	- If $e | a$ and $e | b$ then $e | d$
- $gcd(0, 0) = 0$
- *Euclidean algorithm example*: find $gcd$ of $f(x) = x^2 + 7x + 6$ and $g(x) = x^2 - 5x - 6$ in $QQ[x]$: $ f(x) & = g(x) + 12(x + 1) \ g(x) & = 1/12 x dot.op 12(x + 1) - 6(x + 1) \ 12(x + 1) & = -2 dot.op -6(x + 1) + 0 $ Remainder is now zero so stop. A $gcd$ is given by the last non-zero remainder, $-6(x + 1)$. We can write $-6(x + 1)$ as a combination of $f(x)$ and $g(x)$: $ -6(x + 1) & = g(x) - 1/12 x dot.op 12(x + 1) \ & = g(x) - 1/12 x dot.op (f(x) - g(x)) \ & = (1 + 1/12 x) g(x) - 1/12 x f(x) $
- Let $R$ be integral domain, $a, b in R$ and $d = gcd(a, b)$. Then $forall u in R^times$, $u d$ is also a $gcd(a, b)$. Also, for $d$ and $d'$ $gcd$s of $a$ and $b$, $exists u in R^times$ such that $d = u d'$ (so $gcd$ is unique up to units).
- Polynomial is *monic* if leading coefficient is $1$
- There always exists a unique monic $gcd$ of two polynomials in $F[x]$
- Let $R = ZZ "or" F[x]$, $a, b in R$. Then
	- A $gcd(a, b)$ always exists
	- $a != 0 "or" b != 0$ then a $gcd(a, b)$ can be computed by Euclidean algorithm
	- If $d$ is a $gcd(a, b)$ then $exists x, y in R$ such that $a x + b y = d$

= Factorisations in rings

- $r in R$ *irreducible* if:
	- $r in.not R^times$ and
	- If $r = a b$ then $a in R^times$ or $b in R^times$
- $a in F$ is *root* of $f(x) in F[x]$ if $f(a) = 0$
- Let $f(x) in F[x]$.
	- If $deg(f) = 1$, $f$ is irreducible.
	- If $deg(f) = 2 "or" 3$ then $f$ is irreducible iff it has no roots in $F$.
	- If $deg(f) = 4$ then $f$ is irreducible iff it has no roots in $F$ and it is not the product of two quadratic polynomials.
- Let $f(x) = a_0 + a_1 x + ... + a_n x^n in ZZ[x]$, $deg(f) >= 1$. If $f(p \/ q) = 0$, $gcd(p, q) = 1$, then $p | a_0$ and $q | a_n$.
- *Gauss's lemma*: let $f(x) = a_0 + a_1 x + ... + a_n x^n in ZZ[x]$, $deg(f) >= 1$. Then $f(x)$ is irreducible in $ZZ[x]$ iff it is irreducible in $QQ[x]$ and $gcd(a_0, a_1, ..., a_n) = 1$.
- If monic polynomial in $ZZ[x]$ factors in $QQ[x]$ then it factors into integer monic polynomials.
- Let $R$ be commutative, $x in R$ be irreducible and $u in R^times$. Then $u x$ is also irreducible.
- *Eisenstein's criterion*: let $f(x) = a_0 + a_1 x + ... + a_n x^n in ZZ[x]$, $p$ be prime with $p divides a_0$, $p divides a_1, ..., p divides a_(n - 1)$, $p divides.not a_n$, $p^2 divides.not a_0$. Then $f(x)$ is irreducible in $QQ[x]$
- Let $f(x) in F[x]$, then $f$ can be uniquely factorised into a product of irreducible elements, up to order of factors and multiplication by units.
- Let $R$ be commutative. $x in R$ is *prime* if:
	- $x != 0$ and $x in.not R^times$ and
	- If $x divides a b$ then $x divides a$ or $x divides b$
- If $R = ZZ "or" F[x]$ then $a in R$ is prime iff it is irreducible.
- Let $R$ be an integral domain and $x in R$ prime. Then $x$ is irreducible.
- Integral domain $R$ is *unique factorisation domain (UFD)* if every non-zero non-unit element in $R$ can be written as a unique product of irreducible elements, up to order of factors and multiplication by units.

= Ring homomorphisms

- For $R, S$ rings, $f: R -> S$ is *homomorphism* if:
	- $f(1) = 1$ and
	- $f(a + b) = f(a) + f(b)$ and
	- $f(a b) = f(a) f(b)$
- Let $f: R -> S$ homomorphism, then
	- $f(0) = 0$ and
	- $f(-a) = f(a)$
- *Kernel*: $ ker(f) := {a in R: f(a) = 0} $
- *Image*: $ "Im"(f) := {f(a): a in R} $
- *Isomorphism*: bijective homomorphism.
- $R$ and $S$ *isomorphic*, $R tilde.eqq S$ if there exists isomorphism between them.
- Homomorphism $f$ injective iff $ker(f) = {0}$.
- *Direct product* of $R$ and $S$, $R times S$:
	- $(r, s) + (r', s') = (r + r', s + s')$.
	- $(r, s) (r', s') = (r r', s s')$.
	- Identity is $(1, 1)$.
- For $p_1(r, s) = r$ and $p_2(r, s) = s$, $ker(p_1) = {(0, s): s in S}$ and $ker(p_2) = {(r, 0): r in R}$. These are both rings, with $ker(p_1) tilde.eqq S$ (via $(0, s) -> s$) and $ker(p_2) tilde.eqq R$ (via $(r, 0) -> r$). ($ker(p_1)$ and $ker(p_2)$ are not subrings of $R times S$ though). So $ ker(p_1) times ker(p_2) tilde.eqq R times S $

= Ideals and quotient rings

- $I subset.eq R$ is an *ideal* if $I$ closed under addition and if $x in I$, $r in R$ then $r x in I$ and $x r in I$.
- *Left ideal*: $I$ closed under addition and if $x in I$, $r in R$ then $r x in I$.
- *Right ideal*: $I$ closed under addition and if $x in I$, $r in R$ then $x r in I$.
- If $x in I$, then $(-1)x = x(-1) = -x in I$ so $I$ closed under negation.
- For $f: R -> S$ homomorphism, $ker(f)$ is ideal of $R$.
- For $R$ commutative ring and $a in R$, *principal ideal generated by $a$* is $ (a) := {r a: r in R} $
- For $R$ commutative and $a_1, ... a_n in R$, $ (a_1, ..., a_n) := {r_1 a_1 + dots.h.c + r_n a_n: r_1, ..., r_n in R} $ is an ideal. $(a_1, ..., a_n)$ is *generated* by $a_1, ..., a_n$. $a_i in (a_1, ..., a_n)$ for all $i$.
- If ideal $I$ contains unit $u$, then $u^(-1) u = 1 in I$ so $forall r in R, r dot.op 1 = r in I$. So $R subset.eq I$ so $R = I$.
- For field $F$, any ideal is either ${0}$ or $F$.
- Let $I_1 = (a_1, ..., a_m)$, $I_2 = (b_1, ..., b_n)$ then $I_1 = I_2$ iff $a_1, ..., a_m in I_2$ and $b_1, ..., b_n in I_1$.
- $a, b in R$ *equivalent modulo $I$* if $a - b in I$. Write $overline(a) = overline(b)$ or $a ident b quad (mod I)$.
- Let $a(x) in QQ[x]$, then $p(x) = q(x) a(x) + r(x)$ with $deg(r) < deg(a)$. $p(x) - r(x) = q(x) a(x) in (a(x))$ so $overline(p(x)) = overline(r(x))$. $r(x)$ is *representative* of the class $overline(p(x))$.
- Let $I subset.eq R$ ideal. *Coset* of $I$ generated by $x in I$ is $ overline(x) := x + I = {x + r: r in I} subset.eq R $ $x$ is a *representative* of $x + I$.
- For $x, y in R$, $ x + I = y + I <==> x + I sect y + I != nothing <==> x - y in I $
- If $x$ is a representative of $x + I$, so is $x + r$ for every $r in I$.
- *Quotient* of $R$ by $I$ ("$R mod I$"): set of all cosets of $R$ by $I$: $ R \/ I := {overline(x): x in R} = {x + I: x in R} $ with
	- $(x + I) + (y + I) = (x + y) + I$.
	- $(x + I) (y + I) = x y + I$.
- $R \/ I$ is a ring, with zero element $0 + I = I$ and identity $1 + I in R \/ I$.
- *Quotient map (canonical map/homomorphism)*: $R -> R \/ I$, $r -> overline(r) = r + I$.
- Kernel of quotient map is $I$ and image is $R \/ I$. Hence every ideal is a kernel.
- *First isomorphism theorem (FIT)*: Let $phi: R -> S$ be homomorphism. Then $ overline(phi): R \/ ker(phi) -> "Im"(phi), overline(phi)(overline(x)) = phi(x) $ is an isomorphism: $R \/ ker(phi) tilde.eqq "Im"(phi)$.

= Prime and maximal ideals

- Ideal $I subset.eq R$ *prime ideal* if $I != R$ and $a b in I ==> a in I$ or $b in I$.
- $I subset.eq R$ *maximal* if only ideals containing $I$ are $I$ and $R$ (so no ideals strictly between $I$ and $R$).
- $x in R$ is prime iff $(x)$ is prime ideal.
- To contain is to divide: $ a in (x) <==> (a) subset.eq (x) <==> x | a $
- For $R$ commutative and $I$ ideal:
	- $I$ prime iff $R \/ I$ integral domain.
	- $I$ maximal iff $R \/ I$ field.
- $(I, x)$ is ideal generated by $I$ and $x$: $ (I, x): {r x + x': r in R, x' in I} $
- If $I$ is maximal ideal, then it is prime.

= Principal ideal domains

- *Principal ideal domain (PID)*: integral domain where every ideal is principal.
- $ZZ$, $F[x]$, $ZZ[i]$ and $ZZ[sqrt(plus.minus 2)]$ are PIDs.
- Every PID is a UFD.
- Let $R$ be PID and $a, b in R$. Then $d = gcd(a, b)$ exists and $(d) = (a, b)$.

= Fields as quotients

- Let $R$ be PID, $a in R$ irreducible. Then $(a)$ is maximal.
- Let $f(x) in F[x]$ irreducible. Then $F[x] \/ (f(x))$ is field and $F[x] \/ (f(x))$ is a vector space over $F$ with basis ${overline(1), overline(x), ..., overline(x)^(n - 1)}$ where $n = deg(f)$. So every element in $F[x] \/ f(x)$ can be uniquely written as $overline(a_0 + a_1x + dots.h.c + a_(n - 1) x^(n - 1))$, $a_i in F$.
- Let $p$ prime and $n in NN$, then there exists irreducible $f(x) in (ZZ \/ p)[x]$ with $deg(f) = n$ and $(ZZ \/ p)[x] \/ (f(x))$ is a field with $p^n$ elements. Any two such fields are isomorphic so unique (up to isomorphism) field with $p^n$ elements is written $FF_(p^n)$.

= The Chinese remainder theorem

- $a, b in R$ *coprime* if no irreducible element divides $a$ and $b$.
- Let $R$ be PID, $a, b in R$ coprime. Then $(a, b) = (1) = R$ so $a x + b y = 1$ for some $x, y in R$. So any $gcd(a, b)$ is a unit.
- *Chinese remainder theorem (CRT)*: Let $R$ be PID, $a_1, ..., a_k$ pairwise coprime. Then $ phi: R \/ (a_1 dots.h.c a_k) -> R \/ (a_1) times dots.h.c times R \/ (a_k) \ phi(r + (a_1 dots.h.c a_k)) = (r + (a_1), ..., r + (a_k)) $ is an isomorphism.