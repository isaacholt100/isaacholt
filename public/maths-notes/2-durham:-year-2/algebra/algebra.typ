#import "../../template.typ": template
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
	- $f(-a) = -f(a)$
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

= Basics of groups

- *Group* $(G, compose)$: set $G$ with binary operation $compose: G times G -> G$ satisfying:
	- *Closure*: $g compose h in G, h compose g in G$.
	- *Associativity*: $a compose (b compose c) = (a compose b) compose c$.
	- *Identity*: $g compose e = g$ and $e compose g = g$ for some $e in G$.
	- *Inverse*: $g compose h = h compose g = e$ for some $h = g^(-1) in G$.
- Group *abelian* if $compose$ commutative: $g compose h = h compose g$.
- $H subset.eq G$ is *subgroup* of $(G, compose)$, $H < G$ if $H$ is group under same operation.
- Subgroup $H$ *proper* if $H != {e}$ and $H != G$.
- *Subgroup criterion*: $H < G$ iff:
	- $H$ non-empty.
	- $h_1, h_2 in H ==> h_1 compose h_2 in H$.
	- $h in H ==> h^(-1) in H$.
- *Order* of group $G$ is number of elements in it, $|G|$.
- *Lagrange's theorem*: Let $G$ finite, $H < G$, then $ \#H divides \#G $
- Let $H < G$, $g in G$. *Left coset* of $g$ with respect to $H$ in $G$: $ g compose H := {g compose h: h in H} $
- All left cosets with respect to $H$ have same cardinality as cardinality of $H$.
- *Right coset* of $g in G$ with respect to $H < G$ in $G$: $ H compose g := {h compose g: h in H} $
- $H < G$ *normal*, $H triangle.stroked.small.l G$, if $forall g in G, g H = H g$.
- $H$ is normal iff $forall g in G$, $ forall h in H, g h g^(-1) in H <==> g H g^(-1) subset H $ where $g H g^(-1) = {g h g^(-1): h in H}$.
- Every subgroup of abelian group is normal.
- *Subgroup of $G$ generated by $g$*: $ angle.l g angle.r := {g^n: n in ZZ} $
- *Subgroup of $G$ generated by $S subset.eq G$*: $ angle.l S angle.r := {"all finite products of elements in" S "and their inverses"} $ so if $G$ abelian (doesn't hold for non-abelian), for $S = {g_1, ..., g_n}$, $ angle.l S angle.r = {g_1^(a_1) dots.h.c g_n^(a_n): a_i in ZZ} $
- If $G$ not abelian, $ angle.l g, h angle.r = {g^(a_1) h^(b_1) dots.h.c g^(a_m) h^(a_m)} $
- *Order* of $g in G$, $"ord"_G(g)$ is smallest $r > 0$ such that $g^r = e$. If $r$ doesn't exist, order is $oo$.
- Order of $overline(m) in ZZ \/ n$ is $n \/ gcd(m, n)$.

= Specific families of groups

- Quaternion group: $ Q_8 = {plus.minus 1 plus.minus i, plus.minus j, plus.minus k}, quad i^2 = j^2 = k^2 = -1, i j = k = -j i $
- *Cyclic group*: can be generated by single element.
- *Example of cyclic group*: $ C_n = {e^((2 pi i) / n k): 0 <= k < n} $
- Cyclic groups are abelian.
- If $|G|$ is prime, $G$ is cyclic and is generated by any $e != g in G$.
- *Permutation* of $X != nothing$: bijection $X -> X$.
- $S_X := {"bijection" X -> X}$.
- *Notation*: $S_n := S_{1, ..., n}$.
- $(S_X, compose)$ is group where $compose$ is composition of permutations.
- $(S_n, compose)$ is *symmetric group of degree $n$* (or *symmetric group on $n$ letters*).
- *Notation*: write $sigma in S_n$ as $ mat(1, 2, ..., n; sigma(1), sigma(2), ..., sigma(n)) $
- $|S_n| = n!$.
- *Cycle of length $k$ (or $k$-cycle)*: permutation $sigma$ in $S_n$, with $ sigma(i_1) = i_2, quad sigma(i_2) = i_3, ..., sigma(i_(k - 1)) = i_k, quad sigma(i_k) = i_1 $ and leaves all other elements fixed. Write as $(i_1 space i_2 space ... space i_k)$ or $ mat(i_1, i_2, ..., i_k; i_2, i_3, ..., i_1) $
- $2$-cycles are *transpositions* (or *inversions*).
- $k$-cycle has order $k$.
- There are $k$ ways of writing $k$ cycle.
- Cycles are *disjoint* if they don't have any common elements.
- Disjoint cycles commute.
- Every permutation is product of disjoint cycles, unique up to swapping cycles and $k$ ways of writing a $k$-cycle.
- $k$-cycle can be written as product of transpositions: $ (i_1 space i_2 space ... space i_k) = (i_1 space i_2) (i_2 space i_3) dots.h.c (i_(k - 1) space i_k) $
- When composing cycles, *work right to left*.
- $g, g' in G$ *conjugate* in $G$ to each other if for some $h in G$, $h g h^(-1) = g'$.
- Any conjugate of transposition in $S_n$ is transposition.
- Every $sigma in S_n$ can be factored into product of transpositions.
- *Parity* of number of transpositions needed in any factorisation of $sigma$ is the same. So remainder of this number modulo $2$ is well-defined.
- Element made of disjoint cycles of lengths $k_1, ..., k_m$ has order $"lcm"(k_1, ..., k_m)$.
- *Sign of permutation $sigma$*: $ "sgn"(sigma) := (-1)^t = cases(
	1 & "if" t "is even",
	-1 & "if" t "is odd"
) $ where $t$ is number of transpositions needed in factorisation of $sigma$. If $t$ even, $sigma$ is *even*, else $sigma$ is *odd*.
- *Alternating group*, $A_n$: subgroup of even permutations of $S_n$.
- $|A_n| = (n!) / 2$.
- $A_n$ normal in $S_n$.
- $A_n$ generated by $3$-cycles.
- *Isometry*: map from plane to itself which preserves distances between points.
- For $n >= 3$, there are $2n$ isometries of the plane which preserve regular $n$-gon.
- Group of isometries of regular $n$-gon form group, the *dihedral group*, $D_n$.
- $D_n$ *alternative definition*: group with two generators $r$ (rotation) and $s$ (reflection), with $s r s^(-1) = r^(-1)$, $r^n = e$ and $s^2 = e$. So $D_n = angle.l r, s angle.r$.
- Every element in $D_n$ can be written $r^j s^k$, $0 <= j < n$, $0 <= k <= 1$.
- $|D_n| = 2n$.
- Rotations of plane which preserve regular $n$-gon form cyclic subgroup of $D_n$, which is normal in $D_n$.

= Relating, identifying and distinguishing groups

- *Group homomorphism*: map $phi: G -> G'$ between groups, with $ phi(g_1 g_2) = phi(g_1) phi(g_2) $
- *Group isomorphism*: bijective group homomorphism.
- $G$ and $G'$ *isomorphic*, $G tilde.eqq G'$ if exists isomorphism between them.
- *Kernel* of group homomorphism: $ ker(phi) := {g in G: phi(g) = e} $
- *Image* of group homomorphism: $ "im"(phi) := {phi(g): g in G} $
- $ker(phi)$ is normal subgroup of $G$.
- $"im"(phi)$ is subgroup of $G'$.
- Let $N$ normal subgroup of $G$. *Quotient group (factor group)* of $G$ with respect to $N$, is $G \/ N := {g N: g in G}$, with group multiplication $ (g_1 N) (g_2 N) = (g_1 g_2) N $ and inverse $ (g N)^(-1) = (g^(-1)) N $
- *First isomorphism theorem for groups (FIT)*: let $phi: G -> G'$ homomorphism, then $ G \/ ker(phi) tilde.eqq "im"(phi) $
- Let $p$ prime, then every group of order $p$ is isomorphic to $(ZZ \/ p, +)$.
- Each cyclic group of order $n$ isomorphic to $(ZZ \/ n, +)$.
- Each infinite cyclic group isomorphic to $(ZZ, +)$.
- For groups $G, H$, $G times H$ also a group, with $e = (e_G, e_H)$, $(g, h) compose (g', h') = (g compose_G g', h compose_H h')$, inverse $(g, h)^(-1) = (g^(-1), h^(-1))$.
- $ZZ \/ 2 times ZZ \/ 3 tilde.eqq ZZ \/ 6$.
- $ZZ \/ (m n) tilde.eqq ZZ \/ m times ZZ \/ n <==> gcd(m, n) = 1$.
- Group isomorphism preserves:
	- Order of group.
	- Set of orders of elements (with multiplicity - i.e. count repeated occurences of an order).
	- Size of its centre.
	- Property of being abelian/non-abelian.
	- Property of having proper (normal) subgroups and their sizes.
- *Notation*: for $E_1, E_2 subset.eq G$, $ E_1 compose E_2 := {e_1 compose e_2: e_1 in E_1, e_2 in E_2} $
- Let $H, K$ subgroups of $G$ with:
	- $H compose K = G$,
	- $H sect K = {e}$,
	- $forall h in H, k in K, h k = k h$.
	Then $G tilde.eqq H times K$.
- Group of symmetries of unit cube in $RR^3$ isomorphic to $S_4$.
- *Cayley's theorem*: Every group $(G, dot.op)$ is isomorphic to a subgroup of $(S_G, compose)$ where $S_G$ is set of bijections of $G$ by the isomorphism $psi(g) = L_g$, where $L_g(h) = g h$.

= Group actions

- *Action of group $G$ on non-empty set $X$*: homomorphism $ phi: G -> S_X $ $G$ acts on $X$.
- Let $phi: G -> S_X$ group action, $x in X$. *Orbit* of $x$ inside $X$ is $ G(x) := cal(O)(x) := {phi(g)(x): g in G} $
- Let $phi: G -> S_X$ group action, $x in X$. *Stabiliser* of $x$ in $G$ is $ G_x := "Stab"_G(x) := {g in G: phi(g)(x)= x} $
- For every $x in X$, $"Stab"_G(x)$ is subgroup of $G$.
- *Notation*: can write $g(x)$ instead of $phi(g)(x)$.
- Let $phi: G -> S_X$ group action. Then all orbits $cal(O)(x)$ partition $X$ so:
	- Every orbit non-empty subset of $X$.
	- Union of all orbits is $X$.
	- Two orbits either disjoint or equal.
- Action of group on itself:
	- By left translation: $g(h) = g h$.
	- By conjugation: $g(h) = g h g^(-1)$.
- *Conjugacy class* of $g in G$ is set of all elements conjugate to $g$: $ "ccl"_G(g) := {h g h^(-1): h in G} $
- Conjugacy class of $g$ is orbit of conjugation action of $g$.
- Conjugacy classes of $G$ all of size $1$ iff $G$ abelian.
- *Orbit-stabiliser theorem*: Let $G$ act on $X$. Then $forall x in X$, exists bijection $ beta: cal(O)(x) -> {"left cosets of" "Stab"_G(x) "in" G} \ beta(g(x)) = g "Stab"_G(x) $
- *Consequence of Orbit-Stabiliser theorem*: if finite $G$ acts on finite $X$, then $forall x in X$, $ |cal(O)(x)| dot.op |"Stab"_G(x)| = |G| $
- So size of each conjugacy class in $G$ divides $|G|$.
- If $x in cal(O)(y)$, then $"Stab"_G(x)$ and $"Stab"_G(y)$ conjugate to each other: $ exists h in G, quad "Stab"_G(x) = h "Stab"_G(y) h^(-1) $ (here $h(y) = x$).

= Cauchy's theorem and classification of groups of order $2p$

- *Cauchy's theorem*: let $G$ finite group, $p$ prime, $p divides |G|$. Then exists subgroup of $G$ of order $p$.
- Let $p$ odd prime, then any group of order $2p$ is either cyclic or dihedral.

= Classification of groups of order $p^2$

- *Centre* of group $G$: $ Z(G) := {g in G: forall h in G, g h = h g} $
- $Z(G)$ is normal subgroup of $G$.
- $Z(G)$ is union of all conjugacy classes of size $1$. So every $z in Z(G)$ has $|"ccl"_G(z)| = 1$.
- $Z(G) = G$ iff $G$ abelian.
- If $G$ acts on itself via conjugation then for every $h in G$, $Z(G) subset "Stab"_G(h)$.
- Let $p$ prime, $|G| = p^r$, $r >= 0$. Then $Z(G)$ non-trivial ($Z(G) != {e}$).
- If $|G| = p^2$, $p$ prime, then $G$ abelian.
- Let $p$ prime, $|G| = p^2$. Then $G tilde.eqq ZZ \/ p^2$ or $G tilde.eqq ZZ \/ p times ZZ \/ p$.
- *Sylow's theorem*: let $G$ group, $|G| = p^r m$, $gcd(p, m) = 1$. Then $G$ has subgroup of order $p^r$ (and subgroup of order $p^i$ for all $1 <= i <= r$).

= Classification of finitely generated abelian groups

- $G$ *finitely generated* if exists set ${g_1, ..., g_r}$ such that $G = angle.l g_1, ..., g_r angle.r$.
- Any finitely generated abelian group can be written as $ G tilde.eqq ZZ^n \/ K $ for some $n >= 0$, $K$ is subgroup of $ZZ^n$, $K = {underline(a) in ZZ^n: a_1 g_1 + dots.h.c + a_n g_n = 0}$. $underline(a) in K$ is *relation* and $K$ is *relation subgroup* of $G$.
- $G$ is *free abelian group of rank $n$* if no non-trivial solutions in $K$, i.e. $a_1 g_1 + dots.h.c + a_r g_r = 0 ==> a_1 = dots.h.c = a_r = 0$. Here, $K = {underline(0)}$.
- Every subgroup of $ZZ^n$ is free abelian group generated by $r <= n$ elements, so rank $<= n$.
- *Fundamental theorem of finitely generated abelian groups*: let $G$ be finitely generated abelian group. Then $ G tilde.eqq ZZ \/ d_1 times dots.h.c times ZZ \/ d_k times ZZ^r $ where $r >= 0$, $k >= 0$, $d_j >= 1$. If $d_1 divides d_2 divides dots.h.c divides d_k$ and $d_1 > 1$, then this form is unique.
- $r$ is *rank* of $G$, $d_1, ..., d_k$ are *torsion invariants (torsion coefficients)*. Torsion coefficients are given with repetitions (multiplicities).
- To classify all groups of order $n$, use that $d_1 dots.h.c d_k = n$ and $1 < d_1 divides d_2 divides dots.h.c divides d_k$.
- Let $e != x in S_n$ be written as product of disjoint cycles: $ x = (a_1 space a_2 space ... space a_(k_1)) (b_1 space b_2 space ... space b_(k_2)) dots.h.c (t_1 space t_2 space ... space t_(k_r)) $ where $r >= 1$, $2 <= k_1 <= k_2 <= dots.h.c <= k_r$, $n >= k_1 + dots.h.c + k_r$. Then $x$ has *cycle shape* $[k_1, k_2, ..., k_r]$.
- Let $x = (i_1 space i_2 space ... space i_k) in S_n$, $g in S_n$. Then action of $g$ on $x$ by conjugation is $ g x g^(-1) = (g(i_1) space g(i_2) space ... space g(i_k)) $
- Let $x in S_n$, then $"ccl"_(S_n)(x)$ consists of all permutations with same cycle shape as $x$.
- Conjugacy classes of $S_n$ have cycle shapes given by non-decreasing partitions of $n$, without $1$ (except for cycle shape $[1]$).
- Let $x = (a_1 space a_2 space ... space a_m) in S_n$, then $ gamma(n\; m) := |"ccl"_(S_n)(x)| = (n(n - 1) dots.h.c (n - m + 1)) / m $
- Let $x in S_n$ have cycle shape $[m_1, ..., m_r]$, $m_1 < m_2 < dots.h.c < m_r$. Then $ gamma(n\; m_1, ..., m_r) := |"ccl"_(S_n)(x)| = product_(k = 1)^r gamma(n - sum_(i = 1)^(k - 1) m_i\; m_k) $
- Let $x in S_n$ has cycle shape $[m_1, ..., m_1, m_2, ..., m_2, ..., m_r, ..., m_r]$, $m_1 < m_2 < dots.h.c < m_r$, $m_i$ repeated $s_i$ times, then number of elements of that cycle shape is $ |"ccl"_(S_n)(x)| = (gamma(n\; m_1, ..., m_1, m_2, ..., m_2, ..., m_r, ..., m_r)) / (s_1! s_2! dots.h.c s_r!) $
- Let $H$ subgroup of $G$. Then $H$ normal in $G$ iff $H$ is union of conjugacy classes of $G$.
- So if $H$ normal then sum of sizes of its conjugacy classes divides $|G|$. But converse doesn't imply $H$ is subgroup.
- To find all normal subgroups $H$ of $S_n$, use that size of $H$ is sum of sizes of conjugacy classes of $S_n$. Use formula above to work out all possible sizes of conjugacy classes, and fact that $H$ must contain identity so must include $1$ in its sum (size of conjugacy class of $1$ is $1$). Then use Lagrange's theorem to restrict the possible sums of the sizes. Then check that each set formed by the union is a group.