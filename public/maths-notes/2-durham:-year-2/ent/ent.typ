#import "../../template.typ": template
#show: template

= Introduction, the natural numbers

- $NN = {1, 2, 3, ...}$
- $NN_0 = {0, 1, 2, 3, ...} = NN union {0}$
- *Peano's axioms*: three primitive terms: $NN_0$, $0$ and *successor function*, $S$.
	- $0 in NN_0$.
	- $forall a in NN_0, S(a) != 0$.
	- $S(a) = S(b) => a = b$.
	- If $X subset.eq NN_0$ and
		- $0 in X$ and
		- $forall a in X, S(a) in X$
		then $X = NN_0$.
- Last axiom applied to $X = {n in NN_0: P(n) "true"}$ gives *Principle of Mathematical Induction (PMI)*: for statement $P(n)$, if $P(0)$ true and $forall n in NN_0, P(n) => P(n + 1)$ then $P(n)$ true for every $n in NN_0$.
- *PMI variants*:
	- If $P(0)$ true and if for every $n in NN_0$, $P(x)$ for every $x < n$ implies $P(n)$, then $P(n)$ true for every $n in NN_0$.
	- Same as two variants above but with base case $P(1)$ true leading to $P(n)$ true for every $n in NN$.
- *Addition of natural numbers*: let $a in NN_0$.
	- $a + 0 = a$.
	- $a + S(b) = S(a + b)$
- *Well ordering principle (WOP)*: let $S subset.eq NN_0$, $S != nothing$, then $S$ has a smallest element.

= Divisibility

- $a$ *divides* $b$, $a | b$ if $exists d in ZZ, b = a d$. If not, write $a divides.not b$.
- *Properties of divisibility*:
	- $a | 0$.
	- If $a != 0$, $0 divides.not a$.
	- $1 | a$ and $a | a$.
	- $a divides b ==> a divides b c$.
	- $a divides b$ and $b divides c ==> a divides c$.
	- $a divides b$ and $a divides c ==> a divides (b x + c y)$ for any $x, y in ZZ$.
	- $a divides b$ and $b divides a ==> a = plus.minus b$.
	- $a | b, a > 0, b > 0 ==> a <= b$.
	- $a divides b ==> a c divides b c$.
- *Division algorithm*: let $a in ZZ$, $b in NN$. Then exist unique $q$ and $r$ such that $ a = q b + r, quad 0 <= r < b $
- *Common divisor* $d$ of $a$ and $b$ is such that $d | a$ and $d | b$.
- *Greatest common divisor ($gcd$)* of $a$ and $b$ is maximal common divisor.
- *Properties of $gcd$*:
	- $gcd(a, b) = gcd(b, a)$.
	- If $a > 0$, $gcd(a, 0) = a$.
	- $gcd(a, b) = gcd(-a, b)$.
	- If $a > 0, b > 0$, $gcd(a, b) <= min{a, b}$.
- For every $a, b, q in ZZ$, $ gcd(a, b) = gcd(a, b - a) = dots.h.c = gcd(a, b - q a) $
- *Euclidean algorithm*: let $a, b in NN$. Repeating the division algorithm: $ a & = q_1 b + r_1 \ b & = q_2 r_1 + r_2 \ r_1 & = q_3 r_2 + r_3 \ & dots.v \ r_(n - 2) & = q_n r_(n - 1) + r_n $ Then exists smallest $n$ such that $r_n = 0$. Then if $n = 1$, $gcd(a, b) = b$, else $gcd(a, b) = r_(n - 1)$. Also, exists $x, y in ZZ$ such that $ gcd(a, b) = a x + b y $

= Primes, composite numbers, and the FTA

- $n in NN$ *prime* if $n > 1$ and if $d | n$ then $d = n$ or $d = 1$. If $n > 1$ not prime, $n$ *composite*.
- There are infinitely many primes.
- There are infinitely many primes of form $4n - 1$.
- *Dirichlet's theorem*: Let $a, b$ coprime. Then exist infinitely many primes of form $a n + b$.
- *Euclid's lemma*: Let $p > 1$. $p$ prime iff for every $a, b in ZZ$, $p divides a b ==> p divides a "or" p divides b$.
- Let $p$ prime. If $p | a_1 dots.h.c a_n$ then $p | a_i$ for some $i$.
- *Fundamental theorem of arithmetic (FTA)*: let $n > 1$, then $n$ can be written as product of primes, unique up to reordering. So exist distinct primes $p_1, ..., p_r$ and $e_1, ..., e_r in NN$ such that $ n = p_1^(e_1) dots.h.c p_r^(e_r) $ and if $n = q_1^(f_1) dots.h.c q_s^(f_s)$ for distinct primes $q_i$, then $r = s$ and up to reordering, $p_i = q_i$ and $e_i = f_i$ for every $i$.

= Classical equations and integer solutions

- *Pythagorean triple* $(x, y, z) in NN^3$: solution to $x^2 + y^2 = z^2$. *Primitive* if $gcd(x, y, z) = 1$.
- Every primitive Pythagorean triple $(x, y, z)$, with $2 divides x$, given by $ cases(
	x = 2 s t,
	y = s^2 - t^2,
	z = s^2 + t^2
) $ with $s > t >= 1$, $gcd(s, t) = 1$ and $s ident.not t quad (mod 2)$.
- *Fermat's theorem*: no integer solutions exist to $x^4 + y^4 = z^2$.
- *Diophantine equation*: equation where integer or rational solutions are sought.

= Modular arithmetic and congruences

- $a$ *congruent to* $b$ *modulo $n$*, $a ident b quad (mod n)$ if $n divides (a - b)$.
- *Residue (congruence) class*: set of integers congruent $mod n$.
- If $a ident b quad (mod n)$ and $a' ident b' quad (mod n)$ then:
	- $a + a' ident b + b' quad (mod n)$ and
	- $a a' ident b b' quad (mod n)$.
- There are $n$ residue classes $mod n$: $overline(0), overline(1), ..., overline(n - 1)$.
- If $gcd(c, n) = 1$, then $a c ident b c quad (mod n)$ implies $a ident b quad (mod n)$.
- *Complete set of residues mod $n$*: subset $R subset ZZ$ of size $n$ whose remainders $mod n$ are distinct.
- Let $R$ be complete set of residues mod $n$ and let $gcd(a, n) = 1$, then $ a R := {a x: x in RR} $ is also complete set of residues mod $n$.
- *Linear congruence*: $a x ident b quad (mod n)$.
- If $gcd(a, n) = 1$, linear congruence has solution, unique up to adding multiples of $n$ (solutions lie in same congruence class).
- *Method for solving linear congruence* (if $gcd(a, n) = 1$):
	- Use Euclidean algorithm to find $u, v$ such that $1 = a u + n v$.
	- $a u ident 1 quad (mod n)$ so $a (u b) ident b quad (mod n)$ so solutions are $ x ident u b quad (mod n) $
- Linear congruence solvable iff $gcd(a, n) divides b$.
- *Chinese remainder theorem (CRT)*: let $m, n in NN$ coprime, $a, b in ZZ$. Then exists solution to $ x & ident a quad (mod m) \ x & ident b quad (mod n) $ Any solutions are congruent $mod m n$ and exists unique solution $x$ with $0 <= x < m n$.
- *Method to solve CRT problem*:
	- Use Euclidean algorithm to find $r, s$ such that $1 = r m + s n$, so $r m ident 1 quad (mod n)$ and $s n ident 1 quad (mod m)$.
	- So $b r m ident b quad (mod n)$ and $a s n ident a quad (mod m)$.
	- So $a s n + b r m ident b quad (mod n)$ and $a s n + b r m ident a quad (mod m)$.
	- So $x = b r m + a s n$ is solution.
- *Euler $phi$-function*: $phi: NN -> NN$: $ phi(n) := |{r in NN: r <= n "and" gcd(r, n) = 1}| $
- $phi(p) = p - 1$ for prime $p$.
- For prime $p$, $phi(p^n) = p^n - p^(n - 1) = p^(n - 1) (p - 1)$.
- If $gcd(m, n) = 1$, then $phi(m n) = phi(m) phi(n)$.
- Let $n$ have prime factorisation $n = product_(i = 1)^r p_i^(e_i)$. Then $ phi(n) = n product_(i = 1)^r (1 - 1/p_i) $
- Let $n in NN$, then $ sum_(d divides n) phi(d) = n $ where sum is over positive divisors of $n$.
- *Euler's theorem*: For $a in ZZ$, $n in NN$, $gcd(a, n) = 1$, $ a^(phi(n)) ident 1 quad (mod n) $
- *Fermat's little theorem*: let $p$ prime, $a in ZZ$, $p divides.not a$. Then $ a^(p - 1) ident 1 quad (mod p) $

= Primitive roots

- Let $n in NN$, $a in ZZ$, $gcd(a, n) = 1$. *(Multiplicative) order* of $a mod n$, $"ord"_n(a) = "ord"(a)$, is smallest $d in NN$ such that $ a^d ident 1 quad (mod n) $
- If $a^d ident 1 quad (mod n)$ for some $d$, then $"ord"(a) divides d$. So $"ord"(a) divides phi(n)$.
- Let $gcd(a, n) = 1$, $a$ is *primitive root $mod n$* if $"ord"_n(a) = phi(n)$.
- Let $p$ prime, $f(x)$ polynomial with integer coefficients of degree $n$. Then $f$ has at most $n$ roots $mod p$, so $f(x) ident 0 quad (mod p)$ has at most $n$ solutions $mod p$.
- Let $p$ prime, $d divides p - 1$. Then $x^d - 1 ident 0 quad (mod p)$ has exactly $d$ solutions $mod p$.
- Let $p$ prime, then there are $phi(p - 1)$ primitive roots $mod p$.
- Let $g$ primitive root $mod p$, $gcd(a, p) = 1$. Then for some $r in NN$, $ a ident g^r quad (mod p) $ ($g, g^2, ..., g^(p - 1)$ are distinct and form complete set of residues $mod p$).
- Primitive roots $mod n$ exist iff $n = 2, 4, p^k$ or $2 p^k$ for odd prime $p$, $k in NN$.

= Quadratic residues

- Let $p$ prime, $a in ZZ$, $gcd(a, p) = 1$. $a$ is *quadratic residue (QR) $mod p$* if for some $x in ZZ$, $x^2 ident a quad (mod p)$. If not, $a$ is *quadratic non-residue (NQR) $mod p$*.
- For $p$ odd prime, there are $(p - 1)/2$ QR's and $(p - 1)/2$ QNR's $mod p$.
- Products of QR's and NQR's satisfy: $ Q R times Q R = Q R \ Q R times N R = N R \ N R times N R = Q R $
- Let $p$ prime, $a in ZZ$, *Legendre symbol* is $ (a / p) := cases(
	1 & "if" a "QR",
	-1 & "if" a "NQR",
	0 & "if" p divides a
) $
- $ ((a b) / p) = (a / p) (b / p) $
- $(a / p) = (b / p)$ if $a ident b quad (mod p)$.
- *Euler's criterion*: Let $p$ odd prime, $a in ZZ$, $gcd(a, p) = 1$, then $ a^((p - 1)\/2) ident (a / p) quad (mod p) $
- $-1$ is QR if $p ident 1 quad (mod 4)$ and is NQR if $p ident 3 quad (mod 4)$.
- *Quadratic reciprocity law (QRL)*: let $p != q$ odd primes, then $ (p / q) (q / p) = (-1)^((p - 1) / 2 (q - 1) / 2) $ If $p = 2$, $ (2 / q) = (-1)^((q^2 - 1) / 8) $
- *Algorithm for computing Legendre symbol* $(a / p)$:
	- Divide $a$ by $p$ to get $a = t p + r$ so $(a / p) = (r / p)$.
	- If $r = 0$, $(r / p) = 0$ so stop.
	- If $r = 1$, $(r / p) = 1$ so stop.
	- If $r != 0, 1$ factorise into primes $r = q_1^(e_1) dots.h.c q_k^(e_k)$ so $(r / p) = product_(i = 1)^k (q_i / p)^(e_i)$.
	- $r < p$ so $q_i < p$, so calculate $(q_i / p)$ for each $i$.
		- If $q_i = 2$, use $(2 / p) = (-1)^((p^2 - 1)/8)$.
		- If $q_i > 2$, use $(q_i / p) = (-1)^(((q_i - 1)(p - 1))/4) (p / q_i)$ and go to step $1$ to calculate $(p / q_i)$.
- *Note*: to evaluate $((-1) / p)$, easier to use Euler's criterion.
- There are infinitely many primes of form $4n + 1$.

= Sums of two squares

- If $m$ and $n$ are sums of two squares, then so is $m n$ since $(a^2 + b^2) (c^2 + d^2) = (a c + b d)^2 + (a d - b c)^2$.
- Let $p$ odd prime. Then $p$ sum of two squares iff $p ident 1 quad (mod 4)$ (and if $p ident 1 quad (mod 4)$, this sum of two squares is unique).
- Let $n > 1$, $n = p_1 p_2 dots.h.c p_k N^2$, $p_i$ distinct primes, $N in NN$. Then $n$ sum of two squares iff $p_i = 2$ or $p_i ident 1 quad (mod 4)$ for all $i$.

= Continued fractions

- *Finite continued fraction (CF)*: $ [a_0; a_1, ..., a_n] = a_0 + 1/(a_1 + 1/(dots.down + 1/a_n)) $
- *Simple* CF: $a_0 in ZZ$, $a_1, ..., a_n in NN$.
- Any rational number can be written as finite simple continued fraction.
- *$k$th convergent* of CF $[a_0; a_1, ..., a_n]$: $ C_k := [a_0; a_1, ..., a_k] $
- $C_n = p_n \/ q_n$, where $ mat(p_k, p_(k - 1); q_k, q_(k - 1)) = mat(a_0, 1; 1, 0) mat(a_1, 1; 1, 0) dots.h.c mat(a_k, 1; 1, 0) $ so $p_1 = a_0 a_1 + 1$, $p_0 = a_0$, $q_1 = a_1$, $q_0 = 1$ and $p_k = a_k p_(k - 1) + p_(k - 2)$, $q_k = a_k q_(k - 1) + q_(k - 2)$
- If $[a_0; a_1, ..., a_n]$ is simple CF, then $q_(k - 1) <= q_k$ and $q_(k - 1) < q_k$ if $k > 1$.
- $ p_k q_(k - 1) - q_k p_(k - 1) = (-1)^(k + 1) $
- $gcd(p_k, q_k) = 1$.
- Let $alpha = [a_0; a_1, ..., a_n]$, $k = 0, ..., n - 1$, then even numbered convergents increasing:  $ C_0 < C_2 < dots.h.c < C_(2m)$, odd numbered convergents decreasing $C_(2m + 1) < dots.h.c < C_3 < C_1$ and for every $k$ with $2k + 1 <= n$, $ p_(2k) / q_(2k) < alpha <= p_(2k + 1) / q_(2k + 1) $ and $ |alpha - p_k / q_k| <= 1/(q_k q_(k + 1)) $
- *Infinite CF* $[a_0; a_1, ...]$ is limit of convergents $C_n = [a_0; a_1, ..., a_n]$.
- For simple infinite CF, limit always exists.
- *Pell's equation*: $x^2 - d y^2 = 1$, $d in NN$ not square.
- *Negative Pell's equation*: $x^2 - d y^2 = -1$.
- Infinite CF *periodic* if of form $ [a_0; a_1, ..., a_m, a_(m + 1), ..., a_(m + n), a_(m + 1), ..., a_(m + n), ...] $ $a_0; a_1, ..., a_m$ is initial part, $a_(m + 1), ..., a_(m + n), a_(m + 1), ..., a_(m + n), ...$ is periodic part. In periodic part, $a_i = a_j$ if $i ident j quad (mod n)$. Write as $ [a_0; a_1, ..., a_m, overline(a_(m + 1)\, ...\, a_(m + n))] $ $n$ is *period*.
- If $d$ not square, CF of $sqrt(d)$ is periodic with initial part only $a_0$.
- Let $p_k \/ q_k$ be convergents of simple CF expansion of $sqrt(d)$ with period $n$, then for all $k >= 1$, $ p_(k n - 1)^2 - d q_(k n - 1)^2 = (-1)^(k n) $
- So if $n$ even or $k$ even, $(x, y) = (p_(k n - 1), q_(k n - 1))$ are solution to Pell's equation. Else $(x, y) = (p_(k n - 1), q_(k n - 1))$ are solution to negative Pell's equation. *All* positive solutions to (negative) Pell equation given by above.