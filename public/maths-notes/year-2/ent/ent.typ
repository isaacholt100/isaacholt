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
- $gcd(0, 0)$ doesn't exist.
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

- *Pythagorean triple* $(x, y, z)$: solution to $x^2 + y^2 = z^2$. *Primitive* if $gcd(x, y, z) = 1$.
- Every Pythagorean triple $(x, y, z)$, with $2 divides x$, given by $ cases(
	x = 2 s t,
	y = s^2 - t^2,
	z = s^2 + t^2
) $ with $s > t >= 1$, $gcd(s, t) = 1$ and $s ident.not t quad (mod 2)$.
- *Fermat's theorem*: no integer solutions exist to $x^4 + y^4 = z^2$.

= Modular arithmetic and congruences

- *Residue (congruence) class*: set of integers congruent $mod n$.
- $a ident b quad (mod n)$ if $n divides (a - b)$.
- If $a ident a quad (mod n)$ and $a' ident b' quad (mod n)$ then:
	- $a + a' ident b + b' quad (mod n)$ and
	- $a a' ident b b' quad (mod n)$.
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
- Let $g$ primitive root $mod p$, $gcd(a, p) = 1$. Then for some $r in NN$, $ a ident g^r quad (mod p) $ ($g, g^2, ..., g^(p - 1)$ are distinct).
- Primitive roots $mod n$ exist iff $n = 2, 4, p^k$ or $2 p^k$ for odd prime $p$, $k in NN$.

= Quadratic residues

- Let $p$ prime, $a in ZZ$, $gcd(a, n) = 1$. $a$ is *quadratic residue (QR) $mod p$* if for some $x in ZZ$, $x^2 ident a quad (mod p)$. If not, $a$ is *quadratic non-residue (NQR) $mod p$*.
- For $p$ odd prime, there are $(n - 1)/2$ QR's and QNR's $mod p$.
- Products of QR's and NQR's satisfy: $ Q R times Q R = Q R \ Q R times N R = N R \ N R times N R = Q R $
- Let $p$ prime, $a in ZZ$, *Legendre symbol* is $ (a / p) := cases(
	1 & "if" a "QR",
	-1 & "if" a "NQR",
	0 & "if" p divides a
) $
- $ ((a b) / p) = (a / p) (b / p) $
- $(a / p) = (b / p)$ if $a ident b quad (mod p)$.
- Let $p$ odd prime, $a in ZZ$, $gcd(a, p) = 1$, then $ a^((p - 1)\/2) ident (a / p) quad (mod p) $