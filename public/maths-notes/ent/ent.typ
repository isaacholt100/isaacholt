#import "../template.typ": template
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