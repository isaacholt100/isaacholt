#import "../../template.typ": template
#show: template

#let modulo(n) = $thick mod #n$
#let lmodulo(n) = $quad mod #n$
#let PAI = $overline(O)$

= Introduction

- Basic encryption process:
    - A has a message (*plaintext*) which is *encrypted* using an *encryption key* to produce the *ciphertext*, which is sent to $B$.
    - B uses a *decryption key* (which depends on the encryption key) to *decrypt* the ciphertext and recover the original plaintext.
    - It should be computationally infeasible to determine the plaintext without knowing the decryption key.
- *Caesar cipher*:
    - Add a constant to each letter in the plaintext to produce the ciphertext: $ "ciphertext letter" = "plaintext letter" + k quad mod 26 $
    - To decrypt, $ "plaintext letter" = "ciphertext letter" - k quad mod 26 $
    - The key is $k thick mod 26$.
- Cryptosystem objectives:
    - *Secrecy*: the intercepted message should be not able to be decrypted
    - *Integrity*: a message should not allowed to be altered without the receiver knowing
    - *Authenticity*: the receiver should be certain of the identity of the sender
    - *Non-repudiation*: the sender should not be able to claim they sent a message; the receiver should be able to prove they did.
- *Kerckhoff's principle*: a cryptographic system should be secure even if the details of the system are known to an attacker.
- Types of attack:
    - *Ciphertext-only*: the plaintext is deduced from the ciphertext.
    - *Known-plaintext*: intercepted ciphertext and associated stolen plaintext are used to determine the key.
    - *Chosen-plaintext*: an attacker tricks a sender into encrypting various chosen plaintexts and observes the ciphertext, then uses this information to determine the key.
    - *Chosen-ciphertext*: an attacker tricks the receiver into decrypting various chosen ciphertexts and observes the resulting plaintext, then uses this information to determine the key.

= Symmetric key ciphers

- *Converting letters to numbers*: treat letters as integers modulo $26$, with $A = 1$, $Z = 0 equiv 26 thick (mod 26)$. Treat a string of text as a vector of integers modulo $26$.
- *Symmetric key cipher*: one in which encryption and decryption keys are equal.
- *Key size*: $log_2 ("number of possible keys")$.
- *Substitution cipher*: key is permutation of ${a, ..., z}$. Key size is $log_2 (26!)$. It is vulnerable to plaintext attacks and ciphertext-only attacks, since different letters (and letter pairs) occur with different frequencies in English.
- *Stirling's formula*: $ n! approx sqrt(2 pi n) (n / e)^n $
- *One-time pad*: key is uniformly, independently random sequence of integers $mod 26$, $(k_1, k_2, ...)$, it is known to the sender and receiver. If message is $(m_1, m_2, ..., m_r)$ then ciphertext is $(c_1, c_2, ..., c_r) = (k_1 + m_1, k_2 + m_2, ..., k_r + m_r)$. To decrypt the ciphertext, $m_i = c_i - k_i$. Once $(k_1, ..., k_r)$ have been used, they must never be used again.
    - One-time pad is information-theoretically secure against ciphertext-only attack: $PP(M = m | C = c) = PP(M = m)$.
    - Disadvantage is keys must never be reused, so must be as long as message.
    - Keys must be truly random.
- *Chinese remainder theorem*: let $m, n in NN$ coprime, $a, b in ZZ$. Then exists unique solution $x modulo(m n)$ to the congruences $ x equiv a & lmodulo(m) \ x equiv b & lmodulo(n) $
- *Block cipher*: group characters in plaintext into blocks of $n$ (the *block length*) and encrypt each block with a key. So plaintext $p = (p_1, p_2, ...)$ is divided into blocks $P_1, P_2, ...$ where $P_1 = (p_1, ..., p_n)$, $P_2 = (p_(n + 1), ..., p_(2n))$. Then ciphertext blocks are given by $C_i = f("key", P_i)$ for some encryption function $f$.
- *Hill cipher*:
    - Plaintext divided into blocks $P_1, ..., P_r$ of length $n$.
    - Each block represented as vector $P_i in (ZZ \/ 26 ZZ)^n$
    - Key is invertible $n times n$ matrix $M$ with elements in $ZZ \/ 26 ZZ$.
    - Ciphertext for block $P_i$ is $ C_i = M P_i $ It can be decrypted with $P_i = M^(-1) C$.
    - Let $P = (P_1, ..., P_r)$, $C = (C_1, ..., C_r)$, then $C = M P$.
- *Confusion*: each character of ciphertext depends on many characters of key.
- *Diffusion*: each character of ciphertext depends on many characters of plaintext. Ideal diffusion changes a proportion of $(S - 1)\/S$ of the characters of the ciphertext, where $S$ is the number of possible symbols.
- For Hill cipher, $i$th character of ciphertext depends on $i$th row of key - this is medium confusion. If $j$th character of plaintext changes and $M_(i j) != 0$ then $i$th character of ciphertext changes. $M_(i j)$ is non-zero with probability roughly $25\/26$ so good diffusion.
- Hill cipher is susceptible to known plaintext attack:
    - If $P = (P_1, ..., P_n)$ are $n$ blocks of plaintext with length $n$ such that $P$ is invertible and we know $P$ and the corresponding $C$, then we can recover $M$, since $C = M P ==> M = C P^(-1)$.
    - If enough blocks of ciphertext are intercepted, it is very likely that $n$ of them will produce an invertible matrix $P$.

= Public key cryptography and the RSA algorithm

- *Euler $phi$ function*: $ phi: NN -> NN, phi(n) = |{1 <= a <= n: gcd(a, n) = 1}| = |(ZZ \/ n ZZ)^times| $
- $phi(p^r) = p^r - p^(r - 1)$, $phi(m n) = phi(m) phi(n)$ for $gcd(m, n) = 1$.
- *Euler's theorem*: if $gcd(a, n) = 1$, $a^(phi(n)) equiv 1 quad (mod n)$.
- *Public key cryptography*:
    - Create two keys, $k_D$ and $k_E$. $k_E$ is public, $k_D$ is private.
    - Plaintext $m$ is encrypted as $c = f(m, k_E)$.
    - Ciphertext decrypted by $m = g(c, k_D)$.
- *RSA*:
    - $k_E$ is pair $(n, e)$ where $n = p q$ is product of two distinct primes and $e in ZZ$ is coprime to $phi(n)$.
    - $k_D$ is integer $d$ such that $d e equiv 1 quad (mod phi(n))$.
    - $m$ is an integer modulo $n$, $m$ and $n$ are coprime.
    - Encryption: $c = m^e quad (mod n)$.
    - Decryption: $m = c^d quad (mod n)$.
- *RSA problem*: given $n = p q$ a product of two unknown primes, $e$ and $m^e quad (mod n)$, recover $m$. If $n$ can be factored, the RSA is solved.
- It is recommended that $n$ have at least $2048$ bits. A typical choice of $e$ is $2^16 + 1$.
- *Attacks on RSA*:
    - If you can factor $n$, you can compute $d$, so can break RSA (as then you know $phi(n)$ so can compute $e^(-1) quad (mod phi(n))$).
    - If $phi(n)$ is known, then we have $p q = n$ and $(p - 1)(q - 1) = phi(n)$ so $p + q = n - phi(n) + 1$. Hence $p$ and $q$ are roots of $x^2 - (n - phi(n) + 1) + n = 0$.
    - *Known $d$*: we have $d e - 1$ is multiple of $phi(n)$. Look for a factor $A$ of $d e - 1$ such that $(p - 1) | A$, $(q - 1) divides.not A$. Then try $x^A - 1$ for random $x$, this satisfies $x^A - 1$ is divisible by $p$, hence $gcd(x^A - 1, n) = p$.
- *RSA signatures*:
    - Public key is $(n, e)$ and private key is $d$.
    - When sending a message $m$, message is *signed* by also sending $s = m^d mod n$.
    - $(m, s)$ is received, *verified* by checking if $m = s^e mod n$.
    - Forging a signature on a message $m$ would require finding $s$ with $m = s^e mod n$. This is the RSA problem.
    - However, choosing signature $s$ first then taking $m = s^e mod n$.
    - To solve this, $(m, s)$ is sent where $s = h(m)^d$, $h$ is *hash function*. Then the message receiver verifies $h(m) = s^e mod n$.
    - Now, for a signature to be forged, an attacker would have to find $m$ with $h(m) = s^e mod n$.
- *Hash function* is function $h: {"messages"} -> cal(H)$ that:
    - Can be computed efficiently
    - Is preimage-resistant: can't quickly find $m$ with given $h(m)$.
    - Is collision-resistant: can't quickly find $m, m'$ with $h(m) = h(m')$.
    Example is SHA-256.
- *Theorem*: it is no easier to find $phi(n)$ than to factorise $n$.
- *Theorem*: it is no easier to find $d$ than to factor $n$.
- *Miller-Rabin algorithm*:
    + Choose random $x mod n$.
    + Let $n - 1 = 2^r s$, $y = x^s$.
    + Compute $y, y^2, ..., y^(2^r) mod n$.
    + If $1$ isn't in this list, $n$ is *composite* (with witness $x$).
    + If $1$ is in list preceded bynumber other than $plus.minus 1$, $n$ is *composite* (with witness $a$).
    + Other, $n$ is *possible prime* (to base $x$).

== Factorisation

- *Trial division algorithm*: for $p = 2, 3, 5, ...$ test whether $p | n$.
- *Fermat's method*:
    - Let $a = ceil(sqrt(n))$. Compute $a^2 mod n$, $(a + 1)^2 mod n$ until a square $x^2 equiv (a + i)^2 mod n$ appears. Then compute $gcd(a + i - x, n)$.
    - Works well under special conditions on the factors: if $|p - q| <= 2 sqrt(2) root(4, n)$ then Fermat's method takes one step: $x = ceil(sqrt(n))$ works.
- An integer is $B$-smooth if all its prime factors are $<= B$.
- *Quadratic sieve*:
    - Choose $B$ and let $m$ be numberof primes $<= B$.
    - Look at integers $x = ceil(sqrt(n)) + k$, $k = 1, 2, ...$ and check whether $y = x^2 - n$ is $B$-smooth.
    - Once $y_1 = x_1^2 - n, ..., y_t = x_t^2 - n$ are all $B$-smooth with $t > m$, find some product of them that is a square.
    - Deduce a congruence between the squares.
- *Other factorisation algorithms*:
    - Pollard's $rho$ algorithm.
    - Pollard's $p - 1$ algorithm.
    - Lenstra's algorithm using elliptic curves.
    - General number field sieve
    - Shor's algorithm: $ln(N)^2 ln(ln(N))$.

== Primitive roots

- Let $p$ prime, $g in FF_p^times$. *Order* of $g$ is smallest $a in NN_0$ such that $g^a = 1$. $g$ is *primitive root* if its order is $p - 1$.
- Let $p$ prime, $g in FF_p^times$ primitive root. If $x in FF_p^times$ then $x = g^L$ for some $0 <= L < p - 1$. Then $L$ is *discrete logarithm* of $x$ to base $g$. Write $L = L_g (x)$. It satisfies:
    - $g^(L_g (x)) equiv x quad (mod p)$ and $g^a equiv x quad (mod p) <==> a equiv L_g (x) quad (mod p - 1)$.
    - $L_g (1) = 0$, $L_g (g) = 1$.
    - $L_g (x y) equiv L_g (x) + L_g (y) quad (mod p - 1)$.
    - $h$ is primitive root mod $p$ iff $L_g (h)$ coprime to $p - 1$. So number of primitive roots mod $p$ is $phi(p - 1)$.
- *Discrete logarithm problem*: given $p, g, x$, compute $L_g (x)$.
- *Diffie-Hellman key exchange*:
    - Two parties agree on prime $p$ and primitive root $g mod p$.
    - Alice chooses secret $alpha mod (p - 1)$ and sends $g^alpha mod p$ to Bob.
    - Bob chooses secret $beta mod (p - 1)$ and sends $g^beta mod p$ to Alice.
    - Alice and Bob both compute $kappa = g^(alpha beta) = (g^alpha)^beta) = (g^beta)^alpha mod p$.
- *Diffie-Hellman problem*: given $p, g, g^alpha, g^beta$, compute $g^(alpha beta)$.
- If discrete logarithm problem cna be solved, so can Diffie-Hellman problem (since could compute $alpha = L_g (g^a)$ or $beta = L_g (g^beta)$).

- *Elgamal* public key encryption:
    - Alice chooses prime $p$, primitive root $g$, private key $alpha med med mod (p - 1)$.
    - Her public key is $y = g^alpha$.
    - Bob chooses random $k mod (p - 1)$
    - To send message $m$ (integer mod $p$), he sends the pair $(r, m') = (g^k, m y^k)$.
    - To descript the message, Alice computes $r^alpha = g^(alpha k) = y^k$ and then $m = m' y^(-k) = m' r^(-alpha)$.
    - If Diffie-Hellman problem is hard, then Elgamal encryption is secure against known plaintext attack.
    - Key $k$ must be random and different each time.
- *Decision Diffie-Hellman problem*: given $g^a, g^b, c$ in $FF_p^times$, decide whether $c = g^(a b)$.
    - This problem is not always hard, as can tell if $g^(a b)$ is square or not. Can fix this by taking $g$ to have large prime order $q | (p - 1)$. $p = 2q + 1$ is a good choice.
- *Elgamal signatures*:
    - Public key is $(p, g)$, $y = g^alpha$ for private key $alpha$.
    - *Valid Elgamal signature* on $m$ is pair $(r, s)$, $r >= 0$, $s < p - 1$ such that  $ y^r r^s = g^m quad (mod p) $
    - Alice computes $r = g^k$, $k in (ZZ\/(p - 1))^times$ random.
    - Then $g^(alpha r) g^(k s) equiv g^m quad mod p$ so $alpha r + k s equiv m quad (mod p - 1)$ so $s = k^(-1) (m - alpha r) quad mod p - 1$.
- *Elgamal signature problem*: given $p, g, y, m$, find $r, s$ such that $y^r r^s = m$.
- *Discrete logarithm problem*: given prime $p$, primitive root $g thick mod p$, $x in FF_p^times$, calculate $L_g (x)$.
- *Baby-step giant-step algorithm* for solving DLP:
  - Let $N = ceil(sqrt(p - 1))$.
  - Baby-steps: compute $g^j thick mod p$ for $0 <= j < N$.
  - Giant-steps: compute $x g^(-N k) thick mod p$ for $0 <= k < N$.
  - Look for a match between baby-steps and giant-steps lists: $g^j = x g^(-N k) ==> x = g^(j + N k)$.
  - Always works since if $x = g^L$ for $0 <= L < p - 1 <= N^2$, so $L$ can be written as $j + N k$ with $j, k in {0, ..., N - 1}$.

= Elliptic curves

- *Definition*: *abelian group* $(G, compose)$ satisfies:
    - *Associativity*: $forall a, b, c, in G, a compose (b compose c) = (a compose b) compose c$.
    - *Identity*: $exists e in G: forall g in G, e times g = g$.
    - *Inverses*: $forall g in G, exists h in G: g compose h = h compose g = e$
    - *Commutativity*: $forall a, b in G, a compose b = b compose a$.
- *Notation*: for $g in G$, write $[n] g$ for $g compose dots.h.c compose g$ $n$ times if $n > 0$, $e$ if $n = 0$, $[-n] g$ if $n < 0$.
- *DLP for abelian groups*: given $G$ a cyclic abelian group, $g in G$ a generator of $G$, $x in G$, find $L$ such that $[L]g = x$. $L$ is well-defined modulo $|G|$.
- *Fundamental theorem of finite abelian groups*: let $G$ finite abelian group, then there exist unique integers $2 <= n_1, ..., n_r$ with $n_i | n_(i + 1)$ for all $i$, such that $ G tilde.eq (ZZ \/ n_1) times dots.h.c times (ZZ \/ n_r) $ In particular, $G$ is isomorphic to a product of cyclic groups.
- *Definition*: let $K$ field, $"char"(K) > 3$. An *elliptic curve* over $K$ is defined by the equation $ y^2 = x^3 + a x + b $ where $a, b in K$, $Delta_E = 4a^3 + 27b^2 != 0$.
- *Remark*: elliptic curve over $QQ$ is also elliptic curve over $RR$ or $CC$.
- *Remark*: $Delta_E != 0$ is equivalent to $x^3 + a x + b$ having no repeated roots (i.e. $E$ is smooth).
- *Definition*: for elliptic curve $E$ defined over $K$, a *$K$-point* (*point*) on $E$ is either:
    - A *normal point*: $(x, y) in K^2$ satisfying the equation defining $E$.
    - The *point at infinity* $PAI$ which can be thought of as infinitely far along the $y$-axis (in either direction).
    Denote set of all $K$-points on $E$ as $E(K)$.
- Any elliptic curve $E(K)$ is an abelian group, with group operation $plus.circle$ is defined as:
    - We should have $P plus.circle Q plus.circle R = PAI$ iff $P, Q, R$ lie on straight line.
    - In this case, $P plus.circle Q = -R$.
    - To find line $ell$ passing through $P = (x_0, y_0)$ and $Q = (x_1, y_1)$:
        - If $x_0 != x_1$, then equation of $ell$ is $y = lambda x + mu$, where $ lambda = (y_1 - y_0)/(x_1 - x_0), quad mu = y_0 - lambda x_0 $ Now $ y^2 & = x^3 + a x + b = (lambda x + mu)^2 \ ==> 0 & = x^3 - lambda^2 x^2 + (a - 2 lambda mu)x + (b - mu^2) $ Since sum of roots of monic polynomial is equal to minus the coefficient of the second highest power, and two roots are $x_0$ and $x_1$, the third root is $x_2 = lambda^2 - x_0 - x_1$. Then $y_2 = lambda x_2 + mu$ and $R = (x_2, y_2)$.
        - If $x_0 = x_1$, then using implicit differentiation: $ & y^2 = x^3 + a x + b \ ==> & (dif y)/(dif x) = (3x^2 + a)/(2y) $ and the rest is as above, but instead with $lambda = (3x_0^2 + a)/(2y_0)$.
- *Definition*: *group law* of elliptic curves: let $E: y^2 = x^3 + a x + b$. For all normal points $P = (x_0, y_0), Q = (x_1, y_1) in E(K)$, define
    - $PAI$ is group identity: $P plus.circle PAI = PAI plus.circle P = P$.
    - If $P = -Q$, $P plus.circle Q = PAI$.
    - Otherwise, $P plus.circle Q = (x_2, -y_2)$, where $ x_2 & = lambda^2 - (x_0 + x_1), \ y_2 & = lambda x_2 + mu, \ lambda & = cases((y_1 - y_0)/(x_1 - x_0) & "if" x_0 != x_1, (3x_0^2 + a)/(2y_0) & "if" x_0 = x_1), \ mu & = y_0 - lambda x_0 $
- *Example*:
    - Let $E$ be given by $y^2 = x^3 + 17$ over $QQ$, $P = (-1, 4) in E(QQ)$, $Q = (2, 5) in E(QQ)$. To find $P plus.circle Q$, $ lambda = (5 - 4)/(2 - (-1)) = 1/3, quad mu = 4 - lambda(-1) = 13/3 $ So $x_2 = lambda^2 - (-1) -2 = -8/9$ and $y_2 = -(lambda x_2 + mu) = -109/27$ hence $ P plus.circle Q = (-8/9, -109/27) $ To find $[2]P$, $ lambda = (3(-1)^2 + 0)/(2 dot.op 4) = 3/8, quad mu = 4 - 3/8 dot.op (-1) = 35/8 $ so $x_3 = lambda^2 - 2 dot.op (-1) 137/64$, $y_3 = -(lambda x_3 + mu) = -2651/512$ hence $ [2]P = (x_3, y_3) = (137/64, -2651/512) $
- *Hasse's theorem*: let $|E(FF_p)| = N$, then $ |N - (p + 1)| <= 2 sqrt(p) $
- *Elliptic curve Elgamal signatures*:
    - Use agreed elliptic curve $E$ over $FF_p$, point $P in E(FF_p)$ of prime order $n$.
    - Alice wants to sign message $m$, encoded as integer mod $n$.
    - Alice generates private key $alpha in ZZ\/n$ and public key $Q = [alpha] P$.
    - A valid signature is $(R, s)$ where $R = (x_R, y_R) in E(FF_p)$, $s in ZZ\/n$, $[tilde(x_R)] Q plus.circle [s] R = [m] P$.
    - To generate a valid signature, Alice chooses random $k in ZZ\/n$ and sets $R = [k] P$, $s = k^(-1) (m - tilde(x_R) alpha)$.
    - $k$ must be randomly generated for each message.
- *Baby-step giant-step algorithm for elliptic curve DLP*: given $P$ and $Q = [alpha] P$, find $alpha$:
    - Let $N = ceil(sqrt(n))$, $n$ is order of $P$.
    - Compute $P, [2] P, ..., [N - 1]P$.
    - Compute $Q plus.circle [-N]P, Q plus.circle [-2N]P, ..., Q plus.circle [-(N - 1)N]P$ and find a match between these two lists: $[i]P = Q plus.circle [-j N]P$, then $[i + j N]P = Q$ so $alpha = i + j N$.
- For well-chosen elliptic curves, the best algorithm is the baby-step giant-step algorithm, with run time $O(sqrt(n)) approx O(sqrt(p))$. This is much slower than the index-calculus method for the DLP in $FF_p^times$.
- *Pollard's $p - 1$ algorithm* to factorise $n$:
    - Choose smoothness bound $B$.
    - Choose random $2 <= a <= n - 2$. Set $a_1 = a$, $i = 1$.
    - Compute $a_(i + 1) = a_i^i thick mod n$, increment $i$ by $1$. Find $d = gcd(a_(i + 1) - 1, n)$. If $1 < d < n$, we have found a nontrivial factor of $n$. If $d = n$, pick new $a$ and retry. If $d = 1$, repeat this step.
    - A variant is instead of computing $a_(i + 1) = a_i^i$, compute $a_(i + 1) = a_i^(m_i)$ where $m_1, ..., m_r$ are the prime powers $<= B$.
    - The algorithm works if $p - 1$ is $B$-powersmooth (all prime power factors are $<= B$).
- *Lenstra's algorithm* to factorise $n$:
    - Choose smoothness bound $B$.
    - Choose random elliptic curve $E$ over $ZZ\/n$ and $P = (x, y)$ a point on $E$.
    - Set $P_1 = P$, attempt to compute $P_i$, $2 <= i <= B$ by $P_i = [i] P_(i - 1)$. If this fails, a divisor of $n$ has been found (by failing to compute an inverse $mod n$). If this divisor is trivial, restart with new curve and point.
    - If $i = B$ is reached, restart with new curve and point.
- Lenstra's algorithm works if $|E(ZZ\/p)|$ is $B$-powersmooth. Since we can vary $E$, it is very likely to work eventually.
- Running time depends on $p$: $ O(exp(sqrt(2 log(p) log log (p)))) $ Compare this to the general number field sieve running time: $ O(exp(C (log n)^(2\/3) (log log n)^(2\/3))) $

== Torsion points

- *Definition*: let $G$ abelian group. $g in G$ is a *torsion* if it has finite order. If order divides $n$, then $[n]g = e$ and $g$ is *$n$-torsion*.
- *Definition*: *$n$-torsion subgroup* is $ G[n] := {g in G: [n]g = e} $
- *Definition*: *torsion subgroup* of $G$ is $ G_"tors" = {g in G: g "is torsion"} = union.big_(n in NN) G[n] $
- *Example*:
    - In $ZZ$, only $0$ is torsion.
    - In $(ZZ\/10)^times$, by Lagrange's theorem, every point is $4$-torsion.
    - For finite groups $G$, $G_"tors" = G = G[ |G| ]$ by Lagrange's theorem.

== Rational points

- *Nagell-Lutz theorem*: let $E$ elliptic curve, let $P = (x, y) in E(QQ)_"tors"$. Then $x, y in ZZ$, and either $y = 0$ (in which case $P$ is $2$-torsion) or $y^2 divides Delta_E$.
- *Corollary*: $E(QQ)_"tors"$ is finite.
- *Example*: can use Nagell-Lutz to show a point is not torsion.
    - $P = (0, 1)$ lies on elliptic curve $y^2 = x^3 -x + 1$. $[2]P = (1/4, -7/8) in.not ZZ^2$. Then $[2]P$ is not torsion, hence $P$ is not torsion. So $E(QQ)$ contains $..., [-2]P, -P, PAI, P, [2]P, ...$, hence $E$ has infinitely many solutions in $QQ$.
- *Mazur's theorem*: let $E$ be elliptic curve over $QQ$. Then $E(QQ)_"tors"$ is either:
    - cyclic of order $1 <= N <= 10$ or order $12$, or
    - of the form $ZZ\/2 times ZZ\/2N$ for $1 <= N <= 4$.
