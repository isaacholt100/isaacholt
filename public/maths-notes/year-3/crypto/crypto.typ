#import "../../template.typ": template
#show: template

#import "@preview/lemmify:0.1.5": *

#let (
    theorem, lemma, corollary, definition, remark, proposition, example, proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")

#let modulo(n) = $thick mod #n$
#let lmodulo(n) = $quad mod #n$
#let PAI = $overline(O)$
#let vd(v) = $bold(#v)$
#let span = $op("span")$
#let ideal(..args) = $angle.l #args.pos().join(",") angle.r$

= Introduction

- Encryption process:
    - Alice has a message (*plaintext*) which is *encrypted* using an *encryption key* to produce the *ciphertext*, which is sent to Bob.
    - Bob uses a *decryption key* (which depends on the encryption key) to *decrypt* the ciphertext and recover the original plaintext.
    - It should be computationally infeasible to determine the plaintext without knowing the decryption key.
- *Caesar cipher*:
    - Add constant $k$ to each letter in plaintext to produce ciphertext: $ "ciphertext letter" = "plaintext letter" + k quad mod 26 $
    - To decrypt, $ "plaintext letter" = "ciphertext letter" - k quad mod 26 $
    - The key is $k thick mod 26$.
- Cryptosystem objectives:
    - *Secrecy*: an intercepted message is not able to be decrypted
    - *Integrity*: it is impossible to alter a message without the receiver knowing
    - *Authenticity*: receiver is certain of identity of sender
    - *Non-repudiation*: sender cannot claim they sent a message; the receiver can prove they did.
- *Kerckhoff's principle*: a cryptographic system should be secure even if the details of the system are known to an attacker.
- Types of attack:
    - *Ciphertext-only*: the plaintext is deduced from the ciphertext.
    - *Known-plaintext*: intercepted ciphertext and associated stolen plaintext are used to determine the key.
    - *Chosen-plaintext*: an attacker tricks a sender into encrypting various chosen plaintexts and observes the ciphertext, then uses this information to determine the key.
    - *Chosen-ciphertext*: an attacker tricks the receiver into decrypting various chosen ciphertexts and observes the resulting plaintext, then uses this information to determine the key.

= Symmetric key ciphers

- *Converting letters to numbers*: treat letters as integers modulo $26$, with $A = 1$, $Z = 0 equiv 26 thick (mod 26)$. Treat string of text as vector of integers modulo $26$.
- *Symmetric key cipher*: one in which encryption and decryption keys are equal.
- *Key size*: $log_2 ("number of possible keys")$.
- Caesar cipher is a *substitution cipher*. A stronger substitution cipher is this: key is permutation of ${a, ..., z}$. But vulnerable to plaintext attacks and ciphertext-only attacks, since different letters (and letter pairs) occur with different frequencies in English.
- *One-time pad*: key is uniformly, independently random sequence of integers $mod 26$, $(k_1, k_2, ...)$, known to sender and receiver. If message is $(m_1, m_2, ..., m_r)$ then ciphertext is $(c_1, c_2, ..., c_r) = (k_1 + m_1, k_2 + m_2, ..., k_r + m_r)$. To decrypt the ciphertext, $m_i = c_i - k_i$. Once $(k_1, ..., k_r)$ have been used, they must never be used again.
    - One-time pad is information-theoretically secure against ciphertext-only attack: $PP(M = m | C = c) = PP(M = m)$.
    - Disadvantage is keys must never be reused, so must be as long as message.
    - Keys must be truly random.
- *Chinese remainder theorem*: let $m, n in NN$ coprime, $a, b in ZZ$. Then exists unique solution $x modulo(m n)$ to the congruences $ x equiv a & lmodulo(m) \ x equiv b & lmodulo(n) $
- *Block cipher*: group characters in plaintext into blocks of $n$ (the *block length*) and encrypt each block with a key. So plaintext $p = (p_1, p_2, ...)$ is divided into blocks $P_1, P_2, ...$ where $P_1 = (p_1, ..., p_n)$, $P_2 = (p_(n + 1), ..., p_(2n)), ...$. Then ciphertext blocks are given by $C_i = f("key", P_i)$ for some encryption function $f$.
- *Hill cipher*:
    - Plaintext divided into blocks $P_1, ..., P_r$ of length $n$.
    - Each block represented as vector $P_i in (ZZ \/ 26 ZZ)^n$
    - Key is invertible $n times n$ matrix $M$ with elements in $ZZ \/ 26 ZZ$.
    - Ciphertext for block $P_i$ is $ C_i = M P_i $ It can be decrypted with $P_i = M^(-1) C$.
    - Let $P = (P_1, ..., P_r)$, $C = (C_1, ..., C_r)$, then $C = M P$.
- *Confusion*: each character of ciphertext depends on many characters of key.
- *Diffusion*: each character of ciphertext depends on many characters of plaintext. Ideal diffusion is when changing single character of plaintext changes a proportion of $(S - 1)\/S$ of the characters of the ciphertext, where $S$ is the number of possible symbols.
- For Hill cipher, $i$th character of ciphertext depends on $i$th row of key - this is medium confusion. If $j$th character of plaintext changes and $M_(i j) != 0$ then $i$th character of ciphertext changes. $M_(i j)$ is non-zero with probability roughly $25\/26$ so good diffusion.
- Hill cipher is susceptible to known plaintext attack:
    - If $P = (P_1, ..., P_n)$ are $n$ blocks of plaintext with length $n$ such that $P$ is invertible and we know $P$ and the corresponding $C$, then we can recover $M$, since $C = M P ==> M = C P^(-1)$.
    - If enough blocks of ciphertext are intercepted, it is very likely that $n$ of them will produce an invertible matrix $P$.

= Public key encryption and RSA

- *Public key cryptosystem*:
    - Bob produces encryption key, $k_E$, and decryption key, $k_D$. He publishes $k_E$ and keeps $k_D$ secret.
    - To encrypt message $m$, Alice sends ciphertext $c = f(m, k_E)$ to Bob.
    - To decrypt ciphertext $c$, Bob computes $g(c, k_D)$, where $g$ satisfies $ g(f(m, k_E), k_D) = m $ for all messages $m$ and all possible keys.
    - Computing $m$ from $f(m, k_E)$ should be hard without knowing $k_D$.
- *Converting between messages and numbers*:
    - To convert message $m_1 m_2 ... m_r$, $m_i in {0, ..., 25}$ to number, compute $ m = sum_(i = 1)^r m_i 26^(i - 1) $
    - To convert number $m$ to message, add character $m mod 26$ to message. If $m < 26$, stop. Otherwise, floor divide $m$ by $26$ and repeat.
- *Fermat's little theorem*: let $p$ prime, $a in ZZ$ coprime to $p$, then $a^(p - 1) equiv 1 thick (mod p)$.
- *Euler $phi$ function*: $ phi: NN -> NN, phi(n) = |{1 <= a <= n: gcd(a, n) = 1}| = |(ZZ \/ n ZZ)^times| $
- $phi(p^r) = p^r - p^(r - 1)$, $phi(m n) = phi(m) phi(n)$ for $gcd(m, n) = 1$.
- *Euler's theorem*: if $gcd(a, n) = 1$, $a^(phi(n)) equiv 1 quad (mod n)$.
- *RSA algorithm*:
    - $k_E$ is pair $(n, e)$ where $n = p q$, the *RSA modulus*, is product of two distinct primes and $e in ZZ$, the *encryption exponent*, is coprime to $phi(n)$.
    - $k_D$, the *decryption exponent*, is integer $d$ such that $d e equiv 1 quad (mod phi(n))$.
    - $m$ is an integer modulo $n$, $m$ and $n$ are coprime.
    - Encryption: $c = m^e quad (mod n)$.
    - Decryption: $m = c^d quad (mod n)$.
    - It is recommended that $n$ have at least $2048$ bits. A typical choice of $e$ is $2^16 + 1$.
- *RSA problem*: given $n = p q$ a product of two unknown primes, $e$ and $m^e quad (mod n)$, recover $m$. If $n$ can be factored, the RSA is solved.
- *Factorisation problem*: given $n = p q$ for large distinct primes $p$ and $q$, find $p$ and $q$.
- *RSA signatures*:
    - Public key is $(n, e)$ and private key is $d$.
    - When sending a message $m$, message is *signed* by also sending $s = m^d mod n$, the *signature*.
    - $(m, s)$ is received, *verified* by checking if $m = s^e mod n$.
    - Forging a signature on a message $m$ would require finding $s$ with $m = s^e mod n$. This is the RSA problem.
    - However, choosing signature $s$ first then taking $m = s^e mod n$ produces valid pairs.
    - To solve this, $(m, s)$ is sent where $s = h(m)^d$, $h$ is *hash function*. Then the message receiver verifies $h(m) = s^e mod n$.
    - Now, for a signature to be forged, an attacker would have to find $m$ with $h(m) = s^e mod n$.
- *Hash function* is function $h: {"messages"} -> cal(H)$ that:
    - Can be computed efficiently
    - Is *preimage-resistant*: can't quickly find $m$ given $h(m)$.
    - Is *collision-resistant*: can't quickly find $m, m'$ such that $h(m) = h(m')$.
- *Attacks on RSA*:
    - If you can factor $n$, you can compute $d$, so can break RSA (as then you know $phi(n)$ so can compute $e^(-1) thick mod phi(n)$).
    - If $phi(n)$ is known, then we have $p q = n$ and $(p - 1)(q - 1) = phi(n)$ so $p + q = n - phi(n) + 1$. Hence $p$ and $q$ are roots of $x^2 - (n - phi(n) + 1)x + n$.
    - *Known $d$ attack*:
        - $d e - 1$ is multiple of $phi(n)$ so $p, q | x^(d e - 1) - 1$.
        - Look for factor $K$ of $d e - 1$ with $x^K - 1$ divisible by $p$ but not $q$ (or vice versa) (equivalently, $(p - 1) | K$ but $(q - 1) divides.not K$).
        - Let $d e - 1 = 2^r s$, $gcd(2, s) = 1$, choose random $x mod n$. Let $y = x^s$, then $y^(2^r) = x^(2^r s) = x^(d e - 1) equiv 1 thick mod n$.
        - If $y equiv 1 thick mod n$, restart with new random $x$. Find first occurence of $1$ in $y, y^2, ..., y^(2^r)$: $y^(2^j) equiv.not 1 thick mod n$, $y^(2^(j + 1)) equiv 1 thick mod n$ for some $j >= 0$.
        - Let $a := y^(2^j)$, then $a^2 equiv 1 thick mod n$, $a equiv.not 1 thick mod n$. If $a equiv -1 thick mod n$, restart with new random $x$.
        - Now $n = p q | a^2 - 1 = (a + 1)(a - 1)$ but $n divides.not (a + 1), (a - 1)$. So $p$ divides one of $a + 1$, $a - 1$ and $q$ divides the other. So $gcd(a - 1, n)$, $gcd(a + 1, n)$ are prime factors of $n$.
- *Theorem*: it is no easier to find $phi(n)$ than to factorise $n$.
- *Theorem*: it is no easier to find $d$ than to factor $n$.
- *Miller-Rabin algorithm* for probabilistic primality testing of $n$:
    + Let $n - 1 = 2^r s$, $gcd(2, s) = 1$.
    + Choose random $x mod n$, compute $y = x^s mod n$.
    + Compute $y, y^2, ..., y^(2^r) mod n$.
    + If $1$ isn't in this list, $n$ is *composite* (with witness $x$).
    + If $1$ is in list preceded by number other than $plus.minus 1$, $n$ is *composite* (with witness $x$).
    + Other, $n$ is *possible prime* (to base $x$).
- *Theorem*:
    - If $n$ prime then it is possible prime to every base.
    - If $n$ composite then it is possible prime to $<= 1\/4$ of possible bases.
    In particular, if $k$ random bases are chosen, probability of composite $n$ being possible prime for all $k$ bases is $<= 4^(-k)$.

== Factorisation

- *Trial division algorithm*: for $p = 2, 3, 5, ...$ test whether $p | n$.
- If $x^2 equiv y^2 mod n$ but $x equiv.not plus.minus y mod n$, then $x - y$ is divisible by factor of $n$ but not by $n$ itself, so $gcd(x - y, n)$ gives proper factor of $n$ (or $1$).
- *Fermat's method*:
    - Let $a = ceil(sqrt(n))$. Compute $a^2 mod n$, $(a + 1)^2 mod n$ until a square $x^2 equiv (a + i)^2 mod n$ appears. Then compute $gcd(a + i - x, n)$.
    - Works well under special conditions on the factors: if $|p - q| <= 2 sqrt(2) root(4, n)$ then Fermat's method takes one step: $x = ceil(sqrt(n))$ works.
- *Definition*: an integer is *$B$-smooth* if all its prime factors are $<= B$.
- *Quadratic sieve*:
    - Choose $B$ and let $m$ be number of primes $<= B$.
    - Look at integers $x = ceil(sqrt(n)) + k$, $k = 1, 2, ...$ and check whether $y = x^2 - n$ is $B$-smooth.
    - Once $y_1 = x_1^2 - n, ..., y_t = x_t^2 - n$ are all $B$-smooth with $t > m$, find some product of them that is a square.
    - Deduce a congruence between the squares.
    - Time complexity is $exp(sqrt(log n log log n))$.

= Diffie-Hellman key exchange

- *Primitive root theorem*: let $p$ prime, then there exists $g in FF_p^times$ such that $1, g, ..., g^(p - 2)$ is complete set of residues $mod p$.
- Let $p$ prime, $g in FF_p^times$. *Order* of $g$ is smallest $a in NN_0$ such that $g^a = 1$. $g$ is *primitive root* if its order is $p - 1$ (equivalently, $1, g, ..., g^(p - 2)$ is complete set of residues $mod p$).
- Let $p$ prime, $g in FF_p^times$ primitive root. If $x in FF_p^times$ then $x = g^L$ for some $0 <= L < p - 1$. Then $L$ is *discrete logarithm* of $x$ to base $g$. Write $L = L_g (x)$.
- *Proposition*:
    - $g^(L_g (x)) equiv x quad (mod p)$ and $g^a equiv x quad (mod p) <==> a equiv L_g (x) quad (mod p - 1)$.
    - $L_g (1) = 0$, $L_g (g) = 1$.
    - $L_g (x y) equiv L_g (x) + L_g (y) quad (mod p - 1)$.
    - $L_g (x^(-1)) = -L_g (x) thick (mod p - 1)$.
    - $L_g (g^a mod p) equiv a thick (mod p - 1)$.
    - $h$ is primitive root mod $p$ iff $L_g (h)$ coprime to $p - 1$. So number of primitive roots mod $p$ is $phi(p - 1)$.
- *Discrete logarithm problem*: given $p, g, x$, compute $L_g (x)$.
- *Diffie-Hellman key exchange*:
    - Alice and Bob publicly choose prime $p$ and primitive root $g mod p$.
    - Alice chooses secret $alpha mod (p - 1)$ and sends $g^alpha mod p$ to Bob publicly.
    - Bob chooses secret $beta mod (p - 1)$ and sends $g^beta mod p$ to Alice publicly.
    - Alice and Bob both compute shared secret $kappa = g^(alpha beta) = (g^alpha)^beta) = (g^beta)^alpha mod p$.
- *Diffie-Hellman problem*: given $p, g, g^alpha, g^beta$, compute $g^(alpha beta)$.
- If discrete logarithm problem cna be solved, so can Diffie-Hellman problem (since could compute $alpha = L_g (g^a)$ or $beta = L_g (g^beta)$).
- *Elgamal public key encryption*:
    - Alice chooses prime $p$, primitive root $g$, private key $alpha med med mod (p - 1)$.
    - Her public key is $y = g^alpha$.
    - Bob chooses random $k mod (p - 1)$
    - To send message $m$ (integer mod $p$), he sends the pair $(r, m') = (g^k, m y^k)$.
    - To decrypt message, Alice computes $r^alpha = g^(alpha k) = y^k$ and then $m' r^(-alpha) = m' y^(-k) = m g^(alpha k) g^(-alpha k) m$.
    - If Diffie-Hellman problem is hard, then Elgamal encryption is secure against known plaintext attack.
    - Key $k$ must be random and different each time.
- *Decision Diffie-Hellman problem*: given $g^a, g^b, c$ in $FF_p^times$, decide whether $c = g^(a b)$.
    - This problem is not always hard, as can tell if $g^(a b)$ is square or not. Can fix this by taking $g$ to have large prime order $q | (p - 1)$. $p = 2q + 1$ is a good choice.
- *Elgamal signatures*:
    - Public key is $(p, g)$, $y = g^alpha$ for private key $alpha$.
    - *Valid Elgamal signature* on $m in {0, ..., p - 2}$ is pair $(r, s)$, $0 <= r, s <= p - 1$ such that  $ y^r r^s = g^m quad (mod p) $
    - Alice computes $r = g^k$, $k in (ZZ\/(p - 1))^times$ random. $k$ should be different each time.
    - Then $g^(alpha r) g^(k s) equiv g^m quad mod p$ so $alpha r + k s equiv m quad (mod p - 1)$ so $s = k^(-1) (m - alpha r) quad mod p - 1$.
- *Elgamal signature problem*: given $p, g, y, m$, find $r, s$ such that $y^r r^s = m$.
- *Discrete logarithm problem*: given prime $p$, primitive root $g thick mod p$, $x in FF_p^times$, calculate $L_g (x)$.
- *Baby-step giant-step algorithm* for solving DLP:
  - Let $N = ceil(sqrt(p - 1))$.
  - Baby-steps: compute $g^j thick mod p$ for $0 <= j < N$.
  - Giant-steps: compute $x g^(-N k) thick mod p$ for $0 <= k < N$.
  - Look for a match between baby-steps and giant-steps lists: $g^j = x g^(-N k) ==> x = g^(j + N k)$.
  - Always works since if $x = g^L$ for $0 <= L < p - 1 <= N^2$, $L$ can be written as $j + N k$ with $j, k in {0, ..., N - 1}$.
- *Index calculus* method for solving DLP $x = g^L$:
    - Fix smoothness bound $B$.
    - Find many multiplicative relations between $B$-smooth numbers and powers of $g mod p$.
    - Solve these relations to find discrete logarithms of primes $<= B$.
    - For $i = 1, 2, ...$ compute $x g^i mod p$ until one is $B$-smooth, then use result from previous step.
- *Pohlig-Hellman algorithm* computes discrete logarithms $mod p$ with approximate complexity $log(p) sqrt(ell)$ where $ell$ is largest prime factor of $p - 1$, so is fast if $p - 1$ is $B$-smooth. Therefore $p$ is chosen so that $p - 1$ has large prime factor, e.g. choose *Germain prime* $p = 2q + 1$, with $q$ prime.

= Elliptic curves

- *Definition*: *abelian group* $(G, compose)$ satisfies:
    - *Associativity*: $forall a, b, c, in G, a compose (b compose c) = (a compose b) compose c$.
    - *Identity*: $exists e in G: forall g in G, e times g = g$.
    - *Inverses*: $forall g in G, exists h in G: g compose h = h compose g = e$
    - *Commutativity*: $forall a, b in G, a compose b = b compose a$.
- *Definition*: $H subset.eq G$ is *subgroup* of $G$ if $(H, compose)$ is group.
- To show $H$ is subgroup, sufficient to show $g, h in H => g compose h in H$ and $h^(-1) in H$.
- *Notation*: for $g in G$, write $[n] g$ for $g compose dots.h.c compose g$ $n$ times if $n > 0$, $e$ if $n = 0$, $[-n] g^(-1)$ if $n < 0$.
- *Definition*: *subgroup generated by $g$* is $ angle.l g angle.r = {[n]g: n in ZZ} $ If $angle.l g angle.r$ finite, it has *order $n$*, and $g$ has *order $n$*. If $G = angle.l g angle.r$ for some $g in G$, $G$ is *cyclic* and $g$ is *generator*.
- *Lagrange's theorem*: let $G$ finite group, $H$ subgroup of $G$, then $|H| | |G|$.
- *Corollary*: if $G$ finite, $g in G$ has order $n$, then $n | |G|$.
- *DLP for abelian groups*: given $G$ a cyclic abelian group, $g in G$ a generator of $G$, $x in G$, find $L$ such that $[L]g = x$. $L$ is well-defined modulo $|G|$.
- *Definition*: let $(G, compose)$, $(H, circle.filled.small)$ abelian groups, *homomorphism* between $G$ and $H$ is $f: G -> H$ with $ forall g, g' in G, quad f(g compose g') = f(g) circle.filled.small f(g') $ *Isomorphism* is bijective homomorphism. $G$ and $H$ are *isomorphic*, $G tilde.equiv H$, if there is isomorphism between them.
- *Fundamental theorem of finite abelian groups*: let $G$ finite abelian group, then there exist unique integers $2 <= n_1, ..., n_r$ with $n_i | n_(i + 1)$ for all $i$, such that $ G tilde.eq (ZZ \/ n_1) times dots.h.c times (ZZ \/ n_r) $ In particular, $G$ is isomorphic to product of cyclic groups.
- *Definition*: let $K$ field, $"char"(K) > 3$. An *elliptic curve* over $K$ is defined by the equation $ y^2 = x^3 + a x + b $ where $a, b in K$, $Delta_E := 4a^3 + 27b^2 != 0$.
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
    - If $P = -Q =: (x_0, -y_0)$, $P plus.circle Q = PAI$.
    - Otherwise, $P plus.circle Q = (x_2, -y_2)$, where $ x_2 & = lambda^2 - (x_0 + x_1), \ y_2 & = lambda x_2 + mu, \ lambda & = cases((y_1 - y_0)/(x_1 - x_0) & "if" x_0 != x_1, (3x_0^2 + a)/(2y_0) & "if" x_0 = x_1), \ mu & = y_0 - lambda x_0 $
- *Example*:
    - Let $E$ be given by $y^2 = x^3 + 17$ over $QQ$, $P = (-1, 4) in E(QQ)$, $Q = (2, 5) in E(QQ)$. To find $P plus.circle Q$, $ lambda = (5 - 4)/(2 - (-1)) = 1/3, quad mu = 4 - lambda(-1) = 13/3 $ So $x_2 = lambda^2 - (-1) -2 = -8/9$ and $y_2 = -(lambda x_2 + mu) = -109/27$ hence $ P plus.circle Q = (-8/9, -109/27) $ To find $[2]P$, $ lambda = (3(-1)^2 + 0)/(2 dot.op 4) = 3/8, quad mu = 4 - 3/8 dot.op (-1) = 35/8 $ so $x_3 = lambda^2 - 2 dot.op (-1) 137/64$, $y_3 = -(lambda x_3 + mu) = -2651/512$ hence $ [2]P = (x_3, y_3) = (137/64, -2651/512) $
- *Hasse's theorem*: let $|E(FF_p)| = N$, then $ |N - (p + 1)| <= 2 sqrt(p) $
- *Theorem*: $E(FF_p)$ is isomorphic to either $ZZ\/k$ or $ZZ\/m times ZZ\/n$ with $m | n$.
- *Elliptic curve Diffie-Hellman*:
    - Alice and Bob publicly choose elliptic curve $E(FF_p)$ and $P in FF_p$ with order a large prime $n$.
    - Alice chooses random $alpha in {0, ..., n - 1}$ and publishes $Q_A = [alpha]P$.
    - Bob chooses random $beta in {0, ..., n - 1}$ and publishes $Q_B = [beta]P$.
    - Alice computes $[alpha]Q_B = [alpha beta]P$, Bob computes $[beta]Q_A = [beta alpha]P$.
    - Shared key is $K = [alpha beta] P$.
- *Elliptic curve Elgamal signatures*:
    - Use agreed elliptic curve $E$ over $FF_p$, point $P in E(FF_p)$ of prime order $n$.
    - Alice wants to sign message $m$, encoded as integer mod $n$.
    - Alice generates private key $alpha in ZZ\/n$ and public key $Q = [alpha] P$.
    - Valid signature is $(R, s)$ where $R = (x_R, y_R) in E(FF_p)$, $s in ZZ\/n$, $[tilde(x_R)] Q plus.circle [s] R = [m] P$.
    - To generate a valid signature, Alice chooses random $0 != k in ZZ\/n$ and sets $R = [k] P$, $s = k^(-1) (m - tilde(x_R) alpha)$.
    - $k$ must be randomly generated for each message.
- *Baby-step giant-step algorithm for elliptic curve DLP*: given $P$ and $Q = [alpha] P$, find $alpha$:
    - Let $N = ceil(sqrt(n))$, $n$ is order of $P$.
    - Compute $P, [2] P, ..., [N - 1]P$.
    - Compute $Q plus.circle [-N]P, Q plus.circle [-2N]P, ..., Q plus.circle [-(N - 1)N]P$ and find a match between these two lists: $[i]P = Q plus.circle [-j N]P$, then $[i + j N]P = Q$ so $alpha = i + j N$.
- For well-chosen elliptic curves, the best algorithm for solving DLP is the baby-step giant-step algorithm, with run time $O(sqrt(n)) approx O(sqrt(p))$. This is much slower than the index-calculus method for the DLP in $FF_p^times$.
- *Pollard's $p - 1$ algorithm* to factorise $n = p q$:
    - Choose smoothness bound $B$.
    - Choose random $2 <= a <= n - 2$. Set $a_1 = a$, $i = 1$.
    - Compute $a_i = a_(i - 1)^i thick mod n$. Find $d = gcd(a_i - 1, n)$. If $1 < d < n$, we have found a nontrivial factor of $n$. If $d = n$, pick new $a$ and retry. If $d = 1$, increment $i$ by $1$ and repeat this step.
    - A variant is instead of computing $a_i = a_(i - 1)^i$, compute $a_i = a_(i - 1)^(m_(i - 1))$ where $m_1, ..., m_r$ are the prime powers $<= B$ (each prime power is the maximal prime power $<= B$ for that prime).
    - The algorithm works if $p - 1$ is *$B$-powersmooth* (all prime power factors are $<= B$), since if $b$ is order of $a mod p$, then $b | (p - 1)$ so $b | B!$ (also $b | m_1 dots.h.c m_r$). If the first $i$ for which $i!$ (or $m_1 dots.h.c m_i$) is divisible by $d$ and order of $a mod q$, then $a_i - 1 = a^(i!) - 1 mod n$ is divisible by both $p$ and $q$, so must retry with different $a$.
- Let $n = p q$, $p, q$ prime, $a, b in ZZ$, $gcd(4a^3 + 27b^2, n) = 1$. Then $E: y^2 = x^3 + a x + b$ defines elliptic curve over $FF_p$ and over $FF_q$. If $(x, y) in ZZ\/n$ is solution to $E mod n$ then can reduce coordinates $mod p$ to obtain non-infinite point of $E(FF_p)$ and $mod q$ to obtain non-infinite point of $E(FF_q)$.
- *Proposition*: let $P_1, P_2 in E mod n$, with $ (P_1 mod p) plus.circle (P_2 mod p) & = PAI \ (P_1 mod q) plus.circle (P_2 mod q) & != PAI $ Then $gcd(x_1 - x_2, n)$ (or $gcd(2x_1, n)$ if $P_1 = P_2$) is factor of $n$.
- *Lenstra's algorithm* to factorise $n$:
    - Choose smoothness bound $B$.
    - Choose random elliptic curve $E$ over $ZZ\/n$ with $gcd(Delta_E, n) = 1$ and $P = (x, y)$ a point on $E$.
    - Set $P_1 = P$, attempt to compute $P_i$, $2 <= i <= B$ by $P_i = [i] P_(i - 1)$. If one of these fails, a divisor of $n$ has been found (by failing to compute an inverse $mod n$). If this divisor is trivial, restart with new curve and point.
    - If $i = B$ is reached, restart with new curve and point.
    - Again, a variant is calculating $P_i = [m_i]P_(i - 1)$ instead of $[i]P_(i - 1)$ where $m_1, ..., m_r$ are the prime powers $<= B$
- Lenstra's algorithm works if $|E(ZZ\/p)|$ is $B$-powersmooth but $|E(ZZ\/q)|$ isn't. Since we can vary $E$, it is very likely to work eventually.
- Running time depends on $p$ (the smaller prime factor): $ O(exp(sqrt(2 log(p) log log (p)))) $ Compare this to the general number field sieve running time: $ O(exp(C (log n)^(1\/3) (log log n)^(2\/3))) $

== Torsion points

- *Definition*: let $G$ abelian group. $g in G$ is a *torsion* if it has finite order. If order divides $n$, then $[n]g = e$ and $g$ is *$n$-torsion*.
- *Definition*: *$n$-torsion subgroup* is $ G[n] := {g in G: [n]g = e} $
- *Definition*: *torsion subgroup* of $G$ is $ G_"tors" = {g in G: g "is torsion"} = union.big_(n in NN) G[n] $
- *Example*:
    - In $ZZ$, only $0$ is torsion.
    - In $(ZZ\/10)^times$, by Lagrange's theorem, every point is $4$-torsion.
    - For finite groups $G$, $G_"tors" = G = G[ |G| ]$ by Lagrange's theorem.

== Rational points

- *Note*: for elliptic curve $E: y^2 = x^3 + a x + b$ over $QQ$, can assume that $a, b in ZZ$.
- *Nagell-Lutz theorem*: let $E$ elliptic curve, let $P = (x, y) in E(QQ)_"tors"$. Then $x, y in ZZ$, and either $y = 0$ (in which case $P$ is $2$-torsion) or $y^2 divides Delta_E$.
- *Corollary*: $E(QQ)_"tors"$ is finite.
- *Example*: can use Nagell-Lutz to show a point is not torsion.
    - $P = (0, 1)$ lies on elliptic curve $y^2 = x^3 -x + 1$. $[2]P = (1/4, -7/8) in.not ZZ^2$. Then $[2]P$ is not torsion, hence $P$ is not torsion. So $E(QQ)$ contains  distinct points $..., [-2]P, -P, PAI, P, [2]P, ...$, hence $E$ has infinitely many solutions in $QQ$.
- *Mazur's theorem*: let $E$ be elliptic curve over $QQ$. Then $E(QQ)_"tors"$ is either:
    - cyclic of order $1 <= N <= 10$ or order $12$, or
    - of the form $ZZ\/2 times ZZ\/2N$ for $1 <= N <= 4$.
- *Definition*: let $E: y^2 = x^3 + a x + b$ defined over $QQ$, $a, b in ZZ$. For odd prime $p$, taking reductions $overline(a)$, $overline(b) mod p$ gives curve over $FF_p$: $ overline(E): y^2 = x^3 + overline(a) x + overline(b) $ This is elliptic curve if $Delta_E equiv.not 0 mod p$, in which case $p$ is *prime of good reduction* for $E$.
- *Theorem*: let $E: y^2 = x^3 + a x + b$ defined over $QQ$, $a, b in ZZ$, $p$ be odd prime of good reduction for $E$. Then $f: E(QQ)_"tors" -> overline(E)(FF_p)$ defined by $ f(x, y) := (overline(x), overline(y)), quad f\(PAI\) := PAI $ is injective (note $x, y in ZZ$ by Nagell-Lutz).
- So $E(QQ)_"tors"$ can be thought of as subgroup of $E(FF_p)$ for any prime $p$ of good reduction, so by Lagrange's theorem, $|E(QQ)_"tors"|$ divides $|E(FF_p)|$.
- *Mordell's theorem*: if $E$ is elliptic curve over $QQ$, then $ E(QQ) tilde.equiv E(QQ)_"tors" times ZZ^r $ for some $r >= 0$ the *rank* of $E$. So for some $P_1, ..., P_r in E(QQ)$, $ E(QQ) = \{n_1 P_1 + dots.h.c + n_r P_r + T: n_i in ZZ, T in E(QQ)_"tors"\} $ $P_1, ..., P_r, T$ are *generators* for $E(QQ)$.

= Basic coding theory

== First definitions

- *Definition*:
    - *Alphabet* $A$ is finite set of symbols.
    - $A^n$ is set of all lists of $n$ symbols from $A$ - these are *words of length $n$*.
    - *Code of block length $n$ on $A$* is subset of $A^n$.
    - *Codeword* is element of a code.
- *Definition*: if $|A| = 2$, codes on $A$ are *binary* codes. If $|A| = 3$, codes on $A$ are *ternary codes*. If $|A| = q$, codes on $A$ are *$q$-ary* codes. Generally, use $A = {0, 1, ..., q - 1}$.
- *Definition*: let $x = x_1 ... x_n, y = y_1 ... y_n in A^n$. *Hamming distance* between $x$ and $y$ is number of indices where $x$ and $y$ differ: $ d: A^n times A^n -> {0, ..., n}, quad d(x, y) := |{i in [n]: x_i != y_i}| $ So $d(x, y)$ is minimum number of changes needed to change $x$ to $y$. If $x$ transmitted and $y$ received, then $d(x, y)$ *symbol-errors* have occurred.
- *Proposition*: let $x, y$ words of length $n$.
    - $0 <= d(x, y) <= n$.
    - $d(x, y) = 0 <==> x = y$.
    - $d(x, y) = d(y, x)$.
    - $forall z in A^n, d(x, y) <= d(x, z) + d(z, y)$.
- *Definition*: *minimum distance* of code $C$ is $ d(C) := min{d(x, y): x, y in C, x != y} in NN $
- *Notation*: code of block length $n$ with $M$ codewords and minimum distance $d$ is called $(n, M, d)$ (or $(n, M)$) code. A $q$-ary code is called an $\(n, M, d\)_q$ code.
- *Definition*: let $C subset.eq A^n$ code, $x$ word of length $n$. A *nearest neighbour* of $x$ is codeword $c in C$ such that $d(x, c) = min{d(x, y): y in C}$.

== Nearest-neighbour decoding

- *Definition*: *nearest-neighbour decoding (NND)* means if word $x$ received, it is decoded to a nearest neighbour of $x$ in a code $C$.
- *Proposition*: let $C$ be code with minimum distance $d$, let word $x$ be received with $t$ symbol errors. Then
    - If $t <= d - 1$, then we can detect that $x$ has some errors.
    - If $t <= floor((d - 1)/2)$, then NND will correct the errors.

== Probabilities

- *Definition*: *$q$-ary symmetric channel with symbol-error probability $p$* is channel for $q$-ary alphabet $A$ such that:
    - For every $a in A$, probability that $a$ is changed in channel is $p$.
    - For every $a != b in A$, probability that $a$ is changed to $b$ in channel is $ PP(b "received" | a "sent") = p/(q - 1) $
    i.e. symbol-errors in different positions are independent events.
- *Proposition*: let $c$ codeword in $q$-ary code $C subset.eq A^n$ sent over $q$-ary symmetric channel with symbol-error probability $p$. Then $ PP(x "received" | c "sent") = (p/(q - 1))^t (1 - p)^(n - t), quad "where" t = d(c, x) $
- *Example*: let $C = {000, 111} subset {0, 1}^3$.
#figure(table(
    columns: (auto, auto, auto, auto, auto),
    $x$, $t = d(000, x)$, [chance $000$ received as $x$], [chance if $p = 0.01$], [NND decodes correctly?],
    $000$, $0$, $(1 - p)^3$, $0.970299$, "yes",
    $100$, $1$, $p(1 - p)^2$, $0.009801$, "yes",
    $010$, $1$, $p(1 - p)^2$, $0.009801$, "yes",
    $001$, $1$, $p(1 - p)^2$, $0.009801$, "yes",
    $110$, $2$, $p^2(1 - p)$, $0.000099$, "no",
    $101$, $2$, $p^2(1 - p)$, $0.000099$, "no",
    $011$, $2$, $p^2(1 - p)$, $0.000099$, "no",
    $111$, $3$, $p^3$, $0.000001$, "no",
))
- *Corollary*: if $p < (q - 1)/q$ then $P(x "received" | c "sent")$ increases as $d(x, c)$ decreases.
- *Remark*: by Bayes' theorem, $ PP(c "sent" | x "received") = PP(c "sent and" x "received") / PP(x "received") = (PP(c "sent") PP(x "received" | c "sent"))/PP(x "received") $
- *Proposition*: let $C$ be $q$-ary $(n, M, d)$ code used over $q$-ary symmetric channel with symbol-error probability $p < (q - 1)\/q$, and each codeword $c in C$ is equally likely to be sent. Then for any word $x$, $PP(c "sent" | x "received")$ increases as $d(x, c)$ decreases.

== Bounds on codes

- *Proposition (singleton bound)*: for $q$-ary code $(n, M, d)$ code, $M <= q^(n - d + 1)$.
- *Definition*: code which saturates singleton bound is called *maximum distance separable (MDS)*.
- *Example*: let $C_n$ be *binary repetition code* of block length $n$, $ C_n := \{underbrace(00...0, n), underbrace(11...1, n)\} subset {0, 1}^n $ $C_n$ is $(n, 2, n)_2$ code, and $2 = 2^(n - n + 1)$ so $C_n$ is MDS code.
- *Definition*: let $A$ be alphabet, $|A| = q$. Let $n in NN$, $0 <= t <= n$, $t in NN$, $x in A^n$.
    - *Ball of radius $t$ around $x$* is $ S(x, t) := {y in A^n: d(y, x) <= t} $
    - Code $C subset.eq A^n$ is *perfect* if $ exists t in NN: A^n = product.co_(c in C) S(c, t) $ where $product.co$ is disjoint union.
- *Example*: for $C = {000, 111} subset {0, 1}^3$, $S(000, 1) = {000, 100, 010, 001}$ and $S(111, 1) = {111, 011, 101, 110}$. These are disjoint and $S(000, 1) union S(111, 1) = {0, 1}^3$, so $C$ is perfect.
- *Example*: let $C = {111, 020, 202} subset {0, 1, 2}^3$. $forall c in C, d(c, 012) = 2$. So $012$ is not in any $S(c, 1)$ but is in every $S(c, 2)$, so $C$ is not perfect.
- *Lemma*: let $|A| = q$, $x in AA^n$, then $ |S(x, t)| = sum_(k = 0)^t binom(n, k) (q - 1)^k $
- *Example*: let $C = {111, 020, 202} subset {0, 1, 2}^3$, so $q = 3$, $n = 3$. So $|S(x, 1)| = binom(3, 0) + binom(3, 1) (3 - 1) = 7$, $|S(x, 2)| = binom(3, 0) + binom(3, 1)(3 - 1) + binom(3, 2) (3 - 1)^2 = 19$. But $|{0, 1, 2}|^3 = 27$ and $7 divides.not 27$, $19 divides.not 27$, so ${0, 1, 2}^3$ can't be partioned by balls of either size. So $C$ can't be perfect. $|S(x, 3)| = 27$, but then $C$ must contain only one codeword to be perfect, and $|S(x, 0)| = 1$, but then $C = A^n$ to be perfect. These are trivial, useless codes.
- *Proposition (Hamming/sphere-packing bound)*: $q$-ary $(n, M, d)$ code satisfies $ M sum_(k = 0)^t binom(n, k) (q - 1)^k <= q^n, quad "where" t = floor((d - 1)/2) $
- *Corollary*: code saturates Hamming bound iff it is perfect.

= Linear codes

== Finite vector spaces

- *Definition*: *linear code* of block length $n$ is subspace of $FF_q^n$.
- *Example*: let $vd(x) = (0, 1, 2, 0)$, $vd(y) = (1, 1, 1, 1)$, $vd(z) = (0, 2, 1, 0) in FF_3^4$. $C_1 = {vd(x), vd(y), vd(0)}$ is not linear code since e.g. $vd(x) + vd(y) = (1, 2, 0, 1) in.not C_1$. $C_2 = {vd(x), vd(z), vd(0)}$ is linear code.
- *Notation*: spanning set of $S$ is $ideal(S)$.
- *Proposition*: if linear code $C subset.eq FF_q^n$ has $dim(C) = k$, then $|C| = q^k$.
- *Definition*: a $q$-ary $[n, k, d]$ code is linear code: a subspace of $FF_q^n$ of dimension $k$ with minimum distance $d$. Note: a $q$-ary $[n, k, d]$ code is a $q$-ary $(n, q^k, d)$ code.

== Weight and minimum distance

- *Definition*: *weight* of $vd(x) in FF_q^n$, $w(vd(x))$, is number of non-zero entries in $vd(x)$: $ w(vd(x)) = |{i in [n]: x_i != 0}| $
- *Lemma*: $forall vd(x), vd(y) in FF_q^n$, $d(vd(x), vd(y)) = w(vd(x) - vd(y))$. In particular, $w(vd(x)) = d(vd(x), vd(0))$.
- *Proposition*: let $C subset.eq FF_q^n$ linear code, then $ d(C) = min{w(vd(c)): vd(c) in C, vd(c) != vd(0)} $
- *Remark*: to find $d(C)$ for linear code with $q^k$ words, only need to consider $q^k$ weights instead of $binom(q^k, 2)$ distances.

= Codes as images

== Generator-matrices

- *Definition*: let $C subset.eq FF_q^n$ be linear code. Let $G in M_(k, n)(FF_q)$, $f_G: FF_q^k -> FF_q^n$ be linear map defined by $f_G (vd(x)) = vd(x) G$. Then $G$ is *generator-matrix* for $C$ if
    - $C = im(f) = \{vd(x) G: vd(x) in FF_q^k\} subset.eq FF_q^n$.
    - The rows of $G$ are linearly independent.
    i.e. $G$ is generator-matrix for $C$ iff rows of $G$ form basis for $C$ (note $vd(x) G = x_1 vd(g_1) + dots.h.c + x_k vd(g_k)$ where $vd(g_i)$ are rows of $G$).
- *Remark*: given linear code $C = ideal(vd(a)_1, ..., vd(a)_m)$, a generator-matrix can be found for $C$ by constructing the matrix $A$ with rows $vd(a)_i$, then performing elementary row operations to bring $A$ into RREF. Once the $m - k$ bottom zero rows have been removed, the resulting matrix is a generator-matrix.
- *Example*: let $C = ideal({(0, 0, 3, 1, 4), (2, 4, 1, 4, 0), (5, 3, 0, 1, 6)}) subset.eq FF_7^5$. $
    A = mat(2, 4, 1, 4, 0; 5, 3, 0, 1, 6; 0, 0, 3, 1, 4) limits(->_(A_(12)(1))) mat(2, 4, 1, 4, 0; 0, 0, 1, 5, 6; 0, 0, 3, 1, 4) limits(->_(M_1 (4))) mat(1, 2, 4, 2, 0; 0, 0, 1, 5, 6; 0, 0, 3, 1, 4) limits(->_(A_(21)(3), A_(23)(4))) mat(1, 2, 0, 3, 4; 0, 0, 1, 5, 6; 0, 0, 0, 0, 0)
$ So $G = mat(1, 2, 0, 3, 4; 0, 0, 1, 5, 6)$ is generator matrix for $C$ and $dim(C) = 2$.

== Encoding and channel decoding

== Equivalence and standard form

- *Definition*: codes $C_1, C_2$ of block length $n$ over alphabet $A$ are *equivalent* if we can transform one to the other by applying sequence of the following two kinds of changes to all the codewords (simultaneously):
    - Permute the $n$ positions.
    - In a particular position, permuting the $|A| = q$ symbols.
- *Proposition*: equivalent codes have the same parameters $(n, M, d)$.
- *Definition*: linear codes $C_1, C_2 subset.eq FF_q^n$ are *monomially equivalent* if we can obtain one from the other by applying sequence of the following two kinds of changes to all codewords (simultaneously):
    - Permuting the $n$ positions.
    - In particular position, multiply by $lambda in FF_q^times$.
    If only the first change is used, the codes are *permutation equivalent*.
- *Definition*: $P in M_n (FF_q)$ is *permutation matrix* if it has a single $1$ in each row and column, and zeros elsewhere. Any permutation of $n$ positions of row vector in $FF_q^n$ can be described as right multiplication by permutation matrix.
- *Proposition*: permutation matrices are orthogonal: $P^T = P^(-1)$.
- *Proposition*: let $C_1, C_2 subset.eq FF_q^n$ linear codes with generator matrices $G_1, G_2$. Then if $G_1 = G_2 P$ for permutation matrix $P$, then $C_1$ and $C_2$ are permutation equivalent.
- *Definition*: $M in M_m (FF_q)$ is *monomial matrix* if it has exactly one non-zero element in each row and column.
- *Proposition*: monomial matrix $M$ can always be written as $M = D P$ or $M = P D'$ where $P$ is permutation matrix and $D, D'$ are diagonal matrices. $P$ is *permutation part*, $D$ and $D'$ are *diagonal parts* of $M$.
- *Example*: $ mat(0, 2, 0; 0, 0, 3; 1, 0, 0) = mat(2, 0, 0; 0, 3, 0; 0, 0, 1) mat(0, 1, 0; 0, 0, 1; 1, 0, 0) = mat(0, 1, 0; 0, 0, 1; 1, 0, 0) mat(1, 0, 0; 0, 2, 0; 0, 0, 3) $
- *Proposition*: let $C_1, C_2 subset.eq FF_q^n$ be linear codes with generator-matrices $G_1, G_2$. Then if $G_2 = G_1 M$ for some monomial matrix $M$, then $C_1$ and $C_2$ are monomially equivalent.
- *Definition*: let $C subset.eq FF_q^n$ linear code. If $G = (I_k | A)$, with $A in M_(k, n - k)(FF_q)$, is generator-matrix for $C$, then $G$ is in *standard form*.
- *Note*: not every linear code has generator-matrix in standard form.
- *Proposition*: every linear code is permutation equivalent to a linear code with generator-matrix in standard form.
- *Example*: let $C_1 subset.eq FF_7^5$ have generator matrix $G_1 = mat(1, 2, 0, 3, 4; 0, 0, 1, 5, 6)$. Then applying permutation matrix $ P = mat(1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1) ==> G_1 P = mat(1, 0, 2, 3, 4; 0, 1, 0, 5, 6) = (I_2 | A) $

= Codes as kernels

== Dual codes

- *Definition*: let $C subset.eq FF_q^n$ linear code. *Dual* of $C$ is $ C^perp := {vd(v) in FF_q^n: forall vd(u) in C, vd(v) dot.op vd(u) = 0} $
- *Proposition*: if $G$ is generator matrix for linear code $C$ then $ C^perp = \{vd(v) in FF_q^n : vd(v) G^T = vd(0)\} = ker(f_(G^T)) $ where $f_(G^T): FF_q^n -> FF_q^k$, $f(x) = x G^T$ is linear map.
- *Proposition*: let $C subset.eq FF_q^n$ linear code. Then $C^perp$ is also linear code and $dim(C) + dim(C^perp) = n$.
- *Proposition*: let $C subset.eq FF_q^n$ linear code, then $(C^perp)^perp = C$.
- *Proposition*: let $C subset.eq FF_q^n$ have generator-matrix in standard form, $G = (I_k | A)$, then $H = (-A^T | I_(n - k))$ is generator-matrix for $C^perp$.
- *Proposition*: let $G$ be generator matrix of $C subset.eq FF_q^n$, let $P in M_n (FF_q)$ permutation matrix such that $G P = (I_k | A)$ for some $A in M_(k, n - k)(FF_q)$. Then $H = (-A^T | I_(n - k)) P^T$ is generator matrix for $C^perp$.
- *Algorithm*: to find basis for dual code $C^perp$, given generator matrix $G = (g_(i j)) in M_(k, n)(FF_q)$ for $C$ in RREF:
    + Let $L = {1 <= j <= n: G "has leading" 1 "in column" j}$.
    + For each $1 <= j <= n$, $j in.not L$, construct $vd(v)_j$ as follows:
        + For $m in.not L$, $m$th entry of $vd(j)$ is $1$ if $m = j$ and $0$ otherwise.
        + Fill in the other entries of $vd(v)_j$ (left to right) as $-g_(1 j), ..., -g_(k j)$.
    + The $n - k$ vectors $vd(j)$ are basis for $C^perp$.
- *Example*: let $C subset.eq FF_5^7$ be linear code with generator-matrix $ G = mat(1, 2, 0, 3, 4, 0, 0; 0, 0, 1, 1, 2, 0, 3; 0, 0, 0, 0, 0, 1, 4) $ Then $L = {1, 3, 6}$.
    - $v_2 = (3, 1, 0, 0, 0, 0, 0)$
    - $v_4 = (2, 0, 4, 1, 0, 0, 0)$
    - $v_5 = (1, 0, 3, 0, 1, 0, 0)$
    - $v_7 = (0, 0, 2, 0, 0, 1, 1)$
    - So generator matrix for $C^perp$ is $ H = mat(3, 1, 0, 0, 0, 0, 0; 2, 0, 4, 1, 0, 0, 0; 1, 0, 3, 0, 1, 0, 0; 0, 0, 2, 0, 0, 1, 1) $

== Check-matrices

