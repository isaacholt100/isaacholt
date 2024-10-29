#import "../../template.typ": *
#show: doc => template(doc, hidden: ("proof",), slides: false)

// FIND: - \*(\w+)\*: ([\s\S]*?)(?=\n-|\n\n)\n
// REPLACE: #$1[\n    $2\n]\n

#let modulo(n) = $thick mod #n$
#let lmodulo(n) = $quad mod #n$
#let PAI = $overline(O)$
#let vd(v) = $bold(#v)$
#let span = $op("span")$
#let ideal(..args) = $angle.l #args.pos().join(",") angle.r$

= Introduction

#definition[
    Encryption process:
    - Alice has a message (*plaintext*) which is *encrypted* using an *encryption key* to produce the *ciphertext*, which is sent to Bob.
    - Bob uses a *decryption key* (which depends on the encryption key) to *decrypt* the ciphertext and recover the original plaintext.
    - It should be computationally infeasible to determine the plaintext without knowing the decryption key.
]
#definition[
    *Caesar cipher*:
    - Add constant $k$ to each letter in plaintext to produce ciphertext: $ "ciphertext letter" = "plaintext letter" + k quad mod 26 $
    - To decrypt, $ "plaintext letter" = "ciphertext letter" - k quad mod 26 $
    - The key is $k thick mod 26$.
]
#note[
    $Z$ is represented as $0 = 26 mod 26$, $A$ as $1 mod 26$.
]
#definition[
    We define the following cryptosystem objectives:
    - *Secrecy*: an intercepted message is not able to be decrypted
    - *Integrity*: it is impossible to alter a message without the receiver knowing
    - *Authenticity*: receiver is certain of identity of sender (they can tell if an impersonator sent the message)
    - *Non-repudiation*: sender cannot claim they did not send a message; the receiver can prove they did.
]
#definition[
    *Kerckhoff's principle*: a cryptographic system should be secure even if the details of the system are known to an attacker.
]
#definition[
    There are 4 types of attack:
    - *Ciphertext-only*: the plaintext is deduced from the ciphertext.
    - *Known-plaintext*: intercepted ciphertext and associated stolen plaintext are used to determine the key.
    - *Chosen-plaintext*: an attacker tricks a sender into encrypting various chosen plaintexts and observes the ciphertext, then uses this information to determine the key.
    - *Chosen-ciphertext*: an attacker tricks the receiver into decrypting various chosen ciphertexts and observes the resulting plaintext, then uses this information to determine the key.
]

= Symmetric key ciphers

#note[
    When converting letters to numbers, treat letters as integers modulo $26$, with $A = 1$, $Z = 0 equiv 26 thick (mod 26)$. Treat string of text as vector of integers modulo $26$.
]
#definition[
    A *symmetric key cipher* is one in which encryption and decryption keys are equal.
]
#definition[
    *Key size* is $log_2 ("number of possible keys")$.
]
#example[
    Caesar cipher is a *substitution cipher*. A stronger substitution cipher is this: key is permutation of ${a, ..., z}$. But vulnerable to known-plaintext attacks and ciphertext-only attacks, since different letters (and letter pairs) occur with different frequencies in English.
]
#definition[
    *One-time pad*: key is uniformly, independently random sequence of integers $mod 26$, $(k_1, k_2, ...)$, known to sender and receiver. If message is $(m_1, m_2, ..., m_r)$ then ciphertext is $(c_1, c_2, ..., c_r) = (k_1 + m_1, k_2 + m_2, ..., k_r + m_r)$. To decrypt the ciphertext, $m_i = c_i - k_i$. Once $(k_1, ..., k_r)$ have been used, they must never be used again.
    - One-time pad is information-theoretically secure against ciphertext-only attack: $PP(M = m | C = c) = PP(M = m)$.
    - Disadvantage is keys must never be reused, so must be as long as message.
    - Keys must be truly random.
]
#theorem("Chinese remainder theorem")[
    Let $m, n in NN$ coprime, $a, b in ZZ$. Then exists unique solution $x modulo(m n)$ to the congruences $ x equiv a & lmodulo(m) \ x equiv b & lmodulo(n) $
]
#definition[
    *Block cipher*: group characters in plaintext into blocks of $n$ (the *block length*) and encrypt each block with a key. So plaintext $p = (p_1, p_2, ...)$ is divided into blocks $P_1, P_2, ...$ where $P_1 = (p_1, ..., p_n)$, $P_2 = (p_(n + 1), ..., p_(2n)), ...$. Then ciphertext blocks are given by $C_i = f("key", P_i)$ for some encryption function $f$.
]
#definition[
    *Hill cipher*:
    - Plaintext divided into blocks $P_1, ..., P_r$ of length $n$.
    - Each block represented as column vector $P_i in (ZZ \/ 26 ZZ)^n$
    - Key is invertible $n times n$ matrix $M$ with elements in $ZZ \/ 26 ZZ$.
    - Ciphertext for block $P_i$ is $ C_i = M P_i $ It can be decrypted with $P_i = M^(-1) C_i$.
    - Let $P = (P_1, ..., P_r)$, $C = (C_1, ..., C_r)$, then $C = M P$.
]
#definition[
    *Confusion* means each character of ciphertext depends on many characters of key.
]
#definition[
    *Diffusion* means changing single character of plaintext changes many characters of ciphertext. Ideal diffusion is when changing single character of plaintext changes a proportion of $(S - 1)\/S$ of the characters of the ciphertext, where $S$ is the number of possible symbols.
]
#remark[
    Confusion and diffusion make ciphertext-only attacks difficult.
]
#example[
    For Hill cipher, $i$th character of ciphertext depends on $i$th row of key (so depends on $n$ characters of the key $M$) - this is medium confusion. If $j$th character of plaintext changes and $M_(i j) != 0$ then $i$th character of ciphertext changes. $M_(i j)$ is non-zero with probability roughly $25\/26$ so good diffusion.
]
#example[
    Hill cipher is susceptible to known plaintext attack:
    - If $P = (P_1, ..., P_n)$ are $n$ blocks of plaintext with length $n$ such that $P$ is invertible and we know $P$ and the corresponding $C$, then we can recover $M$, since $C = M P ==> M = C P^(-1)$.
    - If enough blocks of ciphertext are intercepted, it is very likely that $n$ of them will produce an invertible matrix $P$.
]

= Public key encryption and RSA

#definition[
    *Public key cryptosystem*:
    - Bob produces encryption key, $k_E$, and decryption key, $k_D$. He publishes $k_E$ and keeps $k_D$ secret.
    - To encrypt message $m$, Alice sends ciphertext $c = f(m, k_E)$ to Bob.
    - To decrypt ciphertext $c$, Bob computes $g(c, k_D)$, where $g$ satisfies $ g(f(m, k_E), k_D) = m $ for all messages $m$ and all possible keys.
    - Computing $m$ from $f(m, k_E)$ should be hard without knowing $k_D$.
]
#algorithm[
    *Converting between messages and numbers*:
    - To convert message $m_1 m_2 ... m_r$, $m_i in {0, ..., 25}$ to number, compute $ m = sum_(i = 1)^r m_i 26^(i - 1) $
    - To convert number $m$ to message, append character $m mod 26$ to message. If $m < 26$, stop. Otherwise, floor divide $m$ by $26$ and repeat.
]
#theorem("Fermat's little theorem")[
    Let $p$ prime, $a in ZZ$ coprime to $p$, then $a^(p - 1) equiv 1 thick (mod p)$.
]
#definition[
    *Euler $phi$ function* is $ phi: NN -> NN, quad phi(n) = |{1 <= a <= n: gcd(a, n) = 1}| = |(ZZ \/ n ZZ)^times| $
]
#proposition[
    $phi(p^r) = p^r - p^(r - 1)$, $phi(m n) = phi(m) phi(n)$ for $gcd(m, n) = 1$.
]
#theorem("Euler's theorem")[
    If $gcd(a, n) = 1$, $a^(phi(n)) equiv 1 quad (mod n)$.
]
#algorithm("RSA")[
    - $k_E$ is pair $(n, e)$ where $n = p q$, the *RSA modulus*, is product of two distinct primes and $e in ZZ$, the *encryption exponent*, is coprime to $phi(n)$.
    - $k_D$, the *decryption exponent*, is integer $d$ such that $d e equiv 1 quad (mod phi(n))$.
    - $m$ is an integer modulo $n$, $m$ and $n$ are coprime.
    - Encryption: $c = m^e quad (mod n)$.
    - Decryption: $m = c^d quad (mod n)$.
    - It is recommended that $n$ have at least $2048$ bits. A typical choice of $e$ is $2^16 + 1$.
]
#definition[
    *RSA problem*: given $n = p q$ a product of two unknown primes, $e$ and $m^e quad (mod n)$, recover $m$. If $n$ can be factored, then RSA is solved.
]
#definition[
    *Factorisation problem*: given $n = p q$ for large distinct primes $p$ and $q$, find $p$ and $q$.
]
#definition[
    *RSA signatures*:
    - Public key is $(n, e)$ and private key is $d$.
    - When sending a message $m$, message is *signed* by also sending $s = m^d mod n$, the *signature*.
    - $(m, s)$ is received, *verified* by checking if $m = s^e mod n$.
    - Forging a signature on a message $m$ would require finding $s$ with $m = s^e mod n$. This is the RSA problem.
    - However, choosing signature $s$ first then taking $m = s^e mod n$ produces valid pairs.
    - To solve this, $(m, s)$ is sent where $s = h(m)^d$, $h$ is *hash function*. Then the message receiver verifies $h(m) = s^e mod n$.
    - Now, for a signature to be forged, an attacker would have to find $m$ with $h(m) = s^e mod n$.
]
#definition[
    *Hash function* is function $h: {"messages"} -> cal(H)$ that:
    - Can be computed efficiently
    - Is *preimage-resistant*: can't quickly find $m$ given $h(m)$.
    - Is *collision-resistant*: can't quickly find $m, m'$ such that $h(m) = h(m')$.
]
#example("Attacks on RSA")[
    - If you can factor $n$, you can compute $d$, so can break RSA (as then you know $phi(n)$ so can compute $e^(-1) thick mod phi(n)$).
    - If $phi(n)$ is known, then we have $p q = n$ and $(p - 1)(q - 1) = phi(n)$ so $p + q = n - phi(n) + 1$. Hence $p$ and $q$ are roots of $x^2 - (n - phi(n) + 1)x + n$.
    - *Known $d$ attack*:
        - $d e - 1$ is multiple of $phi(n)$ so $p, q | x^(d e - 1) - 1$.
        - Look for factor $K$ of $d e - 1$ with $x^K - 1$ divisible by $p$ but not $q$ (or vice versa) (so likely that $(p - 1) | K$ but $(q - 1) divides.not K$).
        - Let $d e - 1 = 2^r s$, $gcd(2, s) = 1$, choose random $x mod n$. Let $y = x^s$, then $y^(2^r) = x^(2^r s) = x^(d e - 1) equiv 1 thick mod n$.
        - If $y equiv 1 thick mod n$, restart with new random $x$. Find first occurence of $1$ in $y, y^2, ..., y^(2^r)$: $y^(2^j) equiv.not 1 thick mod n$, $y^(2^(j + 1)) equiv 1 thick mod n$ for some $j >= 0$.
        - Let $a := y^(2^j)$, then $a^2 equiv 1 thick mod n$, $a equiv.not 1 thick mod n$. If $a equiv -1 thick mod n$, restart with new random $x$.
        - Now $n = p q | a^2 - 1 = (a + 1)(a - 1)$ but $n divides.not (a + 1), (a - 1)$. So $p$ divides one of $a + 1$, $a - 1$ and $q$ divides the other. So $gcd(a - 1, n)$, $gcd(a + 1, n)$ are prime factors of $n$.
]
#theorem[
    it is no easier to find $phi(n)$ than to factorise $n$.
]
#theorem[
    it is no easier to find $d$ than to factor $n$.
]
#algorithm("Miller-Rabin")[
    To probabilistically check whether $n$ is prime:
    + Let $n - 1 = 2^r s$, $gcd(2, s) = 1$.
    + Choose random $x mod n$, compute $y = x^s mod n$.
    + Compute $y, y^2, ..., y^(2^r) mod n$.
    + If $1$ isn't in this list, $n$ is *composite* (with witness $x$).
    + If $1$ is in list preceded by number other than $plus.minus 1$, $n$ is *composite* (with witness $x$).
    + Other, $n$ is *possible prime* (to base $x$).
]
#theorem[
    - If $n$ prime then it is possible prime to every base.
    - If $n$ composite then it is possible prime to $<= 1\/4$ of possible bases.
    In particular, if $k$ random bases are chosen, probability of composite $n$ being possible prime for all $k$ bases is $<= 4^(-k)$.
]

== Factorisation

#algorithm("Trial division factorisation")[
    For $p = 2, 3, 5, ...$ up to $sqrt(n)$, test whether $p | n$.
]
#algorithm("Fermat's method for factorisation")[
    - If $x^2 equiv y^2 mod n$ but $x equiv.not plus.minus y mod n$, then $x - y$ is divisible by factor of $n$ but not by $n$ itself, so $gcd(x - y, n)$ gives proper factor of $n$ (or $1$).
    - Let $a = ceil(sqrt(n))$. Compute $a^2 mod n$, $(a + 1)^2 mod n$ until a square $x^2 equiv (a + i)^2 mod n$ appears. Then compute $gcd(a + i - x, n)$.
    - Works well under special conditions on the factors: if $|p - q| <= 2 sqrt(2) root(4, n)$ then Fermat's method takes one step: $x = ceil(sqrt(n))$ works.
]
#definition[
    An integer is *$B$-smooth* if all its prime factors are $<= B$.
]
#algorithm("Quadratic sieve")[
    - Choose $B$ and let $m$ be number of primes $<= B$.
    - Look at integers $x = ceil(sqrt(n)) + k$, $k = 1, 2, ...$ and check whether $y = x^2 - n$ is $B$-smooth.
    - Once $y_1 = x_1^2 - n, ..., y_t = x_t^2 - n$ are all $B$-smooth with $t > m$, find some product of them that is a square.
    - Deduce a congruence between the squares. Use difference of two squares and $gcd$ to factor $n$.
    - Time complexity is $exp(sqrt(log n log log n))$.
]

= Diffie-Hellman key exchange

#theorem("Primitive root theorem")[
    Let $p$ prime, then there exists $g in FF_p^times$ such that $1, g, ..., g^(p - 2)$ is complete set of residues $mod p$.
]
#definition[
    Let $p$ prime, $g in FF_p^times$. *Order* of $g$ is smallest $a in NN$ such that $g^a = 1$. $g$ is *primitive root* if its order is $p - 1$ (equivalently, $1, g, ..., g^(p - 2)$ is complete set of residues $mod p$).
]
#definition[
    Let $p$ prime, $g in FF_p^times$ primitive root. If $x in FF_p^times$ then $x = g^L$ for some $0 <= L < p - 1$. Then $L$ is *discrete logarithm* of $x$ to base $g$. Write $L = L_g (x)$.
]
#proposition[
    - $g^(L_g (x)) equiv x quad (mod p)$ and $g^a equiv x quad (mod p) <==> a equiv L_g (x) quad (mod p - 1)$.
    - $L_g (1) = 0$, $L_g (g) = 1$.
    - $L_g (x y) equiv L_g (x) + L_g (y) quad (mod p - 1)$.
    - $L_g (x^(-1)) = -L_g (x) thick (mod p - 1)$.
    - $L_g (g^a mod p) equiv a thick (mod p - 1)$.
    - $h$ is primitive root mod $p$ iff $L_g (h)$ coprime to $p - 1$. So number of primitive roots mod $p$ is $phi(p - 1)$.
]
#definition[
    *Discrete logarithm problem*: given $p, g, x$, compute $L_g (x)$.
]
#definition[
    *Diffie-Hellman key exchange*:
    - Alice and Bob publicly choose prime $p$ and primitive root $g mod p$.
    - Alice chooses secret $alpha mod (p - 1)$ and sends $g^alpha mod p$ to Bob publicly.
    - Bob chooses secret $beta mod (p - 1)$ and sends $g^beta mod p$ to Alice publicly.
    - Alice and Bob both compute shared secret $kappa = g^(alpha beta) = (g^alpha)^beta) = (g^beta)^alpha mod p$.
]
#definition[
    *Diffie-Hellman problem*: given $p, g, g^alpha, g^beta$, compute $g^(alpha beta)$.
]
#remark[
    If discrete logarithm problem can be solved, so can Diffie-Hellman problem (since could compute $alpha = L_g (g^a)$ or $beta = L_g (g^beta)$).
]
#definition[
    *Elgamal public key encryption*:
    - Alice chooses prime $p$, primitive root $g$, private key $alpha med med mod (p - 1)$.
    - Her public key is $y = g^alpha$.
    - Bob chooses random $k mod (p - 1)$
    - To send message $m$ (integer mod $p$), he sends the pair $(r, m') = (g^k, m y^k)$.
    - To decrypt message, Alice computes $r^alpha = g^(alpha k) = y^k$ and then $m' r^(-alpha) = m' y^(-k) = m g^(alpha k) g^(-alpha k) = m$.
    - If Diffie-Hellman problem is hard, then Elgamal encryption is secure against known plaintext attack.
    - Key $k$ must be random and different each time.
]
#definition[
    *Decision Diffie-Hellman problem*: given $g^a, g^b, c$ in $FF_p^times$, decide whether $c = g^(a b)$.
    
    This problem is not always hard, as can tell if $g^(a b)$ is square or not. Can fix this by taking $g$ to have large prime order $q | (p - 1)$. $p = 2q + 1$ is a good choice.
]
#definition[
    *Elgamal signatures*:
    - Public key is $(p, g)$, $y = g^alpha$ for private key $alpha$.
    - *Valid Elgamal signature* on $m in {0, ..., p - 2}$ is pair $(r, s)$, $0 <= r, s <= p - 1$ such that  $ y^r r^s = g^m quad (mod p) $
    - Alice computes $r = g^k$, $k in (ZZ\/(p - 1))^times$ random. $k$ should be different each time.
    - Then $g^(alpha r) g^(k s) equiv g^m quad mod p$ so $alpha r + k s equiv m quad (mod p - 1)$ so $s = k^(-1) (m - alpha r) quad mod p - 1$.
]
#definition[
    *Elgamal signature problem*: given $p, g, y, m$, find $r, s$ such that $y^r r^s = m$.
]
#algorithm("Baby-step giant-step algorithm")[
    To solve DLP:
    - Let $N = ceil(sqrt(p - 1))$.
    - Baby-steps: compute $g^j thick mod p$ for $0 <= j < N$.
    - Giant-steps: compute $x g^(-N k) thick mod p$ for $0 <= k < N$.
    - Look for a match between baby-steps and giant-steps lists: $g^j = x g^(-N k) ==> x = g^(j + N k)$.
    - Always works since if $x = g^L$ for $0 <= L < p - 1 <= N^2$, $L$ can be written as $j + N k$ with $j, k in {0, ..., N - 1}$.
]
#algorithm("Index calculus")[
    To solve DLP:
    - Fix smoothness bound $B$.
    - Find many multiplicative relations between $B$-smooth numbers and powers of $g mod p$.
    - Solve these relations to find discrete logarithms of primes $<= B$.
    - For $i = 1, 2, ...$ compute $x g^i mod p$ until one is $B$-smooth, then use result from previous step.
]
#remark[
    *Pohlig-Hellman algorithm* computes discrete logarithms $mod p$ with approximate complexity $log(p) sqrt(ell)$ where $ell$ is largest prime factor of $p - 1$, so is fast if $p - 1$ is $B$-smooth. Therefore $p$ is chosen so that $p - 1$ has large prime factor, e.g. choose *Germain prime* $p = 2q + 1$, with $q$ prime.
]

= Elliptic curves

#definition[
    *abelian group* $(G, compose)$ satisfies:
    - *Associativity*: $forall a, b, c, in G, a compose (b compose c) = (a compose b) compose c$.
    - *Identity*: $exists e in G: forall g in G, e times g = g$.
    - *Inverses*: $forall g in G, exists h in G: g compose h = h compose g = e$
    - *Commutativity*: $forall a, b in G, a compose b = b compose a$.
]
#definition[
    $H subset.eq G$ is *subgroup* of $G$ if $(H, compose)$ is group.
]
#remark[
    To show $H$ is subgroup, sufficient to show $g, h in H => g compose h in H$ and $h^(-1) in H$.
]
#notation[
    for $g in G$, write $[n] g$ for $g compose dots.h.c compose g$ $n$ times if $n > 0$, $e$ if $n = 0$, $[-n] g^(-1)$ if $n < 0$.
]
#definition[
    *subgroup generated by $g$* is $ angle.l g angle.r = {[n]g: n in ZZ} $ If $angle.l g angle.r$ finite, it has *order $n$*, and $g$ has *order $n$*. If $G = angle.l g angle.r$ for some $g in G$, $G$ is *cyclic* and $g$ is *generator*.
]
#theorem("Lagrange's theorem")[
    Let $G$ finite group, $H$ subgroup of $G$, then $|H| | |G|$.
]
#corollary[
    if $G$ finite, $g in G$ has order $n$, then $n | |G|$.
]
#definition[
    *DLP for abelian groups*: given $G$ a cyclic abelian group, $g in G$ a generator of $G$, $x in G$, find $L$ such that $[L]g = x$. $L$ is well-defined modulo $|G|$.
]
#definition[
    let $(G, compose)$, $(H, circle.filled.small)$ abelian groups, *homomorphism* between $G$ and $H$ is $f: G -> H$ with $ forall g, g' in G, quad f(g compose g') = f(g) circle.filled.small f(g') $ *Isomorphism* is bijective homomorphism. $G$ and $H$ are *isomorphic*, $G tilde.equiv H$, if there is isomorphism between them.
]
#theorem("Fundamental theorem of finite abelian groups")[
    Let $G$ finite abelian group, then there exist unique integers $2 <= n_1, ..., n_r$ with $n_i | n_(i + 1)$ for all $i$, such that $ G tilde.eq (ZZ \/ n_1) times dots.h.c times (ZZ \/ n_r) $ In particular, $G$ is isomorphic to product of cyclic groups.
]
#definition[
    let $K$ field, $"char"(K) > 3$. An *elliptic curve* over $K$ is defined by the equation $ y^2 = x^3 + a x + b $ where $a, b in K$, $Delta_E := 4a^3 + 27b^2 != 0$.
]
#remark[
    $Delta_E != 0$ is equivalent to $x^3 + a x + b$ having no repeated roots (i.e. $E$ is smooth).
]
#definition[
    for elliptic curve $E$ defined over $K$, a *$K$-point* (*point*) on $E$ is either:
    - A *normal point*: $(x, y) in K^2$ satisfying the equation defining $E$.
    - The *point at infinity* $PAI$ which can be thought of as infinitely far along the $y$-axis (in either direction).
    Denote set of all $K$-points on $E$ as $E(K)$.
]
#remark[
    Any elliptic curve $E(K)$ is an abelian group, with group operation $plus.circle$ is defined as:
    - We should have $P plus.circle Q plus.circle R = PAI$ iff $P, Q, R$ lie on straight line.
    - In this case, $P plus.circle Q = -R$.
    - To find line $ell$ passing through $P = (x_0, y_0)$ and $Q = (x_1, y_1)$:
        - If $x_0 != x_1$, then equation of $ell$ is $y = lambda x + mu$, where $ lambda = (y_1 - y_0)/(x_1 - x_0), quad mu = y_0 - lambda x_0 $ Now $ y^2 & = x^3 + a x + b = (lambda x + mu)^2 \ ==> 0 & = x^3 - lambda^2 x^2 + (a - 2 lambda mu)x + (b - mu^2) $ Since sum of roots of monic polynomial is equal to minus the coefficient of the second highest power, and two roots are $x_0$ and $x_1$, the third root is $x_2 = lambda^2 - x_0 - x_1$. Then $y_2 = lambda x_2 + mu$ and $R = (x_2, y_2)$.
        - If $x_0 = x_1$, then using implicit differentiation: $ & y^2 = x^3 + a x + b \ ==> & (dif y)/(dif x) = (3x^2 + a)/(2y) $ and the rest is as above, but instead with $lambda = (3x_0^2 + a)/(2y_0)$.
]
#definition[
    *Group law* of elliptic curves: let $E: y^2 = x^3 + a x + b$. For all normal points $P = (x_0, y_0), Q = (x_1, y_1) in E(K)$, define
    - $PAI$ is group identity: $P plus.circle PAI = PAI plus.circle P = P$.
    - If $P = -Q =: (x_0, -y_0)$, $P plus.circle Q = PAI$.
    - Otherwise, $P plus.circle Q = (x_2, -y_2)$, where $ x_2 & = lambda^2 - (x_0 + x_1), \ y_2 & = lambda x_2 + mu, \ lambda & = cases((y_1 - y_0)/(x_1 - x_0) & "if" x_0 != x_1, (3x_0^2 + a)/(2y_0) & "if" x_0 = x_1), \ mu & = y_0 - lambda x_0 $
]
#example[
    - Let $E$ be given by $y^2 = x^3 + 17$ over $QQ$, $P = (-1, 4) in E(QQ)$, $Q = (2, 5) in E(QQ)$. To find $P plus.circle Q$, $ lambda = (5 - 4)/(2 - (-1)) = 1/3, quad mu = 4 - lambda(-1) = 13/3 $ So $x_2 = lambda^2 - (-1) -2 = -8/9$ and $y_2 = -(lambda x_2 + mu) = -109/27$ hence $ P plus.circle Q = (-8/9, -109/27) $ To find $[2]P$, $ lambda = (3(-1)^2 + 0)/(2 dot.op 4) = 3/8, quad mu = 4 - 3/8 dot.op (-1) = 35/8 $ so $x_3 = lambda^2 - 2 dot.op (-1) 137/64$, $y_3 = -(lambda x_3 + mu) = -2651/512$ hence $ [2]P = (x_3, y_3) = (137/64, -2651/512) $
]
#theorem("Hasse's theorem")[
    Let $|E(FF_p)| = N$, then $ |N - (p + 1)| <= 2 sqrt(p) $
]
#theorem[
    $E(FF_p)$ is isomorphic to either $ZZ\/k$ or $ZZ\/m times ZZ\/n$ with $m | n$.
]
#definition[
    *Elliptic curve Diffie-Hellman*:
    - Alice and Bob publicly choose elliptic curve $E(FF_p)$ and $P in FF_p$ with order a large prime $n$.
    - Alice chooses random $alpha in {0, ..., n - 1}$ and publishes $Q_A = [alpha]P$.
    - Bob chooses random $beta in {0, ..., n - 1}$ and publishes $Q_B = [beta]P$.
    - Alice computes $[alpha]Q_B = [alpha beta]P$, Bob computes $[beta]Q_A = [beta alpha]P$.
    - Shared key is $K = [alpha beta] P$.
]
#definition[
    *Elliptic curve Elgamal signatures*:
    - Use agreed elliptic curve $E$ over $FF_p$, point $P in E(FF_p)$ of prime order $n$.
    - Alice wants to sign message $m$, encoded as integer mod $n$.
    - Alice generates private key $alpha in ZZ\/n$ and public key $Q = [alpha] P$.
    - Valid signature is $(R, s)$ where $R = (x_R, y_R) in E(FF_p)$, $s in ZZ\/n$, $[tilde(x_R)] Q plus.circle [s] R = [m] P$.
    - To generate a valid signature, Alice chooses random $0 != k in (ZZ\/n)^times$ and sets $R = [k] P$, $s = k^(-1) (m - tilde(x_R) alpha)$.
    - $k$ must be randomly generated for each message.
]
#algorithm("Elliptic curve DLP baby-step giant-step algorithm")[
    Given $P$ and $Q = [alpha] P$, find $alpha$:
    - Let $N = ceil(sqrt(n))$, $n$ is order of $P$.
    - Compute $P, [2] P, ..., [N - 1]P$.
    - Compute $Q plus.circle [-N]P, Q plus.circle [-2N]P, ..., Q plus.circle [-(N - 1)N]P$ and find a match between these two lists: $[i]P = Q plus.circle [-j N]P$, then $[i + j N]P = Q$ so $alpha = i + j N$.
]
#remark[
    For well-chosen elliptic curves, the best algorithm for solving DLP is the baby-step giant-step algorithm, with run time $O(sqrt(n)) approx O(sqrt(p))$. This is much slower than the index-calculus method for the DLP in $FF_p^times$.
]
#algorithm([Pollard's $p - 1$ algorithm])[
    To factorise $n = p q$:
    - Choose smoothness bound $B$.
    - Choose random $2 <= a <= n - 2$. Set $a_1 = a$, $i = 2$.
    - Compute $a_i = a_(i - 1)^i thick mod n$. Find $d = gcd(a_i - 1, n)$. If $1 < d < n$, we have found a nontrivial factor of $n$. If $d = n$, pick new $a$ and retry. If $d = 1$, increment $i$ by $1$ and repeat this step.
    - A variant is instead of computing $a_i = a_(i - 1)^i$, compute $a_i = a_(i - 1)^(m_(i - 1))$ where $m_1, ..., m_r$ are the prime powers $<= B$ (each prime power is the maximal prime power $<= B$ for that prime).
    - The algorithm works if $p - 1$ is *$B$-powersmooth* (all prime power factors are $<= B$), since if $b$ is order of $a mod p$, then $b | (p - 1)$ so $b | B!$ (also $b | m_1 dots.h.c m_r$). If the first $i$ for which $i!$ (or $m_1 dots.h.c m_i$) is divisible by $d$ and order of $a mod q$, then $a_i - 1 = a^(i!) - 1 mod n$ is divisible by both $p$ and $q$, so must retry with different $a$.
]
#remark[
    Let $n = p q$, $p, q$ prime, $a, b in ZZ$, $gcd(4a^3 + 27b^2, n) = 1$. Then $E: y^2 = x^3 + a x + b$ defines elliptic curve over $FF_p$ and over $FF_q$. If $(x, y) in ZZ\/n$ is solution to $E mod n$ then can reduce coordinates $mod p$ to obtain non-infinite point of $E(FF_p)$ and $mod q$ to obtain non-infinite point of $E(FF_q)$.
]
#proposition[
    let $P_1 = (x_1, y_1), P_2 = (x_2, y_2) in E mod n$, with $ (P_1 mod p) plus.circle (P_2 mod p) & = PAI \ (P_1 mod q) plus.circle (P_2 mod q) & != PAI $ Then $gcd(x_1 - x_2, n)$ (or $gcd(2x_1, n)$ if $P_1 = P_2$) is factor of $n$.
]
#algorithm("Lenstra's algorithm")[
    To factorise $n$:
    - Choose smoothness bound $B$.
    - Choose random elliptic curve $E$ over $ZZ\/n$ with $gcd(Delta_E, n) = 1$ and $P = (x, y)$ a point on $E$.
    - Set $P_1 = P$, attempt to compute $P_i$, $2 <= i <= B$ by $P_i = [i] P_(i - 1)$. If one of these fails, a divisor of $n$ has been found (by failing to compute an inverse $mod n$). If this divisor is trivial, restart with new curve and point.
    - If $i = B$ is reached, restart with new curve and point.
    - Again, a variant is calculating $P_i = [m_i]P_(i - 1)$ instead of $[i]P_(i - 1)$ where $m_1, ..., m_r$ are the prime powers $<= B$
]
#remark[
    Lenstra's algorithm works if $|E(ZZ\/p)|$ is $B$-powersmooth but $|E(ZZ\/q)|$ isn't. Since we can vary $E$, it is very likely to work eventually.

    Running time depends on $p$ (the smaller prime factor): $ O(exp(sqrt(2 log(p) log log (p)))) $ Compare this to the general number field sieve running time: $ O(exp(C (log n)^(1\/3) (log log n)^(2\/3))) $
]

== Torsion points

#definition[
    Let $G$ abelian group. $g in G$ is a *torsion* if it has finite order. If order divides $n$, then $[n]g = e$ and $g$ is *$n$-torsion*.
]
#definition[
    *$n$-torsion subgroup* is $ G[n] := {g in G: [n]g = e} $
]
#definition[
    *torsion subgroup* of $G$ is $ G_"tors" = {g in G: g "is torsion"} = union.big_(n in NN) G[n] $
]
#example[
    - In $ZZ$, only $0$ is torsion.
    - In $(ZZ\/10)^times$, by Lagrange's theorem, every point is $4$-torsion.
    - For finite groups $G$, $G_"tors" = G = G[ |G| ]$ by Lagrange's theorem.
]

== Rational points

#note[
    for elliptic curve $E: y^2 = x^3 + a x + b$ over $QQ$, can assume that $a, b in ZZ$. So assume $a, b in ZZ$ in this section.
]
#theorem("Nagell-Lutz")[
    Let $E$ elliptic curve, let $P = (x, y) in E(QQ)_"tors"$. Then $x, y in ZZ$, and either $y = 0$ (in which case $P$ is $2$-torsion) or $y^2 divides Delta_E$.
]
#corollary[
    $E(QQ)_"tors"$ is finite.
]
#example[
    can use Nagell-Lutz to show a point is not torsion.
    - $P = (0, 1)$ lies on elliptic curve $y^2 = x^3 -x + 1$. $[2]P = (1/4, -7/8) in.not ZZ^2$. Then $[2]P$ is not torsion, hence $P$ is not torsion. So $E(QQ)$ contains  distinct points $..., [-2]P, -P, PAI, P, [2]P, ...$, hence $E$ has infinitely many solutions in $QQ$.
]
#theorem("Mazur")[
    Let $E$ be elliptic curve over $QQ$. Then $E(QQ)_"tors"$ is either:
    - cyclic of order $1 <= N <= 10$ or order $12$, or
    - of the form $ZZ\/2 times ZZ\/2N$ for $1 <= N <= 4$.
]
#definition[
    let $E: y^2 = x^3 + a x + b$ defined over $QQ$, $a, b in ZZ$. For odd prime $p$, taking reductions $overline(a)$, $overline(b) mod p$ gives curve over $FF_p$: $ overline(E): y^2 = x^3 + overline(a) x + overline(b) $ This is elliptic curve if $Delta_E equiv.not 0 mod p$, in which case $p$ is *prime of good reduction* for $E$.
]
#theorem[
    let $E: y^2 = x^3 + a x + b$ defined over $QQ$, $a, b in ZZ$, $p$ be odd prime of good reduction for $E$. Then $f: E(QQ)_"tors" -> overline(E)(FF_p)$ defined by $ f(x, y) := (overline(x), overline(y)), quad f\(PAI\) := PAI $ is an injective homomorphism (note $x, y in ZZ$ by Nagell-Lutz).
]
#corollary[
    $E(QQ)_"tors"$ can be thought of as subgroup of $E(FF_p)$ for any prime $p$ of good reduction, so by Lagrange's theorem, $|E(QQ)_"tors"|$ divides $|E(FF_p)|$.
]
#theorem("Mordell")[
    If $E$ is elliptic curve over $QQ$, then $ E(QQ) tilde.equiv E(QQ)_"tors" times ZZ^r $ for some $r >= 0$ the *rank* of $E$. So for some $P_1, ..., P_r in E(QQ)$, $ E(QQ) = \{n_1 P_1 + dots.h.c + n_r P_r + T: n_i in ZZ, T in E(QQ)_"tors"\} $ $P_1, ..., P_r$ (together with $T$) are *generators* for $E(QQ)$.
]

= Basic coding theory

== First definitions

#definition[
    - *Alphabet* $A$ is finite set of symbols.
    - $A^n$ is set of all lists of $n$ symbols from $A$ - these are *words of length $n$*.
    - *Code of block length $n$ on $A$* is subset of $A^n$.
    - *Codeword* is element of a code.
]
#definition[
    If $|A| = 2$, codes on $A$ are *binary* codes. If $|A| = 3$, codes on $A$ are *ternary codes*. If $|A| = q$, codes on $A$ are *$q$-ary* codes. Generally, use $A = {0, 1, ..., q - 1}$.
]
#definition[
    Let $x = x_1 ... x_n, y = y_1 ... y_n in A^n$. *Hamming distance* between $x$ and $y$ is number of indices where $x$ and $y$ differ: $ d: A^n times A^n -> {0, ..., n}, quad d(x, y) := |{i in [n]: x_i != y_i}| $ So $d(x, y)$ is minimum number of changes needed to change $x$ to $y$. If $x$ transmitted and $y$ received, then $d(x, y)$ *symbol-errors* have occurred.
]
#proposition[
    Let $x, y$ words of length $n$.
    - $0 <= d(x, y) <= n$.
    - $d(x, y) = 0 <==> x = y$.
    - $d(x, y) = d(y, x)$.
    - $forall z in A^n, d(x, y) <= d(x, z) + d(z, y)$.
]
#definition[
    *Minimum distance* of code $C$ is $ d(C) := min{d(x, y): x, y in C, x != y} in NN $
]
#notation[
    Code of block length $n$ with $M$ codewords and minimum distance $d$ is called $(n, M, d)$ (or $(n, M)$) code. A $q$-ary code is called an $\(n, M, d\)_q$ code.
]
#definition[
    Let $C subset.eq A^n$ code, $x$ word of length $n$. A *nearest neighbour* of $x$ is codeword $c in C$ such that $d(x, c) = min{d(x, y): y in C}$.
]

== Nearest-neighbour decoding

#definition[
    *Nearest-neighbour decoding (NND)* means if word $x$ received, it is decoded to a nearest neighbour of $x$ in a code $C$.
]
#proposition[
    Let $C$ be code with minimum distance $d$, let word $x$ be received with $t$ symbol errors. Then
    - If $t <= d - 1$, then we can detect that $x$ has some errors.
    - If $t <= floor((d - 1)/2)$, then NND will correct the errors.
]

== Probabilities

#definition[
    *$q$-ary symmetric channel with symbol-error probability $p$* is channel for $q$-ary alphabet $A$ such that:
    - For every $a in A$, probability that $a$ is changed in channel is $p$ (i.e. symbol-errors in different positions are independent events).
    - For every $a != b in A$, probability that $a$ is changed to $b$ in channel is $ PP(b "received" | a "sent") = p/(q - 1) $
    i.e. given that a symbol has changed, it is equally likely to change to any of the $q - 1$ other symbols.
]
#proposition[
    Let $c$ codeword in $q$-ary code $C subset.eq A^n$ sent over $q$-ary symmetric channel with symbol-error probability $p$. Then $ PP(x "received" | c "sent") = (p/(q - 1))^t (1 - p)^(n - t), quad "where" t = d(c, x) $
]
#example[
    Let $C = {000, 111} subset {0, 1}^3$.
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
]
#corollary[
    If $p < (q - 1)/q$ then $P(x "received" | c "sent")$ increases as $d(x, c)$ decreases.
]
#remark[
    By Bayes' theorem, $ PP(c "sent" | x "received") = PP(c "sent and" x "received") / PP(x "received") = (PP(c "sent") PP(x "received" | c "sent"))/PP(x "received") $
]
#proposition[
    Let $C$ be $q$-ary $(n, M, d)$ code used over $q$-ary symmetric channel with symbol-error probability $p < (q - 1)\/q$, and each codeword $c in C$ is equally likely to be sent. Then for any word $x$, $PP(c "sent" | x "received")$ increases as $d(x, c)$ decreases.
]

== Bounds on codes

#proposition("Singleton bound")[
    For $q$-ary code $(n, M, d)$ code, $M <= q^(n - d + 1)$.
]
#definition[
    Code which saturates singleton bound is called *maximum distance separable (MDS)*.
]
#example[
    Let $C_n$ be *binary repetition code* of block length $n$, $ C_n := \{underbrace(00...0, n), underbrace(11...1, n)\} subset {0, 1}^n $ $C_n$ is $(n, 2, n)_2$ code, and $2 = 2^(n - n + 1)$ so $C_n$ is MDS code.
]
#definition[
    Let $A$ be alphabet, $|A| = q$. Let $n in NN$, $0 <= t <= n$, $t in NN$, $x in A^n$.
    - *Ball of radius $t$ around $x$* is $ S(x, t) := {y in A^n: d(y, x) <= t} $
    - Code $C subset.eq A^n$ is *perfect* if $ exists t in NN_0: A^n = product.co_(c in C) S(c, t) $ where $product.co$ is disjoint union.
]
#example[
    For $C = {000, 111} subset {0, 1}^3$, $S(000, 1) = {000, 100, 010, 001}$ and $S(111, 1) = {111, 011, 101, 110}$. These are disjoint and $S(000, 1) union S(111, 1) = {0, 1}^3$, so $C$ is perfect.
]
#example[
    Let $C = {111, 020, 202} subset {0, 1, 2}^3$. $forall c in C, d(c, 012) = 2$. So $012$ is not in any $S(c, 1)$ but is in every $S(c, 2)$, so $C$ is not perfect.
]
#lemma[
    Let $|A| = q$, $x in A^n$, then $ |S(x, t)| = sum_(k = 0)^t binom(n, k) (q - 1)^k $
]
#example[
    Let $C = {111, 020, 202} subset {0, 1, 2}^3$, so $q = 3$, $n = 3$. So $|S(x, 1)| = binom(3, 0) + binom(3, 1) (3 - 1) = 7$, $|S(x, 2)| = binom(3, 0) + binom(3, 1)(3 - 1) + binom(3, 2) (3 - 1)^2 = 19$. But $|{0, 1, 2}|^3 = 27$ and $7 divides.not 27$, $19 divides.not 27$, so ${0, 1, 2}^3$ can't be partioned by balls of either size. So $C$ can't be perfect. $|S(x, 3)| = 27$, but then $C$ must contain only one codeword to be perfect, and $|S(x, 0)| = 1$, but then $C = A^n$ to be perfect. These are trivial, useless codes.
]
#proposition("Hamming/sphere-packing bound")[
    $q$-ary $(n, M, d)$ code satisfies $ M sum_(k = 0)^t binom(n, k) (q - 1)^k <= q^n, quad "where" t = floor((d - 1)/2) $
]
#corollary[
    Code saturates Hamming bound iff it is perfect.
]

= Linear codes

== Finite vector spaces

#definition[
    *Linear code* of block length $n$ is subspace of $FF_q^n$.
]
#example[
    Let $vd(x) = (0, 1, 2, 0)$, $vd(y) = (1, 1, 1, 1)$, $vd(z) = (0, 2, 1, 0) in FF_3^4$. $C_1 = {vd(x), vd(y), vd(0)}$ is not linear code since e.g. $vd(x) + vd(y) = (1, 2, 0, 1) in.not C_1$. $C_2 = {vd(x), vd(z), vd(0)}$ is linear code.
]
#notation[
    Spanning set of $S$ is $ideal(S)$.
]
#proposition[
    If linear code $C subset.eq FF_q^n$ has $dim(C) = k$, then $|C| = q^k$.
]
#definition[
    A $q$-ary $[n, k, d]$ code is linear code: a subspace of $FF_q^n$ of dimension $k$ with minimum distance $d$. Note: a $q$-ary $[n, k, d]$ code is a $q$-ary $(n, q^k, d)$ code.
]

== Weight and minimum distance

#definition[
    *Weight* of $vd(x) in FF_q^n$, $w(vd(x))$, is number of non-zero entries in $vd(x)$: $ w(vd(x)) = |{i in [n]: x_i != 0}| $
]
#lemma[
    $forall vd(x), vd(y) in FF_q^n$, $d(vd(x), vd(y)) = w(vd(x) - vd(y))$. In particular, $w(vd(x)) = d(vd(x), vd(0))$.
]
#proposition[
    Let $C subset.eq FF_q^n$ linear code, then $ d(C) = min{w(vd(c)): vd(c) in C, vd(c) != vd(0)} $
]<min-dist-as-weight>
#remark[
    To find $d(C)$ for linear code with $q^k$ words, only need to consider $q^k$ weights instead of $binom(q^k, 2)$ distances.
]

= Codes as images

== Generator-matrices

#definition[
    Let $C subset.eq FF_q^n$ be linear code. Let $G in M_(k, n)(FF_q)$, $f_G: FF_q^k -> FF_q^n$ be linear map defined by $f_G (vd(x)) = vd(x) G$. Then $G$ is *generator-matrix* for $C$ if
    - $C = im(f) = \{vd(x) G: vd(x) in FF_q^k\} subset.eq FF_q^n$.
    - The rows of $G$ are linearly independent.
    i.e. $G$ is generator-matrix for $C$ iff rows of $G$ form basis for $C$ (note $vd(x) G = x_1 vd(g_1) + dots.h.c + x_k vd(g_k)$ where $vd(g_i)$ are rows of $G$).
]
#remark[
    Given linear code $C = ideal(vd(a)_1, ..., vd(a)_m)$, a generator-matrix can be found for $C$ by constructing the matrix $A$ with rows $vd(a)_i$, then performing elementary row operations to bring $A$ into RREF. Once the $m - k$ bottom zero rows have been removed, the resulting matrix is a generator-matrix.
]
#example[
    Let $C = ideal({(0, 0, 3, 1, 4), (2, 4, 1, 4, 0), (5, 3, 0, 1, 6)}) subset.eq FF_7^5$. $
    A = mat(2, 4, 1, 4, 0; 5, 3, 0, 1, 6; 0, 0, 3, 1, 4) limits(->_(A_(12)(1))) mat(2, 4, 1, 4, 0; 0, 0, 1, 5, 6; 0, 0, 3, 1, 4) limits(->_(M_1 (4))) mat(1, 2, 4, 2, 0; 0, 0, 1, 5, 6; 0, 0, 3, 1, 4) limits(->_(A_(21)(3), A_(23)(4))) mat(1, 2, 0, 3, 4; 0, 0, 1, 5, 6; 0, 0, 0, 0, 0)
$ So $G = mat(1, 2, 0, 3, 4; 0, 0, 1, 5, 6)$ is generator matrix for $C$ and $dim(C) = 2$.
]

== Encoding and channel decoding

- Let $C$ be $q$-ary $[n, k]$ code with generator matrix $G in M_(k, n)(FF_q)$. To encode a message $x in FF_q^k$, multiply by $G$: codeword is $c = x G$.
- Note that rows of $G$ being linearly independent implies $f_G$ is injective, so no two messages are mapped to same codeword.
- If we want the code to correct (and detect) errors, we must have $k < n$.
- The received word $y in FF_q^n$ is decoded to the codeword $c' in C$.
- *Channel decoding* is finding the unique word $x'$ such that $x' G = c'$, i.e. $x' dot g_i = c'_i$ where $g_i$ is $i$th column of $G$. This gives $n$ equations in $k$ unknowns. Since $c'$ is a codeword, these equations are consistent, and since $f_G$ is injective, there is a unique solution.
- To solve $x' G = c'$, either use that $G^t (x')^t = (c')^t$ and row-reduce augmented matrix $(G^t | (c')^t)$, or pick generator-matrix in RREF, which then picks out each $x'_i$.

== Equivalence and standard form

#definition[
    Codes $C_1, C_2$ of block length $n$ over alphabet $A$ are *equivalent* if we can transform one to the other by applying sequence of the following two kinds of changes to all the codewords (simultaneously):
    - Permute the $n$ positions.
    - In a particular position, permuting the $|A| = q$ symbols.
]
#proposition[
    Equivalent codes have the same parameters $(n, M, d)$.
]
#definition[
    Linear codes $C_1, C_2 subset.eq FF_q^n$ are *monomially equivalent* if we can obtain one from the other by applying sequence of the following two kinds of changes to all codewords (simultaneously):
    - Permuting the $n$ positions.
    - In particular position, multiply by $lambda in FF_q^times$.
    If only the first change is used, the codes are *permutation equivalent*.
]
#definition[
    $P in M_n (FF_q)$ is *permutation matrix* if it has a single $1$ in each row and column, and zeros elsewhere. Any permutation of $n$ positions of row vector in $FF_q^n$ can be described as right multiplication by permutation matrix.
]
#proposition[
    Permutation matrices are orthogonal: $P^T = P^(-1)$.
]
#proposition[
    Let $C_1, C_2 subset.eq FF_q^n$ linear codes with generator matrices $G_1, G_2$. Then if $G_1 = G_2 P$ for permutation matrix $P$, then $C_1$ and $C_2$ are permutation equivalent.
]
#definition[
    $M in M_m (FF_q)$ is *monomial matrix* if it has exactly one non-zero element in each row and column.
]
#proposition[
    Monomial matrix $M$ can always be written as $M = D P$ or $M = P D'$ where $P$ is permutation matrix and $D, D'$ are diagonal matrices. $P$ is *permutation part*, $D$ and $D'$ are *diagonal parts* of $M$.
]
#example[
    $ mat(0, 2, 0; 0, 0, 3; 1, 0, 0) = mat(2, 0, 0; 0, 3, 0; 0, 0, 1) mat(0, 1, 0; 0, 0, 1; 1, 0, 0) = mat(0, 1, 0; 0, 0, 1; 1, 0, 0) mat(1, 0, 0; 0, 2, 0; 0, 0, 3) $
]
#proposition[
    Let $C_1, C_2 subset.eq FF_q^n$ be linear codes with generator-matrices $G_1, G_2$. Then if $G_2 = G_1 M$ for some monomial matrix $M$, then $C_1$ and $C_2$ are monomially equivalent.
]
#definition[
    Let $C subset.eq FF_q^n$ linear code. If $G = (I_k | A)$, with $A in M_(k, n - k)(FF_q)$, is generator-matrix for $C$, then $G$ is in *standard form*.
]
#note[
    Not every linear code has generator-matrix in standard form.
]
#proposition[
    Every linear code is permutation equivalent to a linear code with generator-matrix in standard form.
]
#example[
    Let $C_1 subset.eq FF_7^5$ have generator matrix $G_1 = mat(1, 2, 0, 3, 4; 0, 0, 1, 5, 6)$. Then applying permutation matrix $ P = mat(1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1) ==> G_1 P = mat(1, 0, 2, 3, 4; 0, 1, 0, 5, 6) = (I_2 | A) $
]

= Codes as kernels

== Dual codes

#definition[
    Let $C subset.eq FF_q^n$ linear code. *Dual* of $C$ is $ C^perp := {vd(v) in FF_q^n: forall vd(u) in C, vd(v) dot.op vd(u) = 0} $
]
#proposition[
    If $G$ is generator matrix for linear code $C$ then $ C^perp = \{vd(v) in FF_q^n : vd(v) G^T = vd(0)\} = ker(f_(G^T)) $ where $f_(G^T): FF_q^n -> FF_q^k$, $f(x) = x G^T$ is linear map.
]<dual-as-kernel>
#proposition[
    Let $C subset.eq FF_q^n$ linear code. Then $C^perp$ is also linear code and $dim(C) + dim(C^perp) = n$.
]
#proposition[
    Let $C subset.eq FF_q^n$ linear code, then $(C^perp)^perp = C$.
]
#proof[
    Show $dim((C^perp)^perp) = dim(C)$ and $C subset.eq (C^perp)^perp$.
]
#proposition[
    Let $C subset.eq FF_q^n$ have generator-matrix in standard form, $G = (I_k | A)$, then $H = (-A^T | I_(n - k))$ is generator-matrix for $C^perp$.
]
#proof[
    Show $forall y in FF_q^(n - k)$, $y H in C^perp$, let $f_H (y) = y H$ so $"im"(f_H) subset.eq C^perp$ and show $dim("im"(f_H)) = dim(C^perp)$.
]
#proposition[
    Let $G$ be generator matrix of $C subset.eq FF_q^n$, let $P in M_n (FF_q)$ permutation matrix such that $G P = (I_k | A)$ for some $A in M_(k, n - k)(FF_q)$. Then $H = (-A^T | I_(n - k)) P^T$ is generator matrix for $C^perp$.
]
#proof[
    Similar to previous proposition, use that $P^T = P^(-1)$.
]
#algorithm[
    To find basis for dual code $C^perp$, given generator matrix $G = (g_(i j)) in M_(k, n)(FF_q)$ for $C$ in RREF:
    + Let $L = {1 <= j <= n: G "has leading" 1 "in column" j}$.
    + For each $1 <= j <= n$, $j in.not L$, construct $vd(v)_j$ as follows:
        + For $m in.not L$, $m$th entry of $vd(v)_j$ is $1$ if $m = j$ and $0$ otherwise.
        + Fill in the other entries of $vd(v)_j$ (left to right) as $-g_(1 j), ..., -g_(k j)$.
    + The $n - k$ vectors $vd(v)_j$ are basis for $C^perp$.
]
#example[
    Let $C subset.eq FF_5^7$ be linear code with generator-matrix $ G = mat(1, 2, 0, 3, 4, 0, 0; 0, 0, 1, 1, 2, 0, 3; 0, 0, 0, 0, 0, 1, 4) $ Then $L = {1, 3, 6}$.
    - $v_2 = (3, 1, 0, 0, 0, 0, 0)$
    - $v_4 = (2, 0, 4, 1, 0, 0, 0)$
    - $v_5 = (1, 0, 3, 0, 1, 0, 0)$
    - $v_7 = (0, 0, 2, 0, 0, 1, 1)$
    - So generator matrix for $C^perp$ is $ H = mat(3, 1, 0, 0, 0, 0, 0; 2, 0, 4, 1, 0, 0, 0; 1, 0, 3, 0, 1, 0, 0; 0, 0, 2, 0, 0, 1, 1) $
]

== Check-matrices

#definition[
    Let $C$ be $[n, k]_q$ code, assume there exists $H in M_(n - k, n)(FF_q)$ with linearly independent rows, such that $ C = {vd(v) in FF_q^n: vd(v) H^t = vd(0)} $ Then $H$ is *check-matrix* for $C$.
]
#proposition[
    If code $C$ has generator-matrix $G$ and check-matrix $H$, then $C^perp$ has check-matrix $G$ and generator-matrix $H$.
]
#proof[
    Use @dual-as-kernel to show $G$ is check-matrix for $C^perp$. Show rows of $H$ form basis for $C^perp$.
]
#remark[
    We can use above algorithm for the $G <--> H$ algorithm: obtain a generator-matrix for $C$ from a check-matrix for $C$, or vice versa.
]

== Minimum distance from a check-matrix

#lemma[
    Let $C$ be $[n, k]_q$ code, $C = {vd(x) in FF_q^n: vd(x) A^T = vd(0)}$ for some $A in M_(m, n) (FF_q)$. The following are equivalent:
    - There are $d$ linearly dependent columns of $A$.
    - $exists vd(c) in C: 0 < w(vd(c)) <= d$.
]
#proof[
    - $==>$: use definition of linear dependence, construct a _word_ $vd(c)$ with $d$ at most non-zero symbols, based on the definition. Show that $vd(c) in C$.
    - $<==$: use non-zero entries of $vd(c)$ as coefficients for linear dependence between $d$ corresponding columns of $A$.
]
#example[
    Let $C = {vd(x) in FF_7^5: vd(x) A^T = vd(0)}$ where $ A = mat(3, 1, 1, 4, 1; 2, 2, 5, 1, 4; 6, 3, 5, 0, 2) in M_(3, 5)(FF_7) $ We have $(0, 1, 2, 0, 4) A^T = vd(0)$. So $(0, 1, 2, 0, 4) in C$, so $C$ has codeword of weight $3$. Also, $1 (1, 2, 3) + 2 (1, 5, 5) + 4 (1, 2, 4) = (0, 0, 0)$ so $A$ has $3$ linearly dependent columns.
]
#theorem[
    Let $C = {vd(x) in FF_q^n: vd(x) A^T = vd(0)}$ for some $A in M_(m, n)(FF_q)$. Then there is a linearly dependent set of $d(C)$ columns of $A$, but any set of $d(C) - 1$ columns of $A$ is linearly independent.

    So $d(C)$ is the smallest possible size of a set of linearly dependent columns of $A$.
]
#proof[
    Use @min-dist-as-weight and above lemma.
]

= Polynomials and cyclic codes

== Non-prime finite fields

#theorem[
    Let $f(x) in FF_q [x]$, then $FF_q [x] \/ ideal(f(x))$ is ring. $FF_q [x] \/ ideal(f(x))$ is field iff $f(x)$ irreducible in $FF_q [x]$.
]
#proposition[
    If $f(x) = lambda m(x) in FF_q [x]$, with $0 != lambda in FF_q$, then $ FF_q [x] \/ ideal(f(x)) = FF_q [x] \/ ideal(m(x)) $ In particular, we only need to consider monic polynomials.
]
#definition[
    $alpha in FF_q$ is *primitive* if $ FF_q^times = {alpha^j: j in {0, ..., q - 2}} $ Every finite field has a primitive element.
]
#definition[
    Let $f(x) in FF_q [x]$ irreducible. If $x$ is primitive in $FF_q [x] \/ ideal(f(x))$, then $f(x)$ is *primitive polynomial* over $FF_q$.
]
#theorem[
    Let $q = p^r$, $p$ prime, $r >= 2$ integer. Then there exists monic, irreducible $f(x) in FF_p [x]$ with $deg(f) = r$. In particular, $FF_q = FF_p [x] \/ ideal(f(x))$ is field with $q = p^r$ elements. Moreover, we can choose $f(x)$ to be primitive.
]

== Cyclic codes

#definition[
    Code $C$ is *cyclic* if it is linear and $ (a_0, ..., a_(n - 1)) in C <==> (a_(n - 1), a_0, ..., a_(n - 2)) in C $ i.e. any cyclic shift of a codeword is also a codeword.
]
#notation[
    Let $R_n = FF_q [x] \/ (x^n - 1)$. Note $R_n$ is not field. There is correspondence between elements in $R_n$ and vectors in $FF_q^n$: $ a(x) = a_0 + dots.h.c + a_(n - 1) x^(n - 1) <--> vd(a) = (a_0, ..., a_(n - 1)) $
]
#lemma[
    If $a(x) <--> vd(a)$, then $x a(x) <--> (a_(n - 1), a_0, ..., a_(n - 2))$.
]<lem:cyclic-shift-polynomial>
#proposition[
    $C subset.eq R_n$ is cyclic iff $C$ is ideal in $R_n$, i.e. $a(x), b(x) in C ==> a(x) + b(x) in C$ and $a(x) in C, r(x) in R_n ==> r(x) a(x) in C$.
]
#proof[
    - $==>$: use linearity of $C$ and @lem:cyclic-shift-polynomial.
    - $<==$: for linearity, use $r(x) = r_0$ constant. For cyclicity, use @lem:cyclic-shift-polynomial with $r(x) = x^m$.
]
#definition[
    For $f(x) in R_n$, the *code generated by $f(x)$* is $ ideal(f(x)) := {r(x) f(x): r(x) in R_n} $
]
#proposition[
    For any $f(x) in R_n$, $ideal(f(x))$ is cyclic code.
]
#example[
    Let $R_3 = FF_2 [x] \/ (x^3 - 1)$, $f(x) = x^2 + 1 in R_3$. Then $ ideal(f(x)) = & {0, 1 + x, 1 + x^2, x + x^2} subset.eq R_3 \ <--> & {(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)} subset.eq FF_2^3 $
]
#theorem[
    Let $C$ cyclic code in $R_n$ over $FF_q$, $C != {0}$. Then
    - There is unique monic polynomial $g(x)$ of smallest degree in $C$.
    - $C = ideal(g(x))$.
    - $g(x) | x^n - 1$.
]
#remark[
    Converse of above theorem holds: every monic factor $g(x)$ of $x^n - 1$ is the unique generator polynomial of $ideal(g(x))$, so distinct factors generate distinct codes. So to find all cyclic codes in $R_n$, find each monic divisor $g(x)$ of $x^n - 1$ to give cyclic code $ideal(g(x))$.
]
#proof[
    - First assume there are two such $g(x)$ which are different, obtain contradiction.
    - Use division algorithm to show $C subset.eq ideal(g(x))$ and that $g(x) | x^n - 1$.
]
#remark[
    If $C = {0}$, then setting $g(x) = x^n - 1$, we have $C = ideal(g(x))$.
]
#definition[
    In cyclic code $C$, monic polynomial of minimal degree is the *generator-polynomial* of $C$.
]
#example[
    To find all binary cyclic codes of block-length $3$, consider $R_3 = FF_2 [x]\/ideal(x^3 - 1)$. In $FF_2 [x]$, $x^3 - 1 = (x + 1)(x^2 + x + 1)$ and $x^2 + x + 1$ is irreducible. So the possible candidates for the generator-polynomial are
    #figure(table(
        columns: (auto, auto, auto),
        "generator", [code in $R_3$], [code in $FF_2^3$],
        $1$, $R_3$, $FF_2^3$,
        $x + 1$, ${0, 1 + x, 1 + x^2, x + x^2}$, ${(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)}$,
        $x^2 + x + 1$, ${0, 1 + x + x^2}$, ${(0, 0, 0), (1, 1, 1)}$,
        $x^3 - 1$, ${0}$, ${(0, 0, 0)}$
    ))
]

== Matrices for cyclic codes

#proposition[
    If $C$ is cyclic code with generator-polynomial $g(x) = g_0 + dots.h.c + g_r x^r$, then $dim(C) = n - r$ and $C$ has generator-matrix $ G = mat(g_0, g_1, dots.h.c, g_r,0, dots.h.c, dots.h.c, 0; 0, g_0, g_1, dots.h.c, g_r, 0, dots.h.c, 0; 0, 0, g_0, g_1, dots.h.c, g_r, 0, dots.h.c; 0, dots.h.c, 0, dots.down, dots.down, dots.down, dots.down, dots.down; 0, dots.h.c, dots.h.c, 0, g_0, g_1, dots.h.c, g_r) in M_(n - r, n)(FF_q) $
]
#proof[
    - Show $g_0 != 0$, use this to show rows are linearly independent.
    - Show rows of $G$ span $C$ by using polynomial representation of $C$.
]
#example[
    Let $C = {(0, 0, 0), (1, 1, 0), (0, 1, 1), (1, 0, 1)} in FF_2^3$. $C = ideal(1 + x)$ so $dim(C) = 3 - 1 = 2$, $ G = mat(1, 1, 0; 0, 1, 1) $
]
#definition[
    Let $C subset.eq R_n$ be $[n, k]$ cyclic code with generator polynomial $g(x)$, let $g(x) h(x) = x^n - 1 in FF_q [x]$. Then $h(x)$ is the *check-polynomial* of $C$.
]
#lemma[
    Check-polynomial of cyclic $[n, k]$ code is monic of degree $k$.
]
#proposition[
    Let $C$ be cyclic code in $R_n$ with check-polynomial $h(x)$. Then $c(x) in C$ iff $c(x) h(x) = 0$ in $R_n$.
]<check-polynomial-for-containment>
#proof[
    - $==>$: use that $C = ideal(g(x))$.
    - $<==$: use division algorithm.
]
#definition[
    The *reciprocal polynomial* of $h(x) = h_0 + h_1 x + dots.h.c + h_k x^k$ is $ overline(h)(x) = h_k + h_(k - 1) x + dots.h.c + h_0 x^k = x^k h(x^(-1)) $
]
#proposition[
    Let $C$ cyclic $[n, k]$ code with check-polynomial $h(x) = h_0 + dots.h.c + h_k x^k$. Then
    - $C$ has check-matrix $ H = mat(h_k, h_(k - 1), dots.h.c, h_0, 0, dots.h.c, dots.h.c, 0; 0, h_k, h_(k - 1), dots.h.c, h_0, 0, dots.h.c, 0; 0, 0, h_k, h_(k - 1), dots.h.c, h_0, 0, dots.h.c; 0, dots.h.c, 0, dots.down, dots.down, dots.down, dots.down, dots.down; 0, dots.h.c, dots.h.c, 0, h_k, h_(k - 1), dots.h.c, h_0) $
    - $C^perp$ is cyclic and generated by $overline(h)(x)$ (i.e. $h_0^(-1) overline(h)(x)$ is generator-polynomial for $C^perp$).
]
#proof[
    - Show that $H$ is generator matrix for $C^perp$:
        - Show rows of $H$ are linearly independent.
        - Show rows of $H$ are in $C^perp$:
            - Let $c(x) in C$, use @check-polynomial-for-containment to show $c(x) h(x) = b(x) x^n - b(x)$ for some $b(x) in FF_q [x]$, $deg(b) <= k - 1$.
    - Show that $overline(h)(x) | x^n - 1$ (hint: write $x^n = x^k x^(n - k)$).
    - Show that if $overline(h)(x)$ monic, then $ideal(overline(h)(x))$ and $C^perp$ have a common generator-matrix.
    - If $overline(h)(x)$ not monic, show that multiplying by $h_0$ is row operation, and so $ideal(overline(h)(x))$ and $C^perp$ have a common generator matrix.
]

= MDS and perfect codes

== Reed-Solomon codes

#notation[
    Let $bold(P)_k = FF_q [z]_(<k)$ be vector space of polynomials of degree $< k$ in $FF_q$: $ FF_q [z]_(<k) = {a_0 + dots.h.c + a_(k - 1) z^(k - 1): a_i in FF_q} $ Dimension of $FF_q [z]_(< k)$ is $k$.
]
#definition[
    Let $0 <= k <= n <= q$, $vd(a) = (a_1, ..., a_n)$, $vd(b) = (b_1, ..., b_n) in FF_q^n$ with all $a_j$ distinct and all $b_j$ non-zero. Define the linear map $ phi_(vd(a), vd(b)): bold(P)_k -> FF_q^n, quad phi_(vd(a), vd(b)) (f(z)) := (b_1 f(a_1), ..., b_n f(a_n)) in FF_q^n $ The *$q$-ary Reed-Solomon code* $"RS"_k (vd(a), vd(b))$ is the image of $phi_(vd(a), vd(b))$: $ "RS"_k (vd(a), vd(b)) = phi_(vd(a), vd(b))(bold(P)_k) subset.eq FF_q^n $
]
#proposition[
    - $"RS"_k (vd(a), vd(b))$ is a $q$-ary $[n, k, n - k + 1]$ code. In particular, it is an MDS code.
    - A generator-matrix for $"RS"_k (vd(a), vd(b))$ is $ G = \(b_j a_j^(i - 1)\)_(i, j) = mat(phi_(vd(a), vd(b))(1); dots.v; phi_(vd(a), vd(b))(z^(k - 1))) in M_(k, n)(FF_q) $ where $1 <= i <= k$, $1 <= j <= n$.
]
#proof[
    - To show dimension is $k$, show that $phi_(vd(a), vd(b))$ is injective, by showing it has trivial kernel.
    - To show minimum distance is $n - k + 1$, show for $f(z) != 0$ that $w(phi_(vd(a), vd(b))(z)) >= n - (k - 1)$.
    - Use linearity and injectivity of $phi_(vd(a), vd(b))$ and fact that ${1, ..., z^(k - 1)}$ is basis for $bold(P)_k$ to show $G$ is generator-matrix for $"RS"_k (vd(a), vd(b))$.
]
#remark[
    We have $ {0} = "RS"_0 (vd(a), vd(b)) subset "RS"_1 (vd(a), vd(b)) subset dots.c subset "RS"_n (vd(a), vd(b)) = FF_q^n $ (since a row is added to the generator matrix each time).
]
#example[
    Let $q = 7$, $n = 5$, $k = 3$, $vd(a) = (0, 1, 6, 2, 3)$, $vd(b) = (5, 4, 3, 2, 1)$. Then $ phi_(vd(a), vd(b)): bold(P)_3 & -> FF_7^5, \ f(z) & |-> (5 f(0), 4 f(1), 3 f(6), 2 f(2), 1 f(3)) $ So a generator matrix for $"RS"_3 (vd(a), vd(b))$ is $ G = mat(5, 4, 3, 2, 1; 0, 4, 4, 4, 3; 0, 4, 3, 1, 2) $
]
#definition[
    $alpha in FF_q$ is *primitive $n$-th root of unity* if $alpha^n = 1$ and $forall 0 < j < n$, $ alpha^j != 1$.
]
#proposition[
    Let $alpha in FF_q$ primitive $n$-th root of unity, $m in ZZ$, define $ vd(a)^((m)) = ((alpha^0)^m, ..., (alpha^(n - 1))^m) in FF_q^n $ Then for $0 <= k <= n$, $"RS"_k (vd(alpha)^((1)), vd(alpha)^((m)))$ is cyclic.
]
#proof[
    - Show cyclic permutation of $vd(alpha)^((m))$ is equivalent to multiplying by $alpha^(-m) in FF_q$.
    - Show rows of generator matrix of $"RS"_k (vd(alpha)^((1)), vd(alpha)^((m)))$ has rows $vd(alpha)^((m + i - 1))$ for $1 <= i <= k$.
    - Use linearity of a permutation to conclude result.
]
#example[
    In $FF_5$, $2^1 = 2$, $2^2 = 4$, $2^3 = 3$, $2^4 = 1$ so $2$ is primitive $4$th root of unity in $FF_5$ so $vd(alpha)^m = (1^m, 2^m, 4^m, 3^m)$. We have $vd(alpha)^((1)) = (1, 2, 4, 3)$, $vd(alpha)^((2)) = (1, 4, 1, 4)$, so a generator matrix for $"RS"_2 (vd(alpha)^((1)), vd(alpha)^((2)))$ is $ G = mat(1, 4, 1, 4; 1, 3, 4, 2) $ By performing ERO's, we obtain another generator matrix $ G' = mat(3, 1, 1, 0; 0, 3, 1, 1) $ This is generator matrix for the cyclic code with generator polynomial $g(x) = (x - 1)(x - 3) = x^2 + x + 3$. So $"RS"_2 (vd(alpha)^((1)), vd(alpha)^((2)))$ is cyclic with generator polynomial $g(x)$. Note $x^4 - 1 = (x - 1)(x - 2)(x - 3)(x - 4)$ so $g(x) | x^4 - 1$.
]
#proposition[
    For $vd(a), vd(b)in FF_q^n$ with $a_j$ all distinct and $b_j$ all non-zero,
    - There exists $vd(c)$ with all $c_j != 0$ such that for $1 <= k <= n - 1$, $ ("RS"_k (vd(a), vd(b)))^perp = "RS"_(n - k)(vd(a), vd(c)) $
    - $vd(c)$ is given by the $1 times n$ check-matrix for $"RS"_(n - 1)(vd(a), vd(b))$.
]
#proof[
    - First consider $k = n - 1$. Let $vd(c)$ be the $1 times n$ check-matrix for $"RS"_(n - 1)(vd(a), vd(b))$.
        - Use that $"RS"_(n - 1)(vd(a), vd(b))$ saturates singleton bound to show all $c_j != 0$, and so that $"RS"_1 (vd(a), vd(c))$ and $("RS"_(n - 1)(vd(a), vd(b)))^perp$ share a generator matrix (so are the same code).
        - $forall f(z) in bold(P)_(n - 1)$, since $phi_(vd(a), vd(b)) (f(z)) in "RS"_(n - 1)(vd(a), vd(b))$, and $vd(c)$ is check-matrix for $"RS"_(n - 1)(vd(a), vd(b))$, $ phi_(vd(a), vd(b)) (f(z)) dot vd(c) = 0 $
    - Since $dim("RS"_(n - k)(vd(a), vd(c))) = n - k = dim\(("RS"_k (vd(a), vd(b)))^perp\)$, enough to show $"RS"_(n - k)(vd(a), vd(c)) subset.eq ("RS"_k (vd(a), vd(b)))^perp$:
        - By considering degrees, show that for $g(z) in bold(P)_k$ and $g(z) in bold(P)_(n - k)$, $(f g)(z) in bold(P)_(n - 1)$. Deduce that $phi_(vd(a), vd(c))(g(z)) dot phi_(vd(a), vd(b))(f(z)) = 0$.
]

== Hamming codes

#definition[
    Let $r >= 2$, $n = 2^r - 1$, let $H in M_(r, n)(FF_2)$ have columns corresponding to all non-zero vectors in $FF_2^r$. The *binary Hamming code of redundancy $r$* is $ "Ham"_2 (r) = {vd(x) in FF_2^n: vd(x) H^t = vd(0)} $ Note the order of columns is not specified, so we have a collection of permutation-equivalent codes.
]
#example[
    For $r = 2, 3$, we can take $ H_2 = mat(0, 1, 1; 1, 0, 1), quad H_3 = mat(0, 0, 0, 1, 1, 1, 1; 0, 1, 1, 0, 0, 1, 1; 1, 0, 1, 0, 1, 0, 1) $
]
#proposition[
    For $r >= 2$, $"Ham"_2 (r)$ is perfect $[2^r - 1, 2^r - r - 1, 3]$ code with check-matrix $H$.
]
#proof[
    - $n = 2^r - 1$: count rows in $H^t$.
    - To show $H$ is check-matrix, verify its rows are linearly independent by considering its column rank.
    - $k = 2^r - r - 1$: $k = n - "number of rows of" H$.
    - $d = 3$: use criterion of minimum distance from linearly (in)dependent columns. No column is multiple of another, but columns $vd(e_1), vd(e_2)$ and $vd(e_1) + vd(e_2)$ are linearly dependent.
    - $"Ham"_2 (r)$ is perfect: we have $|"Ham"_2 (r)| = 2^k = 2^(2^r - r - 1)$, $t = floor((d - 1)/2) = 1$. $|S(c, 1)| = 1 + n = 2^r$ and the $S(c, 1)$ are disjoint, so $|union_(c in C) S(c, 1)| = 2^(2^r - r - 1) dot 2^r = 2^n$.
]
#definition[
    Can define Hamming codes for $q > 2$. Consider $FF_q^r$ for $r >= 2$. $vd(v), vd(w) in FF_q^r - {0}$ are *equivalent* if $vd(v) = lambda dot vd(w)$ for some $lambda in FF_q^times$. For $vd(v) in FF_q^r - {0}$, set $ L_(vd(v)) = {vd(w) in FF_q^r: vd(w) "equivalent to" vd(v)} = {lambda vd(v): lambda in FF_q^times} $ Note $|L_(vd(v))| = q - 1$ and $w in L_(vd(v))$ iff $L_(vd(w)) = L_(vd(v))$. Also, if $L_(vd(v)) != L_(vd(w))$ then $L_(vd(v)) sect L_(vd(w)) = emptyset$. Hence the $L_(vd(v))$ partition $FF_q^r - {0}$ and there are $(q^r - 1)\/(q - 1)$ of them.
]
#example[
    For $q = 3$, $r = 2$ there are $(3^2 - 1)\/(3 - 1) = 4$ sets: $ L_((0, 1)) & = {(0, 1), (0, 2)}, quad L_((1, 0)) & = {(1, 0), (2, 0)}, \ L_((1, 1)) & = {(1, 1), (2, 2)}, quad L_((1, 2)) & = {(1, 2), (2, 1)} $
]
#definition[
    For $r >= 2$, $n = (q^r - 1)\/(q - 1)$, construct $H in M_(r, n)(FF_q)$ by taking one column from each of the $n$ different $L_v$. The *Hamming code of redundancy $r$* is $ "Ham"_q (r) = {vd(x) in FF_q^n: vd(x) H^t = vd(0)} $ Note that different choices of $H$ give monomially equivalent codes.
]
#example[
    For $"Ham"_3 (2)$, we can choose e.g. $ H = mat(0, 2, 2, 2; 1, 2, 0, 1) quad "or" quad H = mat(2, 1, 2, 0; 1, 1, 0, 1) $
]
#proposition[
    For $r >= 2$, $"Ham"_q (r)$ is perfect $[n, n - r, 3]$ code, with check-matrix $H$.
]