#import "../../template.typ": template
#show: template

= Symmetric key ciphers

- *Symmetric key cipher*: one in which encryption and decryption keys are equal.
- *Key size*: $log_2 ("number of possible keys")$.
- *Caesar cipher*: shift all characters by a constant amount. Key size is $log_2 (26)$
- *Substitution cipher*: key is permutation of ${a, ..., z}$. Key size is $log_2 (26!)$.
- *Stirling's formula*: $ n! approx sqrt(2 pi n) (n / e)^n $
- If any statistical properties of plaintext are reflected in cipher text, then we can use this as basis for an attack. We compare the most common letters in the English language with the most common letters in the message. We can also compare letter pairs.
- *One-time pad*: key is random sequence of integers $mod 26$, $(k_1, k_2, ...)$. If message is $(m_1, m_2, ..., m_r)$ then ciphertext is $(c_1, c_2, ...) = (k_1 + m_1, k_2 + m_2, ...)$. To decrypt the ciphertext, $m_i = c_i - k_i$. Once $(k_1, ..., k_r)$ have been used, they must never be used again.
    - One-time pad is information-theoretically secure against ciphertext-only attack: $PP(M = m | C = c) = PP(M = m)$.
    - Keys must never be reused, so must be as long as message.
    - Keys must be truly random.
- *Hill cipher*:
    - Plaintext divided into blocks $P_1, ..., P_r$ of length $n$.
    - Each block represented as vector $P_i in (ZZ \/ 26 ZZ)^n$
    - Key is invertible $n times n$ matrix $M$ with elements in $ZZ \/ 26 ZZ$.
    - Ciphertext for block $P_i$ is $ C_i = M P_i $ It can be decrypted with $P_i = M^(-1) C$.
    - Let $P = (P_1, ..., P_r)$, $C = (C_1, ..., C_r)$, then $C = M P$.
- *Confusion*: each character of ciphertext depends on many characters of key.
- *Diffusion*: each character of ciphertext depends on many characters of plaintext.
- For Hill cipher, $i$th character of ciphertext depends on $i$th row of key - this is medium confusion.
- Hill cipher is susceptible to known plaintext attack:
    - If $P = (P_1, ..., P_n)$ are $n$ blocks of plaintext with length $n$ such that $P$ is invertible and we know $P$ and the corresponding $C$, then we can recover $M$, since $C = M P ==> M = C P^(-1)$.

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