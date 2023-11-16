# Introduction

-   Basic encryption process:

    -   A has a message (**plaintext**) which is **encrypted** using an
        **encryption key** to produce the **ciphertext**, which is sent
        to $B$.

    -   B uses a **decryption key** (which depends on the encryption
        key) to **decrypt** the ciphertext and recover the original
        plaintext.

    -   It should be computationally infeasible to determine the
        plaintext without knowing the decryption key.

-   **Caesar cipher**:

    -   Add a constant to each letter in the plaintext to produce the
        ciphertext:
        $$\text{ ciphertext letter } = \text{ plaintext letter } + k\quad\operatorname{mod}26$$

    -   To decrypt,
        $$\text{ plaintext letter } = \text{ ciphertext letter } - k\quad\operatorname{mod}26$$

    -   The key is $k\:\operatorname{mod}26$.

-   Cryptosystem objectives:

    -   **Secrecy**: the intercepted message should be not able to be
        decrypted

    -   **Integrity**: a message should not allowed to be altered
        without the receiver knowing

    -   **Authenticity**: the receiver should be certain of the identity
        of the sender

    -   **Non-repudiation**: the sender should not be able to claim they
        sent a message; the receiver should be able to prove they did.

-   **Kerckhoff's principle**: a cryptographic system should be secure
    even if the details of the system are known to an attacker.

-   Types of attack:

    -   **Ciphertext-only**: the plaintext is deduced from the
        ciphertext.

    -   **Known-plaintext**: intercepted ciphertext and associated
        stolen plaintext are used to determine the key.

    -   **Chosen-plaintext**: an attacker tricks a sender into
        encrypting various chosen plaintexts and observes the
        ciphertext, then uses this information to determine the key.

    -   **Chosen-ciphertext**: an attacker tricks the receiver into
        decrypting various chosen ciphertexts and observes the resulting
        plaintext, then uses this information to determine the key.

# Symmetric key ciphers

-   **Converting letters to numbers**: treat letters as integers modulo
    $26$, with $A = 1$,
    $Z = 0 \equiv 26\:\left( \operatorname{mod}26 \right)$. Treat a
    string of text as a vector of integers modulo $26$.

-   **Symmetric key cipher**: one in which encryption and decryption
    keys are equal.

-   **Key size**:
    $\log_{2}\left( \text{number of possible keys} \right)$.

-   **Substitution cipher**: key is permutation of
    $\left\{ a,\ldots,z \right\}$. Key size is $\log_{2}(26!)$. It is
    vulnerable to plaintext attacks and ciphertext-only attacks, since
    different letters (and letter pairs) occur with different
    frequencies in English.

-   **Stirling's formula**:
    $$n! \approx \sqrt{2\pi n}\left( \frac{n}{e} \right)^{n}$$

-   **One-time pad**: key is uniformly, independently random sequence of
    integers $\operatorname{mod}26$,
    $\left( k_{1},k_{2},\ldots \right)$, it is known to the sender and
    receiver. If message is $\left( m_{1},m_{2},\ldots,m_{r} \right)$
    then ciphertext is
    $\left( c_{1},c_{2},\ldots,c_{r} \right) = \left( k_{1} + m_{1},k_{2} + m_{2},\ldots,k_{r} + m_{r} \right)$.
    To decrypt the ciphertext, $m_{i} = c_{i} - k_{i}$. Once
    $\left( k_{1},\ldots,k_{r} \right)$ have been used, they must never
    be used again.

    -   One-time pad is information-theoretically secure against
        ciphertext-only attack:
        ${\mathbb{P}}(M = m~|~C = c) = {\mathbb{P}}(M = m)$.

    -   Disadvantage is keys must never be reused, so must be as long as
        message.

    -   Keys must be truly random.

-   **Chinese remainder theorem**: let $m,n \in {\mathbb{N}}$ coprime,
    $a,b \in {\mathbb{Z}}$. Then exists unique solution
    $x{\:\operatorname{mod}mn}$ to the congruences $$\begin{aligned}
    x \equiv a & {\quad\operatorname{mod}m} \\
    x \equiv b & {\quad\operatorname{mod}n}
    \end{aligned}$$

-   **Block cipher**: group characters in plaintext into blocks of $n$
    (the **block length**) and encrypt each block with a key. So
    plaintext $p = \left( p_{1},p_{2},\ldots \right)$ is divided into
    blocks $P_{1},P_{2},\ldots$ where
    $P_{1} = \left( p_{1},\ldots,p_{n} \right)$,
    $P_{2} = \left( p_{n + 1},\ldots,p_{2n} \right)$. Then ciphertext
    blocks are given by $C_{i} = f\left( \text{key},P_{i} \right)$ for
    some encryption function $f$.

-   **Hill cipher**:

    -   Plaintext divided into blocks $P_{1},\ldots,P_{r}$ of length
        $n$.

    -   Each block represented as vector
        $P_{i} \in ({\mathbb{Z}}/26{\mathbb{Z}})^{n}$

    -   Key is invertible $n \times n$ matrix $M$ with elements in
        ${\mathbb{Z}}/26{\mathbb{Z}}$.

    -   Ciphertext for block $P_{i}$ is $$C_{i} = MP_{i}$$ It can be
        decrypted with $P_{i} = M^{- 1}C$.

    -   Let $P = \left( P_{1},\ldots,P_{r} \right)$,
        $C = \left( C_{1},\ldots,C_{r} \right)$, then $C = MP$.

-   **Confusion**: each character of ciphertext depends on many
    characters of key.

-   **Diffusion**: each character of ciphertext depends on many
    characters of plaintext. Ideal diffusion changes a proportion of
    $(S - 1)/S$ of the characters of the ciphertext, where $S$ is the
    number of possible symbols.

-   For Hill cipher, $i$th character of ciphertext depends on $i$th row
    of key - this is medium confusion. If $j$th character of plaintext
    changes and $M_{ij} \neq 0$ then $i$th character of ciphertext
    changes. $M_{ij}$ is non-zero with probability roughly $25/26$ so
    good diffusion.

-   Hill cipher is susceptible to known plaintext attack:

    -   If $P = \left( P_{1},\ldots,P_{n} \right)$ are $n$ blocks of
        plaintext with length $n$ such that $P$ is invertible and we
        know $P$ and the corresponding $C$, then we can recover $M$,
        since $C = MP \Longrightarrow M = CP^{- 1}$.

    -   If enough blocks of ciphertext are intercepted, it is very
        likely that $n$ of them will produce an invertible matrix $P$.

# Public key cryptography and the RSA algorithm

-   **Euler $\varphi$ function**:
    $$\varphi:{\mathbb{N}} \rightarrow {\mathbb{N}},\varphi(n) = \left| \left\{ 1 \leq a \leq n:\gcd(a,n) = 1 \right\} \right| = \left| ({\mathbb{Z}}/n{\mathbb{Z}})^{\times} \right|$$

-   $\varphi(p^{r}) = p^{r} - p^{r - 1}$,
    $\varphi(mn) = \varphi(m)\varphi(n)$ for $\gcd(m,n) = 1$.

-   **Euler's theorem**: if $\gcd(a,n) = 1$,
    $a^{\varphi(n)} \equiv 1\quad\left( \operatorname{mod}n \right)$.

-   **Public key cryptography**:

    -   Create two keys, $k_{D}$ and $k_{E}$. $k_{E}$ is public, $k_{D}$
        is private.

    -   Plaintext $m$ is encrypted as $c = f\left( m,k_{E} \right)$.

    -   Ciphertext decrypted by $m = g\left( c,k_{D} \right)$.

-   **RSA**:

    -   $k_{E}$ is pair $(n,e)$ where $n = pq$ is product of two
        distinct primes and $e \in {\mathbb{Z}}$ is coprime to
        $\varphi(n)$.

    -   $k_{D}$ is integer $d$ such that
        $de \equiv 1\quad\left( \operatorname{mod}\varphi(n) \right)$.

    -   $m$ is an integer modulo $n$, $m$ and $n$ are coprime.

    -   Encryption: $c = m^{e}\quad\left( \operatorname{mod}n \right)$.

    -   Decryption: $m = c^{d}\quad\left( \operatorname{mod}n \right)$.

-   **RSA problem**: given $n = pq$ a product of two unknown primes, $e$
    and $m^{e}\quad\left( \operatorname{mod}n \right)$, recover $m$. If
    $n$ can be factored, the RSA is solved.

-   It is recommended that $n$ have at least $2048$ bits. A typical
    choice of $e$ is $2^{16} + 1$.

-   **Attacks on RSA**:

    -   If you can factor $n$, you can compute $d$, so can break RSA (as
        then you know $\varphi(n)$ so can compute
        $e^{- 1}\quad\left( \operatorname{mod}\varphi(n) \right)$).

    -   If $\varphi(n)$ is known, then we have $pq = n$ and
        $(p - 1)(q - 1) = \varphi(n)$ so $p + q = n - \varphi(n) + 1$.
        Hence $p$ and $q$ are roots of
        $x^{2} - \left( n - \varphi(n) + 1 \right) + n = 0$.

    -   **Known $d$**: we have $de - 1$ is multiple of $\varphi(n)$.
        Look for a factor $A$ of $de - 1$ such that $(p - 1)~|~A$,
        $(q - 1) \nmid A$. Then try $x^{A} - 1$ for random $x$, this
        satisfies $x^{A} - 1$ is divisible by $p$, hence
        $\gcd(x^{A} - 1,n) = p$.

-   **RSA signatures**:

    -   Public key is $(n,e)$ and private key is $d$.

    -   When sending a message $m$, message is **signed** by also
        sending $s = m^{d}\operatorname{mod}n$.

    -   $(m,s)$ is received, **verified** by checking if
        $m = s^{e}\operatorname{mod}n$.

    -   Forging a signature on a message $m$ would require finding $s$
        with $m = s^{e}\operatorname{mod}n$. This is the RSA problem.

    -   However, choosing signature $s$ first then taking
        $m = s^{e}\operatorname{mod}n$.

    -   To solve this, $(m,s)$ is sent where $s = h(m)\hat{}d$, $h$ is
        **hash function**. Then the message receiver verifies
        $h(m) = s^{e}\operatorname{mod}n$.

    -   Now, for a signature to be forged, an attacker would have to
        find $m$ with $h(m) = s^{e}\operatorname{mod}n$.

-   **Hash function** is function
    $h:\left\{ \text{messages} \right\} \rightarrow \mathcal{H}$ that:

    -   Can be computed efficiently

    -   Is preimage-resistant: can't quickly find $m$ with given $h(m)$.

    -   Is collision-resistant: can't quickly find $m,m\prime$ with
        $h(m) = h(m\prime)$.

    Example is SHA-256.

-   **Theorem**: it is no easier to find $\varphi(n)$ than to factorise
    $n$.

-   **Theorem**: it is no easier to find $d$ than to factor $n$.

-   **Miller-Rabin algorithm**:

    1.  Choose random $x\operatorname{mod}n$.

    2.  Let $n - 1 = 2^{r}s$, $y = x^{s}$.

    3.  Compute $y,y^{2},\ldots,y^{2^{r}}\operatorname{mod}n$.

    4.  If $1$ isn't in this list, $n$ is **composite** (with witness
        $x$).

    5.  If $1$ is in list preceded bynumber other than $\pm 1$, $n$ is
        **composite** (with witness $a$).

    6.  Other, $n$ is **possible prime** (to base $x$).

## Factorisation

-   **Trial division algorithm**: for $p = 2,3,5,\ldots$ test whether
    $p~|~n$.

-   **Fermat's method**:

    -   Let $a = \left\lceil \sqrt{n} \right\rceil$. Compute
        $a^{2}\operatorname{mod}n$, $(a + 1)^{2}\operatorname{mod}n$
        until a square $x^{2} \equiv (a + i)^{2}\operatorname{mod}n$
        appears. Then compute $\gcd(a + i - x,n)$.

    -   Works well under special conditions on the factors: if
        $|p - q| \leq 2\sqrt{2}\sqrt[4]{n}$ then Fermat's method takes
        one step: $x = \left\lceil \sqrt{n} \right\rceil$ works.

-   An integer is $B$-smooth if all its prime factors are $\leq B$.

-   **Quadratic sieve**:

    -   Choose $B$ and let $m$ be numberof primes $\leq B$.

    -   Look at integers $x = \left\lceil \sqrt{n} \right\rceil + k$,
        $k = 1,2,\ldots$ and check whether $y = x^{2} - n$ is
        $B$-smooth.

    -   Once $y_{1} = x_{1}^{2} - n,\ldots,y_{t} = x_{t}^{2} - n$ are
        all $B$-smooth with $t > m$, find some product of them that is a
        square.

    -   Deduce a congruence between the squares.

-   **Other factorisation algorithms**:

    -   Pollard's $\rho$ algorithm.

    -   Pollard's $p - 1$ algorithm.

    -   Lenstra's algorithm using elliptic curves.

    -   General number field sieve

    -   Shor's algorithm: ${\ln(N)}^{2}\ln(\ln(N))$.

## Primitive roots

-   Let $p$ prime, $g \in {\mathbb{F}}_{p}^{\times}$. **Order** of $g$
    is smallest $a \in {\mathbb{N}}_{0}$ such that $g^{a} = 1$. $g$ is
    **primitive root** if its order is $p - 1$.

-   Let $p$ prime, $g \in {\mathbb{F}}_{p}^{\times}$ primitive root. If
    $x \in {\mathbb{F}}_{p}^{\times}$ then $x = g^{L}$ for some
    $0 \leq L < p - 1$. Then $L$ is **discrete logarithm** of $x$ to
    base $g$. Write $L = L_{g}(x)$. It satisfies:

    -   $g^{L_{g}(x)} \equiv x\quad\left( \operatorname{mod}p \right)$
        and
        $g^{a} \equiv x\quad\left( \operatorname{mod}p \right) \Longleftrightarrow a \equiv L_{g}(x)\quad\left( \operatorname{mod}p - 1 \right)$.

    -   $L_{g}(1) = 0$, $L_{g}(g) = 1$.

    -   $L_{g}(xy) \equiv L_{g}(x) + L_{g}(y)\quad\left( \operatorname{mod}p - 1 \right)$.

    -   $h$ is primitive root mod $p$ iff $L_{g}(h)$ coprime to $p - 1$.
        So number of primitive roots mod $p$ is $\varphi(p - 1)$.

-   **Discrete logarithm problem**: given $p,g,x$, compute $L_{g}(x)$.

-   **Diffie-Hellman key exchange**:

    -   Two parties agree on prime $p$ and primitive root
        $g\operatorname{mod}p$.

    -   Alice chooses secret $\alpha\operatorname{mod}(p - 1)$ and sends
        $g^{\alpha}\operatorname{mod}p$ to Bob.

    -   Bob chooses secret $\beta\operatorname{mod}(p - 1)$ and sends
        $g^{\beta}\operatorname{mod}p$ to Alice.

    -   Alice and Bob both compute
        $\kappa = g^{\alpha\beta} = \left( g^{\alpha} \right)^{\beta}) = \left( g^{\beta} \right)^{\alpha}\operatorname{mod}p$.

-   **Diffie-Hellman problem**: given $p,g,g^{\alpha},g^{\beta}$,
    compute $g^{\alpha\beta}$.

-   If discrete logarithm problem cna be solved, so can Diffie-Hellman
    problem (since could compute $\alpha = L_{g}\left( g^{a} \right)$ or
    $\beta = L_{g}\left( g^{\beta} \right)$).

-   **Elgamal** public key encryption:

    -   Alice chooses prime $p$, primitive root $g$, private key
        $\alpha\:\:\operatorname{mod}(p - 1)$.

    -   Her public key is $y = g^{\alpha}$.

    -   Bob chooses random $k\operatorname{mod}(p - 1)$

    -   To send message $m$ (integer mod $p$), he sends the pair
        $(r,m\prime) = \left( g^{k},my^{k} \right)$.

    -   To descript the message, Alice computes
        $r^{\alpha} = g^{\alpha k} = y^{k}$ and then
        $m = m\prime y^{- k} = m\prime r^{- \alpha}$.

    -   If Diffie-Hellman problem is hard, then Elgamal encryption is
        secure against known plaintext attack.

    -   Key $k$ must be random and different each time.

-   **Decision Diffie-Hellman problem**: given $g^{a},g^{b},c$ in
    ${\mathbb{F}}_{p}^{\times}$, decide whether $c = g^{ab}$.

    -   This problem is not always hard, as can tell if $g^{ab}$ is
        square or not. Can fix this by taking $g$ to have large prime
        order $q~|~(p - 1)$. $p = 2q + 1$ is a good choice.

-   **Elgamal signatures**:

    -   Public key is $(p,g)$, $y = g^{\alpha}$ for private key
        $\alpha$.

    -   **Valid Elgamal signature** on $m$ is pair $(r,s)$, $r \geq 0$,
        $s < p - 1$ such that
        $$y^{r}r^{s} = g^{m}\quad\left( \operatorname{mod}p \right)$$

    -   Alice computes $r = g^{k}$,
        $k \in \left( {\mathbb{Z}}/(p - 1) \right)^{\times}$ random.

    -   Then $g^{\alpha r}g^{ks} \equiv g^{m}\quad\operatorname{mod}p$
        so
        $\alpha r + ks \equiv m\quad\left( \operatorname{mod}p - 1 \right)$
        so $s = k^{- 1}(m - \alpha r)\quad\operatorname{mod}p - 1$.

-   **Elgamal signature problem**: given $p,g,y,m$, find $r,s$ such that
    $y^{r}r^{s} = m$.

-   **Discrete logarithm problem**: given prime $p$, primitive root
    $g\:\operatorname{mod}p$, $x \in {\mathbb{F}}_{p}^{\times}$,
    calculate $L_{g}(x)$.

-   **Baby-step giant-step algorithm** for solving DLP:

    -   Let $N = \left\lceil \sqrt{p - 1} \right\rceil$.

    -   Baby-steps: compute $g^{j}\:\operatorname{mod}p$ for
        $0 \leq j < N$.

    -   Giant-steps: compute $xg^{- Nk}\:\operatorname{mod}p$ for
        $0 \leq k < N$.

    -   Look for a match between baby-steps and giant-steps lists:
        $g^{j} = xg^{- Nk} \Longrightarrow x = g^{j + Nk}$.

    -   Always works since if $x = g^{L}$ for
        $0 \leq L < p - 1 \leq N^{2}$, so $L$ can be written as $j + Nk$
        with $j,k \in \left\{ 0,\ldots,N - 1 \right\}$.
