#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let Bern = math.op("Bern")
#let sim = sym.tilde

= Entropy

== Introduction

#notation[
    Write $x_1^n := (x_1, ..., x_n) in {0, 1}^n$ for an length $n$ bit string.
]
#notation[
    We use $P$ to denote a probability mass function. Write $P_1^n$ for the joint proability mass function of a sequence of $n$ random variables $X_1^n = (X_1, ..., X_n)$.
]
#definition[
    A random variable $X$ has a *Bernoulli distribution*, $X sim Bern(p)$, if for some fixed $p in (0, 1)$, $
        X = cases(
            1 & "with probability" p,
            0 & "with probability" 1 - p
        ),
    $ i.e. the probability mass function (PMF) of $X$ is $P: {0, 1} -> RR$, $P(0) = 1 - p$, $P(1) = p$.
]
#notation[
    Throughout, we take $log$ to be the base-$2$ logarithm, $log_2$.
]
#definition[
    The *binary entropy function* $h: (0, 1) -> [0, 1]$ is defined as $
        h(p) := -p log p - (1 - p) log(1 - p)
    $
]<def:binary-entropy-function>
#example[
    Let $x_1^n in {0, 1}^n$ be an $n$ bit string which is the realisation of binary random variables (RVs) $X_1^n = (X_1, ..., X_n)$, where the $X_i$ are independent and identically distributed (IID), with common distribution $X_i sim Bern(p)$. Let $k = abs({i in [n]: x_i = 1})$ be the number of ones in $x_1^n$. We have $
        Pr(X_1^n = x_1^n) := P^n (x_1^n) = product_(i = 1)^n P(x_i) = p^k (1 - p)^(n - k).
    $ Now by the law of large numbers, the probability of ones in a random $x_1^n$ is $k\/n approx p$ with high probability for large $n$. Hence, $
        P^n (x_1^n) approx p^(n p) (1 - p)^(n (1 - p)) = 2^(-n h(p)).
    $ Note that this reveals an amazing fact: this approximation is independent of $x_1^n$, so any message we are likely to encounter has roughly the same probability $approx 2^(-n h(p))$ of occurring.
]
#remark[
    By the above example, we can split the set of all possible $n$-bit messages, ${0, 1}^n$, into two parts: the set $B_n$ of *typical* messages which are approximately uniformly distributed with probability $approx 2^(-n h(p))$ each, and the non-typical messages that occur with negligible probability. Since all but a very small amount of the probability is concentrated in $B_n$, we have $abs(B_n) approx 2^(n h(p))$.
]
#remark[
    Suppose an encoder and decoder both already know $B_n$ and agree on an ordering of its elements: $B_n = {x_1^n (1), ..., x_1^n (b)}$, where $b = abs(B_n)$. Then instead of transmitting the actual message, the encoder can transmit its index $j in [b]$, which can be described with $
        ceil(log b) = ceil(log abs(B_n)) approx n h(p)
    $ bits.
]
#remark[
    - The closer $p$ is to $1/2$ (intuitively, the more random the messages are), the larger the entropy $h(p)$, and the larger the number of typical strings $abs(B_n)$.
    - Assuing we ignore non-typical strings, which have vanishingly small probability for large $n$, the "compression rate" of the above method is $h(p)$, since we encode $n$ bit strings using $n h(p)$ strings. $h(p) < 1$ unless the message is uniformly distributed over all of ${0, 1}^n$.
    - So the closer $p$ is to $0$ or $1$ (intuitively, the less random the messages are), the smaller the entropy $h(p)$, so the greater the compression rate we can achieve.
]

== Asymptotic equipartition property

#notation[
    We denote a finite alphabet by $A = {a_1, ..., a_m}$.
]
#notation[
    If $X_1, ..., X_n$ are IID RVs with values in $A$, with common distribution described by a PMF $P: A -> [0, 1]$ (i.e. $P(x) = Pr(X_i = x)$ for all $x in A$), then write $X sim P$, and we say "$X$ has distribution $P$ on $A$".
]
#notation[
    For $i <= j$, write $X_i^j$ for the block of random variables $(X_i, ..., X_j)$, and similarly write $x_i^j$ for the length $j - i + 1$ string $(x_i, ..., x_j) in A^(i - j + 1)$.
]
#notation[
    For IID RVs $X_1, ..., X_n$ with each $X_i sim P$, denote their joint PMF by $P^n: A^n -> [0, 1]$: $
        P^n (x_1^n) = Pr(X_1^n = x_1^n) = product_(i = 1)^n Pr(X_i = x_i) = product_(i = 1)^n P(x_i),
    $ and we say that "the RVs $X_1^n$ have the product distribution $P^n$".
]
#definition[
    A sequence of RVs $(Y_n)_(n in NN)$ *converges in probability* to an RV $Y$ if $forall epsilon > 0$, $
        Pr(abs(Y_n - Y) > epsilon) -> 0 quad "as" n -> oo.
    $
]<def:convergence-in-probability>
#definition[
    Let $X sim P$ be a discrete RV on a countable alphabet $A$. The *entropy* of $X$ is $
        H(X) = H(P) := -sum_(x in A) P(x) log P(x) = EE[-log P(X)].
    $
]<def:entropy>
#remark[
    - We use the convention $0 log 0 = 0$ (this is natural due to continuity: $x log x -> 0$ as $x arrow.b 0$, and also can be derived measure-theoretically).
    - Entropy is technically a functional the probability distribution $P$ and not of $X$, but we use the notation $H(X)$ as well as $H(P)$.
    - $H(X)$ only depends on the probabilities $P(x)$, not on the values $x in A$. Hence for any bijective $f: A -> A$, we have $H(f(X)) = H(X)$.
    - All summands of $H(X)$ are non-negative, so the sum always exists and is in $[0, oo]$, even if $A$ is countable infinite.
    - $H(X) = 0$ iff all summands are $0$, i.e. if $P(x) in {0, 1}$ for all $x in A$, i.e. $X$ is *deterministic* (constant, so equal to a fixed $x_0 in A$ with probability $1$).
]
#theorem[
    Let $X = {X_n: n in NN}$ be IID RVs with common distribution $P$ on a finite alphabet $A$. Then $
        -1/n log P^n (X_1^n) --> H(X_1) quad "in probability" quad "as" n -> oo
    $
]<thm:convergence-to-common-entropy-in-probability>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        P^n (X_1^n) & = product_(i = 1)^n P(X_i) \
        ==> 1/n log P^n (X_1^n) & = 1/n sum_(i = 1)^n log P(X_i) -> EE[-log P(X_1)] quad "in probability"
    $ by the weak law of large numbers (WLLN) for the IID RVs $Y_i = -log P(X_i)$.
]
#corollary(name: "Asymptotic Equipartition Property (AEP)")[
    Let ${X_n: n in NN}$ be IID RVs on a finite alphabet $A$ with common distribution $P$ and common entropy $H = H(X_i)$. Then
    - $(==>)$: for all $epsilon > 0$, the set of *typical strings* $B_n^* (epsilon) subset.eq A^n$ defined by $
        B_n^* (epsilon) := {x_1^n in A^n: 2^(-n(H + epsilon)) <= P^n (x_1^n) <= 2^(-n(H - epsilon))}
    $ satisfies $
        abs(B_n^* (epsilon)) <= 2^(n(H + epsilon)) quad & forall n in NN, quad "and" \
        P^n (B_n^* (epsilon)) = Pr(X_1^n in B_n^* (epsilon)) --> 1 quad & "as" n -> oo
    $
    - $(<==)$: for any sequence $(B_n)_(n in NN)$ of subsets of $A^n$, if $P(X_1^n in B_n) -> 1$ as $n -> oo$, then $forall epsilon > 0$, $
        abs(B_n) & >= (1 - epsilon) 2^(n(H - epsilon)) quad "eventually" \
        "i.e." exists N in NN: forall n >= N, quad abs(B_n) & >= (1 - epsilon) 2^(n(H - epsilon)).
    $
]<cor:aep>
#proofhints[
    - $(==>)$: straightforward.
    - $(<==)$: show that $P^n (B_n sect B_n^* (epsilon)) -> 1$ as $n -> oo$.
]
#proof[
    - $(==>)$:
        - Let $epsilon > 0$. By @thm:convergence-to-common-entropy-in-probability, we have $
            Pr(X_1^n in.not B_n^* (epsilon)) = Pr(abs(-1/n log P^n (X_1^n) - H) > epsilon) -> 0 quad "as" n -> oo.
        $
        - By definition of $B_n^* (epsilon)$, $
            1 >= P^n (B_n^* (epsilon)) = sum_(x_1^n in B_n^* (epsilon)) P^n (x_1^n) >= abs(B_n^* (epsilon)) 2^(-n(H + epsilon)).
        $
    - $(<==)$:
        - We have $P^n (B_n sect B_n^* (epsilon)) = P^n (B_n) + P^n (B_n^* (epsilon)) - P^n (B_n union B_n^* (epsilon)) >= P^n (B_n) + P^n (B_n^* (epsilon)) - 1$, so $P^n (B_n sect B_n^* (epsilon)) -> 1$.
        - So $P^n (B_n sect B_n^* (epsilon)) >= 1 - epsilon$ eventually, and so $
            1 - epsilon & <= P^n (B_n sect B_n^* (epsilon)) = sum_(x_1^n in B_n sect B_n^* (epsilon)) P^n (x_1^n) \
            & <= abs(B_n sect B_n^* (epsilon)) 2^(-n(H - epsilon)) <= abs(B_n) 2^(-n(H - epsilon)).
        $
]
#remark[
    - The $==>$ part of AEP states that a specific object (in this case, the $B_n^* (epsilon)$) can achieve a certain performance, while the $<==$ part states that no other object of this type can significantly perform better. This is common type of result in information theory.
    - @thm:convergence-to-common-entropy-in-probability gives a mathematical interpretation of entropy: the probability of a random string $X_1^n$ generally decays exponentially with $n$ ($P^n (X_1^n) approx 2^(-n H)$ with high probability for large $n$). The AEP gives a more "operational interpretation": the smallest set of strings that can carry almost all the probability of $P^n$ has size $approx 2^(n H)$.
    - The AEP tells us that higher entropy means more typical strings, and so the possible values of $X_1^n$ are more unpredictable. So we consider "high entropy" RVs to be "more random" and "less predictable".
]

== Fixed-rate lossless data compression

#definition[
    A *memoryless source* $X = {X_n: n in NN}$ is a sequence of IID RVs with a common PMF $P$ on the same alphabet $A$.
]<def:source.memoryless>
#definition[
    A *fixed-rate lossless compression code* for a source $X$ consists of a sequence of *codebooks* ${B_n: n in NN}$, where each $B_n subset.eq A^n$ is a set of source strings of length $n$.

    Assume the encoder and decoder share the codebooks, each of which is sorted. To send $x_1^n$, an encoder checks with $x_1^n in B_n$; if so, they send the index of $x_1^n$ in $B_n$, along with a flag bit $1$, which requires $1 + ceil(log abs(B_n))$ bits. Otherwise, they send $x_1^n$ uncompressed, along with a flag bit $0$ to indicate an "error", which requires $1 + ceil(log abs(A)) = 1 + ceil(n log abs(A))$ bits.
]<def:fixed-rate-code>
#definition[
    For each $n in NN$, the *rate* of a fixed-rate code ${B_n: n in NN}$ for a source $X$ is $
        R_n := 1/n (1 + ceil(log abs(B_n))) approx 1/n log abs(B_n) quad "bits/symbol".
    $
]<def:code-rate>
#definition[
    For each $n in NN$, the *error probability* of a fixed-rate code ${B_n: n in NN}$ for a source $X$ is $
        P_e^((n)) := Pr(X_1^n in.not B_n).
    $
]<def:code-error-probability>
#theorem(name: "Fixed-rate coding theorem")[
    Let $X = {X_n: n in NN}$ be a memoryless source with distribution $P$ and entropy $H = H(X_i)$.
    - $(==>)$: $forall epsilon > 0$, there is a fixed-rate code ${B_n^* (epsilon): n in NN}$ with vanishing error probability ($P_e^((n)) -> 0$ as $n -> oo$) and with rate $
        R_n <= H + epsilon + 2/n quad forall n in NN.
    $
    - $(<==)$: let ${B_n: n in NN}$ be a fixed-rate with vanishing error probabilit. Then $forall epsilon > 0$, its rate $R_n$ satisfies $
        R_n > H - epsilon quad "eventually".
    $
]
#proofhints[
    $(==>)$: straightforward.
    $(<==)$: straightforward.
]
#proof[
    - $(==>)$:
        - Let $B_n^* (epsilon)$ be the sets of typical strings defined in AEP (@cor:aep). Then $P_e^((n)) = 1 - Pr(X_1^n in B_n^*) -> 0$ as $n -> oo$ by AEP.
        - Also by AEP, $R_n = 1/n (1 + ceil(log abs(B_n^*))) <= 1/n log abs(B_n^*) + 2/n <= H + epsilon + 2/n$.
    - $(<==)$:
        - WLOG let $0 < epsilon < 1\/2$. By AEP, $
            R_n >= 1/n log abs(B_n^*) + 1/n >= 1/n log(1 - epsilon) + H - epsilon + 1/n = H - epsilon + 1/n log(2(1 - epsilon)) > H - epsilon
        $ eventually.
]