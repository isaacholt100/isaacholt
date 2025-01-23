#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.1" as cetz: canvas

// Everything in the official lecture notes is examinable, except the proofs of Theorems 7.6, 8.1, 12.3, 12.4 and 12.6.

#let name-abbrvs = (
    "Data Processing Inequality for Entropy": "Data Processing",
    "Data Processing Inequalities for Mutual Information": "Data Processing",
    "Chain Rule for Mutual Information": "Chain Rule",
    "Ruzsa Triangle Inequality for Entropy": "Ruzsa Triangle Inequality"
)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)
#set document(
    title: "Information Theory Notes",
    author: "Isaac Holt",
    keywords: ("information theory", "entropy", "information")
)

#let sim = sym.tilde
#let Bern = math.op("Bern")
#let Pois = math.op("Pois")
#let Bin = math.op("Bin")

= Probability basics

TODO: weak and strong laws of large numbers, Markov chains, Cesaro lemma, Markov's inequality, ... probably others.

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
        PP(X_1^n = x_1^n) := P^n (x_1^n) = product_(i = 1)^n P(x_i) = p^k (1 - p)^(n - k).
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
    If $X_1, ..., X_n$ are IID RVs with values in $A$, with common distribution described by a PMF $P: A -> [0, 1]$ (i.e. $P(x) = PP(X_i = x)$ for all $x in A$), then write $X sim P$, and we say "$X$ has distribution $P$ on $A$".
]
#notation[
    For $i <= j$, write $X_i^j$ for the block of random variables $(X_i, ..., X_j)$, and similarly write $x_i^j$ for the length $j - i + 1$ string $(x_i, ..., x_j) in A^(i - j + 1)$.
]
#notation[
    For IID RVs $X_1, ..., X_n$ with each $X_i sim P$, denote their joint PMF by $P^n: A^n -> [0, 1]$: $
        P^n (x_1^n) = PP(X_1^n = x_1^n) = product_(i = 1)^n PP(X_i = x_i) = product_(i = 1)^n P(x_i),
    $ and we say that "the RVs $X_1^n$ have the product distribution $P^n$".
]
#definition[
    A sequence of RVs $(Y_n)_(n in NN)$ *converges in probability* to an RV $Y$ if $forall epsilon > 0$, $
        PP(abs(Y_n - Y) > epsilon) -> 0 quad "as" n -> oo.
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
]<rmk:properties-of-entropy>
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
#corollary("Asymptotic Equipartition Property (AEP)")[
    Let ${X_n: n in NN}$ be IID RVs on a finite alphabet $A$ with common distribution $P$ and common entropy $H = H(X_i)$. Then
    - $(==>)$: for all $epsilon > 0$, the set of *typical strings* $B_n^* (epsilon) subset.eq A^n$ defined by $
        B_n^* (epsilon) := {x_1^n in A^n: 2^(-n(H + epsilon)) <= P^n (x_1^n) <= 2^(-n(H - epsilon))}
    $ satisfies $
        abs(B_n^* (epsilon)) <= 2^(n(H + epsilon)) quad & forall n in NN, quad "and" \
        P^n (B_n^* (epsilon)) = PP(X_1^n in B_n^* (epsilon)) --> 1 quad & "as" n -> oo
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
            PP(X_1^n in.not B_n^* (epsilon)) = PP(abs(-1/n log P^n (X_1^n) - H) > epsilon) -> 0 quad "as" n -> oo.
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
        P_e^((n)) := PP(X_1^n in.not B_n).
    $
]<def:code-error-probability>
#theorem("Fixed-rate Coding Theorem")[
    Let $X = {X_n: n in NN}$ be a memoryless source with distribution $P$ and entropy $H = H(X_i)$.
    - $(==>)$: $forall epsilon > 0$, there is a fixed-rate code ${B_n^* (epsilon): n in NN}$ with vanishing error probability ($P_e^((n)) -> 0$ as $n -> oo$) and with rate $
        R_n <= H + epsilon + 2/n quad forall n in NN.
    $
    - $(<==)$: let ${B_n: n in NN}$ be a fixed-rate with vanishing error probability. Then $forall epsilon > 0$, its rate $R_n$ satisfies $
        R_n > H - epsilon quad "eventually".
    $
]<thm:fixed-rate-coding-theorem>
#proofhints[
    $(==>)$: straightforward.
    $(<==)$: straightforward.
]
#proof[
    - $(==>)$:
        - Let $B_n^* (epsilon)$ be the sets of typical strings defined in AEP (@cor:aep). Then $P_e^((n)) = 1 - PP(X_1^n in B_n^*) -> 0$ as $n -> oo$ by AEP.
        - Also by AEP, $R_n = 1/n (1 + ceil(log abs(B_n^*))) <= 1/n log abs(B_n^*) + 2/n <= H + epsilon + 2/n$.
    - $(<==)$:
        - WLOG let $0 < epsilon < 1\/2$. By AEP, $
            R_n >= 1/n log abs(B_n^*) + 1/n >= 1/n log(1 - epsilon) + H - epsilon + 1/n = H - epsilon + 1/n log(2(1 - epsilon)) > H - epsilon
        $ eventually.
]


= Relative entropy

#definition[
    Suppose $x_1^n in A^n$ are observations generated by IID RVs $X_1^n$ and we want to decide whether $X_1^n sim P^n$ or $Q^n$, for two distinct candidate PMFs $P, Q$ on $A$. A *hypothesis test* is described by a *decision region* $B_n subset.eq A^n$ such that
    - If $x_1^n in B_n$, then we declare that $X_1^n sim P^n$.
    - Otherwise, if $x_1^n in.not B_n$, then we declare that $X_1^n sim Q^n$.

]<def:hypothesis-test>
#definition[
    The associated *error probabilities* for a hypothesis test are $
        e_1^((n)) = e_1^((n)) (B_n) & := PP("declare" P | "data" sim Q) = Q^n (B_n) \
        e_2^((n)) = e_2^((n)) (B_n) & := PP("declare" Q | "data" sim P) = P^n (B_n^c).
    $
]<def:hypothesis-test-error-probability>
#definition[
    The *relative entropy* between PMFs $P$ and $Q$ on the same countable alphabet $A$ is $
        D(P || Q) := sum_(x in A) P(x) log (P(x))/(Q(x)) = EE[log P(X)/Q(X)], quad "where" X sim P.
    $
]<def:relative-entropy>
#remark[
    - We use the convention that $0 log 0/0 = 0$ (this can be avoided by defining relative entropy measure-theoretically).
    - $D(P || Q)$ always exists and $D(P || Q) >= 0$ with equality iff $P = Q$.
    - Relative entropy is not symmetric: $D(P || Q) != D(Q || P)$ in general, and does not satisfy the triangle inequality.
    - Despite this, it is reasonable and natural to think of $D(P || Q)$ as a statistical "distance" between $P$ and $Q$.
]
#remark[
    Let $X sim P$. We have, by WLLN, $
        1/n log ((P^n (X_1^n))/(Q^n (X_1^n))) & = 1/n log product_(i = 1)^n (P(X_i))/(Q(X_i)) \
        & = 1/n sum_(i = 1)^n log (P(X_i))/(Q(X_i)) \
        & --> D(P || Q) "in probability" quad "as" n -> oo.
    $ So for large $n$, $(P^n (X_1^n))/(Q^n (X_1^n)) approx 2^(n D(P || Q))$ with high probability. Hence, the random string $X_1^n$ is exponentially more likely under its true distribution $P$ than under $Q$.
]

== Asymptotically optimal hypothesis testing

#theorem("Stein's Lemma")[
    Let $P, Q$ be PMFs on a finite alphabet $A$, with $D = D(P || Q) in (0, oo)$. Let $X = {X_n: n in NN}$ be a memoryless source on $A$, with either each $X_i sim P$ or each $X_i sim Q$.
    - $(==>)$: for all $epsilon > 0$, there is a hypothesis test with decision regions ${B_n^* (epsilon): n in NN}$ such that $
        forall n in NN, quad e_1^((n)) (B_n^* (epsilon)) <= 2^(-n(D - epsilon))
    $ and $e_2^((n)) -> 0$ as $n -> oo$.
    - $(<==)$: for any hypothesis test with decision regions ${B_n: n in NN}$ such that $e_2^((n)) (B_n) -> 0$ as $n -> oo$, we have $forall epsilon > 0$, $
        e_1^((n)) (B_n) >= 2^(-n(D + epsilon + 1/n)) quad "eventually".
    $
]<thm:steins-lemma>
#proofhints[
    - $(==>)$:
        - Let $B_n^* (epsilon) = {x_1^n in A^n: 2^(n(D - epsilon)) <= (P^n (x_1^n))/(Q^n (x_1^n)) <= 2^(n(D + epsilon))}$. The rest is straightforward (use above remark).
    - $(<==)$:
        - Show that $P^n (B_n^* (epsilon) sect B_n) -> 1$ as $n -> oo$, use that $1/2 = 2^(-n (1\/n))$.
]
#proof[
    - $(==>)$:
        - Let $B_n^* (epsilon) = {x_1^n in A^n: 2^(n(D - epsilon)) <= (P^n (x_1^n))/(Q^n (x_1^n)) <= 2^(n(D + epsilon))}$.
        - Then the convergence in probability of $1/n sum_(i = 1)^n log P(X_i)/Q(X_i)$ is equivalent to $PP(X_1^n in.not B_n^*) = P^n (B_n^* (epsilon)) = e_2^((n)) -> 0$ as $n -> oo$, when $X_1^n sim P^n$.
        - Also, $1 >= P^n (B_n^*) = sum_(x_1^n in B_n^* (epsilon)) Q^n (x_1^n) (P^n (x_1^n))/(Q^n (x_1^n)) >= 2^(n(D - epsilon)) sum_(x_1^n in B_n^* (epsilon)) Q^n (x_1^n) = 2^(n(D - epsilon)) Q^n (B_n^* (epsilon))$.
    - $(<==)$:
        - We havee $e_2^((n)) (B_n^* (epsilon)) = P^n (B_n^* (epsilon)) -> 0$ as $n -> oo$. Suppose $e_2^((n)) (B_n) = P^n (B_n^c) -> 0$. Then $P^n (B_n sect B_n^* (epsilon)) -> 1$. So eventually, $
            1/2 <= P^n (B_n sect B_n^* (epsilon)) & = sum_(x_1^n in B_n sect B_n^* (epsilon)) P^n (x_1^n) (Q^n (x_1^n))/(Q^n (x_1^n)) \
            & <= 2^(n(D + epsilon)) sum_(x_1^n in B_n) Q^n (x_1^n) \
            & = 2^(n(D + epsilon)) Q^n (B_n) = 2^(n(D + epsilon)) e_1^((n)) (B_n)
        $
]
#remark[
    - The decision regions $B_n^*$ are asymptotically optimal in that, among all tests that have $e_2^((n)) -> 0$, they achieve the asymptotically smallest possible $e_1^((n)) approx 2^(-n D)$. However, they are not the most optimal decision regions for finite $n$. For finite regions, the optimal regions are given by the Neyman-Pearson Lemma.
    - Assuming $D != 0$ is a trivial assumption, as otherwise $P = Q$ on $A$, so any test would give the correct answer.
    - Assuming $D < oo$ is a reasonable assumption, as otherwise there is some $a in A$ such that $P(a) > 0$ but $Q(a) = 0$. In that case, we check whether any such $a$ appear in $x_1^n$ or not.
    - In Stein's Lemma, we assume one error vanishes at possibly an arbitrarily slow rate, while the other decays exponentially. This is a natural asymmetry in many applications, e.g. in diagnosing disease.
    - Stein's Lemma shows why the relative entropy is a natural measure of "distance" between two distributions, as large $D$ means a smaller error probability (one vanishes exponentially at rate $D$), so easier to tell apart the distributions from the data.
]

== Relative entropy and optimal hypothesis testing

#theorem("Neyman-Pearson Lemma")[
    For a hypothesis test between $P$ and $Q$ based on $n$ data samples, the *likelihood ratio decision regions* $
        B_"NP" = {x_1^n in A^n: (P^n (x_1^n))/(Q^n (x_1^n)) >= T}, quad "for some threshold" T > 0,
    $ are optimal in that, for any decision region $B_n subset.eq A^n$, if $e_1^((n)) (B_n) <= e_1^((n)) (B_"NP")$, then $e_2^((n)) (B_n) >= e_2^((n)) (B_"NP")$, and vice versa.
]
#proofhints[
    Consider the inequality $
        (P^n (x_1^n) - T Q^n (x_1^n)) (indicator(B_"NP") (x_1^n) - indicator(B_n) (x_1^n)) >= 0
    $ (justify why this holds).
]
#proof[
    - Consider the obvious inequality $
        (P^n (x_1^n) - T Q^n (x_1^n)) (indicator(B_"NP") (x_1^n) - indicator(B_n) (x_1^n)) >= 0
    $
    - Then, summing over all $x_1^n$, $
        0 & <= P^n (B_"NP") - P^n (B_n) - T Q^n (B_"NP") + T Q^n (B_n) \
        & = 1 - e_2^((n)) (B_"NP") - (1 - e_2^((n)) (B_n)) - T(e_1^((n)) (B_"NP") - e_1^((n)) (B_n)) \
        & ==> e_2^((n)) (B_n) - e_2^((n)) (B_"NP") >= T(e_1^((n)) (B_"NP") - e_1^((n)) (B_n))
    $
]
#remark[
    Neyman-Pearson says that if any decision region has an error as small as that of $B_"NP"$, then its other error must be larger than that of $B_"NP"$.
]
#notation[
    Let $hat(P)_n$ denote the empirical distribution (or *type*) induced by $x_1^n$ on $A^n$ (the frequency with which $a in A$ occurs in $x_1^n$): $
        forall a in A, quad hat(P)_n (a) := 1/n sum_(i = 1)^n indicator({x_i = a})
    $
]
#proposition[
    The Neyman-Pearson decision region $B_"NP"$ can be expressed in information-theoretic form as $
        B_"NP" = {x_1^n in A^n: D(hat(P)_n || Q) >= D(hat(P)_n || P) + T'}
    $ where $T' = 1/n log T$.
]
#proofhints[
    Rewrite the expression $1/n log (P^n (x_1^n))/(Q^n (x_1^n))$.
]
#proof[
    We have $
        1/n log (P^n (x_1^n))/(Q^n (x_1^n)) & = 1/n log(product_(i = 1)^n (P(x_i))/(Q(x_i))) \
        & = 1/n sum_(i = 1)^n log (P(x_i))/(Q(x_i)) \
        & = 1/n sum_(i = 1)^n sum_(a in A) indicator({x_i = a}) log (P(a))/(Q(a)) \
        & = sum_(a in A) (1/n sum_(i = 1)^n indicator({x_i = a})) log (P(a))/(Q(a)) \
        & = sum_(a in A) hat(P)_n (a) log((P(a))/Q(a) dot (hat(P)_n (a))/(hat(P)_n (a))) \
        & = D(hat(P)_n || Q) - D(hat(P)_n || P).
    $
]
#theorem("Jensen's Inequality")[
    Let $I$ be an interval, $f: I -> RR$ be convex and $X$ be an RV with values in $I$. Then $
        EE[f(X)] >= f(EE[X]).
    $ Moreover, if $f$ is strictly convex, then equality holds iff $X$ is almost surely constant.
]<thm:jensens-inequality>
#proof[
    Omitted.
]
#theorem("Log-sum Inequality")[
    Let $a_1, ..., a_n$, $b_1, ..., b_n$ be non-negative constants. Then $
        sum_(i = 1)^n a_i log a_i / b_i >= (sum_(i = 1)^n a_i) log (sum_(i = 1)^n a_i)/(sum_(i = 1)^n b_i)
    $ with equality iff $a_i / b_i = c$ for all $i$, for some constant $c$. We use the convention that $0 log 0 = 0 log 0/0 = 0$.
]
#remark[
    This also holds for countably many $a_i$ and $b_i$.
]
#proofhints[
    Use Jensen's inequality with $X$ the RV such that $PP(X = a_i/b_i) = b_i / (sum_(j = 1)^n b_j)$ for all $i in [n]$, and a suitable $f$.
]
#proof[
    - Define $
        f(x) = cases(
            x log x quad & "if" x > 0,
            0 & "otherwise"
        ).
    $ $f$ is strictly convex.
    - Let $A = sum_i a_i$, $B = sum_i b_i$. Let $X$ be the RV with $PP(X = a_i/b_i) = b_i / B$ for all $i in [n]$.
    - Then $EE[f(X)] = sum_i b_i / B a_i/b_i log a_i / b_i = 1/B sum_i a_i log a_i / b_i$.
    - $f(EE[X]) = EE[X] log EE[X] = sum_i a_i / b_i b_i / B log sum_i a_i / b_i b_i / B = A/B log A/B$.
    - So by Jensen's inequality, $A/B log A/B <= 1/B sum_i a_i log a_i / b_i$.
]
#proposition[
    + If $P$ and $Q$ are PMFs on the same finite alphabet $A$, then $
        D(P || Q) >= 0
    $ with equality iff $P = Q$.
    + If $X sim P$ on a finite alphabet $A$, then $
        0<= H(X) <= log abs(A)
    $ with equality to $0$ iff $X$ is a constant, and equality to $log abs(A)$ iff $X$ is uniformly distributed on $A$.
]
#remark[
    This also holds for countably infinite $A$.
]
#proofhints[
    + Straightforward.
    + For $<= log abs(A)$, consider $D(P || Q)$ where $Q$ is the uniform distribution on $A$. $>= 0$ is straightforward.
]
#proof[
    - 
        - By the log-sum inequality, $
            D(P || Q) = sum_(x in A) P(x) log P(x) / Q(x) >= (sum_(x in A) P(x)) log (sum_(x in A) P(x))/(sum_(x in A) Q(x)) = 0
        $ with equality if $P(x)/Q(x)$ is the same constant for all $x in A$, i.e. $P = Q$.
    - 
        - Let $Q$ be the uniform distribution on $A$, so $H(Q) = sum_(x in A) 1/abs(A) log 1/(1\/abs(A)) = log abs(A)$.
        - Now $0 <= D(P || Q) = sum_(x in A) P(x) log P(x) / (1\/abs(A)) = log abs(A) - H(X)$ with equality iff $P = Q$, i.e. $P$ is uniform.
        - Each term in $-H(X)$ is $<= 0$, with equality iff each $P(x) log P(x)$ is $0$, i.e. $P(x) = 0$ or $1$.
]
#remark[
    If $X = {X_n: n in NN}$ is a memoryless source with PMF $P$ on $A$, then we have shown that it can be at best compressed to $approx H(P)$ bits/symbol. This means that we can always achieve non-trivial compression, i.e. a description using $approx H(P) < log abs(A)$ bits/symbol, unless the source $X$ is completely random (i.e. IID and uniformly distribute), in which case we cannot do better than simply describing each $x_1^n$ uncompressed using $ceil(log abs(A^n))/n approx log abs(A)$ bits/symbol.
]


= Properties of entropy and relative entropy

== Joint entropy and conditional entropy

#definition[
    Let $X_1^n$ be an arbitrary finite collection of discrete RVs on corresponding alphabets $A_1, ..., A_n$. Note we can think of $X_1^n$ itself a discrete RV on alphabet $A_1 times dots.c times A_n$. Let $X_1^n$ have PMF $P_n$, then the *joint entropy* of $X_1^n$ is $
        H(X_1^n) = H(P_n) = H(X_1, ..., X_n) := EE[-log P_n (X_1^n)] = -sum_(x_1^n in A^n) P_n (x_1^n) log P_n (x_1^n).
    $
]<def:joint-entropy>
#example[
    Note that if $X$ and $Y$ are independent, then $P_(X, Y)(x, y) = P_X (x) P_Y (y)$, so $ H(X, Y) = EE[-log P_(X, Y)(X, Y)] = EE[-log P_X (X) - log P_Y (Y)] = H(X) + H(Y). $
]
#example[
    Let $X$ and $Y$ have joint PMF given by
    #figure(table(
        columns: (auto, auto, auto, auto, auto),
        $& X \ Y &$, $1$, $2$, $3$, $$,
        $0$, $1\/10$, $1\/5$, $1\/4$, $11\/20$,
        $1$, $1\/5$, $1\/20$, $1\/5$, $9\/20$,
        $$, $3\/10$, $1\/4$, $9\/20$, $$
    ))
    Note that $X$ and $Y$ are not independent. We have $
        H(X) & = -3/10 log 3/10 - 1/4 log 1/4 - 9/20 log 9/20 approx 1.539, \
        H(Y) & = -11/20 log 11/20 - 9/20 log 9/20 approx 0.993, \
        H(X, Y) & = - 1/10 log 1/10 - dots.c - 1/5 log 1/5 approx 2.441 < H(X) + H(Y).
    $
    In general, if $X$ and $Y$ are not independent, then $P_(X Y) (x, y) = P_X (x) P_(Y | X) (y | x)$, so $ H(X, Y) = EE[-log P_(X Y)(x, y)] = EE[-log P_X (x)] + EE[-log P_(Y | X) (y | x)]. $
]
#definition[
    Let $X$ and $Y$ be discrete random variables with joint PMF $P_(X, Y)$, then the *conditional entropy* of $Y$ given $X$ is $ H(Y | X) = EE[-log P_(Y | X)(Y | X)] = -sum_(x, y) P_(X, Y)(x, y) log P_(Y | X)(y | x) $
]<def:conditional-entropy>
#note[
    $P_(Y | X)$ is a function of $(x, y) in X$, and so for the expected value we multiply the $log$ by the probability that $X = x$ and $Y = y$.
]
#proposition[
    For discrete RVs $X$ and $Y$, we have $
        H(Y | X) = H(X, Y) - H(X).
    $
]<prop:joint-entropy-is-single-entropy-plus-conditional-entropy>
#proofhints[
    Straightforward.
]
#proof[
    Note that $P_(Y | X)(y | x) = PP(Y = y | X = x) = PP(Y = y, X = x)/PP(X = x) = P_(X, Y)(x, y) P_X (x)$. Hence $
        H(X, Y) & = EE[-log P_(X, Y) (X, Y)] \
        & = EE[-log P_X (X) - log P_(Y | X)(Y | X)] \
        & = EE[-log P_X (X)] + EE[-log P_(Y | X)(Y | X)].
    $
]

== Properties of entropy, joint entropy and conditional entropy

#proposition("Chain Rule for Entropy")[
    Let $X_1^n$ be a collection of discrete RVs. Then $
        H(X_1^n) = sum_(i = 1)^n H(X_i | X_1^(i - 1)).
    $ In particular, if the $X_1^n$ are independent, then $ H(X_1^n) = sum_(i = 1)^n H(X_i). $
]<prop:entropy-chain-rule>
#proofhints[
    By induction.
]
#proof[
    We can write $
        P_(X_1^n)(x_1^n) & = P_(X_1)(x_1) P_(X_2|X_1)(x_2 | x_1) dots.c P_(X_n | X_1, ..., x_(n - 1))(x_n | x_1, ..., x_(n - 1)) \
        & = product_(i = 1)^n P_(X_i | X_1^(i - 1)) (x_i | x_1^(i - 1)).
    $ Then the result follows by inductively using the above proposition.
]
#proposition("Conditioning Reduces Entropy")[
    For discrete RVs $X$ and $Y$, $ H(Y | X) <= H(Y) $ with equality iff $X$ and $Y$ are independent.
]<prop:conditioning-reduces-entropy>
#proofhints[
    Express $H(Y) - H(Y | X)$ as a relative entropy.
]
#proof[
    We have $
        H(Y) - H(Y | X) & = EE[-log P_Y (Y)] - EE[-log P_(Y | X)(Y | X)] \
        & = EE[log (P_(Y | X)(Y | X))/(P_Y (Y))] \
        & = EE[log (P_(Y | X)(Y | X) P_X (X))/(P_Y (Y) P_X (X))] \
        & = EE[log (P_(X, Y)(X, Y))/(P_X (X) P_Y (Y))] \
        & = D(P_(X, Y) || P_X P_Y).
    $ This is non-negative iff $P_(X, Y) = P_X P_Y$, i.e. $X$ and $Y$ are independent.
]
#definition[
    Discrete RVs $X$ and $Z$ are *conditionally independent given $Y$* if:
    - $P_(X, Z | Y) (x, z | y) = P_(X | Y)(x | y) P_(Z | Y) (z | y)$,
    - or equivalently, $P_(X | Z, Y)(x | z, y) = P_(X | Y)(x | y)$,
    - or equivalently, $P_(Z | X, Y)(z | x, y) = P_(Z | Y)(z | y)$.
    We denote this by writing $X - Y - Z$ and we say that $X, Y, Z$ form a Markov chain. Note that $X - Y - Z$ is equivalent to $Z - Y - X$, but not to $X - Z - Y$.
]<def:conditional-independence>
#note[
    For any function $g$ on $Y$, we have $X - Y - g(Y)$.
]<note:x-y-and-function-of-y-form-markov-chain>
#corollary[
    $H(X_1^n) <= sum_(i = 1)^n H(X_i)$ with equality iff all $X_1^n$ are independent.
]
#proof[
    Straightforward.
]
#proof[
    $H(X_1^n) = sum_(i = 1)^n H(X_i | X_1^(i - 1)) <= sum_(i = 1)^n H(X_i)$ by the chain rule and conditioning reducing entropy.
]
#remark[
    We can write $
        H(Y | X) & = -sum_(x, y) (P_(X, Y)(x, y)) log P_(Y | X)(y | x) \
        & = sum_x P_X (x) (-sum_y P_(Y | X)(y | x) log P_(Y | X)(y | x)) \
        & =: sum_x P_X (x) H(Y | X = x)
    $ Note $H(Y | X = x)$ is *not* a conditional entropy, and in particular, we do not always have $H(Y | X = x) <= H(Y)$. Since $0 <= H(Y | X = x) <= log abs(A_Y)$, we have $0 <= H(Y | X) <= log abs(A_Y)$ with equality to $0$ iff $Y$ is a function of $X$ (i.e. $H(Y | X = x) = 0$ for all $x$).
]<rmk:expression-for-conditional-entropy>
#proposition("Data Processing Inequality for Entropy")[
    Let $X$ be discrete RV on alphabet $A$ and $f$ be function on $A$. Then
    + $H(f(X)|X) = 0$.
    + $H(f(X)) <= H(X)$ with equality iff $f$ is injective.
]<prop:entropy-data-processing>
#proofhints[
    Use that $x |-> (x, f(x))$ is injective and the chain rule.
]
#proof[
    We have already shown the "if" direction of 2. We have $H(X) = H(X, f(X)) = H(f(X)|X) + H(X)$, since $x |-> (x, f(x))$ is injective. Also, $H(X) = H(X, f(X)) = H(X | f(X)) + H(f(X)) >= H(f(X))$. So $H(X) >= H(f(X))$ with equality iff $H(X | f(X)) = 0$, i.e. $X$ is a deterministic function of $f(X)$, i.e. $f$ is invertible.
]
#proposition("Properties of Conditional Entropy")[
    For discrete RVs $X, Y, Z$:
    - Chain rule: $H(X, Z | Y) = H(X | Y) + H(Z | X, Y)$.
    - Subadditivity: $H(X, Z | Y) <= H(X | Y) + H(Z | Y)$ with equality iff $X$ and $Z$ are conditionally independent given $Y$.
    - Conditioning reduces entropy: $H(X | Y, Z) <= H(X | Y)$ with equality iff $X$ and $Z$ are conditionally independent given $Y$.
]
#proof[
    Exercise.
]
#theorem("Fano's Inequality")[
    Let $X$ and $Y$ be RVs on respective alphabets $A$ and $B$. Suppose we are interested in the RV $X$ but only are allowed to observe the possibly correlated RV $Y$. Consider the estimate $hat(X) = f(Y)$, with probability of error $P_e := PP\(hat(X) != X\)$. Then $ H(X | Y) <= h(P_e) + P_e log (abs(A) - 1), $ where $h$ is the binary entropy function.
]
#proofhints[
    Consider an "error" Bernoulli RV $E$ which depends on $X$ and $Y$. Use the chain rule in two directions on $H(X, E | Y)$. Merge these and split up into the cases when $E = 0$ and $E = 1$ (using )
]
#proof[
    Let $E$ be the binary RV taking value $1$ when there is an error (i.e. $hat(X) != X$), and taking value $0$ otherwise. So $E sim Bern(P_e)$ and $H(E) = h(P_e)$. Then $
        H(X, E | Y) = H(X | Y) + H(E | X, Y) = H(X | Y)
    $ since $E$ is function of $(X, Y)$. Using the chain rule in the other direction, $
        H(X, E | Y) = H(E | Y) + H(X | E, Y) <= H(E) + E(X | E, Y).
    $ Now $
        H(X | Y) - h(P_e) & <= H(X | E, Y) \
        & = P_e H(X | E = 1, Y) + (1 - P_e)H(X | E = 0, Y)
    $ When $E = 0$, given $Y$, we can determine $X = f(Y)$ as a function of $Y$, so $H(X | E = 0, Y) = 0$. When $E = 1$, given $Y$, we know $X$ doesn't take value $f(Y)$, so there are $abs(A) - 1$ possible values that it takes, so $H(X | E = 1, Y) <= log(abs(A) - 1)$.
]

== Properties of relative entropy

#theorem("Data Processing Inequality for Relative Entropy")[
    Let $X sim P_X$ and $X' sim Q_X$ be RVs on the same alphabet $A$, and $f: A -> B$ be an arbitrary function. Let $P_(f(X))$ and $Q_(f(X))$ be the PMFs of $f(X)$ and $f(X')$ respectively. Then $
        D(P_(f(X)) || Q_(f(X))) <= D(P_X || Q_X).
    $
]<thm:relative-entropy-data-processing>
#proofhints[
    Use that $P_(f(X))(y) = sum_(x in f^(-1)({y})) P_X (x)$.
]
#proof[
    For each $y in B$, let $A_y = {x in A: f(x) = y} = f^(-1)({y})$. Then $
        D(P_(f(X)) || Q_(f(X))) & = sum_(y in B) P_(f(X))(y) log (P_(f(X))(y))/(Q_(f(X))(y)) \
        & = sum_(y in B) (sum_(x in A_y) P_X (x)) log (sum_(x in A_y) P_X (x))/(sum_(x in A_y) Q_X (x)) \
        & <= sum_(y in B) sum_(x in A_y) P_X (x) log (P_X (x))/(Q_X (x)) quad "by log-sum inequality" \
        & = sum_(x in A) P_X (x) log (P_X (x))/(Q_X (x)) = D(P_X || Q_X).
    $ 
]
#remark[
    The data processing inequality for relative entropy shows that we cannot make two distributions more "distinguishable" by first "processing" the data (by applying $f$).
]
#definition[
    The *total variation distance* between PMFs $P$ and $Q$ on the same alphabet $A$ is $
        norm(P - Q)_"TV" = sum_(x in A) abs(P(x) - Q(x)).
    $
]<def:total-variation-distance>
#remark[
    Let $B = {x in A: P(x) > Q(x)}$, then $
        norm(P - Q)_"TV" & = sum_(x in A) abs(P(x) - Q(x)) \
        & = sum_(x in B) (P(x) - Q(x)) + sum_(x in B^c) (Q(x) - P(x)) \
        & = P(B) - Q(B) + Q(B^c) - P(B^c) \
        & = P(B) - Q(B) + (1 - Q(B)) + (1 - P(B)) \
        & = 2(P(B) - Q(B)).
    $
]
#notation[
    Write $
        D_e (P || Q) = (ln 2) P(D || Q) = sum_(x in A) P(x) log_e P(x) / Q(x)
    $ and more generally, write $
        D_c (P || Q) = (log_c 2) P(D || Q) = sum_(x in A) P(x) log_c P(x) / Q(x).
    $
]
#theorem("Pinsker's Inequality")[
    Let $P$ and $Q$ be PMFs on the same alphabet $A$. Then $
        norm(P - Q)_"TV"^2 <= (2 ln 2) D(P || Q) = 2 D_e (P || Q).
    $
]<thm:pinskers-inequality>
#proofhints[
    - First prove for case that $P$ and $Q$ are PMFs of $Bern(p)$ and $Bern(q)$ (explain why we can assume $q <= p$ WLOG), by definining $Delta(p, q) = 2 D_e (P || Q) - norm(P - Q)_"TV"^2$, and showing that $(partial Delta(p, q))/(partial q) <= 0$.
    - Then show for general PMFs by using data processing, where $f = indicator(B)$ for $B = {x in A: P(x) > Q(x)}$.
]
#proof[
    First, assume that $P$ and $Q$ are the PMFs of the distributions $Bern(p)$ and $Bern(q)$ for some $0 <= q <= p <= 1$ ($q <= p$ WLOG since we can simultaneously interchange both $P$ with $1 - P$ and $Q$ with $1 - Q$ if necessary). Let $
        Delta(p, q) = (2 ln 2) D(P || Q) - norm(P - Q)_"TV"^2 = 2p ln p/q + 2(1 - p) ln (1 - p)/(1 - q) - (2(p - q))^2.
    $ Since $Delta(p, p) = 0$ for all $p$, it suffices to show that $(partial Delta(p, q))/(partial q) <= 0$. Indeed, $
        (partial Delta(p, q))/(partial q) = -2 p/q + 2 (1 - p)/(1 - q) + 8(p - q) = 2(q - p)(1/(q(1 - q)) - 4) <= 0
    $ since $q(1 - q) <= 1/4$ for all $q in [0, 1]$.

    Now, assume $P$ and $Q$ are general PMFs and let $B = {x in A: P(x) > Q(x)}$ and $f = indicator(B)$. Define the RVs $X sim P$ and $X' sim Q$, and let $P_f$ and $Q_f$ be the respective PMFs of the RVs $f(X)$ and $f(X')$. Note that $f(X) sim Bern(p)$, $f(X') sim Bern(q)$ where $p = P(B)$ and $q = Q(B)$. Then $
        2 D_e (P || Q) & >= 2 D_e (P_f || Q_f) quad & "by data-processing" \
        & >= norm(P_f - Q_f)_"TV"^2 quad & "by above" \
        & = (2(p - q))^2 \
        & = (2(P(B) - Q(B)))^2 \
        & = norm(P - Q)_"TV"^2.
    $
]
#theorem("Convexity of Relative Entropy")[
    The relative entropy $D(P || Q)$ is jointly convex in $P, Q$: for all PMFs $P, P', Q, Q'$ on the same alphabet and for all $0 < lambda < 1$, $
        D(lambda P + (1 - lambda) P' || lambda Q + (1 - lambda) Q') <= lambda D(P || Q) + (1 - lambda) D(P' || Q').
    $
]<thm:relative-entropy-is-convex>
#proof[
    Exercise.
]
#corollary("Concavity of Entropy")[
    The entropy of $H(P)$ is a concave function on all PMFs $P$ on a finite alphabet.
]<cor:entropy-is-concave>
#proofhints[
    Use convexity of relative entropy of $P$ and a suitable distribution.
]
#proof[
    Let $P$ be a PMF on finite alphabet $A$ and $U$ be the uniform PMF on $A$. Then by convexity of relative entropy, $D(P || U) = sum_(x in A) p(x) log P(x) / (1\/abs(A)) = log m - H(P)$ is convex in $P$, so $H(P)$ is concave in $P$.
]


= Poisson approximation

== Poisson approximation via entropy

#theorem[
    Let $X_1, ..., X_n$ be IID RVs with each $X_i sim Bern(lambda\/n)$, let $S_n = X_1 + dots.c + X_n$. Then $P_(S_n) -> Pois(lambda)$ in distribution as $n -> oo$, i.e. $forall k in NN$, $
        PP(S_n = k) -> e^(-lambda) lambda^k / k! quad "as" n -> oo
    $
]<thm:binomial-converges-to-poisson>
#remark[
    Using information theory, we can derive stronger and more general statements than the one above.
]
#theorem[
    Let $X_1, ..., X_n$ be (not necessarily independent) RVs with each $X_i sim Bern(p_i)$. Let $S_n = sum_(i = 1)^n X_i$ and $lambda = sum_(i = 1)^n p_i = EE[S_n]$. Then $
        D_e (P_(S_n) || Pois(lambda)) <= sum_(i = 1)^n p_i^2 + (sum_(i = 1)^n H_e (X_i) - H_e (X_1^n)).
    $
]<thm:relative-entropy-between-sum-of-bernoullis-and-poisson-is-bounded>
#proofhints[
    - Let $Z_i = Pois(p_i)$ for each $i in [n]$ be independent Poisson RVs so that $T_n = sum_(i = 1)^n Z_i sim Pois(lambda)$.
    - Use data processing inequality for relative entropy, and prove the fact that $D_e (Bern(p) || Pois(p)) <= p^2$ for all $p in [0, 1]$ (use that $1 - p <= e^(-p)$).
]
#proof[
    Let $Z_i = Pois(p_i)$ for each $i in [n]$ be independent Poisson RVs so that $T_n = sum_(i = 1)^n Z_i sim Pois(lambda)$. Then $
        D_e (P_(S_n) || Pois(lambda)) & = D_e (P_(S_n) || P_(T_n)) \
        & <= D_e (P_(X_1^n) || P_(Z_1^n)) quad "by data-processing with" f(x_1^n) = x_1 + dots.c + x_n \
        & = EE[ln (P_(X_1^n) (X_1^n))/(P_(Z_1^n)(X_1^n))] \
        & = EE[ln ((P_(X_1^n) (x_1^n))/(product_(i = 1)^n P_(Z_1^n)(X_i)) dot (product_(i = 1)^n P_(X_i)(X_i))/(product_(i = 1)^n P_(X_i)(X_i)))] \
        & = EE[ln (product_(i = 1)^n (P_(X_i)(x_i))/(P_(Z_i)(x_i)))] + sum_(x_1^n in A^n) P_(X_1^n) (x_1^n) ln 1/(product_(i = 1)^n P_(X_i)(x_i)) - H_e (X_1^n) \
        & = sum_(i = 1)^n D_e (P_(X_i) || P_(Z_i)) + sum_(i = 1)^n H_e (X_i) - H_e (X_1^n)
    $ since for given $x_1 in A$, $sum_(x_2^n in A^n) P_(X_1^n)(x_1^n) = P_(X_1)(x_1)$ (and similarly for each $x_j$, $j = 2, ..., n$). Now note that $D_e (P_(X_i) || P_(Z_i)) = D_e (Bern(p_i) || Pois(p_i))$, and for all $p in (0, 1)$, $
        D_e (Bern(p) || Pois(p)) & = (1 - p) ln (1 - p)/e^(-p) + p ln p/(p e^(-p)) \
        & = (1 - p) ln(1 - p) + (1 - p)p + p^2 \
        & <= (1 - p) ln(e^(-p)) + p \
        & = p^2
    $ since $1 - p <= e^(-p)$ for all $p in [0, 1]$. Similarly, if $p = 0$ or $1$, then $D_e (Bern(p) || Pois(p)) = 0 <= p^2$.
]
#corollary[
    Let $X_1, ..., X_n$ be independent, with each $X_i sim Bern(p_i)$. Then $
        D_e (P_(S_n) || Pois(lambda)) <= sum_(i = 1)^n p_i^2
    $
]
#corollary[
    @thm:binomial-converges-to-poisson follows directly from @thm:relative-entropy-between-sum-of-bernoullis-and-poisson-is-bounded.
]
#proof[
    Let $P_lambda$ be the PMF of the $Pois(lambda)$ distribution. Then by Pinsker's inequality, $
        norm(P_(S_n) - P_lambda)_"TV"^2 <= 2 D_e (P_(S_n) || Pois(lambda)) <= 2 sum_(i = 1)^n lambda^2 / n^2 = 2 lambda^2 / n.
    $ So for each $k in NN$, $abs(P_(S_n)(k) - P_lambda (k)) <= norm(P_(S_n) - P_lambda)_"TV" <= sqrt(2/n) lambda -> 0$ as $n -> oo$.
]
#remark[
    @thm:relative-entropy-between-sum-of-bernoullis-and-poisson-is-bounded is stronger than @thm:binomial-converges-to-poisson in that it holds for all $n$ rather than being asymptotic. It also provides an easily computable bound on the difference between $P_(S_n)$ and $Pois(lambda)$, and does not assume the $p_i$ are equal, or that the RVs $X_1, ..., X_n$ are independent.
]
#remark[
    It is known that for independent $X_1, ..., X_n$, $P_(S_n) -> Pois(lambda)$ iff $sum_(i = 1)^n p_i^2 -> 0$. So the bound in @thm:relative-entropy-between-sum-of-bernoullis-and-poisson-is-bounded is the best possible.
]

== What is the Poisson distribution?

#lemma("Binomial Maximum Entropy")[
    Let $B_n (lambda)$ be set of distributions on $NN_0$ that arise from sums $sum_(i = 1)^n X_i$ where $X_i sim Bern(p_i)$ are independent and $sum_(i = 1)^n p_i = lambda$. For all $n >= lambda$, $
        H_e ("Bin"(n, lambda\/n)) = sup{H_e (P): P in B_n (lambda)}
    $
]<lem:binomial-maximum-entropy>
#proof[
    Exercise.
]
#theorem("Poisson Maximum Entropy")[
    We have $
        & H_e (Pois(lambda)) \
        = & sup{H_e (S_n): S_n = sum_(i = 1)^n X_i, X_i sim Bern(p_i) "independent" and sum_(i = 1)^n p_i = lambda, n >= 1} \
        = & sup_(n in NN) sup{H_e(P): P in B_n (lambda)}.
    $
]<thm:poisson-maximum-entropy>
#proof[
    Let $H^* = sup_(n in NN) sup\{H_e (P): P in B_n (lambda)\}$. Note that $B_n (lambda) subset.eq B_(n + 1)(lambda)$, hence $H^* = lim_(n -> oo) sup{H_e(P): P in B_n (lambda)} = lim_(n -> oo) H_e (Bin(n, lambda\/n))$.
    
    Let $P_n$ and $Q$ be respective PMFs of $Bin(n, lambda\/n)$ and $Pois(lambda)$. Using that $k! <= k^k <= e^(k^2)$, we have $
        H_e (Q) & = sum_(k = 0)^oo Q(k) ln (k!)/(e^(-lambda) lambda^k) \
        & <= sum_(k = 0)^oo Q(k) (lambda - k ln lambda + k^2) \
        & = lambda^2 + 2 lambda - lambda ln lambda < oo 
    $ since $EE[X] = lambda$ and $EE[X^2] = lambda + lambda^2$ for $X sim Pois(lambda)$. So $H_e (Q)$ is finite. The convergence is left as an exercise.
]


= Mutual information

#definition[
    The *mutual information* between discrete RVs $X$ and $Y$ is $
        I(X; Y) = H(X) - H(X|Y).
    $ The *conditional mutual information* between $X$ and $Y$ given a discrete RV $Z$ is $
        I(X; Y | Z) & = H(X | Z) - H(X | Y, Z) \
        & = H(X | Z) + H(Y | Z) - H(X, Y | Z) \
        & = H(Y | Z) - H(Y | X, Z).
    $
]<def:mutual-information>
#proposition[
    Let $X$ and $Y$ be discrete RVs with marginal PMFs $P_X$ and $P_Y$ respectively, and joint PMF $P_(X, Y)$, then the mutual information can be expressed as: $
        I(X; Y) & = H(X) + H(Y) - H(X, Y) \
        & = H(Y) - H(Y | X) \
        & = D(P_(X, Y) || P_X P_Y).
    $
]<prop:expressions-for-mutual-information>
#proofhints[
    Straightforward.
]
#proof[
    The first two lines are by the chain rule. For the third, we have $
        H(X) + H(Y) - H(X, Y) & = EE[-log P_X (X)] + EE[-log P_Y (Y)] - EE[-log P_(X, Y)(X, Y)] \
        & = EE[log((P_(X, Y)(X, Y))/(P_X (X) P_Y (Y)))] \
        & = D(P_(X, Y) || P_X P_Y).
    $
]
#remark[
    - $I(X; Y)$ is symmetric in $X$ and $Y$.
    - The sum of the information contain in $X$ and $Y$ separately minus the information contained in the pair indeed is the amount of mutual information shared by both.
    - Considering @thm:steins-lemma, we can consider $I(X; Y)$ as a measure of how well data generated from $P_(X, Y)$ can be distinguished from independent pairs $(X', Y')$ generated by the product distribution $P_X P_Y$, so is a measure of how far $X$ and $Y$ are from being independent.
]
#proposition[
    - $0 <= I(X; Y) <= H(X)$ with equality to $0$ iff $X$ and $Y$ are independent.
    - Similarly, $I(X; Z | Y) >= 0$ with equality iff $X - Y - Z$, i.e. $X$ and $Z$ are conditionally independent given $Y$.
]
#proof[
    First is by @prop:expressions-for-mutual-information and non-negativity of conditional entropy, second is an exercise.
]
#proposition("Chain Rule for Mutual Information")[
    For all discrete RVs $X_1, ..., X_n, Y$, $
        I(X_1^n; Y) = sum_(i = 1)^n I(X_i; Y | X_1^(i - 1)).
    $
]<prop:mutual-information-chain-rule>
#proofhints[
    Straighforward.
]
#proof[
    By the chain rule for entropy, $
        I(X_1^n; Y) & = H(X_1^n) - H(X_1^n | Y) \
        & = sum_(i = 1)^n H(X_i | X_1^(i - 1)) - sum_(i = 1)^n H(X_i | X_1^(i - 1), Y) \
        & = sum_(i = 1)^n (H(X_i | X_1^(i - 1)) - H(X_i | X_1^(i - 1), Y)) \
        & = sum_(i = 1)^n I(X_i; Y | X_1^(i - 1)).
    $
]
#theorem("Data Processing Inequalities for Mutual Information")[
    If $X - Y - Z$ (so $X$ and $Z$ are conditionally independent given $Y$), then $
        I(X; Z), I(X; Y | Z) <= I(X; Y).
    $
]<thm:mutual-information-data-processing>
#proofhints[
    Use chain rule for mutual information twice on the same expression.
]
#proof[
    By the chain rule, we have $
        I(X; Y, Z) & = I(X; Y) + I(X; Z | Y) \
        & = I(X; Z) + I(X; Y | Z).
    $ Now $I(X; Z | Y) = 0$ by conditional independence, so $I(X; Y) = I(X; Z) + I(X; Y | Z)$.
]
#example[
    We always have $X - Y - f(Y)$, hence $I(X; f(Y)) <= I(X; Y)$, so applying a function to $Y$ cannot make $X$ and $Y$ "less independent".
]

== Synergy and redundancy

#note[
    $I(X; Y_1, Y_2)$ can greater than, equal to, or less than $I(X; Y_1) + (X; Y_2)$.
]
#definition[
    The *synergy* of $Y_1, Y_2$ about $X$ is $
        S(X; Y_1, Y_2) & = I(X; Y_1, Y_2) - (I(X; Y_1) + I(X; Y_2)) \
        & = I(X; Y_2 | Y_1) - I(X, Y_2).
    $ So the synergy can be $< 0$, $> 0$ or $= 0$.
]<def:synergy>
#definition[
    If $S(X; Y_1, Y_2)$ is:
    - negative, then $Y_1$ and $Y_2$ contain *redundant* information about $X$;
    - zero, then $Y_1$ and $Y_2$ are *orthogonal*;
    - positive, then $Y_1$ and $Y_2$ are *synergistic*. Intuitively, knowing $Y_1$ already makes the information in $Y_2$ more valuable (in that it gives more information about $X$).
]<def:redundancy-orthogonality-synergisticy>
#theorem[
    Let RVs $Y_1, Y_2$ be conditionally independent given $X$, each with distribution $P_(Y | X)$, and RVs $Z_1, Z_2$ be distributed according to $Q_(Z | Y)(dot | Y_1)$, $Q_(Z | Y)(dot | Y_2)$ respectively. Let RV $Y$ have distribution $P_(Y | X)$, and $W_1, W_2$ be conditionally independent given $Y$, distributed according to $Q_(Z | Y)(dot | Y)$.

    If $S(X; W_1, W_2) > 0$, then $I(X; W_1, W_2) > I(X; Z_1, Z_2)$, for independent $Z_1$ and $Z_2$, i.e. correlated observations are better than independent ones.
]
#proofhints[
    Use data processing for mutual information.
]
#proof[
    As in @def:synergy, we have $I(X; W_2 | W_1) > I(X; W_2)$. $I(X; W_2) = I(X; Z_2)$ since $(X, W_2)$ has the same joint distribution as $(X, Z_2)$. By the data processing inequality, we have $I(X; Z_2 | Z_1) = I(Z_2; X | Z_1) <= I(Z_2; X) = I(X; Z_2)$, since $Z_1$ and $Z_2$ are conditionally independent given $X$. Hence $I(X; W_2 | W_1) > I(X; Z_2 | Z_1)$, so $I(X; W_2 | W_1) + I(X; W_1) > I(X; Z_2 | Z_1) + I(X; Z_1)$, and the result follows by the chain rule.
]
#example[
    Given two equally noisy channels of a signal $X$, we want to decide whether it is better (gives more information about $X$) for the channels to be independent (this corresponds with choosing the $Y_1, Y_2, Z_1, Z_2$) or correlated (this corresponds with choosing the $Y, W_1, W_2$).

    The natural assumption that the conditionally independent observations $Z_1, Z_2$ would be "better" than $W_1, W_2$ (i.e. $I(X; Z_1, Z_2) >= I(X; W_1, W_2)$) is *false*.
    We can show diagramatically as
    #figure(grid(columns: 2, gutter: 4em, diagram($
        & X edge("ld", ->) edge("rd", ->) \
        node(P(y | x)) edge("d", ->) & & P(y | x) edge("d", ->) \
        Y_1 edge("d", ->) & & Y_2 edge("d", ->) \
        Q(z | y_1) edge("d", ->) & & Q(z | y_2) edge("d", ->) \
        Z_1 & & Z_2
    $), diagram($
        & X edge("d", ->) \
        & node(P(y | x)) edge("d", ->) \
        & Y edge("ld", ->) edge("rd", ->) \
        Q(z | y) edge("d", ->) & & Q(z | y) edge("d", ->) \
        W_1 & & W_2
    $)))
]
#example[
    For example, let $P_(Y | X)$ be the $Z$-channel: if $X = 0$, then $Y = 0$ with probability $1$, and if $X = 1$, then $Y sim Bern(1 - delta)$ for some $delta in (0, 1)$. Let $Q_(Z | Y)$ be a binary symmetric channel: given $Y$ taking values in $0, 1$, $Z = Y$ with probability $1 - epsilon$, and $Z = 1 - Y$ with probability $epsilon$ for some $epsilon in (0, 1)$. We can represent this as
    #figure(grid(columns: 2, gutter: 4em, diagram(cell-size: 15mm, $
        0 edge("r", ->, label: 1) & 0 \
        1 edge("ru", ->, label: delta) edge("r", ->, label: 1 - delta) & 1
    $), diagram(cell-size: 15mm, $
        0 edge("r", ->, label: 1 - epsilon) edge("rd", ->, label: epsilon) & 0 \
        1 edge("ru", ->, label: epsilon) edge("r", ->, label: 1 - epsilon) & 1
    $)))

    If $X sim Bern(1\/2)$, $delta = 0.85$ and $epsilon = 0.1$, then $I(X; W_1, W_2) approx 0.047 > I(X; Z_1, Z_2) approx 0.039$. So the correlated observations $W_1, W_2$ are better than the independent observations $Z_1, Z_2$.
]


= Entropy and additive combinatorics

== Simple sumset entropy bounds

#definition[
    For $A, B subset.eq ZZ$ the *sumset* of $A$ and $B$ is $
        A + B := {a + b: a in A, b in B}.
    $
]<def:sumset>
#definition[
    For $A, B subset.eq ZZ$ the *difference set* of $A$ and $B$ is $
        A - B := {a - b: a in A, b in B}.
    $
]<def:difference-set>
#proposition[
    Let $A, B subset.eq ZZ$ be finite. Then $
        max{abs(A), abs(B)} <= abs(A + B) <= abs(A) abs(B).
    $
]<prop:sumset-bounds>
#proofhints[
    Trivial.
]
#proof[
    Trivial.
]
#proposition("Ruzsa Triangle Inequality")[
    Let $A, B, C subset.eq ZZ$ be finite. Then $
        abs(A - C) dot abs(B) <= (abs(A - B) abs(B - C)).
    $
]<prop:ruzsa-triangle-inequality>
#proofhints[
    Show that an appropriate function is injective.
]
#proof[
    Fix a presentation $y = a_y - c_y$ (where $a_y in A, c_y in C$) for each $y in A - C$. Let $
        f: B times (A - C) & -> (A - B) times (B - C) \
        (b, y) & |-> (a_y - b, b - c_y).
    $ If $f(b, y) = f(b', y')$, then $a_(y') - b' = a_y - b$ and $b' - c_(y') = b - c_y$. So $a_y - a_(y') = b - b' = c_y - c_(y')$. So $y = a_y - c_y = a_(y') - c_(y') = y'$. Hence $a_y = a_(y')$, and so $b = b'$. So $f$ is injective, so $abs(B times (A - C)) <= abs((A - B) times (B - C))$.
]
#remark[
    If $X_1^n$ is a large collection of IID RVs with common PMF $P$ on alphabet $A$, then the AEP tells us that we can concentrate on the $2^(n H)$ typical strings. $2^(n H) = \(2^H\)^n$ is typically much smaller than all $abs(A)^n = (2^(log abs(A)))^n$ strings. We can think of $\(2^H\)^n$ as the effective support size of $P^n$, and can of $2^H$ as the effective support size of a single RV with entropy $H$.
]
#remark[
    We can use the above interpretation to obtain useful conjectures about bounds for the entropy of discrete RVs, from corresponding results on bounds on sumsets. We start with a sumset bound, then replace subsets of $ZZ$ by independent RVs on $ZZ$, and replace $log abs(A)$ of each set $A$ by the entropy of the corresponding RV.
]
#proposition[
    Let $X$ and $Y$ are independent RVs on alphabet $ZZ$, then $
        max{H(X), H(Y)} <= H(X + Y) <= H(X) + H(Y).
    $
]<prop:sum-entropy-bounds>
#proofhints[
    - For lower bound, show that $H(X) <= H(X + Y)$ using data processing and similarly for $H(Y)$. The upper bound should follow directly from this calculation.
]
#proof[
    For the lower bound, $
        H(X) + H(Y) & = H(X, Y) quad & #[by @prop:entropy-chain-rule] \
        & = H(Y, X + Y) quad & #[by @prop:entropy-data-processing] \
        & = H(X + Y) + H(Y | X + Y) quad & #[by @prop:entropy-chain-rule] \
        & <= H(X + Y) + H(Y) quad & #[by @prop:conditioning-reduces-entropy].
    $ Note we have equality for data processing, since $(x, y) |-> (x, x + y)$ is injective. Hence $H(X + Y) >= H(X)$, and the same argument shows that $H(X + Y) >= H(Y)$.

    For the upper bound, we have $H(X) + H(Y) = H(X + Y) + H(Y | X + Y) >= H(X + Y)$ by non-negativity of conditional entropy.
]
#lemma[
    Let $X, Y, Z$ be independent RVs on alphabet $ZZ$. Then $
        H(X - Z) + H(Y) <= H(X - Y, Y - Z).
    $
]
#proofhints[
    - Show that $I(X; X - Z) <= I(X; (X - Y, Y - Z))$.
    - Rewrite both sides of the above inequality in terms of entropies, using @prop:entropy-data-processing.
]
#proof[
    Since $X - Z = (X - Y) + (Y - Z)$, $X$ and $X - Z$ are conditionally independent given $(X - Y, Y - Z)$ by @note:x-y-and-function-of-y-form-markov-chain. Thus by @thm:mutual-information-data-processing for mutual information, we have $I(X; (X - Y, Y - Z)) >= I(X; X - Z)$. Now $
        I(X; X - Z) & = H(X - Z) - H(X - Z | X) \
        & = H(X - Z) - H(Z | X) = H(X - Z) - H(Z)
    $ by @prop:entropy-data-processing (since, given $X = x$, $x - z |-> z$ is injective), and independence of $X$ and $Z$. Also, $
        I(X; (X - Y, Y - Z)) & = H(X - Y, Y - Z) + H(X) - H(X, X - Y, Y - Z) \
        & = H(X - Y, Y - Z) + H(X) - H(X, Y, Z) \
        & = H(X - Y, Y - Z) - H(Y) - H(Z)
    $ by @prop:entropy-data-processing (since $(x, x - y, y - z) |-> (x, y, z)$ is injective), and independence of $X$, $Y$ and $Z$.
]
#theorem("Ruzsa Triangle Inequality for Entropy")[
    Let $X, Y, Z$ be independent RVs on alphabet $ZZ$. Then $
        H(X - Z) + H(Y) <= H(X - Y) + H(Y - Z).
    $
]<thm:entropy-ruzsa-triangle-inequality>
#proofhints[
    By above lemma.
]
#proof[
    By the above lemma, we have $
        H(X - Z) + H(Y) & <= H(X - Y, Y - Z) \
        & = H(X - Y) + H(Y - Z | X - Y) quad & #[by @prop:entropy-chain-rule] \
        & <= H(X - Y) + H(Y - Z).
    $ by @prop:conditioning-reduces-entropy.
]

== The doubling-difference inequality for entropy

#definition[
    For IID RVs $X_1, X_2$ on alphabet $ZZ$, the *entropy-increase* due to addition ($Delta^+$) or subtraction ($Delta^-$) is $
        Delta^+ & := H(X_1 + X_2) - H(X_1), \
        Delta^- & := H(X_1 - X_2) - H(X_1).
    $
]<def:entropy-increase>
#proposition[
    For IID $X_1, X_2$ on $ZZ$, we have $
        Delta^+ & = I(X_1 + X_2; X_2), \
        Delta^- & = I(X_1 - X_2; X_2).
    $
]
#proofhints[
    Straightforward.
]
#proof[
    We have $
        I(X_1 + X_2; X_2) & = H(X_1 + X_2) + H(X_2) - H(X_1 + X_2, X_2) \
        & = H(X_1 + X_2) + H(X_2) - H(X_1, X_2) \
        & = H(X_1 + X_2) + H(X_2) - H(X_1) - H(X_2)
    $ by @prop:entropy-data-processing (since $(x_1 + x_2, x_2) |-> (x_1, x_2)$ is injective) and @prop:entropy-chain-rule. The proof is identical for $Delta^-$.
]
#lemma[
    Let $X, Y, Z$ be independent RVs on alphabet $ZZ$. Then $
        H(X + Y + Z) + H(Y) <= H(X + Y) + H(Y + Z).
    $
]
#proofhints[
    - Show that $I(X; X + Y + Z) <= I(X + Y; X)$.
    - Rewrite both sides in terms of entropies.
]
#proof[
    Since $X - (X + Y, Z) - (X + Y + Z)$ form a Markov chain by @note:x-y-and-function-of-y-form-markov-chain, we have, by @thm:mutual-information-data-processing and @prop:mutual-information-chain-rule for mutual information, $
        I(X; X + Y + Z) & <= I(X + Y, Z; X) = I(X + Y; X) + I(Z; X | X + Y). \
        & = I(X + Y; X)
    $ since $Z$ is (conditionally) independent of $X$ given $X + Y$. Now $
        I(X + Y; X) & = H(X + Y) + H(X) - H(X + Y, X) \
        & = H(X + Y) + H(X) - H(Y, X) \
        & = H(X + Y) + H(X) - H(Y) - H(X) \
        & = H(X + Y) - H(Y)
    $ since $(y, x) |-> (x + y, x)$ is injective and $X$ and $Y$ are independent. Also, $
        I(X + Y + Z; X) & = H(X + Y + Z) + H(X + Y + Z | X) \
        & = H(X + Y + Z) - H(Y + Z | X) \
        & = H(X + Y + Z) - H(Y + Z)
    $ since, given $X = x$, $x + y + z |-> y + z$ is injective, and $X$ and $Y + Z$ are independent.
]
#theorem("Doubling-difference Inequality")[
    Let $X_1$ and $X_2$ be IID RVs on $ZZ$. Then $
        1/2 <= Delta^+ / Delta^- <= 2.
    $
]
#proofhints[
    - For lower bound, use @thm:entropy-ruzsa-triangle-inequality for appropriate RVs.
    - For upper bound, 
]
#proof[
    For the lower bound, let $X, -Y, Z$ be IID with the same distribution as $X_1$. Then by the @thm:entropy-ruzsa-triangle-inequality, $
        H(X_1 - X_2) + H(X_1) <= H(X_1 + X_2) + H(X_1 + X_2).
    $ So $2(H(X_1 + X_2) - H(X_1)) >= H(X_1 - X_2) - H(X_1)$.

    For the upper bound, let $X, -Y, Z$ be IID with the same distribution as $X_1$. Then by the above lemma and @prop:sum-entropy-bounds, $
        H(X_1 + X_2) + H(X_1) <= H(X_1 - X_2) + H(X_1 - X_2)
    $ so $H(X_1 + X_2) - H(X_1) <= 2(H(X_1 - X_2) - H(X_1))$.
]


= Entropy rate

#definition[
    For an arbitrary source $vd(X) = {X_n: n in NN}$, the *entropy rate* $H(vd(X))$ of $vd(X)$ is the limit of the average number of bits per symbol: $
        H(vd(X)) = lim_(n -> oo) 1/n H(X_1^n)
    $ whenever the limit exists.
]<def:entropy-rate>
#example[
    If $vd(X)$ is memoryless (so a sequence of IID RVs) with common entropy $H = H(X_i)$, then the entropy rate is $
        H(vd(X)) = lim_(n -> oo) 1/n H(X_1^n) = lim_(n -> oo) 1/n sum_(i = 1)^n H(X_i) = H.
    $
]
#example[
    Let $vd(X) = {X_n: n in NN}$ be an irreducible, aperiodic Markov chain on a finite alphabet $A$ with transition matrix $Q$, where $
        Q_(a b) = PP(X_(n + 1) = b | X_n = a), quad forall a, b in A
    $ Let $X_1 sim P_(X_1)$ be the initial distribution and $pi$ be the unique stationary distribution ($PP(X_n = x) -> pi(x)$ as $n -> oo$). $vd(X)$ has a unique invariant distribution $pi$ to which it converges: $
        forall x in A, quad PP(X_n = x) -> pi(x) quad "as" n -> oo
    $ and hence also $
        PP(X_(n- 1) = x, X_n = y) = PP(X_n = x) Q_(x y) -> pi(x) Q_(x y).
    $ Then by the @prop:entropy-chain-rule and conditional independence, $
        H(X_1^n) & = sum_(i = 1)^n H(X_i | X_1^(i - 1)) \
        & = H(X_1) + sum_(i = 2)^n H(X_i | X_(i - 1)) \
        & = H(X_1) - H(X_(n + 1) | X_n) + sum_(i = 1)^n H(X_(i + 1) | X_i).
    $ By the convergence theorem for Markov chains, we have $P_(X_n) -> pi$ as $n -> oo$. $H(X | Y)$ is a continuous function of the joint distribution $P_(X, Y)$, so $H(X_n | X_(n - 1)) -> H(overline(X_1) | overline(X_0))$ as $n -> oo$, where $overline(X_0) sim pi$ and $PP(overline(X_1) = b | overline(X_1) = a) = Q_(a b)$. We have $
        1/n H(X_1^n) = 1/n (H(X_1) - H(X_(n + 1) | X_n)) + 1/n sum_(i = 1)^n H(X_(i + 1) | X_i)
    $ The first term tends to $0$ since the numerator is bounded, and the summands in the second term tend to $H(overline(X_1) | overline(X_0))$. So the entropy rate exists and is equal to $H(vd(X)) = H(overline(X_1) | overline(X_0))$.
]
#definition[
    A source $vd(X)$ is *stationary* if for any block length $n in NN$, the distribution of $X_(k + 1)^(k + n)$ is independent of $k$.
]<def:source.stationary>
#remark[
    If $vd(X) = {X_n: n in NN}$ is one-sided stationary process, then by Kolmogorov's extension theorem, $vd(X)$ admits a unique two-sided extension to $vd(X) = {X_n: n in ZZ}$.
]
#theorem[
    If $vd(X) = {X_n: n in NN}$ is a stationary process on finite alphabet $A$, then its entropy rate exists and is equal to $
        H(vd(X)) = lim_(n -> oo) H(X_n | X_1^(n - 1)).
    $
]<thm:entropy-rate-of-stationary-source>
#proofhints[
    Show that the sequence $\{H(X_n) | X_1^(n - 1): n in NN\}$ is non-increasing and use the Cèsaro Lemma.
]
#proof[
    The sequence $\{H(X_n) | X_1^(n - 1): n in NN\}$ is non-negative by non-negativity of conditional entropy, and is non-increasing, since $
        H(X_(n + 1) | X_1^n) & <= H(X_(n + 1) | X_2^n) quad & #[by @prop:conditioning-reduces-entropy] \
        & = H(X_2^(n + 1)) - H(X_2^n) quad & #[by @prop:entropy-chain-rule] \
        & = H(X_1^n) - H(X_1^(n - 1)) quad & "by stationarity" \
        & = H(X_(n - 1) | X_1^(n - 2)) quad & #[by @prop:entropy-chain-rule].
    $ Hence the limit $lim_(n -> oo) H(X_n | X_1^(n - 1))$ exists, and so by the Cèsaro Lemma, the averages converge to the same limit. But by the @prop:entropy-chain-rule, the averages are $
        1/n sum_(i = 1)^n H(X_i | X_1^(i - 1)) = 1/n H(X_1^n).
    $
]
#theorem[
    For a stationary process $vd(X) = {X_n: n in ZZ}$ on a finite alphabet $A$, $
        H(vd(X)) = H(X_0 | X_(-n)^(-1)) =H(X_0 | X_(-oo)^(-1)).
    $
]<thm:entropy-rate-is-conditional-entropy-given-infinite-past>
#proofhints[
    Non-examinable.
]
#proof[
    By Martingale convergence, we have that $
        P(x_0 | X_(-n)^(-1)) -> P(x_0 | X_(-oo)^(-1)) quad "almost surely" quad "as" n -> oo,
    $ where $P(dot | x_(-n)^(-1))$ is the conditional distribution of $X_0$ given $X_(-n)^(-1) = x_(-n)^(-1)$, and $P(dot | x_(-oo)^(-1))$ is the conditional distribution of $X_0$ given $X_(-oo)^(-1) = x_(-oo)^(-1)$. Now, we can take expectations to obtain that, by the bounded convergence theorem (since $p |-> p log p$ is continuous and bounded for $p in [0, 1]$), $
        H(X_0 | X_(-n)^(-1)) & = EE[-sum_(x_0 in A) P(x_0 | X_(-n)^(-1)) log P(x_0 | X_(-n)^(-1))] \ & -> EE[-sum_(x_0 in A) P(x_0 | X_(-oo)^(-1)) log P(x_0 | X_(-oo)^(-1))] \
        & =: H(X_0 | X_(-oo)^(-1)) quad "almost surely" quad "as" n -> oo.
    $ Finally, $H(X_0 | X_(-n)^(-1)) = H(X_(n + 1) | X_1^n)$ by stationarity, so we are done by @thm:entropy-rate-of-stationary-source.
]
#definition[
    Let $vd(X) = {X_n: n in ZZ}$ be a stationary source on finite alphabet $A$, and define the (left) *shift* operator $T: A^ZZ -> A^ZZ$ on sequences $A^ZZ$ by $
        (T x)_n = x_(n + 1) quad forall n in ZZ.
    $ $vd(X)$ is *ergodic* if all shift invariant events are trivial, i.e. for any measurable $B subset.eq A^ZZ$, we have $
        T^(-1) B = B ==> PP(X_(-oo)^oo in B) = 0 "or" 1.
    $ Intuitively, an ergodic process is one which satisfies the general form of the strong law of large numbers.

    It turns out that ergodicity is equivalent to the validity of the following:
]<def:source.ergodic>
#theorem("Birkhoff's Ergodic Theorem")[
    Let $vd(X) = {X_n: n in ZZ}$ be a stationary ergodic source on alphabet $A$. Then for any measurable function $f: A^ZZ -> RR$ such that $
        EE[abs(f(X_(-oo)^oo))] < oo,
    $ we have $
        1/n sum_(i = 1)^n f(T^i X_(-oo)^oo) -> EE[f(X_(-oo)^oo)] quad "almost surely" quad "as" n -> oo 
    $
]<thm:birkhoff>
#proofhints[
    Beyond the scope of this course.
]
#proof[
    Omitted.
]
#remark[
    The strong law of large numbers follows instantly from Birkhoff by setting $f(x_(-oo)^oo) = x_1$.
]
#example[
    Every IID source is ergodic.
]
#theorem("Shannon-McMillan-Breiman")[
    Let $vd(X) = {X_n: n in NN}$ be a stationary ergodic source on alphahbet $A$ with entropy rate $H = H(vd(X))$, then $
        -1/n log P_n (X_1^n) -> H "almost surely as" n -> oo
    $ where $P_n$ is the PMF of $X_1^n$.
]<thm:shannon-mcmillan-breiman>
#proofhints[
    Non-examinable.
]
#proof[
    Idea: by @prop:entropy-chain-rule, we have $
        -1/n log P_n (X_1^n) = -1/n log product_(i = 1)^n P(X_i | X_1^(i - 1)) = 1/n sum_(i = 1)^n [-log P(X_i | X_1^(i - 1))]
    $ but we cannot directly apply the ergodic theorem to this, since $-log P(X_i | X_1^(i - 1))$ is not of the form $f(T^i x_(-oo)^oo)$. Instead, note that by @thm:birkhoff and @thm:entropy-rate-is-conditional-entropy-given-infinite-past, $
        -1/n log P(X_1^n | X_(-oo)^0) & = 1/n sum_(i = 1)^n [-log P(X_i | X_(-oo)^(i - 1))] \
        & -> EE[-log P(X_0 | X_(-oo)^(-1))] \
        & =: H(X_0 | X_(-oo)^(-1)) = H "almost surely" quad "as" n -> oo.
    $ Also, by @thm:birkhoff, for each fixed $k >= 1$, $
        1/n sum_(i = 1)^n (-log P(X_i | X_(i - k)^(i - 1))) & -> EE[-log P(X_0 | X_(-k)^(-1))] \
        & =: H(X_0 | X_(-k)^(-1)) "almost surely" quad "as" n -> oo.
    $ We have $
        & PP(-1/n log P(X_1^n | X_(-oo)^0) - (-1/n log P_n (X_1^n)) > epsilon) & = PP(1/n log (P_n (X_1^n))/(P(X_1^n | X_(-oo)^0)) > epsilon) \
        = & PP((P_n (X_1^n))/(P(X_1^n | X_(-oo)^0)) > 2^(n epsilon)) \
        <= & 2^(-n epsilon) EE[(P_n (X_1^n))/(P(X_1^n | X_(-oo)^0))] quad "by markov's inequality" \
        <= & 2^(-n epsilon) EE[EE[(P_n (X_1^n))/(P(X_1^n | X_(-oo)^0)) | X_(-oo)^0]] \
        = & 2^(-n epsilon) EE[sum_(x_1^n \ P(x_1^n | X_(-oo)^0) > 0) P(x_1^n | X_(-oo)^0) (P_n (x_1^n))/(P(x_1^n | X_(-oo)^0))] \
        <= & 2^(-n epsilon)
    $ which is summable, so by Borel-Cantelli, $
        liminf_(n -> oo) -1/n log P(X_1^n | X_(-oo)^0) <= liminf_(n -> oo) -1/n log P_n (X_1^n) "almost surely".
    $ For each fixed $k$, consider the sequence of PMFs $Q_n^((k))(x_1^n) = P_k (x_1^k) product_(i = k + 1)^n P(x_i | X_(i - k)^(i - 1))$ for $x_1^n in A^n$. Then $
        & -1/n log Q_n^((k)) (X_1^n) - [-1/n sum_(i = 1)^n log P(x_i | x_(i - k)^(i - 1))] \
        & = -1/n [log P_k (x_1^k) - sum_(i = 1)^k log P(X_i | X_(i - k)^(i - 1))] \
        & -> 0 "almost surely" "as" n -> oo
    $ So suffices to show that $limsup_(n -> oo) -1/n log P_n (X_1^n) <= limsup_(n -> oo) -1/n log Q_n^((k)) (X_1^n)$ almost surely. So again, let $epsilon > 0$ be arbitrary, then $
        & PP(-1/n log P_n (X_1^n) - (-1/n log Q_n^((k))(X_1^n)) > epsilon) \
        & = PP((Q_n^((k))(X_1^n))/(P_n (X_1^n)) > 2^(n epsilon)) <= 2^(-n epsilon) EE[(Q_n^((k)) (X_1^n))/(P_n (X_1^n))] "by Markov's inequality" \
        & <= 2^(-n epsilon) sum_(x_1^n in A^n) P_n (x_1^n) (Q_n^((k))(x_1^n))/(P_n (x_1^n)) = 2^(-n epsilon)
    $ which is summable, so by Borel-Cantelli and the fact that $epsilon > 0$ was arbitrary, we have $
     limsup_(n -> oo) -1/n log P_n (X_1^n) <= limsup_(n -> oo) -1/n sum_(i = 1)^n log P(X_i | X_(i - k)^(i - 1)).
    $
]
// TODO: look at proofs of things relying on AEP, convince yourself the arguments work with this general result in place of AEP.


= Types and large deviations

== The method of types

#definition[
    Let $A$ be a finite alphabet and $x_1^n in A^n$. The *type* of $x_1^n$ is its empirical distribution $hat(P)_n = hat(P)_(x_1^n)$: $
        hat(P)_n (a) = hat(P)_(x_1^n)(a) = 1/n sum_(i = 1)^n bb(1)_{x_i = a}.
    $
]
#notation[
    For a finite alphabet $A = {a_1, ..., a_m}$, let $cal(P)$ denote the set of all PMFs on $A$: $
        cal(P) = {P in [0, 1]^m: sum_(a in A) P(a) = 1}.
    $ Note that $cal(P)$ is an $m$-simplex.
]
#notation[
    We write $cal(P)_n$ for the set of all *$n$-types*: $
        cal(P)_n = {P in cal(P): n P(a) in ZZ thick forall a in A}.
    $ Note that $cal(P)_n$ is finite.
]
#proposition[
    We have $abs(cal(P)_n) <= (n + 1)^m$.
]<prop:upper-bound-on-number-of-n-types>
#proofhints[
    Straightforward.
]
#proof[
    Each $P in cal(P)_n$ is of the form $(k_1 \/ n, ..., k_m \/ n)$. There are at most $(n + 1)$ choices ($0, ..., n$) for each $k_i$.
]
#proposition[
    Let $x_1^n in A^n$ have type $hat(P)_n$. Then for any PMF $Q$, $
        Q^n (x_1^n) = 2^(-n\(H\(hat(P)_n\) + D\(hat(P)_n || Q\)\)).
    $ In particular, if $Q = hat(P)_n$, then $Q^n (x_1^n) = 2^(-n H(Q))$.
]<prop:prob-under-prod-dist-of-string-of-type>
#proofhints[
    Rewrite $log Q^n (x_1^n)$.
]
#proof[
    We have $
        log Q^n (x_1^n) & = sum_(i = 1)^n log Q(x_i) \
        & = sum_(i = 1)^n sum_(a in A) bb(1)_({x_i = a}) log Q(a) \
        & = n sum_(a in A) 1/n sum_(i = 1)^n bb(1)_({x_i = a}) log Q(a) \
        & = n sum_(a in A) hat(P)_n (a) log Q(a) = -sum_(a in A) hat(P)_n (a) log ((hat(P)_n (a))/(Q(a)) 1/(hat(P)_n (a))) \
        & = -n (sum_(a in A) hat(P)_n (a) log (hat(P)_n (a))/(Q(a)) + sum_(a in A) hat(P)_n (a) log 1/(hat(P)_n (a))) \
        & = -n\(D\(hat(P)_n || Q\) + H\(hat(P)_n\))
    $
]
#definition[
    Given a $n$-type $P$, its *type class* is $
        T(P) := {x_1^n in A^n: hat(P)_(x_1^n) = P}.
    $ Note that $A^n = product.co_(P in cal(P)_n) T(P)$: since $A^n$ has size $abs(A)^n$ exponential in $n$, and the union is over $abs(cal(P)_n) <= (n + 1)^m$ (polynomial in $n$) elements, at least one type class must contain exponentially many strings.

    $T(P)$ consists of all possible arrangements of $n P(a_1)$ $a_1$'s, ..., $n P(a_m)$ $a_m$'s, so $
        abs(T(P)) = (n!)/(product_(j = 1)^m (n P(a_j))!).
    $
]
#lemma[
    Let $P in cal(P)_n$. Then $
        P^n (T(P)) = max{P^n (T(Q)): Q in cal(P)_n}.
    $ i.e. the most likely type class under $P^n$ is $T(P)$.
]<lem:most-likely-type-class-under-prod-dist-is-type-class-of-that-dist>
#proofhints[
    - For $Q in cal(P)_n$, find an expression for $P^n (x_1^n)$ which should be independent of $x_1^n$, for each case $x_1^n in T(P)$ and $x_1^n in T(Q)$.
    - Show that $(P^n (T(P)))/(P^n (T(Q))) >= 1$, using the fact that $k! \/ ell! >= ell^(k - ell)$ (why?).
]
#proof[
    Let $Q in cal(P)_n$ be arbitrary. Then $
        (P^n (T(P)))/(P^n (T(Q))) & = (abs(T(P)) dot product_(i = 1)^m P(a_i)^(n P(a_i)))/(abs(T(Q)) dot product_(i = 1)^m P(a_i)^(n Q(a_i))) \
        & = (n!)/(product_(i = 1)^m (n P(a_i))!) dot (product_(i = 1)^m (n Q(a_i))!)/(n!) dot product_(i = 1)^m P(a_i)^(n(P(a_i) - Q(a_i))) \
        & = product_(i = 1)^m P(a_i)^(n(P(a_i) - Q(a_i))) dot product_(i = 1)^m ((n Q(a_i))!)/((n P(a_i))!).
    $ Now since $k! \/ ell! >= ell^(k - ell)$ (to show this, consider $k >= ell$ and $k < ell$ cases separately), this is $
        & >= product_(i = 1)^m P(a_i)^(n(P(a_i) - Q(a_i))) dot product_(i = 1)^m (n(P(a_i)))^(n(Q(a_i) - P(a_i))) \
        & = product_(i = 1)^m n^(n(Q(a_i) - P(a_i))) \
        & = n^(n sum_(i = 1)^m (Q(a_i) - P(a_i))) = 1
    $ since probabilities sum to $1$.
]
#proposition[
    Let $abs(A) = m$. For any $n$-type $P in cal(P)_n$, $
        (n + 1)^(-m) 2^(n H(P)) <= abs(T(P)) <= 2^(H(P)).
    $
]<prop:bounds-on-size-of-type-class>
#proofhints[
    Straightforward.
]
#proof[
    By @prop:prob-under-prod-dist-of-string-of-type, we have $1 >= P^n (T(P)) = abs(T(P)) 2^(-n H(P))$. For the lower bound, $
        1 & = sum_(x_1^n in A^n) P^n (x_1^n) \
        & = sum_(Q in cal(P)_n) P^n (T(Q)) \
        & <= abs(cal(P)_n) P^n (T(P)) & quad #[by @lem:most-likely-type-class-under-prod-dist-is-type-class-of-that-dist] \
        & <= (n + 1)^m abs(T(P)) 2^(-n H(P)).
    $
]
#corollary[
    For any $n$-type $P in cal(P)_n$ and any PMF $Q$ on $A$, $
        (n + 1)^(-m) 2^(-n D(P || Q)) <= Q^n (T(P)) <= 2^(-n D(P || Q)).
    $
]<crl:bounds-on-probability-of-type-class>
#proofhints[
    Straightforward.
]
#proof[
    Let $x_1^n in T(P)$ be arbitrary. Then by @prop:prob-under-prod-dist-of-string-of-type, $
        Q^n (T(P)) = abs(T(P)) Q^n (x_1^n) = abs(T(P)) 2^(-n (H(P) + D(P || Q))).
    $ So we are done by @prop:bounds-on-size-of-type-class.
]

== Sanov's theorem

#theorem("Sanov")[
    Let $X_1^n$ be IID with common PMF $Q$ which has full support on alphabet $A$ (i.e. $Q(a) > 0$ for all $a in A$) with $abs(A) = m$. Let $hat(P)_n$ be the empirical distribution of $X_1^n$. For all $E subset.eq cal(P)$, $
        PP\(hat(P)_n in E\) <= (n + 1)^m 2^(-n D^*).
    $ where $D^* = inf{D(P || Q): P in E}$. Also, if $E = overline("int"(E))$ is equal to the closure of its interior, then $
        lim_(n -> oo) -1/n log PP\(hat(P)_n in E\) = D^* = D(P^* || Q),
    $ where $P^* in E$.
]<thm:sanov>
#proofhints[
    - For the inequality, use that $PP\(hat(P)_n in E\) = PP\(hat(P)_n in E sect cal(P)_n\) = sum_(P in E sect cal(P)_n) Q^n (T(P))$. Explain why $D^*$ is finite.
    - For the equality, use the above inequality, and explain why there is a sequence ${P_n: n in NN}$ with each $P_n in cal(P)_n$ and $P_n -> P^*$ where $D(P^* || Q) = D^*$ (why does $P^*$ exist?)
]
#proof[
    Since $Q$ has full support, for any $P in cal(P)$, we have $D(P || Q) <= -sum_(a in A) log Q(a) < oo$, so $D^*$ is finite. For the upper bound, $
        PP\(hat(P)_n in E\) & = PP\(hat(P)_n in E sect cal(P)_n\) \
        & = sum_(P in E sect cal(P)_n) PP\(hat(P)_n = P\) \
        & = sum_(P in E sect cal(P)_n) PP(X_1^n in T(P)) \
        & = sum_(P in E sect cal(P)_n) Q^n (T(P)) \
        & <= abs(E sect cal(P)_n) max{Q^n (T(P)): P in E sect cal(P)_n} \
        & <= abs(E sect cal(P)_n) max{2^(-n D(P || Q)): P in E sect cal(P)_n} quad & #[ by @crl:bounds-on-probability-of-type-class] \
        & = abs(E sect cal(P)_n) dot 2^(-n min{D(P || Q) thin : med P in E sect cal(P)_n}) \
        & <= (n + 1)^m dot 2^(-n D^*).
    $ So $liminf_(n -> oo) -1/n log Q^n \(hat(P)_n in E\) >= D^*$.
    
    For the lower bound, since $E$ is compact and $D(P || Q)$ is continuous in $P$, the infimum $D^*$ is attained by some $P^*$. (Note that since $cal(P)$ itself is compact, there is always a minimising $P^*$ but this is not necessarily in $E$). Also, note that $union.big_(n in NN) cal(P)_n$ is dense in $cal(P)$, so we can find a sequence ${P_n: n in NN} subset.eq E$ such that each $P_n in cal(P)_n$ and $P_n -> P^*$ (as a vector). Now for each $n in NN$, $
        PP\(hat(P)_n in E\) >= PP\(hat(P)_n = P_n\) = Q^n (T(P_n)) >= (n + 1)^(-m) 2^(-n D(P_n || Q))
    $ by @crl:bounds-on-probability-of-type-class. We have $D(P_n || Q) -> D(P^* || Q)$ as $n -> oo$ since $D(P || Q)$ is continuous in $P$. So $limsup_(n -> oo) -1/n log PP\(hat(P)_n in E\) <= D(P^* || Q) = D^*$.
]
#definition[
    For a random variable $Y$, the *log-moment generating function* of $Y$ is $Lambda: RR -> RR$ defined by $
        Lambda(lambda) := ln EE[e^(lambda Y)].
    $
]
#notation[
    Write $Lambda^* (x) = sup{lambda x - Lambda(lambda): lambda > 0}$.
]
#proposition("Chernoff Bound")[
    Let $X_1^n$ be IID RVs and $f: A -> RR$ have mean $mu = EE[f(X_1)]$. Denote the empirical averages by $S_n := 1/n sum_(i = 1)^n f(X_i)$. Then for all $epsilon > 0$, $
        PP(S_n >= mu + epsilon) <= e^(-n Lambda^* (mu + epsilon)),
    $ where $Lambda$ is the log-moment generating function of the $f(X_i)$.
]<prop:chernoff-bound>
#proofhints[
    Use Markov's inequality.
]
#proof[
    By Markov's inequality, for all $lambda > 0$, $
        PP(S_n >= mu + epsilon) = PP(e^(n lambda S_n) >= e^(n lambda (mu + epsilon))) <= e^(-n lambda (mu + epsilon)) EE[e^(lambda n S_n)].
    $ Now since the $X_i$ are independent, $
        EE[e^(lambda n S_n)] = EE[e^(lambda sum_(i = 1)^n f(X_i))] = EE[product_(i = 1)^n e^(lambda f(X_i))] = product_(i = 1)^n EE[e^(lambda f(X_i))] = e^(n Lambda(lambda)).
    $ Hence, $
        PP(S_n >= mu + epsilon) <= e^(-n lambda(mu + epsilon)) e^(n Lambda(lambda)) = e^(-n (lambda(mu + epsilon) - Lambda(lambda))),
    $ and this holds for all $lambda > 0$, so taking the supremum over $lambda$ gives the result.
]
#example[
    Let $X_1^n$ be IID with common PMF $Q$ on finite alphabet $A$, let $f: A -> RR$ with mean $mu = EE_(X sim Q) [f(X)]$. Denote the empirical averages by $S_n := 1/n sum_(i = 1)^n f(X_i)$. Let $epsilon > 0$. By WLLN, $PP(S_n >= mu + epsilon) -> 0$ as $n -> oo$. We want to estimate how small this probability is as a function of $n$. Typically, the way we bound $PP(S_n >= mu + epsilon)$ is by the @prop:chernoff-bound. Alternatively, we have $
        S_n = 1/n sum_(i = 1)^n f(X_i) = 1/n sum_(i = 1)^n sum_(a in A) bb(1)_({X_i = a}) f(a) = sum_(a in A) hat(P)_n (a) f(a) = EE_(X sim hat(P)_n) [f(X)].
    $ Let $B$ be the event $B = {S_n >= mu + epsilon}$, then we can write $B$ as $\{hat(P)_n in E\}$ where $E = {P in cal(P): EE_(X sim P) [f(X)] >= mu + epsilon}$. But @thm:sanov says that $PP(S_n >= mu + epsilon) = PP\(hat(P)_n in E\) <= (n + 1)^m e^(-n D_e (P^* || Q))$ and in fact it tells us that $D_e (P^* || Q) = inf{D_e (P || Q): P in E}$ is asymptotically the "correct" exponent.
]
#proposition[
    Let $X_1^n$ be IID RVs with common PMF $Q$ on alphabet $A$ and $f: A -> RR$ have mean $mu = EE[f(X_1)]$. Let $P^*$ be the minimiser in @thm:sanov for the event $E = {P in cal(P): EE_(X sim P) [f(X)] >= mu + epsilon}$. Then $
        forall epsilon > 0, quad Lambda^* (mu + epsilon) = D_e (P^* || Q),
    $ where $Lambda$ is the log-moment generating function of the $X_i$.
]
#proofhints[
    - $<=$: show that $S_n = EE_(X sim hat(P)_n) [f(X)]$, then use the @prop:chernoff-bound and @thm:sanov.
    - $>=$: for each $lambda >= 0$, define a PMF on $A$ by $
        P_lambda (a) = (e^(lambda f(a)))/(EE[e^(lambda f(X_1))]) Q(a).
    $
    - Show that $Lambda'(lambda) = EE_(Y sim P_lambda) [f(Y)]$ and $Lambda''(lambda) >= 0$.
    - Deduce that there exists $lambda^* > 0$ such that $Lambda'(lambda^*) = mu + epsilon$, then use the definition of $P^*$ to conclude the result.
]
#proof[
    ($<=$): Let $epsilon > 0$. We have $
        S_n = 1/n sum_(i = 1)^n f(X_i) = 1/n sum_(i = 1)^n sum_(a in A) bb(1)_({X_i = a}) f(a) = sum_(a in A) hat(P)_n (a) f(a) = EE_(X sim hat(P)_n) [f(X)].
    $ So we have $PP\(hat(P)_n in E\) = PP(S_n >= mu + epsilon)$, hence $
        Lambda^* (mu + epsilon) & <= liminf_(n -> oo) -1/n PP(S_n >= mu + epsilon) & quad #[by the @prop:chernoff-bound] \
        & <= lim_(n -> oo) -1/n ln PP\(hat(P)_n in E\) \
        & = D_e (P^* || Q) & quad #[by @thm:sanov].
    $
    ($>=$): For each $lambda >= 0$, define the PMF $P_lambda$ on $A$ by $
        P_lambda (a) = (e^(lambda f(a)))/(EE[e^(lambda f(X_1))]) Q(a).
    $ Then $
        Lambda'(lambda) = (EE[f(X_1) e^(lambda f(X_1))])/(EE[e^(lambda f(X_1))]) = 1/EE[e^(lambda f(X_1))] sum_(a in A) Q(a) f(a) e^(lambda f(a)) = EE_(Y sim P_lambda) [f(Y)]
    $ and also, a straightforward calculation shows that $
        Lambda''(lambda) = "Var"_(Y sim P_lambda) (f(Y)) >= 0.
    $ Hence, $Lambda'(lambda)$ is increasing from $Lambda'(0) = mu$ to $lim_(lambda -> oo) Lambda'(lambda) =: f^*$, so there exists $lambda^* > 0$ such that $Lambda'(lambda^*) = mu + epsilon$, hence $EE_(Y in P_(lambda^*))[f(Y)] = mu + epsilon$, so $P_(lambda^*) in E$. Thus, $
        D_e (P^* || Q) & <= D_e (P_(lambda^*) || Q) \
        & = EE_(Y sim P_(lambda^*))[log (P_(lambda^*)(Y))/Q(Y)] \
        & = EE_(Y sim P_(lambda^*))[log (e^(lambda^* f(Y)))/(EE[e^(lambda^* f(X_1))])] \
        & = lambda^* EE_(Y sim P_(lambda^*))[f(Y)] - Lambda(lambda^*) \
        & = lambda^* (mu + epsilon) - Lambda(lambda^*) <= Lambda^* (mu + epsilon).
    $
]
#corollary[
    Let $X_1^n$ be IID RVs with common PMF $Q$ on alphabet $A$. The minimiser $P^*$ in @thm:sanov for the event $E = {P in cal(P): EE_(X sim P) [f(X)] >= mu + epsilon}$ is unique and is given by $
        P^* (a) = P_(lambda^*)(a) = (e^(lambda^* f(a)))/(EE[e^(lambda^* f(X_1))]) Q(a).
    $ where $lambda^* > 0$ satisfies $EE_(Y sim P_(lambda^*))[f(Y)] = mu + epsilon$.
]<crl:minimising-distribution-in-sanov-is-unique-for-nonempty-closed-convex-events>
#proofhints[
    Existence: by above proposition. Uniqueness: use a property of $D(P || Q)$ and the fact that $E$ is non-empty, convex and closed.
]
#proof[
    $D(P || Q)$ is strictly convex in $P$ for fixed $Q$ and $E$ is non-empty, convex and closed, so the minimising $P^*$ is unique. The existence is by the proof of the above proposition.
]
#theorem("Pythagorean Identity")[
    Let $E subset.eq cal(P)$ be closed and convex. Let $Q in.not E$ have full support on $A$, and let $P^*$ achieve the minimum in Sanov's theorem. Then $
        forall P in E, quad D(P || Q) >= D(P || P^*) + D(P^* || Q).
    $
]<thm:pythagorean-identity>
#proofhints[
    - For $P in E$, define $overline(P)_lambda = lambda P + (1 - lambda) P^*$ for $lambda in [0, 1]$. Show that $D\(overline(P)_lambda || Q\) >= D\(overline(P)_0 || Q\)$ for all $lambda in [0, 1]$.
    - Use the derivative of $D_e \(overline(P)_lambda || Q\)$ at $lambda = 0$ to obtain the result.
]
#proof[
    Let $P in E$. Define the mixture $overline(P)_lambda = lambda P + (1 - lambda) P^*$ for $0 <= lambda <= 1$. Since $E$ is convex, $overline(P)_lambda in E$ for all $lambda in [0, 1]$, and by definition of $P^*$, $D\(overline(P)_lambda || Q\) >= D(P^* || Q) = D\(overline(P)_0 || Q\)$ for all $lambda in [0, 1]$. So we have $
        0 & <= lr(dif / (dif lambda) D_e \(overline(P)_lambda || Q\)|)_(lambda = 0) \
        & = lr(dif / (dif lambda) sum_(a in A) overline(P)_lambda (a) ln (overline(P)_lambda (a))/Q(a)|)_(lambda = 0) \
        & = lr(sum_(a in A) (P(a) - P^* (a)) ln (overline(P)_lambda (a))/Q(a) |)_(lambda = 0) + sum_(a in A) (P(a) - P^* (a)) \
        & = sum_(a in A) P(a) ln (P^* (a) P(a))/(Q(a) P(a)) - sum_(a in A) P^* (a) ln (P^* (a))/Q(a) \
        & = D_e (P || Q) - D_e (P || P^*) - D_e (P^* || Q).
    $
]
#remark[
    - The @thm:pythagorean-identity is an $L^2$-style bound: the minimiser $P^*$ can be viewed as the "orthogonal projection" of $Q$ onto $E$.
    - The @thm:pythagorean-identity provides a quantatitive version of the uniqueness statement in @crl:minimising-distribution-in-sanov-is-unique-for-nonempty-closed-convex-events: if $D(P || Q) = D(P^* || Q)$, then $P = P^*$; additionally, if $D(P || Q) <= D(P^* || Q) + delta$ (i.e. $D(P || Q)$ is close to $D(P^* || Q)$), then $D(P || P^*) <= delta$ (i.e. $P$ is close to $P^*$).
]

== The Gibbs conditioning principle

#lemma[
    Let ${Z_n: n in NN}$ be a bounded sequence of RVs which converges to $z in RR$ in probability. Then $
        EE[Z_n] -> c quad "as" n -> oo.
    $
]<lem:expectation-of-bounded-rvs-converges-to-limit-of-convergence-in-probability>
#proofhints[
    Use Jensen's inequality, then split the expectation into two terms, one bounded above by $epsilon$, the other $-> 0$, to show that $abs(EE[Z_n] - c) -> 0$.
]
#proof[
    Let $epsilon > 0$. Since the $Z_n$ are bounded, we have $abs(Z_n) <= M$ for all $n in NN$, for some constant $M$. By @thm:jensens-inequality, $
        abs(EE[Z_n] - z) <= EE[abs(Z_n - z)] = EE[abs(Z_n - z) dot bb(1)_{abs(Z_n - z) <= epsilon}] + EE[abs(Z_n - z) dot bb(1)_{abs(Z_n - z) > epsilon}].
    $ The first term is bounded above by $epsilon$. The second term is bounded above by $
        (M + abs(z)) dot EE[bb(1)_{abs(Z_n - z) > epsilon}] = (M + abs(z)) dot PP(abs(Z_n - z) > epsilon) -> 0 quad "as" n -> oo.
    $ Thus, $limsup_(n -> oo) abs(EE[Z_n] - c) <= epsilon$, and $epsilon > 0$ was arbitrary.
]
#theorem("Gibbs' Conditioning Principle")[
    Let $X_1^n$ be IID with common PMF $Q$ which has full support on $A$. Let $hat(P)_n$ be the empirical distribution of $X_1^n$. If $E subset.eq cal(P)$ is closed, convex, has non-empty interior, and $Q in.not E$, then $
        forall a in A, quad EE\[hat(P)_n (a) | hat(P)_n in E\] = PP\(X_1 = a | hat(P)_n in E\) -> P^* (a) quad "as" quad n -> oo.
    $
]
#proofhints[
    - Showing the equality is straightforward.
    - Define $B(Q, delta) := {P in cal(P): D(P || Q) <= D(P^* || Q) + delta}$, $C = B(Q, 2 delta) sect E$ and $D = E \\ C$.
    - Show that $PP\(hat(P)_n in D | hat(P)_n in E\) <= (n + 1)^(2m) 2^(-n delta)$.
    - Use the @thm:pythagorean-identity and @thm:pinskers-inequality to show that $PP\(abs(hat(P)_n (a) - P^* (a)) > epsilon | hat(P)_n in E\) -> 0$.
]
#proof[
    The conditional distribution of each $X_i$ given $hat(P)_n in E$ is the same, so $
        EE\[hat(P)_n (a) | hat(P)_n in E\] = 1/n sum_(i = 1)^n PP\(X_i = a | hat(P)_n in E\) = PP\(X_1 = a | hat(P)_n in E\).
    $ Define the relative entropy neighbourhoods $
        B(Q, delta) := {P in cal(P): D(P || Q) <= D(P^* || Q) + delta},
    $ and write $C = B(Q, 2 delta) sect E$ and $D = E \\ C$.
    // #unmarked-fig[
    //     #figure(
    //         canvas({
    //             import cetz.draw: *

    //             polygon(((0, 0), (6, 0), (3, 6 * calc.sqrt(3) / 2)))
    //             blob-2d()
    //         })
    //     )
    // ]
    Then $
        PP\(hat(P)_n in D | hat(P)_n in E\) = (PP\(hat(P)_n in D\))/(PP\(hat(P)_n in E\)).
    $ By @thm:sanov, $
        PP\(hat(P)_n in D\) <= (n + 1)^m 2^(-n inf{D(P || Q): P in D}) <= (n + 1)^m 2^(-n(D(P^* || Q) + 2 delta))
    $ and for the denominator, since ${cal(P)_n: n in NN}$ is dense in $cal(P)$, $cal(P)_n$ eventually intersects every open set in $cal(P)$, so eventually $B(Q, delta) sect E sect cal(P)_n$ is non-empty (since $E$ has non-empty interior). So we can eventually find $P_n in cal(P)_n sect E sect B(Q, delta)$. By @prop:bounds-on-size-of-type-class, $
        PP\(hat(P)_n in E\) & >= PP\(hat(P)_n in B(Q, delta) sect E\) \
        & >= PP\(hat(P)_n = P_n\) = Q^n (T(P_n)) \
        & >= (n + 1)^(-m) 2^(-n D(P_n || Q)) \
        & >= (n + 1)^(-m) 2^(-n (D(P^* || Q) + delta)),
    $ since $P_n in B(Q, delta)$. Combining these, we obtain $
        PP\(hat(P)_n in D | hat(P)_n in E\) <= (n + 1)^(2m) 2^(-n delta) -> 0 quad "as" n -> oo.
    $ For $P in C$, by the @thm:pythagorean-identity, $
        D(P^* || Q) >= D(P || Q) >= D(P || P^*) + D(P^* || Q),
    $ thus $D(P || P^*) <= 2 delta$. So $
        PP(D(hat(P)_n || P^*) <= 2 delta | hat(P)_n in E) >= PP(hat(P)_n in C | hat(P)_n in E) -> 1 quad "as" n -> oo.
    $ Hence by @thm:pinskers-inequality, since $delta > 0$ was arbitrary, $
        PP(norm(hat(P)_n - P^*)_"TV" > epsilon mid(|) hat(P)_n in E) -> 0 "as" n -> oo
    $ for all $epsilon > 0$. Thus also, $PP\(abs(hat(P)_n (a) - P^* (a)) > epsilon | hat(P)_n in E\) -> 0$. So, conditional on $hat(P)_n in E$, $hat(P)_n -> P^*$ in probability as $n -> oo$. Therefore, since $\(hat(P)_n (a)\)$ is a bounded sequence, we also have $EE[hat(P)_n (a) | hat(P)_n in E] -> P^* (a)$ as $n -> oo$ by @lem:expectation-of-bounded-rvs-converges-to-limit-of-convergence-in-probability.
]
#example[
    Suppose a fair die is rolled 1000 times, and the observed average of the rolls is at least $5$. What proportion of the rolls was a $6$?

    Let $X_1^1000$ be IID RVs with uniform distribution $Q$ on $A = {1, 2, 3, 4, 5, 6}$. Let $f(x) = x$, $mu = EE[X_1^1000] = 3.5$, let $E = {P in cal(P): EE_(X sim P)[X] >= 5}$. By @crl:minimising-distribution-in-sanov-is-unique-for-nonempty-closed-convex-events, the minimiser $P^*$ is unique and is given by $
        P^* (a) = e^(lambda^* a) / (sum_(k = 1)^6 e^(lambda^* k)), quad forall a in A,
    $ where $lambda^* > 0$ is such that $EE_(Y sim P_(lambda^*))[Y] = 5$. We can directly compute $lambda^* approx 0.63$ and so $
        P^* approx (0.021, 0.039, 0.14, 0.25, 0.48)
    $ So we expect that about $48%$ of the rolls were $6$.
]

== Error probability in fixed-rate data compression

#theorem[
    Let $vd(X) = {X_n: n in NN}$ be a memoryless source with entropy $H = H(X_1)$ and with PMF $Q$ which has full support on finite alphabet $A$. For any rate $R$ with $H < R < log abs(A)$,
    - $==>$: There is a fixed-rate code ${B_n^*: n in NN}$ with asymptotic rate no more than $R$ bits/symbol: $
        limsup_(n -> oo) 1/n (1 + ceil(log abs(B_n^*))) = limsup_(n -> oo) 1/n log abs(B_n^*) <= R,
    $ and with probability of error $P_e^((n))$ that decays to zero exponentially fast: $
        limsup_(n -> oo) 1/n log P_e^((n)) <= -D^*,
    $ where $
        D^* = inf{D(P || Q): H(P) >= R}.
    $
    - $<==$: for any fixed-rate code ${B_n: n in NN}$ with asymptotic rate no more than $R$ bits/symbol: $
        limsup_(n -> oo) 1/n (1 + ceil(log abs(B_n))) = limsup_(n -> oo) 1/n log abs(B_n) <= R,
    $ then its probability of error $P_e^((n))$ cannot decay faster than exponentially with exponent $D^*$: $
        liminf_(n -> oo) 1/n log P_e^((n)) >= -D^*.
    $
]<thm:error-exponents-for-fixed-rate-compression>
#proofhints[
    - $==>$: let $B_n^*$ be the codebook which is a union over an appropriate set of type classes.
    - $<==$: explain why there is $delta > 0$ such that $inf{D(P || Q): H(P) >= R + delta} <= D^* + epsilon$.
    - Explain why, for all $n$ large enough, there is $P_n in cal(P)_n$ such that $H(P_n) >= R + delta \/ 2$ and $D(P_n || Q) <= D^* + 2 epsilon$.
    - Show that $abs(B_n) \/ abs(T(P_n)) -> 0$ as $n -> oo$, and hence that $P_e^((n)) >= 1/2 (n + 1)^(-m) 2^(-n (D^* + 2 epsilon))$ eventually.
]
#proof[
    $==>$: define the codebook $
        B_n^* = union.big_(P in cal(P)_n \ H(P) < R) T(P).
    $ Then by @prop:upper-bound-on-number-of-n-types and @prop:bounds-on-size-of-type-class, $
        abs(B_n^*) = sum_(P in cal(P)_n \ H(P) < R) abs(T(P)) <= sum_(P in cal(P)_n \ H(P) < R) 2^(n H(P)) <= (n + 1)^m 2^(n R),
    $ and so $limsup_(n -> oo) 1/n log abs(B_n^*) <= R$. For the probability of error, $
        P_e^((n)) = PP(X_1^n in.not B_n^*) = Q^n (union.big_(P in cal(P)_n \ H(P) >= R) T(P)) <= sum_(P in cal(P)_n \ H(P) >= R) Q^n (T(P)) <= (n + 1)^m 2^(-n D^*).
    $
    $<==$: let $epsilon > 0$ be arbitrary. By continuity, there is a $delta > 0$ such that $
        inf{D(P || Q): H(P) >= R + delta} <= D^* + epsilon.
    $ Since the $n$-types ${P_n: n in NN}$ are dense in $cal(P)$, for all $n$ large enough, we can find $P_n in cal(P)_n$ such that $H(P_n) >= R + delta \/ 2$ and $D(P_n || Q) <= D^* + 2 epsilon$. Also, by assumption, there is a sequence $(r_n)$ such that $1/n log abs(B_n) <= R + r_n$ and $r_n -> 0$. Now $
        abs(B_n) / abs(T(P_n)) & <= 2^(n(R + r_n)) / ((n + 1)^(-m) 2^(n H(P_n))) = (n + 1)^m 2^(n (R - H(P_n) + r_n)) \
        & <= (n + 1)^m 2^(n (r_n - delta \/ 2)) -> 0 quad "as" n -> oo.
    $ So $abs(B_n) \/ abs(T(P_n)) <= 1 \/ 2$ eventually. Then, for an arbitrary string $x_1^n in T(P_n)$, we have $
        P_e^((n)) & = PP(X_1^n in B_n^c) >= PP(X_1^n in T(P_n) sect B_n^c) \
        & = abs(T(P_n) sect B_n^c) Q^n (x_1^n) = abs(T(P_n) sect B_n^c) / abs(T(P_n)) Q^n (T(P_n)) \
        & >= (1 - abs(T(P_n) sect B_n) / abs(T(P_n))) (n + 1)^(-m) 2^(-n D(P_n || Q)) \
        & >= (1 - abs(B_n) / abs(T(P_n))) (n + 1)^(-m) 2^(-n D(P_n || Q)) \
        & >= 1/2 (n + 1)^(-m) 2^(-n (D^* + 2 epsilon)) quad "eventually"
    $ Thus, $
        liminf_(n -> oo) 1/n log P_e^((n)) >= -(D^* + 2 epsilon),
    $ and since $epsilon > 0$ was arbitrary, we are done.
]
#remark[
    - @thm:error-exponents-for-fixed-rate-compression gives the rate at which the error probabilities $P_e^((n))$ of the codes in the @thm:fixed-rate-coding-theorem decay.
    - Note that the code $B_n^*$ is *universal*: it achieves the optimal error probability at rate $R$ _simultaneously_ for all memoryless sources with entropy $H < R$.
    - The @thm:fixed-rate-coding-theorem says that $P_e^((n))$ cannot tend to zero if $R < H$. In fact, it is possible to show a "strong converse" of the @thm:fixed-rate-coding-theorem, which says that in this case, $P_e^((n)) -> 1$ exponentially fast.
]


= Variable-rate lossless data compression

#notation[
    Let ${0, 1}^*$ denote the set of all binary strings of finite length.
]
#definition[
    A *variable-rate lossless compression code* of block length $n$ on a finite alphabet $A$ is an injective map $C_n: A^n -> {0, 1}^*$ which maps source strings to *codewords*. $C_n$ is also known as the *encoder*.
    
    Each $C_n$ has an associated *length function* $L_n: A^n -> NN$, defined as $
        L_n (x_1^n) = "length of" C_n (x_1^n).
    $
]<def:variable-rate-code>
#definition[
    A code $C_n$ is *prefix-free* if for all $x_1^n != y_1^n in {0, 1}^n$, the codeword $C_n (x_1^n)$ is not a prefix (an initial segment) of $C_n (y_1^n)$.
]<def:variable-rate-code.prefix-free>
#example[
    #figure(
        grid(
            columns: 4,
            column-gutter: 2em,
            table(
                columns: 2,
                $x$, $C(x)$,
                $a$, $00$,
                $b$, $01$,
                $c$, $10$,
                $d$, $11$
            ),
            table(
                columns: 2,
                $x$, $C(x)$,
                $a$, $0$,
                $b$, $10$,
                $c$, $110$,
                $d$, $111$
            ),
            table(
                columns: 2,
                $x$, $C(x)$,
                $a$, $0$,
                $b$, $00$,
                $c$, $110$,
                $d$, $111$
            ),
            table(
                columns: 2,
                $x$, $C(x)$,
                $a$, $0$,
                $b$, $1$,
                $c$, $00$,
                $d$, $11$
            ),
        )
    )
    The first two codes are prefix-free, the last two are not.
]
#remark[
    An advantage of prefix-free codes is that once a full codeword is received, it is guaranteed to be that codeword and not the start of another.
]
#theorem("Kraft's Inequality")[
    - $(==>)$: for any length function $L_n: A^n -> NN$ satisfying *Kraft's inequality*: $
        sum_(x_1^n in A^n) 2^(-L_n (x_1^n)) <= 1,
    $ there is a prefix-free code $C_n$ on $A^n$ with length function $L_n$.
    - $(<==)$: the length function of any prefix-free code satisfies Kraft's inequality.
]<thm:krafts-inequality>
#proofhints[
    For both directions, consider the complete binary tree of depth $max{L_n (x_1^n): x_1^n in A^n}$.
]
#proof[
    $<==$: let $C_n$ be a prefix-free code with length function $L_n$. Let $L^* = max{L_n (x_1^n): x_1^n in A^n}$ and consider the complete binary tree of depth $L^*$/*TODO: insert diagram*/. If we mark all the codewords on the tree, then the prefix-free property implies that no codeword is a descendant of any other codeword. Each codeword $C_n (x_1^n)$ has $2^(L^* - L_n (x_1^n))$ descendants (possibly including itself) at depth $L^*$. The prefix-free property also implies that these descendants are disjoint for different codewords. Since the total number of leaves at depth $L^*$ is $2^(L^*)$, we have $
        2^(L^*) & >= sum_(x_1^n in A^n) 2^(L^* - L_n (x_1^n)).
    $
    $==>$: given a length function $L_n$ satisfying Kraft's inequality, consider the complete binary tree of depth $L^* = max{L_n (x_1^n): x_1^n in A^n}$. Then, ordering the $x_1^n in A^n$ in the order of increasing $L_n (x_1^n)$, assign to each $x_1^n$ (in order) any available node (i.e. any node that is not a prefix or descandant of any codewords already assigned) at depth $L_n (x_1^n)$. Kraft's inequality guarantees that there will always be such a node.
]
#remark[
    @thm:krafts-inequality informally says "not all codelengths for prefix-free codes can be short".
]

== The codes-distributions correspondence

#theorem("Codes-distributions Correspondence")[
    - $==>$: for any PMF $Q_n$ on $A^n$, there is a prefix-free code $C_n^*$ with length function $L_n^*$ such that $
        forall x_1^n in A^n, quad L_n^* (x_1^n) < -log Q_n (x_1^n) + 1
    $
    - $<==$: for any prefix-free code $C_n$ with length function $L_n$, there is a PMF $Q_n$ on $A^n$ such that $
        forall x_1^n in A^n, quad -log Q_n (x_1^n) <= L_n (x_1^n).
    $
]<thm:codes-distributions-correspondence>
#proofhints[
    - $==>$: straightforward.
    - $<==$: consider  @thm:krafts-inequality to define a suitable $Q_n$.
]
#proof[
    $==>$: Let $L_n^* (x_1^n) = ceil(-log Q_n (x_1^n)) < -log Q_n (x_1^n) + 1$. $L_n^*$ satisfies Kraft's inequality: $
        sum_(x_1^n in A^n) 2^(-L_n (x_1^n)) = sum_(x_1^n in A^n) 2^(-ceil(-log Q_n (x_1^n))) <= sum_(x_1^n in A^n) 2^(log Q_n (x_1^n)) = sum_(x_1^n in A^n) Q_n (x_1^n) = 1.
    $ So we are done by the first part of @thm:krafts-inequality.
    
    $<==$: define the PMF $Q_n$ on $A^n$ by $
        Q_n (x_1^n) = 2^(-L_n (x_1^n)) / (sum_(y_1^n in A^n) 2^(-L_n (y_1^n))).
    $ Then $
        -log Q_n (x_1^n) = L_n (x_1^n) + log(sum_(y_1^n in A^n) 2^(-L_n (y_1^n))) <= L_n (x_1^n).
    $ since $L_n$ satisfies Kraft's inequality (i.e. $sum_(y_1^n in A^n) 2^(-L_n (y_1^n)) <= 1$).
]
#remark[
    - @thm:codes-distributions-correspondence says that the performance of any prefix-free can be dominated by a code with length function $L_n (x_1^n) approx -log Q_n (x_1^n)$ for some PMF $Q_n$ on $A^n$, and that for any distribution $Q_n$ such a code exists. So finding a good code is equivalent to finding a good distribution. This assumes nothing about the distribution of the source $X_1^n$ or the block length $n$.
]
#theorem[
    Let $X_1^n$ have PMF $P_n$ on $A^n$.
    
    $==>$: there is a prefix-free code $C_n^*$ with length function $L_n^*$ that achieves an expected description length of $
        EE[L_n^* (X_1^n)] < H(X_1^n) + 1.
    $
    $<==$: for any prefix-free code $C_n$ with length function $L_n$ on $A^n$, $
        EE[L_n (X_1^n)] >= H(X_1^n).
    $
]<thm:entropic-bounds-on-expected-length-of-prefix-free-codes>
#proofhints[
    Straightforward.
]
#proof[
    $==>$: let $C_n^*$ be the code with length function $L_n^* (x_1^n) = ceil(-log P_n (x_1^n))$ as in the @thm:codes-distributions-correspondence. Then $
        EE[L_n^* (X_1^n)] < EE[-log P_n (X_1^n) + 1] = H(X_1^n) + 1.
    $
    $<==$: let $Q_n$ be as in the @thm:codes-distributions-correspondence. Then $
        EE[L_n (X_1^n)] & >= EE[-log Q_n (X_1^n)] \
        & = EE[log(1/(P_n (X_1^n)) dot (P_n (X_1^n))/(Q_n (X_1^n)))] \
        & = EE[-log P_n (X_1^n)] + EE[log (P_n (X_1^n))/(Q_n (X_1^n))] \
        & = H(X_1^n) + D(P_n || Q_n) >= H(X_1^n).
    $
]
#corollary[
    Let $vd(X) = {X_n: n in NN}$ be a stationary source with entropy rate $H = H(vd(X))$. Then $H$ is the best asymptotically achievable compression rate among all variable-rate prefix-free codes: $
        lim_(n -> oo) inf_((C_n, L_n) "prefix-free") 1/n EE[L_n (X_1^n)] = H.
    $
]
#proofhints[
    Straightforward.
]
#proof[
    By @thm:entropic-bounds-on-expected-length-of-prefix-free-codes, $
        1/n H(X_1^n) <= inf_((C_n, L_n) "prefix-free") 1/n EE[L_n (X_1^n)] < 1/n (H(X_1^n) + 1).
    $
]

== Shannon codes and their properties

#definition[
    A *Shannon code* for a distribution $Q_n$ on $A^n$ is a code with length function $
        L_n (x_1^n) := ceil(-log Q_n (x_1^n)).
    $ Note this is the code used in the proof of the @thm:codes-distributions-correspondence.
]<def:shannon-code>
#remark[
    - Shannon codes do not always achieve the optimal (minimal) expected description length $EE[L_n (X_1^n)]$, which is achieved instead by the Huffman code. However, the difference between the expected description lengths of these codes is less than one bit by @thm:entropic-bounds-on-expected-length-of-prefix-free-codes.
    - Shannon codes give shorter descriptions to likely messages and longer descriptions to unlikely messages.
]
#definition[
    We call the $L_n (x_1^n) = -log Q_n (x_1^n)$ for $x_1^n in A^n$ the *ideal Shannon codelengths*.
]<def:ideal-shannon-codelength>
#theorem("Competitive Optimality of Shannon Codes")[
    Let $P_n$ be a distribution on $A^n$ and $X_1^n sim P_n$. For any other PMF $Q_n$ on $A^n$, $
        PP(-log Q_n (X_1^n) <= -log P_n (X_1^n) - K) <= 2^(-K).
    $
]<thm:competitive-optimality-of-shannon-codes>
#proofhints[
    Use Markov's inequality.
]
#proof[
    By Markov's inequality, we have #qed-multiline($
        PP(-log Q_n (X_1^n) <= -log P_n (X_1^n) - K) & = PP((Q_n (X_1^n))/(P_n (X_1^n)) >= 2^K) \
        & <= 2^(-K) EE[(Q_n (X_1^n))/(P_n (X_1^n))] \
        & = 2^(-K) sum_(x_1^n in A^n) P_n (x_1^n) dot (Q_n (x_1^n))/(P_n (x_1^n)) \
        & = 2^(-K).
    $)
]


= Universal data compression

In this chapter, assume that we want to compress a message $x_1^n in {0, 1}^n$ where each $x_i$ is produced by an unknown distribution $P = P_(theta^*)$ which belongs to the parametric family ${P_theta sim Bern(theta): theta in (0, 1)}$. We also assume codelengths can be non-integral for simplicity, since the actual codelength differs by at most one bit.

Note that in this case, $theta_"MLE" = k \/ n$ where $k$ is the number of $1$s in $x_1^n$. So the maximum likelihood distribution for $x_1^n$ amsong all $P_theta$ is its type $hat(P)_n$, and by @prop:prob-under-prod-dist-of-string-of-type, for all $theta in Theta$, $
    -log P_(theta_"MLE")(x_1^n) = n H(hat(P)_n) <= -log P_theta^n (x_1^n).
$


#definition[
    The *MLE code* first describes $hat(theta)_"MLE"$ to the decoder, then describes $x_1^n$ using the Shannon code for $P_(hat(theta)_"MLE")$.
]<def:mle-code>
#proposition[
    The description length of the MLE code is $
        n H\(hat(P)_n\) + log(n + 1).
    $ In particular, the price of universality of the MLE code is $log n$ bits.
]<prop:mle-code-price-of-universality>
#proofhints[
    Trivial.
]
#proof[
    $theta_"MLE" = k \/ n$ where $k$ is the number of $1$s in $x_1^n$, so $k in {0, ..., n}$. So $k$ can be described using $log(n + 1)$ bits.
    $x_1^n$ is described using $-log P_(theta_"MLE")^n (x_1^n) = n H(hat(P)_n)$ bits.
]
#proposition[
    The expected description length of the MLE code is bounded above by $
        n H(P_(theta^*)^n) + log(n + 1).
    $ In particular, the price of universality in expectation of the MLE code is $log n$ bits.
]<prop:mle-code-expected-price-of-universality>
#proofhints[
    Straightforward.
]
#proof[
    The expected description length is #qed-multiline($
        log(n + 1) + EE[-log P_(theta_"MLE")^n (X_1^n)] & <= log(n + 1) + EE[-log P_(theta^*)^n (X_1^n)] \
        & = log(n + 1) + n H(P_(theta^*)).
    $)
]
#definition[
    The *counting code* first describes $theta_"MLE" = k \/ n$ to the decoder, then describes the index of $x_1^n$ in the ordered list of $binom(n, k)$ binary strings containing $k$ $1$s.
]<def:counting-code>
#proposition[
    The description length of the counting code is $
        log(n + 1) + log binom(n, k).
    $
]<prop:counting-code-description-length>
#proofhints[
    Trivial.
]
#proof[
    Trivial.
]
#definition[
    Given a parametric family of distributions ${P_theta: theta in Theta}$, the *uniform mixture* of ${P_theta^n: theta in Theta}$ is the PMF $Q_n$ on $A^n$ defined by $
        Q_n (x_1^n) = integral_0^1 P_theta^n (x_1^n) dif theta.
    $
]<def:uniform-mixture>
#definition[
    The *mixture code* is the Shannon code for the uniform mixture $Q_n$ of the $P_theta^n$.
]<def:mixture-code>
#lemma[
    For all $k, ell in NN_0$, $
        integral_0^1 theta^k (1 - theta)^ell dif theta = (k! ell!)/(k + ell + 1)!.
    $
]<lem:closed-form-expression-for-uniform-mixture-of-bernoullis>
#proof[
    Exercise.
]
#proposition[
    The description length of the mixture code is $
        log(n + 1) + log binom(n, k).
    $
]<prop:mixture-code-description-length>
#proofhints[
    Straightforward.
]
#proof[
    The uniform mixture is $
        Q_n (x_1^n) = integral_0^1 theta^k (1 - theta)^(n - k) dif theta,
    $ where $k$ is the number of $1$s in $x_1^n$. By the above lemma with $ell = n - k$, the description length is #qed-multiline($
        -log Q_n (x_1^n) = -log (k! (n - k)!)/(n + 1)! = log(n + 1) + log binom(n, k).
    $)
]
#definition[
    The *predictive code* describes the message $x_1^n$ in steps instead of describing it all at once: having already communicated $x_1^i$, the encoder and decoder calculate the estimate $
        hat(theta)_i = (k_i + 1)/(i + 2),
    $ where $k_i$ is the number of $1$s in $x_1^i$. Since $hat(theta)_i$ is known to the decoder, the encoder then describes $x_(i + 1)$ using $-log P_(hat(theta)_i)(x_(i + 1))$ bits. This is repeated for each $i = 1, ..., n - 1$.
]<def:predictive-code>
#proposition[
    The description length of the predictive code is $
        log(n + 1) + log binom(n, k),
    $ where $k$ is the number of $1$s in $x_1^n$.
]<prop:predictive-code-description-length>
#proofhints[
    Straightforward.
]
#proof[
    We have $k_0 = 0$ so $hat(theta)_0 = 1 \/ 2$. The description length is $
        sum_(i = 1)^n -log P_(hat(theta)_(i - 1))(x_i) & = sum_(i = 1)^n -log (hat(theta)_(i - 1)^(x_i) (1 - hat(theta)_(i - 1))^(1 - x_i)) \
        & = -sum_(i = 1)^n (x_i log hat(theta)_(i - 1) + (1 - x_i) log(1 - hat(theta)_(i - 1))) \
        & = -sum_(i = 1)^n (x_i log (k_(i - 1) + 1)/(i + 1) + (1 - x_i) log (i - k_(i - 1))/(i + 1)) \
        & = -sum_(i: x_i = 1) log(k_(i - 1)) - sum_(i: x_i = 0) log(i - k_(i - 1)) + sum_(i = 1)^n log(i + 1) \
        & = -log(k_n !) - log((n - k_n)!) + log((n + 1)!) \
        & = log(n + 1) + log binom(n, k).
    $
]
#lemma[
    Let $n in NN$, $0 <= k <= n$ and $p = k \/ n$. Then $
        binom(n, k) <= 1/sqrt(2pi n p(1 - p)) dot 2^(n H(Bern(p))).
    $
]<lem:exponential-upper-bound-on-binomial-coefficient>
#proof[
    Exercise.
]
#definition[
    The *Fisher information* for a parametric family of PMFS ${P_theta: theta in Theta}$ is defined as $
        J(theta) := EE_(X sim P_theta) [(diff / (diff theta) P_theta (X))/(P_theta (X))^2].
    $
]<def:fisher-information>
#proposition[
    The description length of the counting, mixture and predictive codes is bounded above by $
        n H\(hat(P)_n\) + 1/2 log(n J(theta_"MLE")/(2pi)) + 1.
    $ In particular, the price of universality of the counting, mixture and predictive codes is $1/2 log n$ bits.
]<prop:upper-bound-on-price-of-universality-of-counting-mixture-and-predictive-codes>
#proofhints[
    Straightforward.
]
#proof[
    The description length of all three codes is $log(n + 1) + log binom(n, k)$ by @prop:counting-code-description-length, @prop:mixture-code-description-length and @prop:counting-code-description-length. By @lem:exponential-upper-bound-on-binomial-coefficient, we have $
        log binom(n, k) <= n H(hat(P)_n) - 1/2 log(2pi n theta_"MLE" (1 - theta_"MLE")) = n H(hat(P)_n) + 1/2 log(J(theta_"MLE")/(2pi n)),
    $ where $J(dot)$ is the Fisher information of the family of Bernoulli PMFs. This concludes the result.
]
#notation[
    Partitioning the interval $[0, 1]$ into $sqrt(n)$ intervals of length $1 \/ sqrt(n)$, let $theta_"MDL"$ denote the index of the interval that $theta_"MLE"$ belongs to.
]<ntn:mdl-estimator>
#definition[
    The *MDL code* first describes $theta_"MDL"$ to the decoder, then describes $x_1^n$ using the Shannon code for $P_(theta_"MDL")$.
]<def:mdl-code>
#remark[
    Note that we can write the MLE as $
        theta_"MLE" = 1/n sum_(i = 1)^n X_i = theta^* + 1/sqrt(n) (1/sqrt(n) sum_(i = 1)^n (X_i - theta^*)),
    $ where $theta^*$ is the true underlying parameter. The term in the brackets has mean $mu = 0$ and variance $sigma^2 = theta^* (1 - theta^*)$. So by the central limit theorem, $
        theta_"MLE" approx theta^* + 1/sqrt(n) Z, quad Z sim N(mu, sigma^2).
    $ Hence, $theta_"MLE"$ has fluctuations of order $O(1 \/ sqrt(n))$. This suggests the MLE code strategy of describing it with $O(1 \/ n)$ accuracy is too fine-grained, and the MDL code strategy of describing it with $O(1 \/ sqrt(n))$ accuracy is more appropriate.
]
#proposition[
    The description length of the MDL code is $
        n H(hat(P)_n) + 1/2 log n + O(1).
    $ In particular, the price of universality of the MDL code is $1/2 log n$ bits.
]<prop:mdl-code-description-length>
#proofhints[
    Use that $D(P_(theta_"MLE") || P_(theta_"MDL")) = O((theta_"MLE" - theta_"MLE")^2)$ (since $D(P || Q)$ is locally quadratic in $(P - Q)$).
]
#proof[
    By @prop:prob-under-prod-dist-of-string-of-type, we have $
        -log P_(theta_"MDL")^n (x_1^n) = n D(P_(theta_"MLE") || P_(theta_"MDL")) + n H(hat(P)_n).
    $ Since $D(P || Q)$ is locally quadratic in $(P - Q)$, the Taylor expansion gives $
        D(P_(theta_"MLE") || P_(theta_"MDL")) = O((theta_"MLE" - theta_"MLE")^2).
    $ Now by definition, $abs(theta_"MLE" - theta_"MDL") = O(1 \/ sqrt(n))$. Thus, $
        n D(P_(theta_"MLE") || P_(theta_"MDL")) = O(1),
    $ which concludes the result.
]


= Redundancy and the price of universality

== Redundancy

#definition[
    Suppose $x_1^n in A^n$ is generated by a memoryless source with PMF $P$ on a finite alphabet $A$, with $abs(A) = m$. The *redundancy* on $x_1^n$ of a code with length function $L_n$ is the difference between $L_n (x_1^n)$ and the target compression of $-log P^n (x_1^n)$ bits (the ideal Shannon codelength with respect to $P^n$), so is given by $
        L_n (x_1^n) - (-log P^n (x_1^n)).
    $ If we use the Shannon code with respect to an arbitrary PMF $Q_n$ on $A^n$, the redundancy is $
        rho_n (x_1^n; P, Q_n) = -log Q_n (x_1^n) - (-log P^n (x_1^n)) = log (P^n (x_1^n))/(Q^n (x_1^n)).
    $
]<def:redundancy>
#remark[
    Note that by the @thm:codes-distributions-correspondence, we can restrict our attention to (ideal) Shannon codes (assuming that we ignore integer codelength constraints).
]
#definition[
    The *worst-case maximal redundancy* of the Shannon code with respect to $Q_n$ is its largest redundancy over all strings and all source distributions: $
        sup_(P in cal(P)) max_(x_1^n in A^n) log (P^n (x_1^n))/(Q_n (x_1^n)).
    $
]<def:worst-case-maximal-redundancy>
#definition[
    The *minimax maximal redundancy* $rho_n^*$ over the class of all IID source distributions on $A^n$ is the shortest possible worst-case maximal redundancy: $
        rho_n^* = inf_(Q_n) sup_(P in cal(P)) max_(x_1^n in A^n) log (P^n (x_1^n))/(Q_n (x_1^n)).
    $
]<def:minimax-maximal-redundancy>
#definition[
    The *worst-case average redundancy* of the Shannon code with respect to $Q_n$ is its largest average redundancy over all source distributions: $
        sup_(P in cal(P)) EE_(X_1^n sim P^n) [log (P^n (X_1^n))/(Q_n (X_1^n))] = sup_(P in cal(P)) D(P^n || Q_n).
    $
]<def:worst-case-average-redundancy>
#definition[
    The *minimax average redundancy* over the class of all IID source distributions on $A^n$ is the shortest possible worst-case average redundancy $
        overline(rho)_n = inf_(Q_n) sup_(P in cal(P)) D(P^n || Q_n).
    $
]

== Shtarkov's upper bound

#theorem("Normalised Maximum Likelihood Code")[
    Let ${P_theta: theta in Theta}$ be a parametric family of distributions on a finite alphabet $B$. Denote the minimax maximal redundancy over ${P_theta: theta in Theta}$ by $
        rho^* (Theta) := inf_Q sup_(theta in Theta) max_(x in B) log (P_theta (x))/Q(x).
    $ Then $rho^* (Theta) = log Z$, where $
        Z = sum_(x in B) sup_(theta in Theta) P_theta (x).
    $
]<thm:normalised-maximum-likelihood-code>
#proofhints[
    - For $<=$, consider a suitable distribution $Q^*$ which is defined using $Z$.
    - For $>=$, use that for every $Q$, $Q(x) <= Q^* (x)$ for at least one $x$.
]
#proof[
    Define the distribution $Q^*$ on $B$ by $Q^* (x) = 1/Z sup_(theta in Theta) P_theta (x)$. We have $
        rho^* (Theta) & <= sup_(theta in Theta) max_(x in B) log (P_theta (x))/(Q^* (x)) \
        & = max_(x in B) sup_(theta in Theta) log (P_theta (x))/(Q^* (x)) \
        & = max_(x in B) log (sup_(theta in Theta) P_theta (x))/(Q^* (x)) = max_(x in B) log Z = log Z.
    $ For the lower bound, note that for every $Q$, $Q(x) <= Q^* (x)$ for at least one $x$, say $x^*$. Therefore, $
        sup_(theta in Theta) max_(x in B) log (P_theta (x))/Q(x) >= sup_(theta in Theta) log (P_theta (x^*))/(Q(x^*)) >= sup_(theta in Theta) log (P_theta (x^*))/(Q^* (x^*)) = log (sup_(theta in Theta) P_theta (x^*))/(Q^* (x^*)) = log Z.
    $ Taking the minimum over all $Q$ gives that $rho^* (Theta) >= log Z$ which concludes the result.
]
#definition[
    The *Gamma function* is defined as $
        Gamma(z) := integral_0^oo x^(z - 1) e^(-x) dif x.
    $ Note that for all $n in NN$, $Gamma(n + 1) = n!$.
]<def:gamma-function>
#theorem("Shtarkov")[
    The minimax maximal redundancy over the class of all memoryless sources on $A$ satisfies, for all $n in NN$, $
        rho_n^* <= (m - 1)/2 log (n / 2) + log Gamma(1 \/ 2)/Gamma(m \/ 2) + C' / sqrt(n)
    $ for a constant $C$ depending only on $m$.
]<thm:shtarkov>
#proof("Sketch")[
    // Consider the $(m - 1)$-dimensional parametric family $cal(P) = {P_theta^n: theta in Theta}$, where $Theta = {theta in [0, 1]^(m - 1): sum_(i = 1)^(m - 1) theta_i <= 1}$ and writing $A = {a_1, ..., a_m}$, $
    //     P_theta (a_i) = cases(
    //         theta_i quad & "if" i != m,
    //         1 - sum_(j = 1)^(m - 1) theta_j quad & "if" i = m
    //     ).
    // $ Then applying the previous theorem to this parametric family consisting of all memoryless sources on $A$ gives $
    //         rho_n^* = log(sum_(x_1^n) max_theta P_theta^n (x_1^n)) = log(sum_(x_1^n) hat(P)_(x_1^n)^n (x_1^n))
    //     $ Evaluating this (after some length calculations) gives the result.
    By @thm:normalised-maximum-likelihood-code applied to the parametric family of all IID distributions $P^n$ on $A^n$, we have $
        rho_n^* = log (sum_(x_1^n in A^n) sup_P P^n (x_1^n)).
    $ By @prop:prob-under-prod-dist-of-string-of-type, the MLE in this family is the empirical distribution $hat(P)_n = hat(P)_(x_1^n)$, so $
        rho_n^* = log (sum_(x_1^n in A^n) hat(P)_(x_1^n)^n (x_1^n)).
    $ Evaluating this (after some length calculations) gives the result.
]

== Rissanen's lower bound

#definition[
    Let ${W(y | x): x in A, y in B}$ be a family of conditional PMFs $W(dot | x)$, describing the distribution of the output $y$ of a discrete *channel* with input $x$. The *capacity* of the channel is $
        C = sup I(X; Y),
    $ where the supremum is over all jointly distribution RVs $(X, Y)$, where $X$ has an arbitrary distribution and the distribution of $Y$ given $X$ is $PP(Y = y | X = x) = W(y | x)$.
]<def:channel-capacity>
#theorem("Redundancy-capacity Theorem")[
    Let $cal(P) = {P_theta: theta in Theta}$ be a "nice" parametric family of distributions on a finite alphabet $B$. Denote the minimax average redundancy over ${P_theta: theta in Theta}$ by $
        overline(rho)(Theta) := min_Q max_(theta in Theta) D(P_theta || Q).
    $ Then $overline(rho)(Theta)$ is equal to the capacity of the channel with input $theta$ and output $X sim P_theta$: $
        overline(rho)(Theta) = max_pi I(T; X),
    $ where the maximum is over all probability distributions $pi$ on $Theta$, $T sim pi$ and $X | T = theta sim P_theta$ (so the pair of RVs $(T, X)$ has joint distribution $pi(theta) P_theta (x)$).
]
#proof[
    Omitted (non-examinable).
]
#definition[
    The standard parameterisation of the set of PMFS on $A = {a_1, ..., a_m}$ is ${P_theta: theta in Theta}$, where $Theta = {theta in [0, 1]^(m - 1): sum_(i = 1)^(m - 1) theta_i <= 1}$ and $
        P_theta (a_i) = cases(
            theta_i quad & "if" i != m,
            1 - sum_(j = 1)^(m - 1) theta_j quad & "if" i = m
        ).
    $
]
#theorem("Rissanen")[
    Let ${Q_n: n in NN}$ be an arbitrary sequence of distributions on $A^n$, where $abs(A) = m$. Then for all $epsilon > 0$, there exists a constant $C$ and a subset $Theta_0 subset.eq Theta$ of volume less than $epsilon$ such that for all $theta in.not Theta_0$, $
        D(P_theta^n || Q_n) >= (m - 1)/2 log n - C quad "eventually".
    $ In particular, $overline(rho)_n >= (m - 1)/2 log n - C'$ eventually for some constant $C'$.
]
#proof[
    Non-examinable.
]
#corollary[
    We have (eventually) $
        (m - 1)/2 log n - C' <= overline(rho)_n <= rho_n^* <= (m - 1)/2 log n + C
    $ for some constants $C, C'$.
]
#remark[
    The above bound has a probabilistic interpretation: there exists a sequence of distributions ${Q_n: n in NN}$ which are "uniformly close" to all product distributions: $
        -log Q_n (x_1^n) approx -log P^n (x_1^n) + (m - 1)/2 log n,
    $ for all $P in cal(P)$ and $x_1^n in A^n$. Moreover, the error term $(m - 1)/2 log n$ is the best possible (up to addition of constants).
]