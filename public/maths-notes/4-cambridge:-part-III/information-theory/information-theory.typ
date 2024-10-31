#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let Bern = math.op("Bern")
#let sim = sym.tilde
#let Pois = math.op("Pois")

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
#theorem("Fixed-rate coding theorem")[
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


= Relative entropy

#definition[
    Suppose $x_1^n in A^n$ are observations generated by IID RVs $X_1^n$ and we want to decide whether $X_1^n sim P^n$ or $Q^n$, for two distinct candidate PMFs $P, Q$ on $A$. A *hypothesis test* is described by a *decision region* $B_n subset.eq A^n$ such that
    - If $x_1^n in B_n$, then we declare that $X_1^n sim P^n$.
    - Otherwise, if $x_1^n in.not B_n$, then we declare that $X_1^n sim Q^n$.

]<def:hypothesis-test>
#definition[
    The associated *error probabilities* for a hypothesis test are $
        e_1^((n)) = e_1^((n)) (B_n) & := Pr("declare" P | "data" sim Q) = Q^n (B_n) \
        e_2^((n)) = e_2^((n)) (B_n) & := Pr("declare" Q | "data" sim P) = P^n (B_n^c).
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
        - Then the convergence in probability of $1/n sum_(i = 1)^n log P(X_i)/Q(X_i)$ is equivalent to $Pr(X_1^n in.not B_n^*) = P^n (B_n^* (epsilon)) = e_2^((n)) -> 0$ as $n -> oo$, when $X_1^n sim P^n$.
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
    Use Jensen's inequality with $X$ the RV such that $Pr(X = a_i/b_i) = b_i / (sum_(j = 1)^n b_j)$ for all $i in [n]$, and a suitable $f$.
]
#proof[
    - Define $
        f(x) = cases(
            x log x quad & "if" x > 0,
            0 & "otherwise"
        ).
    $ $f$ is strictly convex.
    - Let $A = sum_i a_i$, $B = sum_i b_i$. Let $X$ be the RV with $Pr(X = a_i/b_i) = b_i / B$ for all $i in [n]$.
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
    Note that $P_(Y | X)(y | x) = Pr(Y = y | X = x) = PP(Y = y, X = x)/PP(X = x) = P_(X, Y)(x, y) P_X (x)$. Hence $
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
#example[
    For any function $g$ on $Y$, we have $X - Y - g(Y)$.
]
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
]
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
    Let $X$ and $Y$ be RVs on respective alphabets $A$ and $B$. Suppose we are interested in the RV $X$ but only are allowed to observe the possibly correlated RV $Y$. Consider the estimate $hat(X) = f(Y)$, with probability of error $P_e := Pr\(hat(X) != X\)$. Then $ H(X | Y) <= h(P_e) + P_e log (abs(A) - 1), $ where $h$ is the binary entropy function.
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
]<thm:data-processing-inequality-for-relative-entropy>
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

#theorem[
    Let $X_1, ..., X_n$ be IID RVs with each $X_i sim Bern(lambda\/n)$, let $S_n = X_1 + dots.c + X_n$. Then $P_(S_n) -> Pois(lambda)$ in distribution as $n -> oo$, i.e. $forall k in NN$, $
        Pr(S_n = k) -> e^(-lambda) lambda^k / n! quad "as" n -> oo
    $
]<thm:binomial-converges-to-poisson>
#remark[
    Using information theory, we can derive stronger and more general statements than the one above.
]
#theorem[
    Let $X_1, ..., X_n$ be (not necessarily independent) RVs with each $X_i sim Bern(p_i)$. Let $S_n = sum_(i = 1)^n X_i$ and $lambda = sum_(i = 1)^n p_i = EE[S_n]$. Then $
        D_e (P_(S_n) || Pois(lambda)) <= sum_(i = 1)^n p_i^2 + (sum_(i = 1)^n H(X_i) - H(X_1^n)).
    $
]
#proof[
    Let $Z_i = Pois(p_i)$ for each $i in [n]$ be independent Poisson RVs so that $T_n = sum_(i = 1)^n Z_i sim Pois(lambda)$. Then $
        D_e (P_(S_n) || Pois(lambda)) & = D_e (P_(S_n) || P_(T_n)) \
        & <= D_e (P_(X_1^n) || P_(Z_1^n)) quad "by data-processing" \
        & = sum_(x_1^n in A^n) P_(X_1^n) (x_1^n) ln ((P_(X_1^n) (x_1^n))/(P_(Z_1^n)(z_1^n)) dot (product_(i = 1)^n P_(X_i)(z_i))/(product_(i = 1)^n P_(X_i)(z_i))) \
        & = sum_(x_1^n in A^n) P_(X_1^n) (x_i) ln (product_(i = 1)^n (P_(X_i)(x_i))/(P_(Z_i)(x_i))) + sum_(x_1^n in A^n) P_(X_1^n) (x_1^n) ln 1/(product_(i = 1)^n P_(X_i)(x_i)) - H_e (X_1^n) \
        & = sum_(i = 1)^n D_e (P_(X_i) || P_(Z_i)) + sum_(i = 1)^n H_e (X_i) - H_e (X_1^n)
    $ Now note that $D_e (P_(X_i) || P_(Z_i)) = D_e (Bern(p_i) || Pois(p_i))$
]
#corollary[
    Let $X_1, ..., X_n$ be independent, with each $X_i sim Bern(p_i)$. Then $
        D_e (P_(S_n) || Pois(lambda)) <= sum_(i = 1)^n p_i^2
    $ and it is known that $P_(S_n) -> Pois(lambda)$ iff $sum_(i = 1)^n p_i^2 -> 0$.
]
#example[
    If each $p_i = lambda/n$, then $D_e (P_("Bin"(n, lambda\/n)) || Pois(lambda)) <= lambda^2 \/ n$.
]