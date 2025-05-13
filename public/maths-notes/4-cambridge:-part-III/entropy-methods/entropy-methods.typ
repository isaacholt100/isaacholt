#import "../../template.typ": *
#import "@preview/cetz:0.3.4" as cetz: canvas, draw
#import "../../diagram-style.typ": *

#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Entropy Methods in Combinatorics Notes",
    author: "Isaac Holt",
    keywords: ("combinatorics", "entropy"),
)

#let line-style(color) = (fill: color, stroke: color, mark: (end: ">"))

#let sim = sym.tilde
#let per = math.op("per")

= The Khinchin axioms for entropy

Note all random variables we deal with will be discrete, unless otherwise stated. We use $log = log_2$.

== Entropy axioms

#definition[
    The *entropy* of a discrete random variable $X$ is a quantity $H(X)$ that takes real values and satisfies the *Khinchin axioms*: @axm:normalisation, @axm:invariance, @axm:extendability, @axm:maximality, @axm:continuity and @axm:additivity.
]<def:entropy-axioms>
#axiom("Normalisation")[
    If $X$ is uniform on ${0, 1}$ (i.e. $X sim "Bern"(1\/2)$), then $H(X) = 1$.
]<axm:normalisation>
#axiom("Invariance")[
    If $X$ takes values in $A$, $Y$ takes values in $B$, $f: A -> B$ is a bijection and $PP(X = a) = PP(Y = f(a))$ for all $a in A$, then $H(Y) = H(X)$ (i.e. the entropy of $X$ depends only on its distribution).
]<axm:invariance>
#axiom("Extendability")[
    If $X$ takes values on a set $A$, $B$ is disjoint from $A$, $Y$ takes values in $A union.sq B$, and for all $a in A$, $PP(Y = a) = PP(X = a)$, then $H(Y) = H(X)$.
]<axm:extendability>
#axiom("Maximality")[
    If $X$ takes values in a finite set $A$ and $Y$ is uniformly distributed in $A$, then $H(X) <= H(Y)$.
]<axm:maximality>
#definition[
    The *total variance distance* between $X$ and $Y$ is $
        sup_(E) abs(PP(X in E) - PP(Y in E)).
    $
]<def:total-variation-distance>
#axiom("Continuity")[
    $H$ depends continuously on $X$ (with respect to total variation distance).
]<axm:continuity>
#definition[
    Let $X$ and $Y$ be random variables. The *conditional entropy* of $X$ given $Y$ is $
        H(X | Y) := sum_(y) PP(Y = y) H(X | Y = y).
    $
]<def:conditional-entropy>
#axiom("Additivity")[
    $H(X, Y) := H((X, Y)) = H(Y) + H(X | Y)$.
]<axm:additivity>

== Properties of entropy

#lemma[
    If $X$ and $Y$ are independent, then $H(X, Y) = H(X) + H(Y)$.
]<lem:entropy-of-two-independent-variables-is-sum-of-entropies>
#proofhints[
    Straightforward.
]
#proof[
    $H(X | Y) & = sum_(y) PP(Y = y) H(X | Y = y)$ Since $X$ and $Y$ are independent, the distribution of $X$ is unaffected by knowing $Y$, so $H(X | Y = y) = H(X)$ for all $y$, which gives the result. (Note we have implicitly used @axm:invariance here).
]
#corollary[
    If $X_1, ..., X_n$ are independent, then $
        H(X_1, ..., X_n) = H(X_1) + dots.c + H(X_n).
    $
]<crl:entropy-of-independent-variables-is-sum-of-entropies>
#proofhints[
    Straightforward.
]
#proof[
    By @lem:entropy-of-two-independent-variables-is-sum-of-entropies and induction.
]
#lemma("Chain Rule")[
    Let $X_1, ..., X_n$ be RVs. Then $
        H(X_1, ..., X_n) = H(X_1) + H(X_2 | X_1) + H(X_3 | X_1, X_2) + dots.c + H(X_n | X_1, ..., X_(n - 1)).
    $
]<lem:chain-rule>
#proofhints[
    Straightforward.
]
#proof[
    The case $n = 2$ is @axm:additivity. In general, $
        H(X_1, ..., X_n) = H(X_1, ..., X_(n - 1)) + H(X_n | X_1, ..., X_(n - 1)),
    $ so the result follows by induction.
]
#lemma[
    Let $X$ and $Y$ be RVs. If $Y = f(X)$, then $H(X, Y) = H(X)$. Also, $H(Z | X, Y) = H(Z | X)$.
]<lem:data-processing-adds-no-information>
#proofhints[
    Consider an appropriate bijection.
]
#proof[
    The map $g: x |-> (x, f(x))$ is a bijection, and $(X, Y) = g(X)$, so the first statement follows from @axm:invariance. Also, $
        H(Z | X, Y) & = H(Z, X, Y) - H(X, Y) quad "by additivity" \
        & = H(Z, X) - H(X) quad "by first part" \
        & = H(Z | X) quad "by additivity"
    $
]
#lemma[
    If $X$ takes only one value, then $H(X) = 0$.
]<lem:single-valued-random-variables-have-zero-entropy>
#proofhints[
    Consider an independent copy of $X$.
]
#proof[
    Let $X'$ be an independent copy of $X$. $(X, X')$ takes only one value, so $H(X, X') = H(X)$ by @axm:invariance. But by independence, $H(X, X') = H(X) + H(X') = 2 H(X)$, so $H(X) = 0$.
]
#proposition[
    If $X$ is uniformly distributed on a set of size $2^n$, then $H(X) = n$.
]<prop:uniformly-distributed-random-variable-on-n-bits-has-n-entropy>
#proofhints[
    Straightforward.
]
#proof[
    Let $X_1, ..., X_n$ be independent RVs, uniformly distributed on ${0, 1}$. By @crl:entropy-of-independent-variables-is-sum-of-entropies and @axm:normalisation, $H(X_1, ..., X_n) = n$. So the result follows by @axm:invariance.
]
#proposition[
    If $X$ is uniformly distributed on a set $A$ of size $n$, then $H(X) = log n$.
]<prop:entropy-of-uniform-rv-is-log-of-support-size>
#proofhints[
    Straightforward.
]
#proof[
    Let $r in NN$ and let $X_1, ..., X_r$ be independent copies of $X$. Then $(X_1, ..., X_r)$ is uniform on $A^r$, and $H(X_1, ..., X_r) = r H(X)$. Now pick $k$ such that $2^k <= n^r <= 2^(k + 1)$. Then by @prop:uniformly-distributed-random-variable-on-n-bits-has-n-entropy, @axm:invariance and @axm:maximality, $k <= r H(X) <= k + 1$. So $k / r <= log n <= (k + 1) / r$ and $k / r <= H(X) <= (k + 1)/r$ for all $r in NN$. So $H(X) = log n$, as claimed.
]
#theorem("Khinchin")[
    If $H$ satisfies the Khinchin axioms and $X$ takes values in a finite set $A$, then $
        H(X) = sum_(a in A) p_a log (1 \/ p_a) = EE[log 1/(P_X (X))],
    $ where $p_a = PP(X = a)$.
]<thm:khinchin>
#proofhints[
    - Explain why it is enough to prove for when the $p_a$ are rational.
    - Pick $n in NN$ such that $p_a = m_a / n$, $m_a in NN_0$. Let $Z$ be uniform on $[n]$. Let ${E_a: a in A}$ be a partition of $[n]$ such that $X = a <=> Z in E_a$.
    - Consider $H(Z | X)$.
]
#proof[
    First we do the case where all $p_a in QQ$. Pick $n in NN$ such that $p_a = m_a / n$, $m_a in NN_0$. Let $Z$ be uniform on $[n]$. Let ${E_a: a in A}$ be a partition of $[n]$ into sets with $abs(E_a) = m_a$. By @axm:invariance, we may assume that $X = a <=> Z in E_a$. Then $
        log n = H(Z) & = H(Z, X) = H(X) + H(Z | X) \
        & = H(X) + sum_(a in A) p_a H(Z | X = a) \
        & = H(X) + sum_(a in A) p_a log m_a \
        & = H(X) + sum_(a in A) p_a (log p_a + log n) \
        & = H(X) + sum_(a in A) p_a log p_a + log n.
    $ Hence $H(X) = -sum_(a in A) p_a log p_a$.

    The general result follows by @axm:continuity.
]
#corollary[
    Let $X$ and $Y$ be random variables. Then $0 <= H(X)$ and $0 <= H(X | Y)$.
]<crl:entropy-non-negativity>
#proofhints[
    Trivial.
]
#proof[
    Immediate consequence of @thm:khinchin.
]
#corollary[
    If $Y = f(X)$, then $H(Y) <= H(X)$.
]<crl:data-processing>
#proofhints[
    Straightforward.
]
#proof[
    $H(X) = H(X, Y) = H(Y) + H(X | Y)$. But $H(X | Y) >= 0$.
]
#proposition("Subadditivity")[
    Let $X$ and $Y$ be RVs. Then $H(X, Y) <= H(X) + H(Y)$.
]<prop:subadditivity>
#proofhints[
    - Let $p_(a b) = PP(X = a, Y = b)$. Explain why it is enough to show for the case when the $p_(a b)$ are rational.
    - Pick $n$ such that $p_(a b) = m_(a b) \/ n$ with each $m_(a b) in NN_0$. Partition $[n]$ into sets $E_(a b)$ of size $m_(a b)$. Let $Z$ be uniform on $[n]$.
    - Show that if $X$ (or $Y$) is uniform, then $H(X | Y) <= H(X)$ and $H(X, Y) <= H(X) + H(Y)$.
    - Let $E_b = union_a E_(a b)$ for each $b$. We can assume $Y = b$ iff $Z in E_b$. Now define an RV $W$ as follows: if $Y = b$, then $W$ is uniformly distributed in $E_b$. Use conditional independence of $X$ and $W$ given $Y$ to conclude the result.
]
#proof[
    Note that for any two RVs $X, Y$, $
        H(X, Y) & <= H(X) + H(Y) \
        <==> H(X | Y) & <= H(X) \
        <==> H(Y | X) & <= H(Y)
    $ by @axm:additivity. Next, observe that $H(X | Y) <= H(X)$ if $X$ is uniform on a finite set, since $H(X | Y) = sum_y PP(Y = y) H(X | Y = y) <= sum_y PP(Y = y) H(X) = H(X)$ by @axm:maximality. By the above equivalence, we also have $H(X | Y) <= H(X)$ if $Y$ is uniform on a finite set. Now let $p_(a b) = PP(X = a, Y = b)$, and assume that all $p_(a b)$ are rational. Pick $n$ such that $p_(a b) = m_(a b) \/ n$ with each $m_(a b) in NN_0$. Partition $[n]$ into sets $E_(a b)$ of size $m_(a b)$. Let $Z$ be uniform on $[n]$. WLOG (by @axm:invariance), $(X, Y) = (a, b)$ iff $Z in E_(a b)$.

    Let $E_b = union_a E_(a b)$ for each $b$. So $Y = b$ iff $Z = E_b$. Now define an RV $W$ as follows: if $Y = b$, then $W in E_b$, but then $W$ is uniformly distributed in $E_b$ and independent of $X$ (and $Z$). So $W$ and $X$ are conditionally independent given $Y$, and $W$ is uniform on $[n]$. Then $H(X | Y) = H(X | Y, W) = H(X | W)$ by conditional independence and by @lem:data-processing-adds-no-information (since $W$ determines $Y$). Since $W$ is uniform, $H(X | W) <= H(X)$.

    The general result follows by @axm:continuity.
]
#corollary[
    $H(X) >= 0$ for any $X$.
]
#proofhints[
    (Without using the formula) straightforward.
]
#proof[
    (Without using the formula). By subadditivity, $H(X | X) <= H(X)$. But $H(X | X) = 0$.
]
#corollary[
    Let $X_1, ..., X_n$ be RVs. Then $
        H(X_1, ..., X_n) <= H(X_1) + dots.c + H(X_n).
    $
]<crl:generalised-subadditivity>
#proofhints[
    Trivial.
]
#proof[
    Trivial by induction.
]
#proposition("Submodularity")[
    Let $X, Y, Z$ be RVs. Then $
        H(X | Y, Z) <= H(X | Z).
    $
]<prop:submodularity>
#proofhints[
    Use that $H(X | Y, Z = z) <= H(X | Z = z)$ (why?).
]
#proof[
    $H(X | Y, Z) = sum_z PP(Z = z) H(X | Y, Z = z) <= sum_z PP(Z = z) H(X | Z = z) = H(X | Z)$ by @prop:subadditivity.
]
#remark[
    @prop:submodularity can be expressed in several equivalent ways. Expanding using @axm:additivity gives $
        H(X, Y, Z) - H(Y, Z) <= H(X, Z) - H(Z)
    $ and $
        H(X, Y, Z) <= H(X, Z) + H(Y, Z) - H(Z)
    $ and $
        H(X, Y, Z) + H(Z) <= H(X, Z) + H(Y, Z).
    $
]
#lemma[
    Let $X, Y, Z$ be RVs with $Z = f(Y)$. Then $H(X | Y) <= H(X | Z)$.
]<lmm:conditional-data-processing>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        H(X | Y) & = H(X, Y) - H(Y) = H(X, Y, Z) - H(Y, Z) \
        & <= H(X, Z) - H(Z) = H(X | Z)
    $ by @prop:submodularity.
]
#lemma[
    Let $X, Y, Z$ be RVs with $Z = f(X) = g(Y)$. Then $
        H(X, Y) + H(Z) <= H(X) + H(Y).
    $
]<lmm:subadditivity-with-additional-difference>
#proofhints[
    Straightforward.
]
#proof[
    By @prop:submodularity, we have $H(X, Y, Z) + H(Z) <= H(X, Z) + H(Y, Z)$, which implies the result, since $Z$ depends on $X$ and $Y$.
]
#lemma[
    Let $X$ be an RV taking values in a finite set $A$ and let $Y$ be uniform on $A$. If $H(X) = H(Y)$, then $X$ is uniform.
]<lmm:entropy-is-maximal-only-if-x-is-uniform>
#proofhints[
    Use Jensen's inequality.
]
#proof[
    Let $p_a = PP(X = a)$. Then $
        H(X) = sum_(a in A) p_a log(1 \/ p_a) = abs(A) dot EE_(a in A) p_a log(1 / p_a).
    $ The function $x |-> x log (1 \/ x)$ is concave on $[0, 1]$. So by Jensen's inequality, $
        H(X) <= abs(A) dot (EE_(a in A) p_a) dot log (1 / (EE_(a in A) p_a)) = log abs(A) = H(Y),
    $ with equality iff $a |-> p_a$ is constant, i.e. $X$ is uniform.
]
#corollary[
    If $H(X, Y) = H(X) + H(Y)$, then $X$ and $Y$ are independent.
]<crl:joint-entropy-maximised-only-if-independent>
#proofhints[
    Go through the proof of @prop:subadditivity and check when equality holds.
]
#proof[
    We go through the proof of subadditivity and check when equality holds. Suppose that $X$ is uniform on $A$. Then $
        H(X | Y) = sum_y PP(Y = y) H(X | Y = y) <= H(X),
    $ with equality iff $X | Y = y$ is uniform on $A$ for all $y$ (by @lmm:entropy-is-maximal-only-if-x-is-uniform), which implies that $X$ and $Y$ are independent.

    At the last stage of the proof, we said $H(X | Y) = H(X | Y, W) = H(X | W) <= H(X)$, where $W$ was uniform, i.e. $H(W | X) <= H(W)$. So equality holds only if $X$ and $W$ are independent, which implies (since $Y$ depends on $W$), that $X$ and $Y$ are independent.
]
#definition[
    Let $X$ and $Y$ be RVs. The *mutual information* $
        I(X : Y) & := H(X) + H(Y) - H(X, Y) \
        & = H(X) - H(X | Y) \
        & = H(Y) - H(Y | X).
    $
]<def:mutual-information>
#remark[
    @prop:subadditivity is equivalent to the statement that $I(X: Y) >= 0$, and @crl:joint-entropy-maximised-only-if-independent implies that $I(X : Y) = 0$ iff $X$ and $Y$ are independent.

    Note that $H(X, Y) = H(X) + H(Y) - I(X : Y)$ (note the similarity to the inclusion-exclusion formula for two sets).
]
#definition[
    Let $X, Y, Z$ be RVs. The *conditional mutual information* of $X$ and $Y$ given $Z$ is $
        I(X : Y | Z) & := sum_z PP(Z = z) I(X | Z = z : Y | Z = z) \
        & = sum_z PP(Z = z) (H(X | Z = z) + H(Y | Z = z) - H(X, Y | Z = z)) \
        & = H(X | Z) + H(Y | Z) - H(X, Y | Z) \
        & = H(X, Z) + H(Y, Z) - H(X, Y, Z) - H(Z).
    $ @prop:submodularity is equivalent to the statement that $I(X : Y | Z) >= 0$.
]<def:conditional-mutual-information>


= A special case of Sidorenko's conjecture

#definition[
    Let $G$ be a bipartite graph with (finite) vertex sets $X$ and $Y$ and density $alpha$ (defined to be $abs(E(G))/(abs(X) dot abs(Y))$). Let $H$ be another (think of it as small) bipartite graph with vertex sets $U$ and $V$. Now let $phi: U -> X$ and $psi: V -> Y$. We say that $(phi, psi)$ is a *homomorphism* if $phi(x) psi(y) in E(G)$ for every edge $x y in E(H)$.
]<def:bipartite-graph-homomorphism>
#conjecture("Sidorenko's Conjecture")[
    For every $G, H$, for random $phi: U -> X$, $psi: V -> Y$, $
        PP((phi, psi) "is a homomorphism") >= alpha^abs(E(H)).
    $
]<cnj:sidorenko>
#remark[
    @cnj:sidorenko is not hard to prove when $H$ is the complete bipartite graph $K_(r, s)$ (the case $K_(2, 2)$ can be proved using Cauchy-Schwarz: exercise).
]
#theorem[
    @cnj:sidorenko is true if $H$ is a path of length $3$.
]<thm:sidorenko-true-if-h-is-path-of-length-3>
#proofhints[
    - Let $(X_1, Y_1)$ be a random edge of $G$ (with $X_1 in X$, $Y_1 in Y$). Now let $X_2$ be a random neighbour of $Y_1$ and $Y_2$ be a random neighbour of $X_2$. Explain why it suffices to prove that $H(X_1, Y_1, X_2, Y_2) >= log(alpha^3 m^2 n^2)$.
    - Find an equivalent way of choosing a uniformly random edge $(X_1, Y_1)$ of $G$ (in terms of vertices). Use this to reaosn that $X_2 Y_1$ and $X_2 Y_2$ are uniformly random in $E(G)$.
    - Find the lower bound for $H(X_1, Y_1, X_2, Y_2)$ using the @lem:chain-rule and @axm:maximality.
]
#proof[
    We want to show that if $G$ is a bipartite graph of density $alpha$ with vertex sets $X, Y$ of size $m$ and $n$, and we choose $x_1, x_2 in X$, $y_1, y_2 in Y$ independently at random, then $PP(x_1 y_1, y_1 x_2, x_2 y_2 in E(G)) >= alpha^3$.

    It would be enough to let $P$ be a path of length $3$ chosen uniformly at random and show that $H(P) >= log (alpha^3 m^2 n^2)$ (by @prop:entropy-of-uniform-rv-is-log-of-support-size). Instead, we shall define a different RV taking values in the set of all paths of length $3$ (including degenerate paths). To do this, let $(X_1, Y_1)$ be a random edge of $G$ (with $X_1 in X$, $Y_1 in Y$). Now let $X_2$ be a random neighbour of $Y_1$ and $Y_2$ be a random neighbour of $X_2$. It will be enough to prove that $
        H(X_1, Y_1, X_2, Y_2) >= log(alpha^3 m^2 n^2).
    $ We can choose $X_1, Y_1$ in three equivalent ways:
    + Pick an edge uniformly from all edges
    + Pick a vertex $x$ with probability proportional to its degree $deg(x)$, and then a random neighbour $Y$ of $x$.
    + Same as above with $x$ and $y$ exchanged.
    By the equivalence, it follows that $Y_1 = y$ with probability $deg(y) \/ abs(E(G))$, so $X_2 Y_1$ is uniform in $E(G)$, so $X_2 = x'$ with probability $d(x') \/ abs(E(G))$, so $X_2 Y_2$ is uniform in $E(G)$.

    Let $U_A$ be the uniform distribution on $A$. Therefore, by the @lem:chain-rule, $
        H(X_1, Y_1, X_2, Y_2) & = H(X_1) + H(Y_1 | X_1) + H(X_2 | X_1, Y_1) + H(Y_2 | X_1, Y_1, X_2) \
        & = H(X_1) + H(Y_1 | X_1) + H(X_2 | Y_1) + H(Y_2 | X_2) \
        & = H(X_1) + H(X_1, Y_1) - H(X_1) + H(X_2, Y_1) - H(Y_1) + H(X_2, Y_2) - H(Y_2) \
        & = 3 H(U_(E(G))) - H(Y_1) - H(X_2) \
        & >= 3 H(U_(E(G))) - H(U_Y) - H(U_X) \
        & = 3 log(alpha m n) - log n - log m \
        & = log(alpha^3 m^2 n^2).
    $ So we are done, by @axm:maximality (since $H(P) >= H(X_1, Y_1, X_2, Y_2)$). Alternative finish to the proof: let $X', Y'$ be uniform in $X, Y$ and independent of each other and $X_1, Y_1, X_2, Y_2$. Then by the above inequality and @crl:entropy-of-independent-variables-is-sum-of-entropies, $
        H(X_1, Y_1, X_2, Y_2, X', Y') & = H(X_1, Y_1, X_2, Y_2) + H(U_X) + H(U_Y) \
        & >= 3 H(U_(E(G))).
    $ So by @axm:maximality, the number of paths of length $3$ times $abs(X)$ times $abs(Y)$ is $>= abs(E(G))^3$.
]


= Bregman's theorem

#definition[
    Let $A$ be an $n times n$ matrix over $RR$. The *permanent* of $A$ is $
        per(A) := sum_(sigma in S_n) product_(i = 1)^n A_(i sigma(i)),
    $ i.e. "the determinant without the signs".
]<def:matrix-permanent>
#proposition[
    Let $G$ be a bipartite graph with vertex sets $X, Y$ of size $n$. Given $(x, y) in X times Y$, let $
        A_(x y) = cases(1 quad & "if" x y in E(G), 0 quad & "if" x y in.not E(G)),
    $ i.e. $A$ is the bipartite adjacency matrix of $G$. Then $per(A)$ is the number of perfect matchings in $G$. (Note that $per(A)$ is well-defined as it is invariant under reordering of the vertices.)
]<prop:permanent-of-bipartite-adjacency-matrix-is-number-of-perfect-matchings>
#proofhints[
    Straightforward.
]
#proof[
    Each (perfect) matching corresponds to a bijection $sigma: X -> Y$ such that $x sigma(x) in E(G)$ for all $x in X$. $sigma in S_n$ contributes $1$ to the sum iff $x sigma(x)$ is an edge of $G$ for all $x in X$ (i.e. iff $sigma$ corresponds to a perfect matching), and $0$ otherwise.
]
Bregman's theorem concerns how large $per(A)$ can be if $A$ is a $0, 1$ matrix and the sum of the entries in the $i$-th row is $d_i$ (i.e. if the degree of $x_i in X$ is $d_i$).
#example[
    Let $G$ be a disjoint union of $K_(a_i, a_i)$'s, $i = 1, ..., k$, with $a_1 + dots.c + a_k = n$. Then the number of perfect matchings in $G$ is $product_(i = 1)^k a_i !$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                content((-2.5, 1), $X$)
                content((-2.5, -1), $Y$)
                set-style(..line-style(diagram-colors.red), fill: diagram-colors.light-red)
                circle((0, 1), radius: (1.5, 0.5))
                circle((4, 1), radius: (1.5, 0.5))
                content((0, -2), $K_(a_1, a_1)$)
                circle((0, -1), radius: (1.5, 0.5))
                circle((4, -1), radius: (1.5, 0.5))
                content((4, -2), $K_(a_2, a_2)$)
                content((7, 1), $dot dot dot$)
                content((7, -1), $dot dot dot$)
                circle((10, 1), radius: (1.5, 0.5))
                circle((10, -1), radius: (1.5, 0.5))
                content((10, -2), $K_(a_k, a_k)$)

                for i in range(-1, 2) {
                    circle((i / 2, 1), ..point-style, name: "circle-1-t-" + str(i))
                    circle((i / 2, -1), ..point-style, name: "circle-1-b-" + str(i))
                }
                for i in range(-1, 2) {
                    for j in range(-1, 2) {
                        line("circle-1-t-" + str(i), "circle-1-b-" + str(j), mark: none)
                    }
                }

                for i in range(0, 2) {
                    circle((i / 2 - 0.25 + 4, 1), ..point-style, name: "circle-2-t-" + str(i))
                    circle((i / 2 - 0.25 + 4, -1), ..point-style, name: "circle-2-b-" + str(i))
                }
                for i in range(0, 2) {
                    for j in range(0, 2) {
                        line("circle-2-t-" + str(i), "circle-2-b-" + str(j), mark: none)
                    }
                }

                for i in range(-1, 3) {
                    circle((i / 2 - 0.25 + 10, 1), ..point-style, name: "circle-3-t-" + str(i))
                    circle((i / 2 - 0.25 + 10, -1), ..point-style, name: "circle-3-b-" + str(i))
                }
                for i in range(-1, 3) {
                    for j in range(-1, 3) {
                        line("circle-3-t-" + str(i), "circle-3-b-" + str(j), mark: none)
                    }
                }
            }),
        )
    ]
]
#theorem("Bregman")[
    Let $G$ be a bipartite graph with vertex sets $X, Y$ of size $n$. Then the number of perfect matchings in $G$ is at most $
        product_(x in X) (deg(x)!)^(1 \/ deg(x)).
    $
]<thm:brigman>
#proofhints[
    - For an enumeration $x_1, ..., x_n$ of $X$ and random matching (a bijection) $sigma$, show that $H(sigma) <= log deg (x_1) + EE_sigma log deg_(x_1)^sigma (x_2) + dots.c + EE_sigma log deg_(x_1, ..., x_(n - 1))^sigma (x_n)$ (find a suitable expression for $deg_(x_1, ..., x_(i - 1))^sigma (x_i)$).
    - Explain why $
        deg_(x_1, ..., x_(i - 1))^sigma (x_i) = d(x_i) - |{j: sigma^(-1)(y_j) "comes earlier than" x_i "in" x_1, ..., x_n}.
    $
    - Show that the average of $log deg_(x_1, ..., x_(i - 1))^sigma (x_i)$ is $1/d(x) (log(d(x)!))$.
]
#proof("(by Radhakrishnan)")[
    Each (perfect) matching corresponds to a bijection $sigma: X -> Y$ such that $x sigma(x) in E(G)$ for all $x in X$. Let $sigma$ be chosen uniformly from all such bijections. Then by the @lem:chain-rule, $
        H(sigma) & = H(sigma(x_1), ..., sigma(x_n)) \
        & = H(sigma(x_1)) + H(sigma(x_2) | sigma(x_1)) + dots.c + H(sigma(x_n) | sigma(x_1), ..., sigma(x_(n - 1))),
    $ where $x_1, ..., x_n$ is some enumeration of $X$. We have $H(sigma(x_1)) <= log deg(x_1)$ by @axm:maximality, and $
        H(sigma(x_2) | sigma(x_1)) <= EE_sigma log deg_(x_1)^sigma (x_2),
    $ where $deg_(x_1)^sigma (x_2) = abs(N(x_2) \\ {sigma(x_1)})$, by the definition of conditional entropy and @axm:maximality. In general, $
        H(sigma(x_i) | sigma(x_1), ..., sigma(x_(i - 1))) <= EE_sigma log deg_(x_1, ..., x_(i - 1))^sigma (x_i),
    $ where $deg_(x_1, ..., x_(i - 1))^sigma (x_i) = abs(N(x_i) \\ {sigma(x_1), ..., sigma(x_(i - 1))})$.

    Key idea: we now regard $x_1, ..., x_n$ as a _random_ enumeration of $X$ and take the average. For each $x in X$, define the *contribution* of $x$ to be $log(d_(x_1, ..., x_(i - 1))^sigma (x_i))$, where $x_i = x$. We shall now fix $sigma$ and $x in X$. Let the neighbours of $x$ be $y_1, ..., y_k$. Then one of the $y_j$ will be $sigma(x)$, say $y_h$. Then $d_(x_1, ..., x_(i - 1))^sigma (x_i)$ (given that $x_i = x$) is $
        d(x) - abs({j: sigma^(-1)(y_j) "comes earlier than" x = sigma^(-1)(y_h)}).
    $ All positions of $sigma^(-1)(y_h)$ are equally likely, so the average contribution of $x$ is $ // TODO: what do we take this average over?
    // TODO: how are they equally likely? sigma^(-1) (y_h) = x is fixed
        & 1/d(x) (log d(x) + log (d(x) - 1) + dots.c + log(1)) \
        = & 1/d(x) log d(x)!.
    $ By linearity of expectation, $
        H(sigma) <= sum_(x in X) 1/d(x) log(d(x)!)
    $ So the number of matchings is at most $product_(x in X) (d(x)!)^(1 \/ d(x))$.
]
#definition[
    Let $G$ be a graph with $2n$ vertices. A *$1$-factor* in $G$ is a collection of $n$ disjoint edges.
]<def:one-factor>
#theorem("Kahn-Lovasz")[
    Let $G$ be a graph with $2n$ vertices. Then the number of $1$-factors in $G$ is at most $
        product_(x in V(G)) (d(x)!)^(1 \/ 2 d(x)).
    $
]<thm:kahn-lovasz>
#proofhints[
    - Let $M$ be the set of $1$-factors of $G$ and let $(M_1, M_2)$ be a uniformly random element of $M times M$.
    - Given a cover of $G$ by $M_1$ and $M_2$, find an expression for the number of pairs $(M'_1, M'_2)$ that give rise to it, in terms of the number of even cycles.
    - Let $G_2$ be the bipartite graph with two vertex sets $V_1, V_2$, which are both copies of $V(G)$. Join $x in V_1$ to $y in V_2$ iff $x y in E(G)$.
    - Explain why each perfect matching of $G_2$ gives a cover of $V(G)$ by isolated vertices, edges and cycles, and find an expression for the number of such perfect matchings that give rise to it.
]
#proof("(by Alon, Friedman)")[
    Let $M$ be the set of $1$-factors of $G$ and let $(M_1, M_2)$ be a uniformly random element of $M times M$. For each $M_1, M_2$, the union $M_1 union M_2$ is a collection of disjoint edges and even cycles that covers all the vertices of $G$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                let points = ((0, 0), (-1, 2), (0, 3), (1, 2.5), (1, 2), (0, 1), (0, 0))
                for i in range(points.len() - 1) {
                    let edge-color = if calc.rem(i, 2) == 0 {
                        diagram-colors.red
                    } else {
                        diagram-colors.blue
                    }
                    line(points.at(i), points.at(i + 1), stroke: edge-color)
                    circle(points.at(i), ..point-style, fill: black)
                    circle(points.at(i + 1), ..point-style, fill: black)
                }

                line((-2, 0), (-3, 1), stroke: diagram-colors.red)
                hobby((-2, 0), (-2.5, 0.8), (-3, 1), stroke: diagram-colors.blue)
                circle((-2, 0), ..point-style, fill: black)
                circle((-3, 1), ..point-style, fill: black)
            }),
        )
    ]
    Call such a union a *cover of $G$ by edges and even cycles*. If we are given such a cover, then the number of pairs $(M_1, M_2)$ that give rise to it is $2^k$, where $k$ is the number of even cycles. Now let's build a bipartite graph $G_2$ out of $G$. $G_2$ has two vertex sets $V_1, V_2$, which are both copies of $V(G)$. Join $x in V_1$ to $y in V_2$ iff $x y in E(G)$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                let (A, B, C, D, E, F) = ((0, 0), (2, 0), (4, 0), (0, 2), (2, 2), (4, 2))
                for p in (A, B, C, D, E, F) {
                    circle(p, ..point-style, fill: black)
                }
                line(A, E)
                line(A, F)
                line(B, D)
                line(B, F)
                line(C, D)
                line(C, E)
            }),
            caption: [$G_2$ if $G$ is the triangle graph],
        )
    ]
    By @thm:brigman, the number of perfect matchings in $G_2$ is at most $product_(x in V(G)) (d(x)!)^(1 \/ d(x))$. Each matching gives a permutation $sigma$ of $V(G)$ such that $x sigma(x) in E(G)$ for all $x in V(G)$. Each such $sigma$ has a cycle decomposition, and each cycle gives a cycle in $G$. So $sigma$ gives a cover of $V(G)$ by isolated vertices, edges and cycles (not necessarily all even). Given such a cover with $k$ cycles, each cycle can be directed in two ways, so the number of $sigma$ that give rise to it is $= 2^k$. So there is an injection from $M times M$ to the set of matchings of $G_2$, since every cover by edges and and even cycles is a cover by vertices, edges and cycles. So $abs(M)^2 <= product_(x in V(G)) (d(x)!)^(1 \/ d(x))$.
]


= Shearer's lemma and applications

#notation[
    Given a random variable $X = (X_1, ..., X_n)$ and $A subset.eq [n]$, $A = {a_1 < ... < a_k}$, write $X_A$ for the random variable $(X_(a_1), ..., X_(a_k))$.
]
#lemma("Shearer")[
    Let $X = (X_1, ..., X_n)$ be an RV and let $cal(A)$ be a family of subsets of $[n]$ such that every $i in [n]$ belongs to at least $r$ of the sets $A in cal(A)$. Then $
        H(X_1, ..., X_n) <= 1/r sum_(A in cal(A)) H(X_A).
    $
]<lem:shearer>
#proofhints[
    For each $a in [n]$, write $X_(< a)$ for $(X_1, ..., X_(a - 1))$. Show that $H(X_A) >= sum_(a in A) H(X_a | X_(< a))$.
]
#proof[
    For each $a in [n]$, write $X_(< a)$ for $(X_1, ..., X_(a - 1))$. For each $A in cal(A)$, $A = {a_1 < dots.c < a_k}$, by the @lem:chain-rule and @prop:submodularity, $
        H(X_A) & = H(X_(a_1)) + H(X_(a_2) | X_(a_1)) + dots.c + H(X_(a_k) | X_(a_1), ..., X_(a_(k - 1))) \
        & >= H(X_(a_1) | X_(< a_1)) + H(X_(a_2) | X_(< a_2)) + dots.c + H(X_(a_k) | X_(< a_k)) \
        & = sum_(a in A) H(X_a | X_(< a)).
    $ Therefore, $sum_(A in cal(A)) H(X_A) >= r sum_(a = 1)^n H(X_a | X_(< a)) = r H(X)$.
]
#example[
    $H(X_1, X_2, X_3) <= 1/2 (H(X_1, X_2) + H(X_1, X_3) + H(X_2, X_3))$.
]
#lemma[
    Let $X = (X_1, ..., X_n)$ be an RV and let $A subset.eq [n]$ be a randomly chosen subset of $[n]$, according to some probability distribution. Suppose that for each $i in [n]$, $PP(i in A) >= mu$. Then $
        H(X) <= mu^(-1) dot EE_A [H(X_A)].
    $
]<lem:probabilistic-shearer>
#proofhints[
    Very similar to proof of @lem:shearer.
]
#proof[
    As in @lem:shearer, $
        H(X_A) >= sum_(a in A) H(X_a | X_(< a)).
    $ So $
        EE_A [H(X_A)] & >= EE_A [sum_(a in A) H(X_a | X_(< a))] \
        & = EE_A [sum_(k = 1)^n H(X_k | X_(< k)) indicator({k in A})] \
        & = sum_(k = 1)^n H(X_k | X_(< k)) EE[indicator({k in A})] \
        & = sum_(k = 1)^n H(X_k | X_(< k)) PP(k in A) \
        & >= mu dot H(X).
    $
]
#definition[
    Let $E subset.eq ZZ^n$ and let $A subset.eq [n]$. Then we write $P_A E$, if $A = {a_1, ..., a_k}$, for the set of $u in ZZ^A$ such that there exists $v in ZZ^([n] \\ A)$ such that $[u, v] in E$, where $[u, v]$ is $u$ suitably intertwined with $v$.
]<def:projection-onto-subset-of-integers-up-to-n>
#corollary[
    Let $E subset.eq ZZ^n$ and let $cal(A)$ be a family of subsets of $[n]$ such that every $i in [n]$ is contained in at least $r$ sets in $cal(A)$. Then $
        abs(E) <= product_(A in cal(A)) abs(P_A E)^(1 \/ r).
    $
]
#proofhints[
    Straightforward.
]
#proof[
    Let $X$ be a uniformly random element of $E$. Then by @lem:shearer, $
        log abs(E) = H(X) <= 1/r dot sum_(A in cal(A)) H(X_A).
    $ But $X_A$ takes values in $P_A E$, so $H(X_A) <= log abs(P_A E)$ by @axm:maximality. Hence, $
        log abs(E) <= 1/r sum_(A in cal(A)) abs(P_A E).
    $
]
#corollary("Discrete Loomis-Whitney Theorem")[
    If $cal(A) = {[n] \\ {i}: i = 1, ..., n}$, we get $
        abs(E) <= product_(i = 1)^n abs(P_([n] \\ {i}) E)^(1 \/ (n - 1)).
    $
]<crl:discrete-loomis-whitney-theorem>
#theorem[
    Let $G$ be a graph with $m$ edges. Then $G$ has at most $1/6 (2m)^(3 \/ 2)$ triangles.
]<thm:upper-bound-on-number-of-triangles-of-graph>
#remark[
    If $m = binom(n, 2)$, then this bound is fairly sharp.
]
#proofhints[
    Consider a uniformly random triangle with an ordering on the vertices, and use @lem:shearer.
]
#proof[
    Let $(X_1, X_2, X_3)$ be a random triple of vertices such that $X_1 X_2$, $X_1 X_3$ and $X_2 X_3$ are all edges (so pick a random triangle with an ordering of the vertices). Let $t$ be the number of triangles in $G$. By @lem:shearer, $
        log(6t) = H(X_1, X_2, X_3) <= 1/2 (H(X_1, X_2) + H(X_1, X_3) + H(X_2, X_3)).
    $ Each $(X_i, X_j)$ (for $i != j$) is supported in the set of edges of $G$, given a direction, so $H(X_i, X_j) <= log(2m)$ by @axm:maximality.
]
#definition[
    Let $V$ be a set of size $n$ and let $cal(G)$ be a set of graphs, all with vertex set $V$. Then $cal(G)$ is *$Delta$-intersecting* (triangle-intersecting) if $G_1 inter G_2$ contains a triangle for all $G_1, G_2 in cal(G)$.
]<def:triangle-intersecting>
#theorem[
    If $abs(V) = n$, then a $Delta$-intersecting family of graphs with vertex set $V$ has size at most $2^(binom(n, 2) - 2)$.
]
#proofhints[
    - Let $cal(G)$ be a $Delta$-intersecting family. View $G in cal(G)$ as a characteristic function from $V^((2))$ to ${0, 1}$. Let $X = (X_e: e in V^((2)))$ be chosen uniformly at random from $cal(G)$.
    - For each $R subset.eq V$, let $G_R = K_R union K_(V \\ R)$ and define $cal(G)_R = {G inter G_R: G in cal(G)}$. Explain why $cal(G)_R$ is an intersecting family, use this to give upper bound on $abs(cal(G)_R)$.
    - What is the probability that an edge $e$ is in a random $G_R$? By considering $X_(G_R)$ taking values in the above family, conclude.
]
#proof[
    Let $cal(G)$ be a $Delta$-intersecting family and let $X$ be chosen uniformly at random from $cal(G)$. We write $V^((2))$ for the set of (unordered) pairs of elements of $V$. We think of any $G in cal(G)$ as a characteristic function from $V^((2))$ to ${0, 1}$. So $X = (X_e: e in V^((2)))$, $X_e in {0, 1}$ (where we fix an ordering of $V^((2))$). For each $R subset.eq V$, let $G_R$ be the graph $K_R union K_(V \\ R)$. For each $R$, we shall look at the projection $X_(G_R)$, which we can think of as taking values in the set ${G inter G_R: G in cal(G)} =: cal(G)_R$.

    Note that if $G_1, G_2 in cal(G)$, $R subset.eq [n]$, then $G_1 inter G_2 inter G_R != emptyset$, since $G_1 inter G_2$ contains a triangle, which must intersect $G_R$ by the pigeonhole principle (the triangle contains $3$ vertices, one of which is contained in one of the two components of $G_R$). Thus, $cal(G)_R$ is an intersecting family, so has size at most $2^(abs(E(G_R)) - 1)$. By @lem:probabilistic-shearer, $
        H(X) <= 2 dot EE_R [H(X_(G_R))] <= 2 dot EE_R [abs(E(G_R)) - 1] = 2 dot (1/2 binom(n, 2) - 1) = binom(n, 2) - 2,
    $ since each $e$ belongs to $G_R$ with probability $1 \/ 2$ (and so $EE_R [abs(E(G_R))] = 1/2 binom(n, 2)$).
]
#definition[
    Let $G$ be a graph and let $A subset.eq V(G)$. The *edge-boundary* $partial A$ of $A$ is the set of edges $x y$ such that $x in A$, $y in.not A$. If $G = ZZ^n$ or ${0, 1}^n$ and $i in [n]$, the *$i$-th boundary* $partial_i A$ is the set of edges $x y in partial A$ such that $x - y = plus.minus e_i$, i.e. $partial_i A$ consists of edges in the edge-boundary in direction $i$.
]<def:edge-boundary>
#theorem([Edge-isoperimetric Inequality in $ZZ^n$])[
    Let $A subset.eq ZZ^n$ be a finite set. Then $
        abs(partial A) >= 2n dot abs(A)^((n - 1) \/ n).
    $
]<thm:edge-isoperimetic-inequality-in-integer-tuples>
#proofhints[
    Use @crl:discrete-loomis-whitney-theorem, the AM-GM inequality, and a suitable lower bound on $abs(partial_i A)$.
]
#proof[
    By the @crl:discrete-loomis-whitney-theorem, $
        abs(A) & <= product_(i = 1)^n abs(P_([n] \\ {i}) A)^(1 \/ (n - 1)) \
        & = (product_(i = 1)^n abs(P_([n] \\ {i}) A)^(1 \/ n))^(n \/ (n - 1)) \
        & <= (1/n sum_(i = 1)^n abs(P_([n] \\ {i}) A))^(n \/ (n - 1)) quad "by AM-GM inequality"
    $ But $abs(partial_i A) >= 2 abs(P_([n] \\ {i}) A)$ since each fibre contributes at least $2$. So $
        abs(A) & <= (1/(2n) sum_(i = 1)^n abs(partial_i A))^(n \/ (n - 1)) \
        & = (1/(2n) abs(partial A))^(n \/ (n - 1))
    $
]
#theorem("Edge-isoperimetric Inequality in the Cube")[
    Let $A subset.eq {0, 1}^n$ (where we take usual graph on ${0, 1}^n$). Then $
        abs(partial A) >= abs(A) (n - log abs(A)).
    $
]<thm:edge-isoperimetric-inequality-in-the-cube>
#proofhints[
    - Let $X = (X_1, ..., X_n)$ be a uniformly random element of $A$. Write $X_(\\ i) = (X_1, ..., X_(i - 1), X_(i + 1), ..., X_n)$.
    - Use @lem:shearer to show that $sum_(i = 1)^n H(X_i | X_(\\ i)) <= H(X)$.
    - What are the possible values of $abs(P_([n] \\ {i})^(-1)(u))$, and what is $H(X_i | X_(\\ i) = u)$ in each case? How many $u$ satisfy $abs(P_([n] \\ {i})^(-1)(u)) = 1$? Use this to deduce an expression for $H(X_i | X_(\\ i))$.
]
#proof[
    Let $X$ be a uniformly random element of $A$ and write $X = (X_1, ..., X_n)$. Write $X_(\\ i)$ for $(X_1, ..., X_(i - 1), X_(i + 1), ..., X_n)$. By @lem:shearer, $
        H(X) & <= 1/(n - 1) sum_(i = 1)^n H(X_(\\ i)) \
        & = 1/(n - 1) sum_(i = 1)^n (H(X) - H(X_i | X_(\\ i))).
    $ Hence, $sum_(i = 1)^n H(X_i | X_(\\ i)) <= H(X)$. But $
        H(X_i | X_(\\ i) = u) = cases(
            1 & "if" abs(P_([n] \\ {i})^(-1) (u)) = 2,
            0 & "if" abs(P_([n] \\ {i})^(-1) (u)) = 1
        )
    $ (Note that we always have $abs(P_([n] \\ {i})^(-1) (u)) in {0, 1, 2}$). The number of points of the second kind is $abs(partial_i A)$. So $
        H(X_i | X_(\\ i)) & = sum_u PP(X_(\\ i) = u) H(X_i | X_(\\ i = u)) \
        & = sum_(u in.not partial_i A) PP(X_(\\ i) = u) \
        & = 1 - sum_(u in partial_i A) PP(X_(\\ i) = u) \
        & = 1 - abs(partial_i A)/abs(A).
    $ So $
        H(X) & >= sum_(i = 1)^n (1 - abs(partial_i A)/abs(A)) \
        & = n - abs(partial A)/abs(A).
    $ Also, $H(X) = log abs(A)$. So we are done.
]
#definition[
    Let $cal(A)$ be a family of sets of size $d$. The *lower shadow* of $cal(A)$ is $
        partial cal(A) = {B: abs(B) = d - 1, exists A in cal(A) "s.t." B subset.eq A}.
    $
]<def:lower-shadow>
#theorem("Kruskal-Katona")[
    If $abs(cal(A)) = binom(t, d) = (t (t - 1) cdots (t - d + 1))/d!$ for some real number $t$, then $
        abs(partial cal(A)) >= binom(t, d - 1).
    $
]
#proofhints[
    - Let $X = (X_1, ..., X_d)$ be a random ordering of the elements of a uniformly random $A in cal(A)$. Give an expression for $H(X)$.
    - Explain why it is enough to show $H(X_1, ..., X_(d - 1)) >= log((d - 1)! binom(t, d - 1))$.
    - Let $T sim "Bern"(p)$ be independent of $X_1, ..., X_(k - 1)$, and given $X_1, ..., X_(k - 1)$, let $
        X^* = cases(
            X_(k + 1) & "if" T = 0,
            X_k & "if" T = 1
        ).
    $
    - Use that $X_k$ and $X^*$ have the same distribution (why?) to show that $H(X_k | X_(< k)) >= H(X^*, T | X_(<= k)) = h(p) + p H(X_(k + 1) | X_(<= k))$.
    - Find the maximum of the lower bound to show that $H(X_k | X_(< k)) >= log(2^H(X_(k + 1) | X_(<= k)) + 1)$.
    - Using the chain rule and the fact that $log(d! binom(t, d))$ is an increasing function for $t >= d$, show that $r + d - 1 <= t$, and use this to conclude the desired bound on $H(X_(< d))$.
]
#proof[
    Let $X = (X_1, ..., X_d)$ be a random ordering of the elements of a uniformly random $A in cal(A)$. Then $H(X) = log(d! abs(A)) = log(d! binom(t, d))$. Note that $(X_1, ..., X_(d - 1))$ is an ordering of the elements of some $B in partial_i A$, so $
        H(X_1, ..., X_(d - 1)) <= log((d - 1)! abs(partial_i A))
    $ So it's enough to show $H(X_1, ..., X_(d - 1)) >= log((d - 1)! binom(t, d - 1))$. Also, $H(X) = H(X_1, ..., X_(d - 1)) + H(X_d | X_1, ..., X_(d - 1))$ and $H(X) = H(X_1) + H(X_2 | X_1) + dots.c + H(X_d | X_1, ..., X_(d - 1))$. We would like an upper bound for $H(X_d | X_(< d))$. Our strategy will be to obtain a lower bound for $H(X_k | X_(< k))$ in terms of $H(X_(k + 1) | X_(< k + 1))$. We shall prove that $2^H(X_k | X_(< k)) >= 2^H(X_(k + 1) | X_(< k + 1)) + 1$ for all $k$.

    Let $T$ be chosen independently of $X$. Let $T sim "Bern"(1 - p)$ ($T = 0$ with probability $p$, $p$ is to be chosen later). Given $X_1, ..., X_(k - 1)$, let $
        X^* = cases(
            X_(k + 1) & "if" T = 0,
            X_k & "if" T = 1
        )
    $ Note that $X_k$ and $X_(k + 1)$ have the same distribution (given $X_1, ..., X_(k - 1)$), so $X^*$ does as well. Then $ // TODO: why do we need the "given" bit?
        H(X_k | X_(< k)) & = H(X^* | X_(< k)) "since" X_k sim X^* \
        & >= H(X^* | X_(<= k)) quad #[by @prop:submodularity] \
        & = H(X^*, T | X_(<= k)) quad #[since $X_(<= k)$ and $X^*$ determine $T$ (since $X_(k + 1) != X_k$)] \
        & = H(T | X_(<= k)) + H(X^* | T, X_(<= k)) quad #[by @axm:additivity] \
        & = H(T) + p H(X^* | X_(<= k), T = 0) + (1 - p) H(X^* | X_(<= k), T = 1) \
        & = H(T) + p H(X_(k + 1) | X_(<= k)) + (1 - p) H(X_k | X_(<= k)) \
        & = h(p) + p s.
    $ where $s = H(X_(k + 1) | X_(<= k))$ and $h(p) = p log 1/p + (1 - p) log 1/(1 - p)$. This is maximised when $p = 2^s / (2^s + 1)$. Then we get $
        2^s / (2^s + 1) (log(2^s + 1) - log(2^s)) + 1/(2^s + 1) (log(2^s + 1)) + (s 2^s)/(2^s + 1) = log(2^s + 1).
    $ This proves the claim.

    Let $r = 2^H(X_d | X_(< d))$. Then by the claim, $
        H(X) & = H(X_1) + dots.c + H(X_d | X_(< d)) \
        & >= log(r + d - 1) + dots.c + log(r) \
        & = log((r + d - 1)!/(r - 1)!) = log(d! binom(r + d - 1, d)).
    $ Since $H(X) = log(d! binom(t, d))$ is an increasing function (for $t >= d$), it follows that $r + d - 1 <= t$, i.e. $r <= t + 1 - d$. It follows that $
        H(X_(< d)) & = log(d! binom(t, d)) - log r \
        & >= log(d! t!/(d! (t - d)! (t + 1 - d))) \
        & = log((d - 1)! binom(t, d - 1)).
    $
]


= The union-closed conjecture

#definition[
    Let $cal(A)$ be a finite family of sets. $cal(A)$ is *union-closed* if $A union B in cal(A)$ for all $A, B in cal(A)$.
]<def:union-closed>
#conjecture("Union-closed Conjecture")[
    If $cal(A)$ is a non-empty union-closed family, then there exists $x$ that belongs to at least $1/2 abs(cal(A))$ sets in $cal(A)$.
]<cnj:union-closed-conjecture>
#theorem("Gilmer")[
    There exists a constant $c > 0$ such that if $cal(A)$ is any union-closed family, then there exists $x$ that belongs to at least $c abs(cal(A))$ of the sets in $cal(A)$.
]<thm:gilmer>
#example[
    Let $cal(A) = [n]^((p n)) union [n]^((>= (2p - p^2 - o(1))n)$. Then with high probability, if $A, B$ are random elements of $[n]^((p n))$, then $abs(A union B) >= (2p - p^2 - o(1))n$ (since the intersect is likely of size at most $p^2 n$). If $1 - (2p - p^2 - o(1)) = p$, then almost all of $cal(A)$ is contained in $[n]^((p n))$. The solutions of $p$ occur roughly when $1 - 3p + p^2 = 0$, which has solutions $p = 1/2 (3 plus.minus sqrt(5))$.
]
If we want to prove @thm:gilmer, it is natural to let $A, B$ be independent uniformly random elements of $cal(A)$ and to consider $H(A union B)$. Since $cal(A)$ is union-closed, $A union B in cal(A)$, so $H(A union B) <= log abs(cal(A))$. Now we would like to get a lower bound for $H(A union B)$ assuming that no $x$ belongs to more than $p abs(cal(A))$ sets in $cal(A)$.

#lemma[
    Suppose $c > 0$ is such that $h(x y) >= c (x h(y) + y h(x))$ for every $x, y in [0, 1]$. Let $cal(A)$ be a family of sets such that every element (of $union cal(A)$) belongs to fewer than $p abs(cal(A))$ members of $cal(A)$. Let $A, B$ be independent uniformly random members of $cal(A)$. Then $
        H(A union B) > c(1 - p) (H(A) + H(B)).
    $
]<lem:converse-of-gilmer-lemma>
#proofhints[
    - Think of $A, B$ as characteristic functions. Write $A_(< k)$ for $(A_1, ..., A_(k - 1))$.
    - Explain why it is enough to prove that $H((A union B)_k | A_(< k), B_(< k)) > c(1 - p)(H(A_k | A_(< k)) + H(B_k | H_(B_(< k))))$ for all $k$.
    - For each $u, v in {0, 1}^(k - 1)$, write $p(u) = PP(A_k = 0 | A_(< k) = u)$ and $q(v) = PP(B_k = 0 | B_(< k) = v)$. Find a (simple) expression for $H((A union B)_k | A_(< k) = u, B_(< k) = v)$.
    - Expand $H((A union B)_k | A_(< k), B_(< k))$, give an upper bound, then simplify it (hint: law of total probability).
]
#proof[
    Think of $A, B$ as characteristic functions. Write $A_(< k)$ for $(A_1, ..., A_(k - 1))$. By the @lem:chain-rule, it is enough to prove for every $k$ that $
        H((A union B)_k | (A union B)_(< k)) > c(1 - p)(H(A_k | A_(< k)) + H(B_k | H_(B_(< k)))).
    $ By @lmm:conditional-data-processing, $
        H((A union B)_k | (A union B)_(< k)) >= H((A union B)_k | A_(< k), B_(< k))
    $ For each $u, v in {0, 1}^(k - 1)$, write $p(u) = PP(A_k = 0 | A_(< k) = u)$ and $q(v) = PP(B_k = 0 | B_(< k) = v)$. Then, since $A$ and $B$ are independent, $
        & H((A union B)_k | A_(< k) = u, B_(< k) = v) \
        = & -sum_(i = 0)^1 PP((A union B)_k = i | A_(< k) = u, B_(< k) = v) log PP((A union B)_k = i | A_(< k) = u, B_(< k) = v) \
        = & h(p(u) q(v)).
    $ which by hypothesis is at least $c(p(u) h(q(v)) + q(v) h(p(u)))$. So $
        H((A union B)_k | (A union B)_(< k)) & >= c sum_(u, v) PP(A_(< k) = u) PP(B_(< k) = v) (p(u) h(q(v)) + q(v) h(p(u))) \
        & = c dot sum_u PP(A_(< k) = u) p(u) dot sum_v PP(B_(< k) = v) h(q(v)) \
        & + c dot sum_u PP_(A_(< k) = u) h(p(u)) dot sum_v PP(B_(< k) = v) q(v)
    $ But by law of total probability, $
        sum_u PP(A_(< k) = u) PP(A_k = 0 | A_(< k) = u) = PP(A_k = 0),
    $ and $
        sum_v PP(B_(< k) = v) h(q(v)) = sum_v PP(B_(< k) = v) H(B_k | B_(< k) = v) = H(B_k | B_(< k))
    $ Similarly for the other term, so the RHS of the inequality equals $
        c(PP(A_k = 0) H(B_k | B_(< k)) + PP(B_k = 0) H(A_k | A_(< k))),
    $ which by hypothesis (since $PP(A_k = 0) =  PP(B_k = 0) > 1 - p$) is greater than $
        c(1 - p) (H(A_k | A_(< k)) + H(B_k | B_(< k)))
    $ as required.
]
#corollary[
    Let $cal(A)$, $p$ and $c$ be as in @lem:converse-of-gilmer-lemma. If $cal(A)$ is union-closed, then we must have $p >= 1 - 1 \/ 2c$.
]<crl:converse-of-gilmer-corollary>
#proofhints[
    Straightforward.
]
#proof[
    Let $A$ and $B$ be independent uniformly random elements of $cal(A)$. Since $cal(A)$ is union-closed, $A union B in cal(A)$, so $H(A union B) <= log abs(cal(A))$. Also, $H(A) = H(B) = log abs(cal(A))$. Hence, by @lem:converse-of-gilmer-lemma, $2 c (1 - p) <= 1$.
]
@crl:converse-of-gilmer-corollary gives a non-trivial bound as long as $c > 1 \/ 2$. We shall obtain $1 \/ (sqrt(5) - 1)$.

We start by proving the diagonal case, i.e. where $x = y$.

#lemma("Boppana")[
    For every $x in [0, 1]$, $
        h(x^2) >= phi dot x dot h(x),
    $ where $phi = 1/2 (sqrt(5) + 1)$.
]<lem:boppana>
#proofhints[
    - Let $psi = 1 \/ phi$. Show that equality holds when $x = psi, 0, 1$.
    - Let $f(x) = h(x^2) - phi dot x dot h(x)$. Show that $f'''(x) = 0$ iff $-phi x^3 - 4x^2 + 3 phi x - 4 + 2phi = 0$. (Advice: use natural logs and find expressions for $h'(x)$, $h''(x)$ and $h'''(x)$ first).
    - Explain why $f'''$ has at most two roots in $(0, 1)$ and so $f$ has at most five roots in $[0, 1]$.
    - Show that $f$ has a double root at $0$ and at $psi$.
    - Explain why $f$ must have constant sign on $[0, 1]$, and by considering small $x$, show that there is $x$ with $f(x) > 0$.
]
#proof[
    Write $psi = 1 \/ phi = 1/2 (sqrt(5) - 1)$. Then $psi^2 = 1 - psi$. So $h(psi^2) = h(1 - psi) = h(psi)$ and $phi psi = 1$, so $h(psi^2) = phi dot psi dot h(psi)$. So equality holds when $x = psi$, and also when $x = 0, 1$.

    Toolkit: $ln(2) dot h(x) = -x ln x - (1 - x) ln (1 - x)$. Then $
        ln(2) dot h'(x) = -ln x - 1 + ln(1 - x) + 1 = ln(1 - x) - ln(x)
    $ and $
        ln(2) dot h''(x) = -1/x - 1/(1 - x) = -1/(x(1 - x))
    $ and $
        ln(2) dot h'''(x) = 1/x^2 - 1/(1 - x)^2 = (1 - 2x)/(x^2 (1 - x)^2).
    $ Let $f(x) = h(x^2) - phi dot x dot h(x)$. Then $
        f'(x) & = 2x h'(x^2) - phi h(x) - phi x h'(x) \
        f''(x) & = 2 h'(x^2) + 4x^2 h''(x^2) - 2 phi h'(x) - phi x h''(x) \
        f'''(x) & = 4x h''(x^2) + 8x h''(x^2) + 8x^3 h'''(x^2) - 3 phi h''(x) - phi x h'''(x) \
        & = 12 x h''(x^2) + 8x^3 h'''(x^2) - 3 phi h''(x) - phi x h'''(x)
    $ So $
        ln(2) f'''(x) & = (-12x)/(x^2 (1 - x^2)) + (8x^3 (1 - 2x^2))/(x^4 (1 - x^2)^2) + (3 phi)/(x (1 - x)) - (phi x (1 - 2x))/(x^2 (1 - x)^2) \
        & = (-12)/(x (1 - x^2)) + (8 (1 - 2x^2))/(x (1 - x^2)^2) + (3phi)/(x(1 - x)) - (phi (1 - 2x))/(x(1 - x)^2) \
        & = (-12 (1 - x^2) + 8(1 - 2x^2) + 3 phi (1 - x) (1 + x)^2 - phi(1 - 2x)(1 + x)^2)/(x(1 - x)^2 (1 + x)^2)
    $ which is zero iff $
        & -12 + 12x + 8 - 16x^2 + 3 phi (1 + x - x^2 - x^3) - phi(1 - 3x^2 - 2x^3) \
        = & -phi x^3 - 4x^2 + 3 phi x - 4 + 2phi = 0.
    $ So the numerator of $f'''(x)$ is a cubic with negative leading coefficient and constant term, so it has a negative root, so it has at most two roots in $(0, 1)$. It follows (by Rolle's theorem) that $f$ has at most five roots in $[0, 1]$, up to multiplicity. But $
        f'(x) = 2x (log(1 - x^2) - log(x^2)) + phi(x log x + (1 - x) log(1 - x)) - phi x (log(1 - x) - log x)
    $ So $f'(0) = 0$, so $f$ has a double root at $0$. Now $
        f'(psi) & = 2 psi(log psi - 2 log psi) + phi(psi log psi + 2(1 - psi) log psi) - (2log psi - log psi) \
        & = -2 psi log psi + log psi + 2 phi log psi - 2 log psi \
        & = 2 log psi (-psi + phi - 1) \
        & = 2 phi log psi (-psi^2 - 1 - psi) = 0
    $ So there is a double root at $psi$. Also, $f(1) = 0$. So $f$ is either non-negative on all of $[0, 1]$ or non-positive on all of $[0, 1]$. If $x$ is small, $
        f(x) & = x^2 log 1/x^2 + (1 - x^2) log 1/(1 - x^2) - phi x (x log 1/x + (1 - x) log 1/(1 - x)) \
        & = 2x^2 log 1/x - phi x^2 log 1/x + O(x^2).
    $ So, because $2 > phi$, there exists $x$ such that $f(x) > 0$.
]
#lemma[
    The function $f(x, y) = h(x y)/(x h(y) + y h(x))$ is minimised on $(0, 1)^2$ at a point where $x = y$.
]<lem:boppana-for-two-variables>
#proofhints[
    - Show that we can extend $f$ continuously to the boundary by setting $f(x, y) = 1$ whenever $x$ or $y$ is $0$ or $1$ (for the case when $x$ or $y$ tend to $0$ separately, consider an expansion for $x y$ small, and for the case when $x$ and $y$ tend to $1$, consider when one of $x$ or $y$ is $1$).
    - Pick any point in $(0, 1)^2$ to show that $f$ is minimised somewhere in that region.
    - Let $(x^*, y^*)$ be a minimum with $f(x^*, y^*) = alpha$. Let $g(x) = h(x) \/ x$.
    - By considering the expression $g(x y) - alpha(g(x) + g(y))$ and partial derivatives, show that $x^* g'(x^*) = y^* g'(y^*)$.
    - Show that $x g'(x)$ is an injection by considering its derivative.
]
#proof[
    We can extend $f$ continuously to the boundary by setting $f(x, y) = 1$ whenever $x$ or $y$ is $0$ or $1$. To see this, note first that it is easy if neither $x$ nor $y$ is $0$. If either $x$ or $y$ is small then $h(x y) = -x y (log x + log y) + O(x y)$, and $
        x h(y) + y h(x) & = -x (y log y + O(y)) - y (x log x + O(x)) \
        & = h(x y) quad "up to" O(x y)
    $ So it tends to $1$ again.

    We can check that $f(1 \/ 2, 1 \/ 2) < 1$, so $f$ is minimised somewhere in $(0, 1)^2$. Let $(x^*, y^*)$ be a minimum with $f(x^*, y^*) = alpha$. For convenience, let $g(x) = h(x) \/ x$ and note that $f(x, y) = g(x y)/(g(x) + g(y))$. Also, $g(x y) - alpha(g(x) + g(y)) >= 0$ with equality at $(x^*, y^*)$. So the partial derivatives of the LHS are both $0$ at $(x^*, y^*)$: $
        y^* g'(x^* y^*) - alpha g'(x^*) & = 0 \
        x^* g'(x^* y^*) - alpha g'(y^*) & = 0.
    $ So $x^* g'(x^*) = y^* g'(y^*)$. So it is enough to prove that $x g'(x)$ is an injection. We have $
        g'(x) = (h'(x)) / x - h(x)/x^2
    $ so $
        x g'(x) & = h'(x) - h(x)/x \
        & = log(1 - x) - log x + (x log x + (1 - x) log(1 - x))/x \
        & = log(1 - x)/x.
    $ Differentiating gives $
        -1/(x (1 - x)) - log(1 - x)/x^2 = (-x - (1 - x) log(1 - x))/(x^2 (1 - x))
    $ The numerator differentiates to $-1 + 1 + log(1 - x)$ which is negative. Also, it equals $0$ at $0$, so it has a constant sign. Thus, $x g'(x)$ is indeed an injection.
]
Combining this with @lem:boppana we get that $
    h(x y) >= phi/2 (x h(y) + y h(x))
$ This allows us to take $p = 1 - 1/phi = (3 - sqrt(5)) / 2$.


= Entropy in additive combinatorics

We shall need two "simple" results from additive combinatorics due to Imre Ruzsa.

#definition[
    Let $G$ be an abelian group and let $A, B subset.eq G$. The *sumset* $A + B$ of $A$ and $B$ is the set $
        {x + y: x in A, y in B}
    $ and the *difference set* $A - B$ is the set $
        {x - y: x in A, y in B}.
    $ Write $2A$ for $A + A$, $3A$ for $A + A + A$, etc.
]<def:sum-and-difference-sets>
#definition[
    The *Ruzsa distance* $d(A, B)$ is $
        abs(A - B) / (abs(A)^(1 \/ 2) dot abs(B)^(1 \/ 2)).
    $
]<def:ruzsa-distance>
#lemma("Ruzsa Triangle Inequality")[
    $d(A, C) <= d(A, B) dot d(B, C)$.
]<lem:ruzsa-triangle-inequality>
#proofhints[
    Expand the stated inequality and consider an appropriate injection.
]
#proof[
    This is equivalent to the statement $
        abs(A - C) dot abs(B) <= abs(A - B) dot abs(B - C).
    $ For each $x in A - C$, pick $a(x) in A$, $c(x) in C$ such that $x = a(x) - c(x)$. Define the map $
        phi: (A - C) times B & -> (A - B) times (B - C), \
        (x, b) & |-> (a(x) - b, b - c(x)).
    $ Adding the coordinates of $phi(x, b)$ gives $x$, so we can calculate $a(x)$ and $c(x)$ from $phi(x, b)$, and hence $b$. So $phi$ is an injection.
]
#lemma("Ruzsa Covering Lemma")[
    Let $G$ be an abelian group and let $A, B subset.eq G$ be finite. Then $A$ can be covered by at most $abs(A + B) \/ abs(B)$ translates of $B - B$.
]<lem:ruzsa-covering-lemma>
#proofhints[
    Consider a maximal subset ${x_1, ..., x_k} subset.eq A$ such that the $x_i + B$ are disjoint, show $k <= abs(A + B) \/ abs(B)$.
]
#proof[
    Let ${x_1, ..., x_k}$ be a maximal subset of $A$ such that the sets $x_i + B$ are disjoint. Then for all, $a in A$, there exists $i$ such that $(a + B) inter (x_i + B) != emptyset$, i.e. $a in (x_i + (B - B))$. So $A$ can be covered by $k$ translates of $B - B$. But since the $x_i + B$ are disjoint, $
        abs(B) k = abs({x_1, ..., x_k} + B) <= abs(A + B).
    $
]
Let $X, Y$ be discrete random variables taking values in an abelian group. What is $X + Y$ when $X$ and $Y$ are independent? For each $z$, $PP(X + Y = z) = sum_(x + y = z) PP(X = x) PP(Y = y)$. Writing $p_x$ and $q_y$ for $PP(X = x)$ and $PP(Y = y)$, this gives $
    sum_(x + y = z) p_x p_y = (p * q)(z)
$ where $p(x) = p_x$, $q(y) = q_y$. So sums of independent random variables correspond to convolutions.
#definition[
    Let $G$ be an abelian group and let $X, Y$ be $G$-valued random variables. The *(entropic) Ruzsa distance* between $X$ and $Y$ is $
        d(X; Y) & = H(X' - Y') - 1/2 H(X) - 1/2 H(Y) \
        & = H(X' - Y') - 1/2 H(X') - 1/2 H(Y').
    $ where $X', Y'$ are independent copies of $X, Y$.
]<def:entropic-ruzsa-distance>
#lemma[
    If $A, B$ are finite subsets of $G$ and $X, Y$ are uniform on $A, B$ respectively, then $
        d(X; Y) <= log d(A, B).
    $
]<lem:entropic-ruzsa-distance-upper-bound-for-uniform-variables>
#proofhints[
    Straightforward.
]
#proof[
    WLOG $X, Y$ are independent. Then $
        d(X, Y) & = H(X - Y) - 1/2 H(X) - 1/2 H(Y) \
        & <= log abs(A - B) - 1/2 log abs(A) - 1/2 log abs(B) = log d(A, B).
    $
]
#lemma[
    Let $X, Y$ be $G$-valued random variables. Then $
        H(X - Y) >= max{H(X), H(Y)} - I(X: Y).
    $
]<lem:lower-bound-for-entropy-of-difference-of-rvs>
#proofhints[
    Use that $H(X - Y) >= H(X - Y | Y)$ and $H(X - Y) >= H(X - Y | X)$.
]
#proof[
    We have $
        H(X - Y) & >= H(X - Y | Y) #[by @prop:subadditivity] \
        & = H(X - Y, Y) - H(Y) \
        & = H(X, Y) - H(Y) #[by @axm:invariance] \
        & = H(X) + H(Y) - H(Y) - I(X: Y) \
        & = H(X) - I(X: Y).
    $ We use @axm:invariance with the bijection $(x, y) |-> (x - y, y)$. By symmetry, we also have $H(X - Y) >= H(Y) - I(X: Y)$.
]
#corollary[
    If $X, Y$ are $G$-valued RVs, then $d(X; Y) >= 0$.
]<crl:entropic-ruzsa-distance-is-non-negative>
#proofhints[
    Straightforward.
]
#proof[
    WLOG $X$ and $Y$ are independent. Then $I(X: Y) = 0$, so $H(X - Y) >= max{H(X), H(Y)} >= 1/2 (H(X) + H(Y))$.
]
#lemma[
    If $X, Y$ are $G$-valued RVs, then $d(X; Y) = 0$ iff there is some (finite) subgroup $H$ of $G$ such that $X$ and $Y$ are uniform on cosets of $H$.
]<lem:criterion-for-zero-entropic-ruzsa-distance>
#proofhints[
    - $<==$: straightforward.
    - $==>$: assume WLOG that $X$ and $Y$ are independent. By considering entropy, explain why $X - Y$ and $Y$ are independent.
    - Deduce that for $X$ supported on $A$ and $Y$ supported on $B$, for all $z in A - B$ and $y_1, y_2 in B$, $PP(X = y_1 + z) = PP(X = y_2 + z)$.
    - Show by contradiction that thus $PP(X = x)$ is non-zero on $z + B$, and so that $z + B subset.eq A$.
    - Deduce that $A = B + z$ for all $z in A - B$, and so that $A - x$ is constant over $x in A$.
    - Deduce that $A - A$ is a subgroup.
]
#proof[
    $<==$: If $X, Y$ are uniform on $x + H, y + H$ then $X' - Y'$ is uniform on $(x - y) + H$, so $H(X' - Y') = H(X) = H(Y)$.

    $==>$: WLOG $X$ and $Y$ are independent. We have $H(X - Y) = 1/2 (H(X) + H(Y))$. So equality must hold throughout the proof of @lem:lower-bound-for-entropy-of-difference-of-rvs and @crl:entropic-ruzsa-distance-is-non-negative, thus $H(X - Y | Y) = H(X - Y)$. Therefore, $X - Y$ and $Y$ are independent. So for every $z in A - B$ and $y_1, y_2 in B$, $
        PP(X - Y = z | Y = y_1) = PP(X - Y = z | Y = y_2),
    $ where $A = {x: PP(X = x) != 0}$ and $B = {y: PP(Y = y) != 0}$. We can write this as $
        PP(X = y_1 + z) = PP(X = y_2 + z)
    $ So $PP(X = x)$ is constant on $z + B$. In particular, $z + B subset.eq A$ ($PP(X = x)$ must be non-zero on $z + B$, as otherwise $(z + B) inter A = emptyset$, i.e. $z in.not A - B$). By the same argument, $A - z subset.eq B$. So $A = B + z$ for all $z in A - B$. So for every $x in A$ and $y in B$, $A = B + x - y$, so $A - x = B - y$. Hence, $A - x$ is the same for every $x in A$. Therefore, $A - x = union_(x in A) (A - x) = A - A$ for all $x in A$. It follows that $
        A - A + A - A = (A - A) - (A - A) = A - x - (A - x) = A - A.
    $ So $A - x = A - A$ is a subgroup, and so $A$ is a coset of $A - A$. $B = A + x$, so $B$ is also a coset of $A - A$. Also, as stated above, $X$ is uniform on $z + B = A$ and $Y$ is uniform on $A - z = B$.
]
#lemma("Entropic Ruzsa Triangle Inequality")[
    Let $X, Y, Z$ be $G$-valued random variables. Then $d(X; Z) <= d(X; Y) + d(Y; Z)$.
]<lem:entropic-ruzsa-triangle-inequality>
#proofhints[
    Simplify the desired inequality and use @lmm:subadditivity-with-additional-difference (where $X - Z$ depends on two different (pairs of) random variables).
]
#proof[
    We must show (assuming WLOG that $X, Y, Z$ are independent) that $
        & H(X - Z) - 1/2 H(X) - 1/2 H(Z) \
        <= & H(X - Y) - 1/2 H(X) - 1/2 H(Y) + H(Y - Z) - 1/2 H(Y) - 1/2 H(Z),
    $ i.e. that $H(X - Z) + H(Y) <= H(X - Y) + H(Y - Z)$. Since $X - Z$ depends on $(X - Y, Y - Z)$ and on $(X, Z)$, by @lmm:subadditivity-with-additional-difference, $
        H(X - Y, Y - Z, X, Z) + H(X - Z) <= H(X - Y, Y - Z) + H(X, Z)
    $ i.e. $H(X, Y, Z) + H(X - Z) <= H(X, Z) + H(X - Y, Y - Z)$. By independence and @prop:subadditivity, we get $H(X - Z) + H(Y) <= H(X - Y) + H(Y - Z)$.
]
#lemma("Submodularity for Sums")[
    If $X, Y, Z$ are independent $G$-valued RVs, then $
        H(X + Y + Z) + H(Z) <= H(X + Z) + H(Y + Z).
    $
]<lem:submodularity-for-sums>
#proofhints[
    Use @lmm:subadditivity-with-additional-difference.
]
#proof[
    $X + Y + Z$ is a function of $(X + Z, Y)$ and of $(X, Y + Z)$. Therefore, by @lmm:subadditivity-with-additional-difference, $
        H(X + Z, Y, X, Y + Z) + H(X + Y + Z) <= H(X + Z, Y) + H(X, Y + Z),
    $ thus $H(X, Y, Z) + H(X + Y + Z) <= H(X + Z) + H(Y) + H(X) + H(Y + Z)$. By independence and cancelling equal terms, we get the desired inequality.
]
#lemma[
    Let $G$ be an abelian group and let $X$ be a $G$-valued random variable. Then $d(X; -X) <= 2 d(X; X)$.
]<lem:negation-of-rv-at-most-doubles-self-entropic-distance>
#proofhints[
    Consider independent copies $X_1, X_2, X_3$ of $X$, use @lem:lower-bound-for-entropy-of-difference-of-rvs and @lem:submodularity-for-sums.
]
#proof[
    Let $X_1, X_2, X_3$ be independent copies of $X$. Then by @lem:lower-bound-for-entropy-of-difference-of-rvs, $
        d(X; -X) & = H(X_1 + X_2) - 1/2 H(X_1) - 1/2 H(X_2) \
        & <= H(X_1 + X_2 - X_3) - H(X) \
        & <= H(X_1 - X_3) + H(X_2 - X_3) - H(X_3) - H(X) \
        & = 2 d(X; X)
    $ by @lem:submodularity-for-sums and since $X_1, X_2, X_3$ are all copies of $X$.
]
#corollary[
    Let $X$ and $Y$ be $G$-valued random variables. Then $d(X; -Y) <= 5 d(X; Y)$.
]
#proofhints[
    Straightforward.
]
#proof[
    By the @lem:entropic-ruzsa-triangle-inequality, $
        d(X; -Y) & <= d(X; Y) + d(Y; -Y) \
        & <= d(X; Y) + 2 d(Y; Y) \
        & <= d(X; Y) + 2(d(Y; X) + d(X; Y)) = 5 d(X; Y).
    $
]
#definition[
    Let $X, Y, U, V$ be $G$-valued random variables. The *conditional distance* is $
        d(X | U; Y | V) & = sum_(u, v) PP(U = u) PP(V = v) d(X | U = u; Y | V = v).
    $
]<def:conditional-distance>
#definition[
    Let $X, Y, U$ be $G$-valued random variables. The *simultaneous conditional distance* of $X$ to $Y$ given $U$ is $
        d(X; Y || U) := sum_u PP(U = u) d(X | U = u; Y | U = u).
    $
]<def:simultaneous-conditional-distance>
#definition[
    We say that $X', Y'$ are *conditionally independent trials* of $X, Y$ given $U$ if $X'$ is distributed like $X$, $Y'$ like $Y$, and for each $u$, $X' | U = u$ is distributed like $X | U = u$, $Y' | U = u$ is distributed like $Y | U = u$, and $X' | U = u$ and $Y' | U = u$ are independent.

    In that case, $d(X; Y || U) = H(X' - Y' | U) - 1/2 H(X' | U) - 1/2 H(Y' | U)$.
]<def:conditionally-independent-trials>
#lemma("Entropic BSG Theorem")[
    Let $A, B$ be $G$-valued RVs. Then $
        d(A; B || A + B) <= 3 I(A: B) + 2 H(A + B) - H(A) - H(B).
    $
]<lem:entropic-bsg-theorem>
#proofhints[
    - Let $A', B'$ be conditionally independent trials of $A, B$ given $A + B$.
    - Show that $H(A' | A + B) = H(A) + H(B) - I(A: B) - H(A + B)$.
    - Let $(A_1, B_1)$ and $(A_2, B_2)$ be conditionally independent trials of $(A, B)$ given $A + B$.
    - Explain why $H(A_1 - B_2) <= H(A_1 - B_2, A_1) + H(A_1 - B_2, B_1) - H(A_1 - B_2, A_1, B_1)$.
    - Use that $A_1 + B_1 = A_2 + B_2$ to bound each of the first two terms on the RHS of the above, and rewrite the $H(A_1 - B_2, A_1, B_1)$ term, using the conditional independence of $(A_1, B_1)$ and $(A_2, B_2)$, to conclude the result.
]
#proof[
    We have $
        d(A, B || A + B) = H(A' - B' | A + B) - 1/2 H(A' | A + B) - 1/2 H(B' | A + B),
    $ where $A', B'$ are conditionally independent trials of $A, B$ given $A + B$. Now $
        H(A' | A + B) & = H(A | A + B) = H(A, A + B) - H(A + B) \
        & = H(A, B) - H(A + B) \
        & = H(A) + H(B) - I(A: B) - H(A + B).
    $ Similarly, $H(B' | A + B) = H(A) + H(B) - I(A: B) - H(A + B)$, so $
        1/2 H(A' | A + B) + 1/2 H(B' | A + B)
    $ is also the same. By @prop:subadditivity, $H(A' - B' | A + B) <= H(A' - B')$. Let $(A_1, B_1)$ and $(A_2, B_2)$ be conditionally independent trials of $(A, B)$ given $A + B$ (here, $A_1$ plays the role of $A'$, $B_2$ plays the role of $B'$, and each comes with another RV since we know the value of $A + B$). Then $H(A' - B') = H(A_1 - B_2)$. By @prop:submodularity, $
        H(A_1 - B_2) <= H(A_1 - B_2, A_1) + H(A_1 - B_2, B_1) - H(A_1 - B_2, A_1, B_1)
    $ Also, $
        H(A_1 - B_2, A_1) = H(A_1, B_2) <= H(A_1) + H(B_2) = H(A) + H(B)
    $ and since $A_1 + B_1 = A_2 + B_2$, $
        H(A_1 - B_2, B_1) = H(A_2 - B_1, B_1) = H(A_2, B_1) <= H(A) + H(B).
    $ Finally, since $A_1 + B_1 = A_2 + B_2 = A + B$, $
        H(A_1 - B_2, A_1, B_1) & = H(A_1, B_1, A_2, B_2) \
        & = H(A_1, B_1, A_2, B_2 | A + B) + H(A + B) \
        & = 2 H(A, B | A + B) + H(A + B) \
        & = 2 H(A, B) - H(A + B) \
        & = 2 H(A) + 2 H(B) - 2 I(A: B) - H(A + B).
    $ where the third line is by conditional independence of $(A_1, B_1)$ and $(A_2, B_2)$. Adding or subtracting as appropriate all these terms gives the required inequality.
]


= A proof of Marton's conjecture in $FF_2^n$

We shall prove the following theorem.
#theorem("Polynomial Freiman-Ruzsa")[
    There is a polynomial $p$ with the following property: if $n in NN$ and $A subset.eq FF_2^n$ is such that $abs(A + A) <= C abs(A)$, then there is a subspace $H subset.eq FF_2^n$ of size at most $abs(A)$ such that $A$ is contained in the union of at most $p(C)$ translates of $H$. Equivalently, there exists $K subset.eq FF_2$, $abs(K) <= p(C)$, such that $A subset.eq K + H$.
]<thm:green-manners-tao-gowers>
#remark[
    @thm:green-manners-tao-gowers is also known as the *Green-Manners-Tao-Gowers theorem*.
]
In fact, we shall prove the following statement:
#theorem("EPFR")[
    Let $G = FF_2^n$. There is an absolute constant $alpha$ with the following property:
    
    Let $X, Y$ be $G$-valued random variables. Then there exists a subgroup $H$ of $G$ such that $
        d(X; U_H) + d(U_H; Y) <= alpha d(X; Y),
    $ where $U_H$ is a random variable distributed uniformly on $H$.
]<thm:epfr>
#remark[
    "EPFR" stands for entropic polynomial Freiman-Ruzsa.
]
#lemma[
    Let $X$ be a discrete random variable and write $p_x = PP(X = x)$. Then there exists $x$ such that $p_x >= 2^(-H(X))$.
]<lem:rv-has-some-mass-greater-than-negative-exponential-of-entropy>
#proofhints[
    By contradiction.
]
#proof[
    If not, then $H(X) = sum_x p_x log(1 \/ p_x) > H(X) sum_x p_x = H(X)$: contradiction.
]
#proposition[
    @thm:epfr implies @thm:green-manners-tao-gowers.
]<prop:epfr-implies-green-manners-tao-gowers>
#proofhints[
    - Let $A subset.eq FF_2^n$ and $abs(A + A) <= C abs(A)$. Let $U_H$ be uniformly distributed on $H$, let $X$ and $Y$ be independent copies of $U_A$. Show that $d(X; U_H) <= 1/2 alpha log C$.
    - Deduce that there exists $z$ such that $
        PP(X + U_H = z) >= abs(A)^(-1 \/ 2) abs(H)^(-1 \/ 2) C^(-alpha \/ 2)
    $ and find an expression for the LHS.
    - Let $B = A inter (z + H)$. Show that $A$ can be covered by at most $abs(A + B)/abs(B)$ translates of $H$.
    - Use that $B subset.eq A, z + H$ to show that $
        abs(A + B)/abs(B) <= C^(alpha \/ 2 + 1) abs(A)^(1 \/ 2) / abs(H)^(1 \/ 2) <= C^(alpha + 1).
    $
    - Consider the cases $abs(H) <= abs(A)$ and $abs(H) > abs(A)$: if the latter, then consider a subgroup $H'$ of $H$ of size between $abs(A) \/ 2$ and $abs(A)$ (why does this exist?).
]
#proof[
    Let $A subset.eq FF_2^n$ and $abs(A + A) <= C abs(A)$. Let $X$ and $Y$ be independent copies of $U_A$. Then by @thm:epfr, there exists a subgroup $H$ such that $d(X; U_H) + d(U_H; X) <= alpha d(X; Y)$, so $d(X; U_H) <= alpha / 2 d(X; Y)$. But since we are in $FF_2^n$, $
        d(X; Y) & = H(U_A - U'_A) - 1/2 H(U_A) - 1/2 H(U'_A) = H(U_A + U'_A) - H(U_A) \
        & <= log C abs(A) - log abs(A) = log C,
    $ by @axm:maximality. So $d(X; U_H) <= 1/2 alpha log C$, i.e. $
        H(X + U_H) & <= 1/2 H(X) + 1/2 H(U_H) + 1/2 alpha log C \
        & = 1/2 log abs(A) + 1/2 log abs(H) + 1/2 alpha log C.
    $ Therefore by @lem:rv-has-some-mass-greater-than-negative-exponential-of-entropy, there exists $z$ such that $
        PP(X + U_H = z) >= abs(A)^(-1 \/ 2) abs(H)^(-1 \/ 2) C^(-alpha \/ 2).
    $ But $PP(X + U_H = z) = abs(A inter (z - H))/(abs(A) abs(H)) = abs(A inter (z + H))/(abs(A) abs(H))$. So there exists $z in G$ such that $
        abs(A inter (z + H)) >= C^(-alpha \/ 2) abs(A)^(-1 \/ 2) abs(H)^(-1 \/ 2).
    $ Let $B = A inter (z + H)$. Let $B = A inter (z + H)$. By @lem:ruzsa-covering-lemma, we can cover $A$ by at most $abs(A + B)/abs(B)$ translates of $B - B = B + B$. But $B subset.eq z + H$ so $B + B subset.eq 2z + H + H = H$. So $A$ can be covered by at most $abs(A + B)/abs(B)$ translates of $H$. But since $B subset.eq A$, $abs(A + B) <= abs(A + A) <= C abs(A)$. So $
        abs(A + B)/abs(B) <= (C abs(A))/(C^(-alpha \/ 2) abs(A)^(1 \/ 2) abs(H)^(1 \/ 2)) = C^(alpha \/ 2 + 1) abs(A)^(1 \/ 2) / abs(H)^(1 \/ 2).
    $ Since $B$ is contained in $z + H$, $abs(H) >= C^(-alpha \/ 2) abs(A)^(1 \/ 2) abs(H)^(1 \/ 2)$, which implies $abs(H) >= C^(-alpha) abs(A)$. So $
        C^(alpha \/ 2 + 1) abs(A)^(1 \/ 2)/abs(H)^(1 \/ 2) <= C^(alpha + 1).
    $ If $abs(H) <= abs(A)$, then we are done (with polynomial $p(x) = x^(alpha + 1)$). Otherwise, since $B subset.eq A$, $abs(A) >= C^(-alpha \/ 2) abs(A)^(1 \/ 2) abs(H)^(1 \/ 2)$, which implies $abs(H) <= C^alpha abs(A)$. Pick a subgroup $H'$ of $H$ of size between $abs(A) \/ 2$ and $abs(A)$. Then $H$ is a union of $abs(H) \/ abs(H') <= 2 C^alpha$ translates of $H'$, so $A$ is a union of at most $2 C^(2 alpha + 1)$ translates of $H'$.
]
Now we reduce further. We shall prove the following statement.
#theorem("EPFR'")[
    There is an absolute constant $eta > 0$ such that if $X$ and $Y$ are any two $FF_2^n$-valued RVs, with $d(X; Y) > 0$, then there exist $FF_2^n$-valued RVs $U$ and $V$ such that $
        tau_(X, Y) (U; V) := d(U; V) + eta (d(U; X) + d(V; Y)) < d(X; Y).
    $
]<thm:epfr-dash>
#proposition[
    @thm:epfr-dash with constant $eta$ implies @thm:epfr with constant $1 \/ eta$.
]<prop:epfr-dash-implies-epfr>
#proofhints[
    - By compactness, we can find $FF_2^n$-valued RVs $U, V$ such that $tau_(X, Y) (U; V)$ is minimised.
    - Assuming that $d(U; V) != 0$, use the @lem:ruzsa-triangle-inequality to derive a contradiction.
    - Conclude using @lem:criterion-for-zero-entropic-ruzsa-distance.
]
#proof[
    By compactness, we can find $FF_2^n$-valued RVs $U, V$ such that $tau_(X, Y) (U; V)$ is minimised. If $d(U; V) != 0$, then by @thm:epfr-dash, there exist $FF_2^n$-valued RVs $Z, W$ such that $tau_(U V)(Z; W) < d(U; V)$. But then by the @lem:ruzsa-triangle-inequality, $
        tau_(X, Y) (Z; W) & = d(Z; W) + eta (d(Z; X) + d(W; Y)) \
        & <= d(Z; W) + eta (d(Z; U) + d(W; V)) + eta (d(U; X) + d(V; Y)) \
        & < d(U; V) + eta (d(U; X) + d(V; Y)) \
        & = tau_(X, Y)(U; V),
    $ which is a contradiction. It follows that $d(U; V) = 0$. So by @lem:criterion-for-zero-entropic-ruzsa-distance, there exists $H$ such that $U$ and $V$ are uniform on cosets of $H$, so $
        eta (d(U; X) + d(V; Y)) = eta (d(U_H; X) + d(U_H; Y)) < d(X; Y),
    $ since $d(dot; dot)$ is invariant under constant shifts of either of its arguments. This gives @thm:epfr with constant $1 \/ eta$.
]
#notation[
    Write $tau_(X, Y)(U | Z; V | W)$ for $sum_(z, w) PP(Z = z) PP(W = w) tau_(X, Y)(U | Z = z; V | W = w)$ and $tau_(X, Y) (U; V || Z)$ for $sum_z PP(Z = z) tau_(X, Y) (U | Z = z; V | Z = z)$.
]
#remark[
    If we can prove @thm:epfr-dash for conditioned random variables, then by averaging, we get it for some pair of random variables (e.g. of the form $U | Z = z$ and $V | W = w$).
]
#lemma("Fibring")[
    Let $G$ and $H$ be abelian groups and let $phi: G -> H$ be a homomorphism. Let $X, Y$ be $G$-valued random variables. Then $
        d(X; Y) = d(phi(X); phi(Y)) + d(X | phi(X); Y | phi(Y)) + I(X - Y: (phi(X), phi(Y)) | phi(X) - phi(Y)).
    $
]<lem:fibring>
#proofhints[
    - May assume WLOG that $X$ and $Y$ are independent.
    - Use @lem:data-processing-adds-no-information and @axm:additivity.
]
#proof[
    We may assume WLOG that $X$ and $Y$ are independent. We have $
        d(X; Y) & = H(X - Y) - 1/2 H(X) - 1/2 H(Y) \
        & = H(phi(X) - phi(Y)) + H(X - Y | phi(X) - phi(Y)) \
        & - 1/2 H(phi(X)) - 1/2 H(X | phi(X)) - 1/2 H(phi(Y)) - 1/2 H(Y | phi(Y)) \
        & = d(phi(X); phi(Y)) + d(X | phi(X); Y | phi(Y)) \
        & + H(X - Y | phi(X) - phi(Y)) - H(X - Y | phi(X), phi(Y))
    $ But the last line equals $
        & H(X - Y | phi(X) - phi(Y)) - H(X - Y | phi(X), phi(Y), phi(X) - phi(Y)) \
        = & I(X - Y: (phi(X), phi(Y)) | phi(X) - phi(Y)).
    $
]
We shall be interested in the following special case.
#corollary[
    Let $G = FF_2^n$ and let $X_1, X_2, X_3, X_4$ be independent $G$-valued RVs. Then $
        d(X_1; X_3) + d(X_2; X_4) & = d((X_1, X_2); (X_3, X_4)) \
        & = d(X_1 + X_2; X_3 + X_4) + d(X_1 | X_1 + X_2; X_3 | X_3 + X_4) \
        & + I(X_1 + X_3, X_2 + X_4: X_1 + X_2, X_3 + X_4 | X_1 + X_2 + X_3 + X_4).
    $
]<crl:fibring-for-pairs>
#proofhints[
    Straightforward.
]
#proof[
    The first equality is easy to see. For the second, apply @lem:fibring with $X = (X_1, X_2)$, $Y = (X_3, X_4)$ and $phi(x, y) = x + y$.
]
#lemma[
    Let $X_1, X_2, X_3, X_4$ be independent $FF_2^n$-valued RVs and $W = X_1 + X_2 + X_3 + X_4$. Then $
        & 2 d(X_1; X_3) + 2 d(X_2; X_4) + d(X_1; X_4) + d(X_2; X_3) \
        >= & 2 d(X_1 + X_2; X_3 + X_4) + d(X_1 + X_4; X_2 + X_3) \
        & + med 2 d(X_1 | X_1 + X_2; X_3 | X_3 + X_4) + d(X_1 | X_1 + X_4; X_2 | X_2 + X_3) \
        & + med 1/3 d(X_1 + X_2; X_1 + X_3 || X_2 + X_3, W) + 1/3 d(X_1 + X_2; X_1 + X_4 || X_2 + X_4, W) \
        & + med 1/3 d(X_1 + X_4; X_1 + X_3 || X_3 + X_4, W)
    $
]<lem:big-inequality>
#proofhints[
    Use @crl:fibring-for-pairs and @lem:entropic-bsg-theorem on $(X_1, X_2, X_3, X_4)$, $(X_1, X_2, X_4, X_3)$ and $(X_1, X_4, X_3, X_2)$, making heavy use of the observation that if $i, j, k, l$ are some permutation of $1, 2, 3, 4$, then $H(X_i + X_j | W) = H(X_k + X_l | W)$.
]
#proof[
    Recall that $d(X; Y || X + Y) <= 3 I(X: Y) + 2 H(X + Y) - H(X) - H(Y)$ by the @lem:entropic-bsg-theorem. Equivalently, $I(X: Y) >= 1/3 (d(X; Y || X + Y) + H(X) + H(Y) - 2 H(X + Y))$. Applying this to the mutual information term in @crl:fibring-for-pairs, we get that it is at least $
        & 1/3 d(X_1 + X_3, X_2 + X_4; X_1 + X_2, X_3 + X_4 || X_2 + X_3, W) + 1/3 H(X_1 + X_3, X_2 + X_4 | W) \
        & + 1/3 H(X_1 + X_2, X_3 + X_4 | W) - 2/3 H(X_2 + X_3, X_2 + X_3 | W).
    $ which simplifies to $
        & 1/3 d(X_1 + X_3, X_2 + X_4; X_1 + X_2, X_3 + X_4 || X_2 + X_3, W) \
        & + med 1/3 H(X_1 + X_3 | W) + 1/3 H(X_1 + X_2 | W) - 2/3 H(X_2 + X_3 | W) \
        = & 1/3 d(X_1 + X_2; X_1 + X_3 || X_2 + X_3, W) \
        & + med 1/3 H(X_1 + X_3 | W) + 1/3 H(X_1 + X_2 | W) - 2/3 H(X_2 + X_3 | W)
    $ Now apply this inequality and @crl:fibring-for-pairs to $(X_1, X_2, X_3, X_4)$, $(X_1, X_2, X_4, X_3)$ and $(X_1, X_4, X_3, X_2)$. We look at the first entropy terms in the above expression: we get $
        & 2 H(X_1 + X_2 | W) + H(X_1 + X_4 | W) \
        & + H(X_1 + X_3 | W) + H(X_1 + X_4 | W) + H(X_1 + X_2 | W) \
        & - 2 H(X_2 + X_3 | W) - 2 H(X_2 + X_4 | W) - 2 H(X_1 + X_2 | W).
    $ which is equal to $0$, where we have made heavy use of the observation that if $i, j, k, l$ are some permutation of $1, 2, 3, 4$, then $H(X_i + X_j | W) = H(X_k + X_l | W)$, which also allowed us e.g. to replace $
        d(X_1 + X_3, X_2 + X_4; X_1 + X_2, X_3 + X_4 || X_2 + X_3, W)
    $ by $
        d(X_1 + X_2; X_1 + X_3 || X_2 + X_3, W).
    $
]
#lemma[
    Let $X_1, X_2$ be independent copies of $X$ and $Y_1, Y_2$ be independent copies of $Y$. Then $
        6 d(X; Y) >= & 2 d(X_1 + X_2; Y_1 + Y_2) + d(X_1 + Y_2; X_2 + Y_1) \
        & + med 2 d(X_1 | X_1 + X_2; Y_1 | Y_1 + Y_2) + d(X_1 | X_1 + Y_1; X_2 | X_2 + Y_2) \
        & + med 2/3 d(X_1 + X_2; X_1 + Y_1 || X_2 + Y_1, X_1 + Y_2) \
        & + med 1/3 d(X_1 + Y_1; X_1 + Y_2 || X_1 + X_2, Y_1 + Y_2).
    $
]<lem:another-big-inequality>
#proofhints[
    Straightforward.
]
#proof[
    Apply @lem:big-inequality to $(X_1, X_2, Y_1, Y_2)$ (all independent). We can swap $Y_1$ and $Y_2$ in the third last term since they are independent copies.
]
Recall that we want $U, V$ such that $tau_(X, Y)(U, V) < d(X; Y)$. @lem:another-big-inequality gives us a collection of distances (some conditioned), at least one of which is at most $6 / 7 d(X; Y)$. So it will be enough to show that for all of them, we get $d(U; X) + d(V; Y) <= C d(X; Y)$ for some absolute constant $C$. Then we can take $eta < 1 \/ 7C$.
#definition[
    We say that $(U, V)$ is *$C$-relevant* to $(X, Y)$ if $d(U; X) + d(V; Y) <= C d(X; Y)$.
]<def:c-relevant>
#lemma[
    $(Y, X)$ is $2$-relevant to $(X, Y)$.
]<lem:swapping-is-two-relevant>
#proofhints[
    Straightforward.
]
#proof[
    $d(Y; X) + d(X; Y) = 2 d(X; Y)$.
]
#lemma[
    Let $U, V, X$ be independent $FF_2^n$-valued RVs. Then $
        d(U + V; X) <= 1/2 (d(U; X) + d(V; X) + d(U; V)).
    $
]<lem:triangle-like-inequality-for-entropic-distance-of-sum>
#proofhints[
    Write $-1/2 H(U + V) = -H(U + V) + 1/2 H(U + V)$ and $H(U + V + X) = 1/2 H(U + V + X) + 1/2 H(U + V + X)$ and use @lem:submodularity-for-sums twice.
]
#proof[
    We have $
        d(U + V; X) & = H(U + V + X) - 1/2 H(U + V) - 1/2 H(X) \
        & = H(U + V + X) - H(U + V) + 1/2 H(U + V) - 1/2 H(X) \
        & <= 1/2 H(U + X) - 1/2 H(U) + 1/2 H(V + X) - 1/2 H(V) + 1/2 H(U + V) - 1/2 H(X) \
        & = 1/2 (d(U; X) + d(V; X) + d(U; V))
    $ by @lem:submodularity-for-sums.
]
#corollary[
    If $(U, V)$ is $C$-relevant to $(X, Y)$ and $U_1, U_2, V_1, V_2$ are copies of $U, V$, then $(U_1 + U_2, V_1 + V_2)$ is $2C$-relevant to $(X, Y)$.
]<crl:sums-of-copies-doubles-relevance>
#proofhints[
    Use @lem:triangle-like-inequality-for-entropic-distance-of-sum and @lem:entropic-ruzsa-triangle-inequality.
]
#proof[
    $
        d(U_1 + U_2; X) + d(V_1 + V_2; Y) & <= 1/2 (2d(U; X) + d(U; U) + 2d(V; Y) + d(V; V)) \
        & <= 2 (d(U; X) + d(V; Y)) <= 2 C d(X; Y)
    $ by @lem:triangle-like-inequality-for-entropic-distance-of-sum and the @lem:ruzsa-triangle-inequality.
]
#corollary[
    Let $X_1, X_2, Y_1, Y_2$ be copies of $X, Y$. Then $(X_1 + X_2, Y_1 + Y_2)$ is $4$-relevant to $(Y, X)$.
]
#proofhints[
    Straightforward.
]
#proof[
    By @lem:swapping-is-two-relevant, $(X, Y)$ is $2$-relevant to $(Y, X)$ so by @crl:sums-of-copies-doubles-relevance, we are done.
]
#corollary[
    If $(U, V)$ is $C$-relevant to $(X, Y)$, then $(U + V, U + V)$ is $(2C + 2)$-relevant to $(X, Y)$.
]<crl:relevance-for-cross-summing>
#proofhints[
    Use @lem:triangle-like-inequality-for-entropic-distance-of-sum on $d(U + V; X)$, similarly for $d(U + V; Y)$.
]
#proof[
    By @lem:triangle-like-inequality-for-entropic-distance-of-sum and the @lem:ruzsa-triangle-inequality, $
        d(U + V; X) & <= 1/2 (d(U; X) + d(V; X) + d(U; V)) \
        & <= 1/2 (d(U; X) + d(V; Y) + d(X; Y) + d(U; X) + d(X; Y) + d(V; Y)) \
        & = d(U; X) + d(V; Y) + d(X; Y),
    $ and similarly for $d(U + V; Y)$.
    // $
    //     d(U + V; X) + d(U + V; Y) & <= 1/2 (d(U; X) + d(V; X) + d(U; Y) + d(V; Y) + 2d(U; V)) \
    //     & <= 1/2 (2d(U; X) + 4d(U; V) + 2d(V; Y)) \
    //     & <= 1/2 (6 d(U; X) + 6 d(V; Y) + 4 d(X; Y))
    // $
]
#lemma[
    Let $U, V, X$ be independent $FF_2^n$-valued RVs. Then $
        d(U | U + V; X) <= 1/2 (d(U; X) + d(V; X) + d(U; V))
    $
]<lem:triangle-like-inequality-for-conditioned-entropic-distance-of-sum>
#proofhints[
    - Show that $d(U | U + V; X) <= H(U + X) - 1/2 H(U) - 1/2 H(V) + 1/2 H(U + V) - 1/2 H(X)$.
    - Show that $d(U | U + V; X) = d(V | U + V; X)$, and average the above inequality with a similar bound.
]
#proof[
    We have $
        d(U | U + V; X) & = H(U + X | U + V) - 1/2 H(U | U + V) - 1/2 H(X) \
        & = H(U + X | U + V) - 1/2 H(U, U + V) + 1/2 H(U + V) - 1/2 H(X) \
        & <= H(U + X) - 1/2 H(U) - 1/2 H(V) + 1/2 H(U + V) - 1/2 H(X).
    $ But $d(U | U + V; X) = d(V | U + V; X)$ since $H(U + X, U + V) = H(X - V, U + V) = H(V + X, U + V)$, so also $
        d(U | U + V; X) <= H(V + X) - 1/2 H(U) - 1/2 H(V) + 1/2 H(U + V) - 1/2 H(X).
    $ Averaging the two inequalities gives the result (as earlier).
]
#corollary[
    Let $U, V$ be independent RVs and suppose that $(U, V)$ is $C$-relevant to $(X, Y)$. Let $U_1, U_2, V_1, V_2$ be independent copies of $U, V$. Then
    + $(U_1 | U_1 + U_2, V_1 | V_1 + V_2)$ is $2C$-relevant to $(X, Y)$.
    + $(U_1 | U_1 + V_1, U_2 | U_2 + V_2)$ is $(2C + 2)$-relevant to $(X, Y)$.
]
#proof[
    Use @lem:triangle-like-inequality-for-conditioned-entropic-distance-of-sum. Then as soon as it is used, we are in exactly the situation we were in when bounding the relevance of $(U_1 + U_2, V_1 + V_2)$ and $(U_1 + V_1, U_2 + V_2)$ (with @crl:sums-of-copies-doubles-relevance and @crl:relevance-for-cross-summing).
]
It remains to tackle the last two terms in @lem:another-big-inequality. For the fifth term, we need to bound $
    d(X_1 + X_2 | X_2 + Y_1, X_1 + Y_2; X) + d(X_1 + Y_1 | X_2 + Y_1, X_1 + Y_2; Y).
$ But the first term of this is at most (by @lem:triangle-like-inequality-for-entropic-distance-of-sum) $
    & 1/2 d(X_1 | X_2 + Y_1, X_1 + Y_2; X) + 1/2 d(X_2 | X_2 + Y_1, X_1 + Y_2; X) + 1/2 d(X_1; X_2 || X_2 + Y_1, X_1 + Y_2) \
    <= & d(X_1 | X_1 + Y_2; X) + d(X_2 | X_2 + Y_1; X) = 2d(X | X + Y; X)
$ by the @lem:ruzsa-triangle-inequality and independence. Now we can use @lem:triangle-like-inequality-for-conditioned-entropic-distance-of-sum, and similarly for the other terms. In this way, we get that the fifth and sixth terms have relevances bounded above by $lambda C$ for an absolute constant $lambda$.

// TODO: note for exams: if not much detail for proof given in lectures, then won't be asked to give much detail for that proof in the exam
