#import "../../template.typ": *

#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Entropy Methods in Combinatorics Notes",
    author: "Isaac Holt",
    keywords: ("combinatorics", "entropy")
)

#let sim = sym.tilde

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
    If $Y = f(X)$ for some bijection $f$, then $H(Y) = H(X)$.
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
    $H(X | Y) & = sum_(y) PP(Y = y) H(X | Y = y)$ Since $X$ and $Y$ are independent, the distribution of $X$ is unaffected by knowing $Y$, so $H(X | Y = y)$ for all $y$, which gives the result. (Note we have implicitly used @axm:invariance here).
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
    Use that $X$ and $X$ are independent.
]
#proof[
    $X$ and $X$ are independent (verify). So by @lem:entropy-of-two-independent-variables-is-sum-of-entropies, $H(X, X) = 2 H(X)$. But by @axm:invariance, $H(X, X) = H(X)$. So $H(X) = 0$.
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
    - Pick $n in NN$ such that $p_a = m_a / n$, $m_a in NN_0$. Let $Z$ be uniform on $[n]$. Let ${E_a: a in A}$ be a partition of $[n]$ into sets with $abs(E_a) = m_a$.
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
    - Let $E_b = union_a E_(a b)$ for each $b$. So $Y = b$ iff $Z = E_b$. Now define an RV $W$ as follows: if $Y = b$, then $W$ is uniformly distributed in $E_b$. Use conditional independence to conclude the result.
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
    Use that $H(X | Y, Z = z) <= H(Z | Z = z)$.
]
#proof[
    // Either:
    // + Use that $(Y, Z)$ determines $Z$ and @crl:data-processing.
    + $H(X | Y, Z) = sum_z PP(Z = z) H(X | Y, Z = z) <= sum_z PP(Z = z) H(X | Z = z) = H(X | Z)$.
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
    $ with equality iff $H(X | Y = y)$ is uniform on $A$ for all $y$ (by @lmm:entropy-is-maximal-only-if-x-is-uniform), which implies that $X$ and $Y$ are independent.

    At the last stage of the proof, we said $H(X | Y) = H(X | Y, W) = H(X | W) <= H(X)$, where $W$ was uniform. So equality holds only if $X$ and $W$ are independent, which implies (since $Y$ depends on $W$), that $X$ and $Y$ are independent.
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
    Let $G$ be a bipartite graph with (finite) vertex sets $X$ and $Y$ and density $alpha$ (defined to be $abs(E(G))/(abs(X) dot abs(Y))$). Let $H$ be another (think of it as small) bipartite graph with vertex sets $U$ and $V$ and $m$ edges. Now let $phi: U -> X$ and $psi: V -> Y$. We say that $(phi, psi)$ is a *homomorphism* if $phi(x) phi(y) in E(G)$ for every edge $x y in E(H)$.
]<def:bipartite-graph-homomorphism>
#conjecture("Sidorenko's Conjecture")[
    For every $G, H$, for random $phi: U -> X$, $psi: V -> Y$, $
        PP((phi, psi) "is a homomorphism") >= alpha^m.
    $
]<cnj:sidorenko>
#remark[
    @cnj:sidorenko is not hard to prove when $H$ is the complete bipartite graph $K_(r, s)$ (the case $K_(2, 2)$ can be proved using Cauchy-Schwarz: exercise).
]
#theorem[
    @cnj:sidorenko is true if $H$ is a path of length $3$.
]<thm:sidorenko-true-if-h-is-path-of-length-3>
#proof[
    We want to show that if $G$ is a bipartite graph of density $alpha$ with vertex sets $X, Y$ of size $m$ and $n$, and we choose $x_1, x_2 in X$, $y_1, y_2 in Y$ independently at random, then $PP(x_1 y_1, y_1 x_2, x_2 y_2 in E(G)) >= alpha^3$.

    It would be enough to let $P$ be a path of length $3$ chosen uniformly at random and show that $H(P) >= log (alpha^3 m^2 n^2)$ (by @prop:entropy-of-uniform-rv-is-log-of-support-size). Instead, we shall define a different RV taking values in the set of all paths of length $3$ (including degenerate paths). To do this, let $(X_1, Y_1)$ be a random edge of $G$ (with $X_1 in X$, $Y_1 in Y$). Now let $X_2$ be a random neighbour of $Y_1$ and $Y_2$ be a random neighbour of $X_2$. It will be enough to prove that $
        H(X_1, Y_1, X_2, Y_2) >= log(alpha^3 m^2 n^2).
    $
]