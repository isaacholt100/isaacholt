#import "../../template.typ": *

#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Entropy Methods in Combinatorics Notes",
    author: "Isaac Holt",
    keywords: ("combinatorics", "entropy")
)

#let sim = sym.tilde

= The Khinchin (Shannon?) axioms for entropy

Note all random variables we deal with will be discrete, unless otherwise stated.

== Entropy axioms

#definition[
    The *entropy* of a discrete random variable $X$ is a quantity $H(X)$ that takes real values and satisfies @axm:normalisation, @axm:invariance, @axm:extendability, @axm:maximality, @axm:continuity and @axm:additivity.
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
    If $X$ is uniformly distributed on a set $A$ of size $r$, then $H(X) = log_2 (r)$.
]
#proof[
    By @prop:uniformly-distributed-random-variable-on-n-bits-has-n-entropy, @axm:maximality and @axm:invariance, we have $floor(log_2 (r)) <= H(X)$ (by considering the random variable $Y$ on a set $A$ where $Y$ is uniformly distributed on a subset of $A$ of size $2^floor(log_2 (r))$). Now by @crl:entropy-of-independent-variables-is-sum-of-entropies, we similarly have that $floor(k log_2 (r)) <= H(X_1, ..., X_k) = k H(X)$ for all $k in NN$, where $X_1, ..., X_k$ are IID and have the same distribution as $X$. So we have $1/k floor(k log_2 (r)) = H(X)$, and taking the limit as $k -> oo$ gives $log_2 (r) <= H(X)$.

    Following a similar argument, by @prop:uniformly-distributed-random-variable-on-n-bits-has-n-entropy, @axm:maximality, and @axm:invariance, we have $H(X) <= ceil(log_2 (r))$. By @crl:entropy-of-independent-variables-is-sum-of-entropies, we have that $k H(X) = H(X_1, ..., X_k) <= ceil(k log_2 (r))$ for all $k in NN$, which gives $H(X) <= log_2 (r)$. 
]