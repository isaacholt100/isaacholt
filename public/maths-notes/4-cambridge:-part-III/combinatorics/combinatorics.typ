#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

= Set systems

#definition[
    Let $X$ be a set. A *set system* on $X$ (also called a *family of subsets of $X$*) is a collection $cal(A) subset.eq powset(X)$.
]
#notation[
    $X^((r)) := {A subset.eq X: |A| = r}$ denotes the family of subsets of $X$ of size $r$.
]
#remark[
    Usually, we take $X = [n] = {1, ..., n}$, so $|X^((r))| = binom(n, r)$.
]
#notation[
    For brevity, we write e.g. $[4]^((2)) = {12, 13, 14, 23, 24, 34}$.
]
#definition[
    We can visualise $powset(A)$ as a graph by joining nodes $A in powset(X)$ and $B in powset(X)$ if $|A Delta B| = 1$, i.e. if $A = B union {i}$ for some $i in.not B$, or vice versa.

    This graph is the *discrete cube* $Q_n$.

    Alternatively, we can view $Q_n$ as an $n$-dimensional unit cube ${0, 1}^n$ by identifying e.g. ${1, 3} subset.eq [5]$ with $10100$ (i.e. identify $A$ with $bb(1)_A$, the characterstic/indicator function of $A$).
]<def:discrete-cube>
#definition[
    $cal(A) subset.eq powset(X)$ is a *chain* if $forall A, B in cal(A)$, $A subset.eq B$ or $B subset.eq A$.
]<def:chain>
#example[
    - $cal(A) = {23, 1235, 123567}$ is a chain.
    - $cal(A) = {emptyset, 1, 12, ..., [n]} subset.eq powset([n])$ is a chain.
]
#definition[
    $cal(A) subset.eq powset(X)$ is an *antichain* if $forall A != B in cal(A)$, $A subset.eq.not B$.
]<def:antichain>
#example[
    - $cal(A) = {23, 137}$ is an antichain.
    - $cal(A) = {1, ..., n} subset.eq powset([n])$ is an antichain.
    - More generally, $cal(A) = X^((r))$ is an antichain for any $r$.
]
#proposition[
    A chain $cal(A) subset.eq powset([n])$ can have at most $n + 1$ elements.
]
#proof[
    For each $0 <= r <= n$, $cal(A)$ can contain at most $1$ $r$-set (set of size $r$).
]



= Isoperimetric inequalities




= Intersecting families