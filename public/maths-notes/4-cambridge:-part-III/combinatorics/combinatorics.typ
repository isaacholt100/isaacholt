#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

= Set systems

== Chains and antichains

#note[
    The ideas in combinatorics often occur in the proofs, so it is advisable to learn the techniques used in proofs, rather than just learning the results and not their proofs.
]
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

    Alternatively, we can view $Q_n$ as an $n$-dimensional unit cube ${0, 1}^n$ by identifying e.g. ${1, 3} subset.eq [5]$ with $10100$ (i.e. identify $A$ with $bb(1)_A$, the characteri stic/indicator function of $A$).
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
    A chain and an antichain can meet at most once.
]
#proofhints[
    Trivial.
]
#proof[
    By definition.
]
#proposition[
    A chain $cal(A) subset.eq powset([n])$ can have at most $n + 1$ elements.
]
#proofhints[
    Trivial.
]
#proof[
    For each $0 <= r <= n$, $cal(A)$ can contain at most $1$ $r$-set (set of size $r$).
]
#theorem(name: "Sperner's Lemma")[
    Let $cal(A) subset.eq powset(X)$ be an antichain. Then $|cal(A)| <= binom(n, floor(n\/2))$, i.e. the maximum size of an antichain is achieved by the set of $X^((floor(n\/2)))$.
]<thm:sperners-lemma>
#proofhints[
    - Let $r < n/2$.
    - Let $G$ be bipartite subgraph of $Q_n$ spanned by $X^((r)) union X^((r + 1))$.
    - By considering an expression and upper bound for number of $S$-$Gamma(S)$ edges in $G$ for each $S subset.eq X^((r))$, show that there is a matching from $X^((r))$ to $X^((r + 1))$.
    - Reason that this induces a matching from $X^((r))$ to $X^((r - 1))$ for each $r > n/2$.
    - Reason that joining these matchings together, together with length $1$ chains of subsets of $X^((floor(n\/2)))$ not included in a matching, result in a partition of $powset(X)$ into $binom(n, floor(n\/2))$ chains, and conclude result from here.
]
#proof[
    - We use the idea: from "a chain meets each layer in $<=1$ points, because a layer is an antichain", we try to decompose the cube into chains.
    - We partition $powset(X)$ into $binom(n, floor(n\/2))$ chains, so each subset of $X$ appears exactly once in one chain. Then we are done (since to form an antichain, we can pick at most one element from each chain).
    - To achieve this, it is sufficient to find:
        - For each $r < n/2$, a matching from $X^((r))$ to $X^((r + 1))$ (a matching is a set of disjoint edges, one for each point in $X^((r))$).
        - For each $r > n/2$, a matching from $X^((r))$ to $X^((r - 1))$.
    - Then put these matchings together to form a set of chains, each passing through $X^((floor(n\/2)))$. If a subset $X^((floor(n\/2)))$ has a chain passing through it, then this chain is unique. The subsets with no chain passing through form their own one-element chain.
    - By taking complements, it is enough to construct the matchings just for $r < n/2$ (since a matching from $X^((r))$ to $X^((r + 1))$ induces a matching from $X^((n - r - 1))$ to $X^((n - r))$: there is a correspondence between $X^((r))$ and $X^((n - r))$ by taking complements, and taking complements reverse inclusion, so edges in the induced matching are guaranteed to exist).
    - Let $G$ be the (bipartite) subgraph of $Q_n$ spanned by $X^((r)) union X^((r + 1))$.
    - For any $S subset.eq X^((r))$, the number of $S$-$Gamma(S)$ edges in $G$ is $|S|(n - r)$ (counting from below) since there are $n - r$ ways to add an element.
    - This number is $<= |Gamma(S)| (r + 1)$ (counting from above), since $r + 1$ ways to remove an element.
    - Hence $|Gamma(S)| >= (|S| (n - r))/(r + 1) >= |S|$ as $r < n/2$.
    - So by Hall's theorem, since there is a matching from $S$ to $Gamma(S)$, there is a matching from $X^((r))$ to $X^((r + 1))$.
]
#remark[
    The proof above doesn't tell us when we have equality in Sperner's Lemma.
]
#definition[
    For $cal(A) subset.eq X^((r))$ ($1 <= r <= n$), the *shadow* of $cal(A)$ is the set of subsets which can be obtained by removing one element from a subset in $cal(A)$: $
        partial cal(A) = partial^- cal(A) := {B in X^((r - 1)): B subset.eq cal(A) "for some" A in cal(A)}.
    $
]<def:shadow>
#example[
    Let $cal(A) = {123, 124, 134, 137} in [7]^((3))$. Then $partial cal(A) = {12, 13, 23, 14, 24, 34, 17, 37}$.
]
#proposition(name: "Local LYM")[
    Let $cal(A) subset.eq X^((r))$, $1 <= r <= n$. Then $
        (|partial cal(A)|)/binom(n, r - 1) >= (|cal(A)|)/binom(n, r).
    $ i.e. the proportion of the level occupied by $partial cal(A)$ is at least the proportion of the level occupied by $cal(A)$.
]<prop:local-lym>
#proofhints[
    Find equation and upper bound for number of $cal(A)$-$partial cal(A)$ edges in $Q_n$.
]
#proof[
    - The number of $cal(A)$-$partial cal(A)$ edges in $Q_n$ is $|A|r$ (counting from above, since we can remove any of $r$ elements from $|A|$ sets) and is $<= |partial cal(A)| (n - r + 1)$ (since adding one of the $n - r + 1$ elements not in $A in partial cal(A)$ to $A$ may not result in a subset of $cal(A)$).
    - So $(|partial cal(A)|)/(|cal(A)|) >= r/(n - r + 1) = binom(n, r - 1)\/binom(n, r)$.
]
#remark[
    For equality in Local LYM, we must have that $forall A in cal(A)$, $forall i in A$, $forall j in.not A$, we must have $(A - {i}) union {j} in cal(A)$, i.e. $cal(A) = emptyset$ or $X^((r))$ for some $r$.
]
#notation[
    Write $cal(A)_r$ for $cal(A) sect X^((r))$.
]
#theorem(name: "LYM Inequality")[
    Let $cal(A) subset.eq powset(X)$ be an antichain. Then $
        sum_(r = 0)^n (|cal(A) sect X^((r))|)/binom(n, r) <= 1.
    $
]<thm:lym-inequality>
#proofhints[
    - Method 1: show the result for the sum $sum_(r = k)^n$ by induction, starting with $k = n$. Use local LYM, and that $partial cal(A)_n$ and $cal(A)_(n - 1)$ are disjoint (and analogous results for lower levels).
    - Method 2: let $cal(C)$ be uniformly random maximal chain, find an expression for $Pr(cal(C) "meets" cal(A))$.
    - Method 3: determine number of maximal chains in $X$, determine number of maximal chains passing through a fixed $r$-set, deduce maximal number of chains passing through $cal(A)$.
]
#proof[
    - Method 1: "bubble down with local LYM".
        - We trivially have that $cal(A)_n \/ binom(n, n) <= 1$.
        - $partial cal(A)_n$ and $cal(A)_(n - 1)$ are disjoint, as $cal(A)$ is an antichain.
        - So $ (|partial cal(A)_n|)/binom(n, n - 1) + (|cal(A)_(n - 1)|)/binom(n, n - 1) = (|partial cal(A)_n union cal(A)_(n - 1)|)/binom(n, n - 1) <= 1. $
        - So by local LYM, $ (|cal(A)_n|)/binom(n, n) + (|cal(A)_(n - 1)|)/binom(n, n - 1) <= 1. $
        - Now, $partial (partial A_n union A_(n - 1))$ and $cal(A)_(n - 2)$ are disjoint, as $cal(A)$ is an antichain.
        - So $ (|partial(partial cal(A)_n union cal(A)_(n - 1))|)/binom(n, n - 2) + (|cal(A)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - So by local LYM, $ (|partial A_n union cal(A)_(n - 1)|)/binom(n, n - 1) + (|cal(A)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - So $ (|cal(A)_n|)/binom(n, n) + (|cal(A)_(n - 1)|)/binom(n, n - 1) + (|cal(A)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - Continuing inductively, we obtain the result.
    - Method 2:
        - Choose uniformly at random a maximal chain $cal(C)$ (i.e. $C_0 subset.neq C_1 subset.eq dots.c subset.neq C_n$ with $abs(C_r) = r$ for all $r$).
        - For any $r$-set $A$, $Pr(A in cal(C)) = 1\/binom(n, r)$, since all $r$-sets are equally likely.
        - So $Pr(cal(C) "meets" cal(A)_r) = abs(cal(A)_r)\/binom(n, r)$, since events are disjoint.
        - So $Pr(cal(C) "meets" cal(A)) = sum_(r = 0)^n abs(cal(A)_r)\/binom(n, r) <= 1$ since events are disjoint (since $cal(A)$ is an antichain).
    - Method 3: equivalently, the number of maximal chains is $n!$, and the number through any fixed $r$-set is $r! (n - r)!$, so $sum_r abs(cal(A)_r) r! (n - r)! <= n!$.
]
#remark[
    To have equality in LYM, we must have equality in each use of local LYM in proof method 1. In this case, the maximum $r$ with $cal(A)_r != emptyset$ has $cal(A)_r = X^((r))$. So equality holds iff $cal(A) = X^((r))$ for some $r$. Hence equality in Sperner's Lemma holds iff $cal(A) = X^((floor(n\/2)))$ or $cal(A) = X^((ceil(n\/2)))$.
]

== Two total orders on $X^((r))$

#definition[
    Let $A != B$ be $r$-sets, $A = a_1 ... a_r$, $B = b_1 ... b_r$ (where $a_1 < dots.c < a_n$, $b_1 < dots.c < b_n$). $A < B$ in the *lexicographic (lex)* ordering if for some $j$, we have $a_i = b_i$ for all $i < j$, and $a_j < b_j$.
]<def:lex-order>
#example[
    The elements of $[4]^((2))$ in lexicographic order are $12, 13, 14, 23, 24, 34$. The elements of $[6]^((3))$ in lexicographic order are $123, 124, 125, 126, 134, 135, 136, 145, 146, 156, 234, 235, 236, 245, 246, 256, 345, 346, 356, 456$.
]
#definition[
    Let $A != B$ be $r$-sets, $A = a_1 ... a_r$, $B = b_1 ... b_r$ (where $a_1 < dots.c < a_n$, $b_1 < dots.c < b_n$). $A < B$ in the *colexicographic (colex)* order if for some $j$, we have $a_i = b_i$ for all $i > j$, and $a_j < b_j$. "avoid large elements".
]<def:colex-order>
#example[
    The elements of $[4]^((2))$ in colex order are $12, 13, 23, 14, 24, 34$. The elements of $[6]^((3))$ are $123, 124, 134, 234, 125, 135, 235, 145, 245, 345, 126, 136, 236, 146, 246, 346, 156, 256, 356, 456$.
]
#remark[
    Lex and colex are both total orders. Note that in colex, $[n - 1]^((r))$ is an initial segment of $[n]^((r))$ (this does not hold for lex). So we can view colex as an enumeration of $NN^((r))$.
]
#remark[
    $A < B$ in colex iff $A^c < B^c$ in lex with ground set order reversed.
]
#remark[
    We want to show that if $cal(A) subset.eq X^((r))$ and $cal(C) subset.eq X^((r))$ is the initial segment of colex with $abs(cal(C)) = abs(cal(A))$, then $abs(partial cal(C)) <= abs(partial cal(A))$. In particular, if $abs(cal(A)) = binom(k, r)$, then $abs(partial cal(A)) >= binom(k, r - 1)$.
]

== Compressions

#remark[
    We want to transform $cal(A) subset.eq X^((r))$ into some $cal(A)' subset.eq X^((r))$ such that:
    - $abs(cal(A)') = abs(cal(A))$,
    - $abs(partial cal(A)') <= abs(partial cal(A))$.
    Ideally, we want a family of such "compressions" $cal(A) -> cal(A)' -> ... -> cal(B)$ such that either $cal(B) = cal(C)$, or $cal(B)$ is similar enough to $cal(C)$ that we can directly check that $abs(partial cal(B)) >= abs(partial cal(C))$.
]

== Shadows

#remark[
    By Local LYM, we know that $abs(partial cal(A)) >= abs(cal(A)) r\/(n - r + 1)$. Equality is rare (only for $cal(A) = X^((r))$ for $0 <= r <= n$). What happens in between, i.e., given $abs(cal(A))$, how should we choose $cal(A)$ to minimise $abs(partial A)$?

    You should be able to convince yourself that if $abs(cal(A)) = binom(k, r)$, then we should take $cal(A) = [k]^((r))$. If $binom(k, r) < abs(cal(A)) < binom(k + 1, r)$, then convince yourself that we should take some $[k]^((r))$ plus some $r$-sets in $[k + 1]^((r))$.

    E.g. for $cal(A) subset.eq X^((r))$ with $abs(cal(A)) = binom(8, 3) + binom(4, 2)$, take $cal(A) = [8]^((3)) union \{9 union B: B in [4]^((2))\}$.
]


= Isoperimetric inequalities




= Intersecting families