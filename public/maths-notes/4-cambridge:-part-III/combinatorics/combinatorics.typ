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
    A chain $cal(A) subset.eq powset([n])$ can have at most $n + 1$ elements.
]
#proof[
    For each $0 <= r <= n$, $cal(A)$ can contain at most $1$ $r$-set (set of size $r$).
]
#theorem(name: "Sperner's Lemma")[
    Let $cal(A) subset.eq powset(X)$ be an antichain. Then $|cal(A)| <= binom(n, floor(n\/2))$, i.e. the maximum size of an antichain is achieved by the set of $X^((floor(n\/2)))$.
]<thm:sperners-lemma>
#proof[
    - We use the idea: from "a chain meets each layer in $<=1$ points, because a layer is an antichain", we try to decompose the cube into chains.
    - We decompose $powset(X)$ into $binom(n, floor(n\/2))$ chains, then we are done (since a chain cannot contain a subset of a chain of size $> 1$).
    - To achieve this, it is sufficient to find:
        - For each $r < n/2$, a matching from $X^((r))$ to $X^((r + 1))$ (a matching is a set of disjoint edges, one for each point in $X^((r))$).
        - For each $r > n/2$, a matching from $X^((r))$ to $X^((r - 1))$.
    - Then put these matchings together to form a set of chains, each passing through $X^((floor(n\/2)))$.
    - By taking complements, it is enough to construct the matchings just for $r < n/2$.
    - Let $G$ be the (bipartite) subgraph of $Q_n$ spanned by $X^((r)) union X^((r + 1))$.
    - For any $S subset.eq X^((r))$, the number of $S$-$Gamma(S)$ edges in $G$ is $|S|(n - r)$ (counting from below) since there are $n - r$ ways to add an element.
    - This number is $<= |Gamma(S)| (r + 1)$ (counting from above), since $r + 1$ ways to remove an element.
    - Hence $|Gamma(S)| <= (|S| (n - r))/(r + 1) >= |S|$ as $r < n/2$.
    - So by Hall's theorem, there is a matching from $S$ to $Gamma(S)$.
]
#remark[
    The proof above doesn't tell us when we have equality in Sperner's Lemma.
]
#definition[
    For $cal(A) subset.eq X^((r))$ ($1 <= r <= n$), the *shadow* of $cal(A)$ is $
        partial cal(A) = partial^- cal(A) := {B in X^((r - 1)): B subset.eq cal(A) "for some" A in cal(A)}.
    $
]<def:shadow>
#example[
    Let $cal(A) = {123, 124, 134, 137} in [7]^((3))$. Then $partial cal(A) = {12, 13, 23, 14, 24, 34, 17, 37}$.
]
#proposition(name: "Local LYM")[
    Let $cal(A) subset.eq X^((r))$, $1 <= r <= n$. Then $
        (|partial cal(A)|)/binom(r, r - 1) >= (|cal(A)|)/binom(n, r).
    $ i.e. the proportion of the level occupied by $partial cal(A)$ is at least the proportion of the level occupied by $cal(A)$.
]<prop:local-lym>
#proof[
    - The number of $cal(A)$-$partial cal(A)$ edges in $Q_n$ is $|A|r$ (counting from above) and is $<= |partial cal(A)| (n - r + 1)$.
    - So $(|partial cal(A)|)/(|cal(A)|) >= r/(n - r + 1) = binom(n, r - 1)\/binom(n, r)$.
]
#remark[
    For equality in Local LYM, we must have that $forall A in cal(A)$, $forall i in A$, $forall j in A$, we must have $A - {i} union {j} in cal(A)$, i.e. $cal(A) = emptyset$ or $X^((r))$.
]
#notation[
    Write $cal(A)_r$ for $cal(A) sect X^((r))$.
]
#theorem(name: "LYM Inequality")[
    Let $cal(A) subset.eq powset(X)$ be an antichain. Then $
        sum_(r = 0)^n (|cal(A) sect X^((r))|)/binom(n, r) <= 1.
    $
]<thm:lym-inequality>
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
]
#remark[
    To have equality in LYM, we must have equality in each use of LYM in proof method 1. In this case, the maximum $r$ with $cal(A)_r != emptyset$ has $cal(A)_r = X^((r))$. So equality holds iff $cal(A) = X^((r))$ for some $r$. Hence equality in Sperner's Lemma holds iff $cal(A) = X^((floor(n\/2)))$ or $cal(A) = X^((ceil(n\/2)))$.
]


= Isoperimetric inequalities




= Intersecting families