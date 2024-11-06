#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

= Set systems

== Chains and antichains

#note[
    The ideas in combinatorics often occur in the proofs, so it is advisable to learn the techniques used in proofs, rather than just learning the results and not their proofs.
]
#definition[
    Let $X$ be a set. A *set system* on $X$ (also called a *family of subsets of $X$*) is a collection $cal(F) subset.eq powset(X)$.
]<def:family>
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
    $cal(F) subset.eq powset(X)$ is a *chain* if $forall A, B in cal(F)$, $A subset.eq B$ or $B subset.eq A$.
]<def:chain>
#example[
    - $cal(F) = {23, 1235, 123567}$ is a chain.
    - $cal(F) = {emptyset, 1, 12, ..., [n]} subset.eq powset([n])$ is a chain.
]
#definition[
    $cal(F) subset.eq powset(X)$ is an *antichain* if $forall A != B in cal(F)$, $A subset.eq.not B$.
]<def:antichain>
#example[
    - $cal(F) = {23, 137}$ is an antichain.
    - $cal(F) = {1, ..., n} subset.eq powset([n])$ is an antichain.
    - More generally, $cal(F) = X^((r))$ is an antichain for any $r$.
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
    A chain $cal(F) subset.eq powset([n])$ can have at most $n + 1$ elements.
]
#proofhints[
    Trivial.
]
#proof[
    For each $0 <= r <= n$, $cal(F)$ can contain at most $1$ $r$-set (set of size $r$).
]
#theorem("Sperner's Lemma")[
    Let $cal(F) subset.eq powset(X)$ be an antichain. Then $|cal(F)| <= binom(n, floor(n\/2))$, i.e. the maximum size of an antichain is achieved by the set of $X^((floor(n\/2)))$.
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
    For $cal(F) subset.eq X^((r))$ ($1 <= r <= n$), the *shadow* of $cal(F)$ is the set of subsets which can be obtained by removing one element from a subset in $cal(F)$: $
        partial cal(F) = partial^- cal(F) := {B in X^((r - 1)): B subset.eq cal(F) "for some" A in cal(F)}.
    $
]<def:shadow>
#example[
    Let $cal(F) = {123, 124, 134, 137} in [7]^((3))$. Then $partial cal(F) = {12, 13, 23, 14, 24, 34, 17, 37}$.
]
#proposition("Local LYM")[
    Let $cal(F) subset.eq X^((r))$, $1 <= r <= n$. Then $
        (|partial cal(F)|)/binom(n, r - 1) >= (|cal(F)|)/binom(n, r).
    $ i.e. the proportion of the level occupied by $partial cal(F)$ is at least the proportion of the level occupied by $cal(F)$.
]<prop:local-lym>
#proofhints[
    Find equation and upper bound for number of $cal(F)$-$partial cal(F)$ edges in $Q_n$.
]
#proof[
    - The number of $cal(F)$-$partial cal(F)$ edges in $Q_n$ is $|A|r$ (counting from above, since we can remove any of $r$ elements from $|A|$ sets) and is $<= |partial cal(F)| (n - r + 1)$ (since adding one of the $n - r + 1$ elements not in $A in partial cal(F)$ to $A$ may not result in a subset of $cal(F)$).
    - So $(|partial cal(F)|)/(|cal(F)|) >= r/(n - r + 1) = binom(n, r - 1)\/binom(n, r)$.
]
#remark[
    For equality in Local LYM, we must have that $forall A in cal(F)$, $forall i in A$, $forall j in.not A$, we must have $(A - {i}) union {j} in cal(F)$, i.e. $cal(F) = emptyset$ or $X^((r))$ for some $r$.
]
#notation[
    Write $cal(F)_r$ for $cal(F) sect X^((r))$.
]
#theorem("LYM Inequality")[
    Let $cal(F) subset.eq powset(X)$ be an antichain. Then $
        sum_(r = 0)^n (|cal(F) sect X^((r))|)/binom(n, r) <= 1.
    $
]<thm:lym-inequality>
#proofhints[
    - Method 1: show the result for the sum $sum_(r = k)^n$ by induction, starting with $k = n$. Use local LYM, and that $partial cal(F)_n$ and $cal(F)_(n - 1)$ are disjoint (and analogous results for lower levels).
    - Method 2: let $cal(C)$ be uniformly random maximal chain, find an expression for $Pr(cal(C) "meets" cal(F))$.
    - Method 3: determine number of maximal chains in $X$, determine number of maximal chains passing through a fixed $r$-set, deduce maximal number of chains passing through $cal(F)$.
]
#proof[
    - Method 1: "bubble down with local LYM".
        - We trivially have that $cal(F)_n \/ binom(n, n) <= 1$.
        - $partial cal(F)_n$ and $cal(F)_(n - 1)$ are disjoint, as $cal(F)$ is an antichain.
        - So $ (|partial cal(F)_n|)/binom(n, n - 1) + (|cal(F)_(n - 1)|)/binom(n, n - 1) = (|partial cal(F)_n union cal(F)_(n - 1)|)/binom(n, n - 1) <= 1. $
        - So by local LYM, $ (|cal(F)_n|)/binom(n, n) + (|cal(F)_(n - 1)|)/binom(n, n - 1) <= 1. $
        - Now, $partial (partial cal(F)_n union cal(F)_(n - 1))$ and $cal(F)_(n - 2)$ are disjoint, as $cal(F)$ is an antichain.
        - So $ (|partial(partial cal(F)_n union cal(F)_(n - 1))|)/binom(n, n - 2) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - So by local LYM, $ (|partial cal(F)_n union cal(F)_(n - 1)|)/binom(n, n - 1) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - So $ (|cal(F)_n|)/binom(n, n) + (|cal(F)_(n - 1)|)/binom(n, n - 1) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - Continuing inductively, we obtain the result.
    - Method 2:
        - Choose uniformly at random a maximal chain $cal(C)$ (i.e. $C_0 subset.neq C_1 subset.eq dots.c subset.neq C_n$ with $abs(C_r) = r$ for all $r$).
        - For any $r$-set $A$, $Pr(A in cal(C)) = 1\/binom(n, r)$, since all $r$-sets are equally likely.
        - So $Pr(cal(C) "meets" cal(F)_r) = abs(cal(F)_r)\/binom(n, r)$, since events are disjoint.
        - So $Pr(cal(C) "meets" cal(F)) = sum_(r = 0)^n abs(cal(F)_r)\/binom(n, r) <= 1$ since events are disjoint (since $cal(F)$ is an antichain).
    - Method 3: equivalently, the number of maximal chains is $n!$, and the number through any fixed $r$-set is $r! (n - r)!$, so $sum_r abs(cal(F)_r) r! (n - r)! <= n!$.
]
#remark[
    To have equality in LYM, we must have equality in each use of local LYM in proof method 1. In this case, the maximum $r$ with $cal(F)_r != emptyset$ has $cal(F)_r = X^((r))$. So equality holds iff $cal(F) = X^((r))$ for some $r$. Hence equality in Sperner's Lemma holds iff $cal(F) = X^((floor(n\/2)))$ or $cal(F) = X^((ceil(n\/2)))$.
]

== Two total orders on $X^((r))$

#definition[
    Let $A != B$ be $r$-sets, $A = a_1 ... a_r$, $B = b_1 ... b_r$ (where $a_1 < dots.c < a_n$, $b_1 < dots.c < b_n$). $A < B$ in the *lexicographic (lex)* ordering if for some $j$, we have $a_i = b_i$ for all $i < j$, and $a_j < b_j$. "use small elements".
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
    By Local LYM, we know that $abs(partial cal(F)) >= abs(cal(F)) r\/(n - r + 1)$. Equality is rare (only for $cal(F) = X^((r))$ for $0 <= r <= n$). What happens in between, i.e., given $abs(cal(F))$, how should we choose $cal(F)$ to minimise $abs(partial cal(F))$?

    You should be able to convince yourself that if $abs(cal(F)) = binom(k, r)$, then we should take $cal(F) = [k]^((r))$. If $binom(k, r) < abs(cal(F)) < binom(k + 1, r)$, then convince yourself that we should take some $[k]^((r))$ plus some $r$-sets in $[k + 1]^((r))$.

    E.g. for $cal(F) subset.eq X^((r))$ with $abs(cal(F)) = binom(8, 3) + binom(4, 2)$, take $cal(F) = [8]^((3)) union \{9 union B: B in [4]^((2))\}$.
]
#remark[
    We want to show that if $cal(F) subset.eq X^((r))$ and $cal(C) subset.eq X^((r))$ is the initial segment of colex with $abs(cal(C)) = abs(cal(F))$, then $abs(partial cal(C)) <= abs(partial cal(F))$. In particular, if $abs(cal(F)) = binom(k, r)$ (so $cal(C) = [k]^((r))$), then $abs(partial cal(F)) >= binom(k, r - 1)$.
]

== Compressions

#remark[
    We want to transform $cal(F) subset.eq X^((r))$ into some $cal(F)' subset.eq X^((r))$ such that:
    - $abs(cal(F)') = abs(cal(F))$,
    - $abs(partial cal(F)') <= abs(partial cal(F))$.
    Ideally, we want a family of such "compressions" $cal(F) -> cal(F)' -> ... -> cal(B)$ such that either $cal(B) = cal(C)$, or $cal(B)$ is similar enough to $cal(C)$ that we can directly check that $abs(partial cal(C)) <= abs(partial cal(B))$.
]
#definition[
    Let $1 <= i < j <= n$. The *$i j$-compression* $C_(i j)$ is defined as:
    - For $A in X^((r))$, $
        C_(i j) (A) = cases(
            (A union i) - j & "if" j in A\, i in.not A,
            A & "otherwise"
        ).
    $
    - For $cal(F) subset.eq X^((r))$, $C_(i j)(A) = {C_(i j) (A): A in cal(F)} union {A in cal(F): C_(i j) (A) in cal(F)}$.
    "replace $j$ by $i$ where possible". This definition is inspired by "colex prefers $i < j$ to $j$".
    Note that $C_(i j) (cal(F)) subset.eq X^((r))$ and $abs(C_(i j)(cal(F))) = abs(cal(F))$.
]<def:compression>
#definition[
    $cal(F)$ is *$i j$-compressed* if $C_(i j) (cal(F)) = cal(F)$.
]<def:compressed>
#example[
    Let $cal(F) = {123, 134, 234, 235, 146, 567}$, then $C_(1 2) (cal(F)) = {123, 134, 234, 135, 146, 567}$.
]
#lemma[
    Let $cal(F) subset.eq X^((r))$, $1 <= i < j <= n$. Then $abs(partial C_(i j) (cal(F))) <= abs(partial cal(F))$.
]
#proofhints[
    - Let $cal(F)' = C_(i j)(cal(F))$, $B in partial cal(F)' - partial cal(F)$.
    - Show that $i in B$ and $j in.not B$.
    - Reason that $B union j - i in partial cal(F)'$.
    - Show that $B union j - i in.not partial cal(F)'$ by contradiction.
    - Conclude the result.
]
#proof[
    - Let $cal(F)' = C_(i j)(cal(F))$. Let $B in partial cal(F)' - partial cal(F)$.
    - We'll show that $i in B$, $j in.not B$, $(B union j) - i in partial cal(F) - partial cal(F)'$.
    - $B union x in cal(F)'$ and $B union x in.not cal(F)$ (since $B in.not partial cal(F)$) for some $x$.
    - So $i in B union x$, $j in.not B union x$, $(B union x union j) - i in cal(F)$.
    - We can't have $x = i$, since otherwise $(B union x union j) - i = B union j$, which gives $B in partial cal(F)$, a contradiction.
    - So $i in B$ and $j in.not B$.
    - Also, $B union j - i in partial cal(F)$, since $B union x union j - i in cal(F)$.
    - Suppose $B union j - i in partial cal(F)'$: so $(B union j - i) union y in cal(F)'$ for some $y$.
    - We cannot have $y = i$, since otherwise $B union j in cal(F)'$, so $B union j in cal(F)$ (as $j in B union j$), contradicting $B in.not partial cal(F)$.
    - Hence $j in (B union j - i) union y$ and $i in.not (B union j - i) union y$.
    - Thus, both $(B union j - i) union y$ and $B union y = C_(i j) ((B union j - i) union y)$ belong to $cal(F)$ (by definition of $cal(F)'$), contradicting $B in.not partial cal(F)$.
]
#remark[
    In the above proof, we actually showed that $partial C_(i j) (cal(F)) subset.eq C_(i j) (partial cal(F))$.
]
#definition[
    $cal(F) subset.eq X^((r))$ is *left-compressed* if $C_(i j) (cal(F)) = cal(F)$ for all $i < j$.
]<def:left-compressed>
#corollary[
    Let $cal(F) subset.eq X^((r))$. Then there exists a left-compressed $cal(B) subset.eq X^((r))$ with $abs(cal(B)) = abs(cal(F))$ and $abs(partial cal(B)) <= abs(partial cal(F))$.
]
#proofhints[
    Define a sequence $cal(F)_0, cal(F)_1, ...$ of subsets of $X^((r))$ with $sum_(A in cal(F)_k) sum_(i in A) i$ strictly decreasing.
]
#proof[
    - Define a sequence $cal(F)_0, cal(F)_1, ...$ as follows:
    - $cal(F)_0 = cal(F)$. Having defined $cal(F)_0, ..., cal(F)_k$, if $cal(F)_k$ is left-compressed the end the sequence with $cal(F)_k$.
    - If not, choose $i < j$ such that $cal(F)_k$ is not $i j$-compressed, and set $cal(F)_(k + 1) = C_(i j)(cal(F)_k)$.
    - This must terminate after a finite number of steps, e.g. since $sum_(A in cal(F)_k) sum_(i in A) i$ is strictly decreasing with $k$.
    - The final term $cal(B) = cal(F)_k$ satisfies $abs(cal(B)) = abs(cal(F))$, and $abs(partial cal(B)) <= abs(partial cal(F))$ by the above lemma.
]
#remark[
    - Another way of proving this is: among all $cal(B) subset.eq X^((r))$ with $abs(cal(F)) = abs(cal(F))$ and $abs(partial cal(B)) <= abs(partial cal(F))$, choose one with minimal $sum_(A in cal(B)) sum_(i in A) i$.
    - We can choose an order of the $C_(i j)$ so that no $C_(i j)$ is applied twice.
    - Any initial segment of colex is left-compressed, but the converse is false, e.g. ${123, 124, 125, 126}$ is left-compressed.
]
#definition[
    Let $U, V subset.eq X$, $abs(U) = abs(V)$, $U sect V = emptyset$ and $max U < max V$. Define the *$U V$-compression* $C_(U V)$ as:
    - For $A subset.eq X$, $
        C_(U V)(A) = cases(
            (A - V) union U & "if" V subset.eq A\, U sect A = emptyset,
            A & "otherwise"
        ).
    $
    - For $cal(F) subset.eq X^((r))$, $
        C_(U V) (cal(F)) = {C_(U V) (A): A in cal(F)} union {A in cal(F): C_(U V)(A) in cal(F)}.
    $
    We have $C_(U V)(cal(F)) subset.eq X^((r))$ and $abs(C_(U V)(cal(F))) = abs(cal(F))$.
    This definition is inspired by "colex prefers $23$ to $14$".
]
#definition[
    $cal(F)$ is *$U V$-compressed* if $C_(U V)(cal(F)) = cal(F)$.
]
#example[
    Let $cal(F) = {123, 124, 147, 237, 238, 149}$, then $C_(23, 14) (cal(F)) = {123, 124, 147, 237, 238, 239}$.
]
#example[
    We can have $abs(partial C_(U V)(cal(F))) > abs(partial cal(F))$.
    E.g. $cal(F) = {147, 157}$ has $abs(partial cal(F)) = 5$, but $C_(23, 14)(cal(F)) = {237, 157}$ has $abs(partial C_(23, 14)(cal(F))) = 6$.
]
#lemma[
    Let $cal(F) subset.eq X^((r))$ be $U V$-compressed for all $U, V subset.eq X$ with $abs(U) = abs(V)$, $U sect V = emptyset$ and $max U < max V$. Then $cal(F)$ is an initial segment of colex.
]
#proofhints[
    Suppose not, consider a compression for appropriate $U$ and $V$.
]
#proof[
    - Suppose not, then there exists $A, B in X^((r))$ with $B < A$ in colex but $A in cal(F)$, $B in.not cal(F)$.
    - Let $V = A \\ B$, $U = B \\ A$. Then $abs(V) = abs(U)$, $U sect V = emptyset$, and $max V > max U$ (since $max(A Delta B) in A$, by definition of colex).
    - Since $cal(F)$ is $U V$-compressed, we have $C_(U V)(A) = B in C_(U V)(cal(F)) = cal(F)$, contradiction.
]
#lemma[
    Let $U, V subset.eq X$, $abs(U) = abs(V)$, $U sect V = emptyset$, $max U < max V$. For $cal(F) subset.eq X^((r))$, suppose that $
        forall u in U, exists v in V: quad cal(F) "is" #[$(U - u, V - v)$-compressed].
    $ Then $abs(partial C_(U V)(cal(F))) <= abs(partial cal(F))$.
]
#proofhints[
    - Let $cal(F)' = C_(U V)(cal(F))$, $B in partial cal(F)' - partial cal(F)$.
    - Show that $U subset.eq B$ and $V sect B = emptyset$.
    - Reason that $(B - U) union V in partial cal(F)$.
    - Show that $(B - U) union V in.not partial cal(F)'$ by contradiction.
]
#proof[
    - Let $cal(F)' = C_(U V)(cal(F))$. For $B in partial cal(F)' - partial cal(F)$, we will show that $U subset.eq B$, $V sect B = emptyset$ and $B union V - U in partial cal(F) - partial cal(F)'$, then we will be done.
    - We have $B union x in cal(F)'$ for some $x in X$, and $B union x in.not cal(F)$.
    - So $U subset.eq B union x$, $V sect (B union x) = emptyset$, and $(B union x union V) - U in cal(F)$, by definition of $C_(U V)$.
    - If $x in U$, then $exists y in V$ such that $cal(F)$ is $(U - x, V - y)$-compressed, so from $(B union x union V) - U in cal(F)$, we have $B union y in cal(F)$, contradicting $B in.not partial cal(F)$.
    - Thus $x in.not U$, so $U subset.eq B$ and $V sect B = emptyset$.
    - Certainly $B union V - U in partial cal(F)$ (since $(B union x union V) - U in cal(F)$), so we just need to show that $B union V - U in.not partial cal(F)'$.
    - Assume the opposite, i.e. $(B - U) union V in partial cal(F)'$, so $(B - U) union V union w in cal(F)'$ for some $w in X$. (This also belongs to $cal(F)$, since it contains $V$).
    - If $w in U$, then since $cal(F)$ is $(U - w, V - z)$-compressed for some $z in V$, we have $B union z = C_(U - w, V - z)((B - U) union V union w) in cal(F)$, contradicting $B in.not partial cal(F)$.
    - So $w in.not U$, and since $V subset.eq (B - U) union V union w$ and $U sect ((B - U) union V union w) = emptyset$, by definition of $C_(U V)$, we must have that both $(B - U) union V union w$ and $B union w = C_(U V)((B - U) union V union w) in cal(F)$, contradicting $B in.not partial cal(F)$.
]
#theorem("Kruskal-Katona")[
    Let $cal(F) subset.eq X^((r))$, $1 <= r <= n$, let $cal(C)$ be the initial segment of colex on $X^((r))$ with $abs(cal(C)) = abs(cal(F))$. Then $abs(partial cal(C)) <= abs(partial cal(F))$.

    In particular, if $abs(cal(F)) = binom(k, r)$, then $abs(partial cal(F)) >= binom(k, r - 1)$.
]<thm:kruskal-katona>
#proofhints[
    - Let $Gamma = {(U, V) in powset(X) times powset(X): abs(U) = abs(V) > 0, U sect V = emptyset, max U < max V} union {(emptyset, emptyset)}$.
    - Define a sequence $cal(F)_0, cal(F)_1, ...$ of $U V$-compressions where $(U, V) in Gamma$, choosing $abs(U) = abs(V) > 0$ minimal each time. Show that this $(U, V)$ satisfies condition of above lemma.
    - Reason that sequence terminates by considering $sum_(A in cal(F)_k) sum_(i in A) 2^i$.
]
#proof[
    - Let $Gamma = {(U, V) in powset(X) times powset(X): abs(U) = abs(V) > 0, U sect V = emptyset, max U < max V} union {(emptyset, emptyset)}$.
    - Define a sequence $cal(F)_0, cal(F)_1, ...$ of set systems in $X^((r))$ as follows:
        - Let $cal(F)_0 = cal(F)$. Having chosen $cal(F)_0, ..., cal(F)_k$, if $cal(F)_k$ is $(U V)$-compressed for all $(U, V) in Gamma$ then stop.
        - Otherwise, choose $(U, V) in Gamma$ with $abs(U) = abs(V) > 0$ minimal, such that $cal(F)_k$ is not $(U V)$-compressed.
        - Note that $forall u in U$, $exists v in V$ such that $(U - u, V - v) in Gamma$ (namely $v = min(V)$).
        - So by the above lemma, $abs(partial C_(U V) (cal(F)_k)) <= abs(partial cal(F)_k)$. Set $cal(F)_(k + 1) = C_(U V) (cal(F)_k)$, and continue.
    - The sequence must terminate, as $sum_(A in cal(F)_k) sum_(i in A) 2^i$ is strictly decreasing with $k$.
    - The final term $cal(B) = cal(F)_k$ satisfies $abs(cal(B)) = abs(cal(F))$, $abs(partial cal(B)) <= abs(partial cal(F))$, and is $(U V)$-compressed for all $(U, V) in Gamma$.
    - So $cal(B) = cal(C)$ by lemma before previous lemma.
]
#remark[
    - Equivalently, if $abs(cal(F)) = binom(k_r, r) + binom(k_(r - 1), r - 1) + dots.c + binom(k_s, s)$ where each $k_i > k_(i - 1)$ and $s >= 1$, then $
        abs(partial cal(F)) >= binom(k_r, r - 1) + binom(k_(r - 1), r - 2) + dots.c + binom(k_s, s - 1).
    $
    - Equality in Kruskal-Katona: if $abs(cal(F)) = binom(k, r)$ and $abs(partial cal(F)) = binom(k, r - 1)$, then $cal(F) = Y^((r))$ for some $Y subset.eq X$ with $abs(Y) = k$. However, it is not true in general that if $abs(partial cal(F)) = abs(partial C)$, then $cal(F)$ is isomorphic to $cal(C)$ (i.e. there is a permutation of the ground set $X$ sending $cal(F)$ to $cal(C)$).
]
#definition[
    For $cal(F) subset.eq X^((r))$, $0 <= r <= n - 1$, the *upper shadow* of $cal(F)$ is $
        partial^+ cal(F) := {A union x: A in cal(F), x in.not A} subset.eq X^((r + 1)).
    $
]<def:upper-shadow>
#corollary[
    Let $cal(F) subset.eq X^((r))$, $0 <= r <= n - 1$, let $cal(C)$ be the initial segment of lex on $X^((r))$ with $abs(cal(C)) = abs(cal(F))$. Then $abs(partial^+ cal(C)) <= abs(partial^+ cal(F))$.
]
#proofhints[
    By Kruskal-Katona.
]
#proof[
    By Kruskal-Katona, since $A < B$ in colex iff $A^c < B^c$ in lex with ground-set ($X$) order reversed, and if $cal(F)' = {A^c: A in cal(F)}$, then $abs(partial^+ cal(F)') = abs(partial cal(F))$.
]
#remark[
    The fact that the shadow of an initial segment of colex on $X^((r))$ is an initial segment of colex on $X^((r - 1))$ (since if $cal(C) = {A in X^((r)): A <= a_1 ... a_r "in colex"}$, then $partial cal(C) = {B in X^((r - 1)): B <= a_2 ... a_r "in colex"}$) gives:
]
#corollary[
    Let $cal(F) subset.eq X^((r))$, $1 <= r <= n$, $cal(C)$ be the initial segment of colex on $X^((r))$ with $abs(cal(C)) = abs(cal(F))$. Then $abs(partial^t cal(C)) <= abs(partial^t cal(F))$ for all $1 <= t <= r$ (where $partial^t$ is shadow applied $t$ times).
]
#proofhints[
    Straightforward.
]
#proof[
    If $abs(partial^t cal(C)) <= abs(partial^t cal(F))$, then $abs(partial^(t + 1) cal(C)) <= abs(partial^(t + 1) cal(F))$, since $partial^t cal(C)$ is an initial segment of colex. So we are done by induction (base case is Kruskal-Katona).
]
#remark[
    So if $abs(cal(F)) = binom(k, r)$, then $abs(partial^t cal(F)) >= binom(k, r - t)$.
]

== Intersecting families

#definition[
    A family $cal(F) in powset(X)$ is *intersecting* if for all $A, B in cal(F)$, $A sect B != emptyset$.

    We are interested in finding intersecting families of maximum size.
]<def:family.intersecting>
#proposition[
    For all intersecting families $cal(F) subset.eq powset(X)$, $abs(cal(F)) <= 2^(n - 1) = 1/2 abs(powset(X))$.
]<prop:size-of-intersecting-family-is-at-most-half-of-size-of-powerset>
#proofhints[
    Straightforward.
]
#proof[
    Given any $A subset.eq X$, at most one of $A$ and $A^c$ can belong to $cal(F)$.
]
#example[
    - $cal(F) = {A subset.eq X: 1 in A}$ is intersecting, and $abs(cal(F)) = 2^(k - 1)$.
    - $cal(F) = {A subset.eq X: abs(A) > n/2}$ for $n$ odd.
]
#example[
    Let $cal(F) subset.eq X^((r))$:
    - If $r > n/2$, then $cal(F) = X^((r))$ is intersecting.
    - If $r = n/2$, then choose one of $A$ and $A^c$ for all $A in X^((r))$. This gives $abs(cal(F)) = 1/2 binom(n, r)$.
    - If $r < n/2$, then $cal(F) = {A in X^((r)): 1 in A}$ has size $binom(n - 1, r - 1) = r/n binom(n, r)$ (since the probability of a random $r$-set containing $1$ is $r/n$). If $(n, r) = (8, 3)$, then $abs(cal(F)) = binom(7, 2) = 21$.
    - Let $cal(F) = {A in X^((r)): abs(A sect {1, 2, 3}) >= 2}$. If $(n, r) = (8, 3)$, then $abs(cal(F)) = 1 + binom(3, 2) binom(5, 1) = 16 < 21$ (since $1$ set $A$ has $abs(B sect [3]) = 3$, $15$ sets $A$ have $abs(A sect [3]) = 2$).
]
#theorem("Erdos-Ko-Rado")[
    Let $cal(F) subset.eq X^((r))$ be an intersecting family, where $r < n/2$. Then $abs(cal(F)) <= binom(n - 1, r - 1)$.
]<thm:erdos-ko-rado>
#proofhints[
    - Method 1:
        - Let $overline(cal(F)) = {A^c: A in cal(F)}$. Show that $partial^(n - 2r) overline(cal(F))$ and $cal(F)$ are disjoint families of $r$-sets.
        - Assume the opposite, show that the size of the union of these two sets is greater than the size of $X^((r))$.
    - Method 2:
        - Let $c: [n] -> ZZ\/n$ be bijection, i.e. cyclic ordering of $[n]$. Show there at most $r$ sets in $cal(F)$ that are intervals (sets with $r$ consecutive elements) under this ordering.
        - Find expression for number of times an $r$-set in $cal(F)$ is an interval all possible orderings, and find an upper bound for this using the above.
]
#proof[
    Proof 1 ("bubble down with Kruskal-Katona"): note that $A sect B != emptyset$ iff $A subset.eq.not B^c$. Let $overline(cal(F)) = {A^c: A in cal(F)} subset.eq X^((n - r))$. We have $partial^(n - 2r) overline(cal(F))$ and $cal(F)$ are disjoint families of $r$-sets (if not, then there is some $A in cal(F)$ such that $A subset.eq B^c$ for some $B in cal(F)$, but then $A sect B = emptyset$). Suppose $abs(cal(F)) > binom(n - 1, r - 1)$. Then $abs(overline(cal(F))) = abs(cal(F)) > binom(n - 1, r - 1) = binom(n - 1, n - r)$. So by Kruskal-Katona, we have $abs(partial^(n - 2r) overline(cal(F))) >= binom(n - 1, r)$. So $abs(cal(F)) + abs(partial^(n - 2r) overline(cal(F))) > binom(n - 1, r - 1) + binom(n - 1, r) = binom(n, r) = abs(X^((r)))$, a contradiction, since $cal(F), partial^(n - 2r) overline(cal(F)) subset.eq X^((r))$.

    Proof 2: pick a cyclic ordering of $[n]$, i.e. a bijection $c: [n] -> ZZ\/n$. There are at most $r$ sets in $cal(F)$ that are intervals ($r$ consecutive elements) under this ordering: for $c_1 ... c_r in cal(F)$, for each $2 <= i <= r$, at most one of the two intervals $c_i ... c_(i + r - 1)$ and $c_(i - r) ... c_(i - 1)$ can belong to $cal(F)$, since they are disjoint and $cal(F)$ is intersecting (the indices of $c$ are taken $mod n$). For each $r$-set $A$, out of the $n!$ cyclic orderings, there are $n dot r! (n - r)!$ which map $A$ to an interval ($r!$ orderings inside $A$, $(n - r)!$ orderings outside $A$, $n$ choices for the start of the interval). Hence, by counting the number of times an $r$-set in $cal(F)$ is an interval under a given ordering (over all $r$-sets in $cal(F)$ and all cyclic orderings), we obtain $abs(cal(F)) n r! (n - r)! <= n! r$, i.e. $abs(cal(F)) <= binom(n - 1, r - 1)$.
]
#remark[
    - The calculation at the end of proof method 1 had to give the correct answer, as the shadow calculations would all be exact if $cal(F) = {A in X^((r)): 1 in A}$ (in this case, $cal(F)$ and $partial^(n - 2r) overline(cal(F))$ partition $X^((r))$).
    - The calculations at the end of proof method 2 had to work out, given equality for the family $cal(F) = {A in X^((r)): 1 in A}$.
    - In method 2, equivalently, we are double-counting the edges in the bipartite graph, where the vertex classes (partition sets) are $cal(F)$ and all cyclic orderings, with $A$ joined to $c$ if $A$ is an interval under $c$. This method is called *averaging* or *Katona's method*.
    - Equality in Erdos-Ko-Rado holds iff $cal(F) = {A in X^((r)): i in A}$, for some $1 <= i <= n$. This can be obtained from proof 1 and equality in Kruskal-Katona, or from proof 2.
]


= Isoperimetric inequalities

We seek to answer questions of the form "how do we minimise the boundary of a set of given size?"

#example[
    In the continuous setting:
    - Among all subsets of $RR^2$ of a given fixed area, the disc minimises the perimeter.
    - Among all subsets of $RR^3$ of a given fixed volume, the solid sphere minimises the surface area.
    - Among all subsets of $S^2$ of given fixed surface area, the circular cap minimises the perimeter.
]
#definition[
    For a $A$ of vertices of a graph $G$, the *boundary* of $A$ is $
        b(A) = {x in G: x in.not A, x y in E "for some" y in A}.
    $
]<def:vertex-set-boundary>
#definition[
    An *isoperimetric inequality* on a graph $G$ is an inequality of the form $
        forall A subset.eq G, quad abs(b(A)) >= f(abs(A))
    $ for some function $f: NN -> RR$.
]<def:isoperimetric-inequality>
#definition[
    The *neighbourhood* of $A subset.eq V(G)$ is $N(A) := A union b(A)$, i.e. $
        N(A) = {x in G: d(x, A) <= 1}.
    $
]<def:vertex-set-neighbourhood>
#example[
    A good (and natural) example for $A$ that minimises $abs(b(A))$ in the discrete cube $Q_n$ might be a ball $B(x, r) = {y in G: d(x, y) <= r}$. Let $A subset.eq powset(X) = V(Q_3)$, $abs(A) = 4$.

    A good guess is that balls are best, i.e. sets of the form $B(emptyset, r) = X^((<= r)) = X^((0)) union dots.c union X^((r))$. What if $abs(X^((<= r))) <= abs(A) <= abs(X^((<= r + 1)))$? A good guess is take $A$ with $X^((<= r)) subset.neq A subset.neq X^((<= r + 1))$. If $A = X^((<= r)) union B$, where $B subset.eq X^((r + 1))$, then $b(A) = (X^((r + 1)) - B) union partial^+ B$, so we would take $B$ to be an initial segment of lex by Kruskal-Katona. This motivates the following definition.
]
#definition[
    The *simplicial ordering* on $powset(X)$ defines $x < y$ if either $abs(x) < abs(y)$, or both $abs(x) = abs(y)$ and $x < y$ in lex.
]<def:simplicial-ordering>
We want to show the initial segments of the simplicial ordering minimise the boundary.
#definition[
    For $A subset.eq powset(X)$ and $1 <= i <= n$, the *$i$-sections* of $A$ are the families $A_-^((i)), A_+^((i)) subset.eq powset(X \\ i)$, given by $
        A_-^((i)) = A_- & := {x in A: i in.not x}, \
        A_+^((i)) = A_+ & := {x - i: x in A, i in x}
    $ Note that $A = A_-^((i)) union \{x union i: x in A_+^((i))\}$, so we can define a family by its $i$-sections.
]<def:i-sections>
#remark[
    When viewing $powset(X)$ as the $n$-dimensional cube $Q_n$, we view the $i$-sections as subgraphs of the $(n - 1)$-dimensional cube $Q_(n - 1)$ (which we view $powset(X \\ i)$ as).
]
#definition[
    The *$i$-compression* of $A subset.eq powset(X)$ is the family $C_i (A) subset.eq powset(X)$ given by its $i$-sections:
    - $(C_i (A))_-^((i))$ is the first $abs(A_-^((i)))$ elements of the simplicial order on $powset(X - i)$, and
    - $(C_i (A))_+^((i))$ is the first $abs(A_+^((i)))$ elements of the simplicial order on $powset(X - i)$.
    Note that $abs(C_i (A)) = abs(A)$, and $C_i (A)$ "looks more like" a Hamming ball than $A$ does.
]<def:i-compression>
#definition[
    $A subset.eq powset(X)$ is *$i$-compressed* if $C_i (A) = A$.
]<def:i-compressed>
#definition[
    A *Hamming ball* is a family $A subset.eq powset(X)$ with $X^((<= r)) subset.eq A subset.eq X^((<= r + 1))$ for some $r$.
]<def:hamming-ball>
#example[
    Note that a set that is $i$-compressed for all $i in [n]$ is not necessarily an initial segment of simplicial, e.g. take ${emptyset, 1, 2, 12}$ in $Q_3$. However...
]
#lemma[
    Let $B subset.eq Q_n$ be $i$-compressed for all $i in [n]$ but not an initial segment of the simplicial order. Then either:
    - $n$ is odd (say $n = 2k + 1$) and $
        B = X^(<= k) \\ underbrace({k + 2, k + 3, ..., 2k + 1}, #[last $k$-set]) union underbrace({1, 2, ..., k + 1}, #[first $(k + 1)$-set]),
    $
    - or $n$ is even (say $n = 2k$), and $
        B = X^((< k)) union {x in X^((k)): 1 in x} \\ underbrace({1, k + 2, k + 3, ..., 2k}, #[last $k$-set with $1$]) union underbrace({2, 3, ..., k + 1}, #[first $k$-set without $1$]).
    $
]
#proof[
    Since $B$ is not an initial segment of simplicial, so there exist $x < y$ (in simplicial) with $y in B$ but $x in.not B$. For each $1 <= i <= n$, we cannot have $i in x$ and $i in y$ (as $B$ is $i$-compressed). For the same reason, we cannot have $i in.not x$ and $i in.not y$. So $x = y^c$. Thus for each $y in B$, there is at most one $x < y$ with $x in.not B$ (namely $x = y^c$), and for each $x in.not B$, there is at most one $y > x$ with $y in B$ (namely $y = x^c$). So no sets lie between $x$ and $y$ in the simplicial ordering. So $B = {z: z <= y} \\ {x}$, with $x$ the predecessor of $y$, and $x = y^c$. Hence if $n = 2k + 1$, then $x$ is the last $k$-set (otherwise sizes of $x$ and $y = x^c$ don't match), and if $n = 2k$, then $x$ is the last $k$-set containing $1$.
]
#theorem("Harper")[
    Let $A subset.eq V(Q_n)$ and let $C$ be the initial segment of the simplicial order on $powset(X) = V(Q_n)$, with $abs(C) = abs(A)$. Then $abs(N(A)) >= abs(N(C))$. So initial segments of the simplicial order minimise the boundary. In particular, if $abs(A) = sum_(i = 0)^r binom(n, i)$, then $abs(N(A)) >= sum_(i = 0)^(r + 1) binom(n, i)$.
]<thm:harper>
#proofhints[
    - Using induction, prove the claim that $abs(N(C_i (A))) <= abs(N(A))$:
        - Find expressions for $N(A)_-$ as union of two sets, similarly for $N(A)_+$, same for $N(B)_-$ and $N(B)_+$.
        - Explain why $N(B_-)$ and $B_+$ are nested, use this to show $abs(N(B_-) union B_+) <= abs(N(A_-) union A_+)$.
        - Do the same with the $+$ and $-$ switched.
]
#proof[
    By induction on $n$. $n = 1$ is trivial. Given $n > 1$, $A subset.eq Q_n$ and $1 <= i <= n$, we claim that $abs(N(C_i (A))) <= abs(N(A))$.
    #proof("of claim")[
        Write $B = C_i (A)$. We have $N(A)_- = N(A_-) union A_+$, and $N(A)_+ = N(A_+) union A_-$. Similarly, $N(B)_- = N(B_-) union B_+$, and $N(B)_+ = N(B_+) union B_-$.
        
        Now $abs(B_+) = abs(A_+)$ by definition of $B$, and by the inductive hypothesis, $abs(N(B_-)) <= abs(N(A_-))$ (since $C_i (A_-) = B_-$). But $B_+$ is an initial segment of the simplicial ordering, and $N(B_-)$ is as well (since the neighbourhood of an initial segment of the simplicial ordering is also an initial segment). So $B_+$ and $N(B_-)$ are nested (one is contained in the other). Hence, $abs(N(B_-) union B_+) <= abs(N(A_-) union A_+)$.
        
        Similarly, $abs(B_-) = abs(A_-)$ by definition of $B$. Since $B_+$ and $C_i (A_+)$ are both initial segments of size $abs(B_+) = abs(A_+)$, we have $B_+ = C_i (A_+)$, hence by the inductive hypothesis, $abs(N(B_+)) <= abs(N(A_+))$. $B_-$ and $N(B_+)$ are initial segments, so are nested. Hence $abs(N(B_+) union B_-) <= abs(N(A_+) union A_-)$.
        
        This gives $abs(N(B)) = abs(N(B)_-) + abs(N(B)_+) <= abs(N(A)_-) + abs(N(A)_+) = abs(N(A))$, which proves the claim.

        Define a sequence $A_0, A_1 ,... subset.eq Q_n$ as follows:
        - Set $A_0 = A_1$.
        - having chosen $A_0, ..., A_k$, if $A_k$ is $i$-compressed for all $i in [n]$, then end the sequence with $A_k$. If not, pick $i$ with $C_i (A_k) != A_k$ and set $A_(k + 1) = C_i (A_k)$, and continue.
        The sequence must terminate, since $sum_(x in A_k) ("position of" x "in simplicial order")$ is strictly decreasing. The final family $B = A_k$ satisfies $abs(B) = abs(A)$, $abs(N(B)) <= abs(N(A))$, and is $i$-compressed for all $i in [n]$.

        So we are done by above lemma, since in each case certainly we have $abs(N(B)) > abs(N(C))$.
    ]
]
#remark[
    - If $A$ was a Hamming ball, then we would be already done by Kruskal-Katona.
    - Conversely, Harper's theorem implies Kruskal-Katona: given $B subset.eq X^((r))$, apply Harper's theorem to $A = X^((<= r - 1)) union B$.
    - We could also prove Harper's theorem using $U V$-compressions.
    - Conversely, we can also prove Kruskal-Katona using these "codimension $1$" compressions.
]
#definition[
    For $A subset.eq Q_n$ and $t in NN$, the *$t$-neighbourhood* of $A$ is $
        A_((t)) = N^t (A) := {x in Q_n: d(x, A) <= t}.
    $
]<def:t-neighbourhood>
#corollary[
    Let $A subset.eq Q_n$ wiht $abs(A) >= sum_(i = 0)^r binom(n, i)$. Then $
        forall t <= n - r, quad abs(N^t (A)) >= sum_(i = 0)^(r - t) binom(n, i).
    $
]
#proof[
    By Harper's theorem and induction on $t$.
]
#remark[
    To get a feeling for the strength of the above corollary, we'll need some estimates on quantities such as $sum_(i = 0)^r binom(n, i)$. Note that $i = n\/2$ maximises $binom(n, i)$, while $i = (1\/2 - epsilon) n$ makes it small: we are going $epsilon sqrt(n)$ standard deviations away from the mean $n\/2$.
]
#proposition[
    Let $0 < epsilon < 1\/k$. Then $
        sum_(i = 0)^floor((1\/2 - epsilon)n) binom(n, i) <= 1/epsilon e^(-epsilon^2 n\/2) dot 2^n.
    $ For $epsilon$ fixed and $n -> oo$, the upper bound is an exponentially small fraction of $2^n$.
]
#proof[
    For $0 <= i <= floor((1\/2 - epsilon) n)$, $
        binom(n, i - 1)\/binom(n, i) = i/(n - i + 1) <= ((1\/2 - epsilon)n)/((1\/2 + epsilon)n) = (1\/2 - epsilon)/(1\/2 + epsilon) = 1 - (2 epsilon)/(1\/2 + epsilon) <= 1 - 2 epsilon.
    $ Hence $
        sum_(i = 0)^floor((1\/2 - epsilon)n) binom(n, i) <= 1/(2 epsilon) binom(n, floor((1\/2 - epsilon) n))
    $ (since this is the sum of geometric progression). The same argument tells us that $
        binom(n, floor((1\/2 - epsilon)n)) <= binom(n, floor(1 \/2 - epsilon\/2)n) (1 - 2 epsilon/2)^(epsilon n \/2 - 1) <= 2^n dot 2 (1 - epsilon)^(epsilon n \/2) <= 2^n dot 2 e^(-epsilon^2 n\/2)
    $ since $1 - epsilon <= e^(-epsilon)$ (we include $-1$ in the exponent due to taking floors). Then $
        sum_(i = 0)^floor((1\/2 - epsilon)n) binom(n, i) <= 1/(2 epsilon) dot 2 e^(-epsilon^2 n\/2) dot 2^n.
    $
]


= Intersecting families