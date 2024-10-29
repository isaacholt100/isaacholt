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
        - Now, $partial (partial A_n union A_(n - 1))$ and $cal(F)_(n - 2)$ are disjoint, as $cal(F)$ is an antichain.
        - So $ (|partial(partial cal(F)_n union cal(F)_(n - 1))|)/binom(n, n - 2) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1. $
        - So by local LYM, $ (|partial A_n union cal(F)_(n - 1)|)/binom(n, n - 1) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1. $
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
    By Local LYM, we know that $abs(partial cal(F)) >= abs(cal(F)) r\/(n - r + 1)$. Equality is rare (only for $cal(F) = X^((r))$ for $0 <= r <= n$). What happens in between, i.e., given $abs(cal(F))$, how should we choose $cal(F)$ to minimise $abs(partial A)$?

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
    - Equality in Kruskal-Katona: if $abs(cal(F)) = binom(k, r)$ and $abs(partial cal(F)) = binom(k, r - 1)$, then $cal(F) = Y^((r))$ for some $Y subset.eq X$ with $abs(Y) = k$. However, it is not true in general that if $abs(partial A) = abs(partial C)$, then $cal(F)$ is isomorphic to $cal(C)$ (i.e. there is a permutation of the ground set $X$ sending $cal(F)$ to $cal(C)$).
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


= Isoperimetric inequalities




= Intersecting families

#definition[
    A family $cal(F) in powset(X)$ is *intersecting* if for all $A, B in cal(F)$, $A sect B != emptyset$.

    We are interested in finding intersecting families of maximum size.
]<def:family.intersecting>
#proposition[
    For all intersecting families $cal(F) subset.eq powset(X)$, $abs(cal(F)) <= 2^(k - 1)$.
]
#proof[
    Given any $A subset.eq X$, at most one of $A$ and $A^c$ can belong to $cal(F)$.
]
#example[
    - $cal(F) = {A subset.eq X: 1 in A}$ is intersecting, and $abs(cal(F)) = 2^(k - 1)$.
    - $cal(F) = {A subset.eq X: abs(A) > n/2}$ for $n$ odd.
]
#example[
    If $A subset.eq X^((r))$:
    - If $r > n/2$, then $cal(F) = X^((r))$ is intersecting.
    - If $r = n/2$, then choose one of $A$ and $A^c$ for all $A in X^((r))$. This gives $abs(cal(F)) = 1/2 binom(n, r)$.
    - If $r < n/2$, then $cal(F) = {A in X^((r)): 1 in A}$ has size $binom(n - 1, r - 1) = r/n binom(n, r)$ (since the probability of a random $r$-set containing $1$ is $r/n$). If $(n, r) = (8, 3)$, then $abs(cal(F)) = binom(7, 2) = 21$.
    - Let $cal(B) = {A in X^((r)): abs(A sect {1, 2, 3}) >= 2}$. If $(n, r) = (8, 3)$, then $abs(cal(B)) = 1 + binom(3, 2) binom(5, 1) = 16 < 21$ (since $1$ set $B$ has $abs(B sect [3]) = 3$, $15$ sets have $abs(B sect [3]) = 2$).
]
#theorem("Erdos-Ko-Rado")[
    Let $cal(F) subset.eq X^((r))$ be an intersecting family, where $r < n/2$. Then $abs(cal(F)) <= binom(n - 1, r - 1)$.
]
#proof[
    Proof 1 ("bubble down with Kruskal-Katona"): note that $A sect B != emptyset$ iff $A subset.eq.not B^c$. Let $overline(cal(F)) = {A^c: A in cal(F)} subset.eq X^((n - r))$. We have $partial^(n - 2r) overline(cal(F))$ and $cal(F)$ are disjoint families of $r$-sets. Suppose $abs(cal(F)) > binom(n - 1, r - 1)$. Then $abs(overline(cal(F))) = abs(cal(F)) > binom(n - 1, r - 1) = binom(n - 1, n - r)$. So by Kruskal=Katona, we have $abs(partial^(n - 2r) overline(cal(F))) >= binom(n - 1, r)$. So $abs(cal(F)) + abs(partial^(n - 2r) overline(cal(F))) > binom(n - 1, r - 1) + binom(n - 1, r) = binom(n, r)$.

    Proof 2: pick a cyclic ordering of $[n]$, i.e. a bijection $c: [n] -> ZZ\/n$. There are at most $r$ sets in $cal(F)$ that are intervals ($r$ consecutive elements) in this ordering: for $c_1 ... c_r in cal(F)$, for each $2 <= i <= r$, at most one of the two intervals $c_i ... c_(i + r - 1)$ and $c_(i - r) ... c_(i - 1)$ can belong to $cal(F)$ (the indices of $c$ are taken $mod n$). For each $r$-set $A$, out of the $n!$ cyclic orderings, there are $n dot r! (n - r)!$ which map $A$ to an interval ($r!$ orderings inside $A$, $(n - r)!$ orderings outside $A$). Hence $abs(cal(F)) n r! (n - r)! <= n! r$, i.e. $abs(cal(F)) <= binom(n - 1, r - 1)$.
]
#remark[
    - The calculation at the end of proof method 1 had to give the correct answer, as the shadow calculations would all be exact if $cal(F) = {A in X^((r)): 1 in A}$.
    - The calculations at the end of proof method 2 had to work out, given equality for the family $cal(F) = {A in X^((r)): 1 in A}$.
    - In method 2, equivalently, we are double-counting the edges in the bipartite graph, where the vertex classes (partition sets) are $cal(F)$ and all cyclic orderings, with $A$ joined to $c$ if $A$ is an interval in $c$. This method is called *averaging* or Katona's method.
    - Equality in Erdos-Ko-Rado holds iff $cal(F) = {A in X^((r)): i in A}$, for some $1 <= i <= n$. This can be obtained from proof 1 and equality in Kruskal-Katona, or from proof 2.
]