#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: (:))
#set document(
    title: "Geometric Group Theory Notes",
    author: "Isaac Holt",
    keywords: ("geometric group theory")
)
#import "@preview/fletcher:0.5.4" as fletcher: diagram, node, edge
#let genrel(..args) = $lr(angle.l #h(1pt) #args.pos().join(", ") #h(1pt) angle.r)$
#let normalclosure(a) = $angle.l angle.l #a angle.r angle.r$

= Combinatorial group theory

== Free groups and presentations

#definition[
    Let $A = {a_1, a_2, a_3, ...}$ be an alphabet. A group $F$ is *free on $A$* if:
    - There exists a map of sets $A -> F$, and
    - The *universal property of free groups* holds: for any group $G$ and any map of sets $A -> G$, there is a unique homomorphism $F -> G$ such that the following diagram commutes:
    #figure(diagram($
        A edge("dr", ->) edge(, ->) & F edge("d", exists!, ->, "dashed") \
        & G
    $))
    $F$ is unique up to unique isomorphism (proof: exercise). We thus write $F = F(A)$.
    #figure(diagram(cell-size: (2mm, 2mm), $
        & A edge("dr", ->) edge("dl", ->) & \
        F_1 #edge("r", "<-", $tilde.equiv$, "dashed", label-pos: 1) & edge(->, "dashed") & F_2
    $))
]<def:group.free>
#remark[
    This leaves open the question of _existence_. We may resolve this question in two different ways:
    - *Topologically*: let $X = or.big_(a in A) S^1$, where all the $S^1$ are disjoint except at the distinguished point. Then $pi_1 (X) tilde.equiv F(A)$ by the Seifert-van Kampen (SVK) theorem.
    - *Combinatorially*: let $A^* = {"words in" a, a^(-1) "for" a in A}$, e.g. $A = {a, b}$. Some examples of words are $1 = emptyset$, $a b a^(-1) b^(-1)$, $a^100 a^(-100) b$.
]
#definition[
    A word $w$ is *reducible* if $w = ... a a^(-1) ...$ or $w = ... a^(-1) a ...$ for some $a in A$. Otherwise, $w$ is *reduced*.
]<def:word.reducible>
#definition[
    We may define the *free group on $A$* as $F(A) = {w in A^*: w "is reduced"}$. The identity is $1 = emptyset$ (the empty word). Multiplication is given by "concatenate, then reduce", e.g. $(a b a^(-1) b^(-1)) (b^2 a) = a b a^(-1) b^(-1) b^2 a = a b a^(-1) b a$.
]<def:free-group>
#definition[
    A *presentation* consists of a set of *generators* $A$ and a set of *relations* $R subset.eq F(A)$.
    
    We write $genrel(A | R)$ or $genrel(a_1\, a_2\, ... | r_1\, r_2\, ...)$ or $genrel(a_1\, a_2\, ... | r_1\, r_2\, ... = 1)$ for the presentation of the group $F(A) \/ normalclosure(R)$, where $normalclosure(R)$ denotes the normal closure of $R$ (the smallest normal subgroup of $F(A)$ containing $R$).
]<def:presentation>
#definition[
    Given $a, b in A$, the *commutator* of $a$ and $b$ is $[a, b] = a b a^(-1) b^(-1)$.
]<def:commutator>
#example[
    - $genrel(a | a^n) tilde.equiv ZZ_n$.
    - $genrel(r, s | r^n, s^2, s r s r) tilde.equiv D_(2n)$.
    - $genrel(A | med) tilde.equiv F(A)$.
    - $genrel(a_1, ..., a_g, b_1, ..., b_g | product_(i = 1)^g [a_i, b_i]) tilde.equiv pi_1 (Sigma_g)$, where $Sigma_g$ is the orientable surface of genus $g$.
    - $genrel(x, y | x^2 y^(-3)) tilde.equiv pi_1 (M_T)$, where $M_T = RR^3 \\ #[$T$-trefoil]$.
]
#remark[
    A corollary of the SVK theorem: for $G = genrel(a_1, a_2, ... | r_1, r_2, ...)$, let $X$ be the "presentation complex" space constructed as follows: take the space $or.big_(a in A) S^1$, where all the $S^1$ are disjoint except at one point, and consider disc for each $r in R$ (these discs are disjoint). Then map the boundary of the each relation disc via the word the relation makes. Then we have $pi_1 (X) tilde.equiv G$.

    We have $G$ is finitely presented iff $X$ is compact.

    Every group appears as a quotient/presentation of a free group, all of which appear as a fundamental group.
]
#problem("Word Problem")[
    For $A, R$ finite, determine whether or not $w in A^*$ represents $1$ in $genrel(A | R)$ (equivalently, whether $u =_G v$, for $u, v in A^*$).
]<prb:word-problem>
#problem("Conjugacy Problem")[
    For $A, R$ finite, determine whether or not $u, v in A^*$ represent conjugate elements in $genrel(A | R)$.
]<prb:conjugacy-problem>
#problem("Isomorphism Problem")[
    Determine if $genrel(A | R) tilde.equiv genrel(A' | R')$ or not (given that they are both finite).
]<prb:isomorphism-problem>
#remark[
    - The conjugacy problem is stronger than the word problem.
    - All these problems turn out to be independent of the choice of finite presentation $genrel(A | R)$. (Proof: exercise...).
    - Dehn was motivated by topology. All these problems ask for algorithms (in 1911!).
    - All these problems are undecidable in full generality. Norikov (1955) and Boone (1959) unsolved the word (and hence conjugacy) problem. Adyan (1955) and Rabin (1958) unsolved the isomorphism problem.
    - Nevertheless, positive solutions exist for "reasonable" classes of groups.
]
#example("Word problem in finitely-generated free groups")[
    Let $w in A^*$. If $w$ is reduced, then $w =_F(A) 1$ iff $w$ is the empty word. Otherwise, $w$ contains a cancelling pair $a a^(-1)$ (or $a^(-1) a$): $w = u a a^(-1) v$. Cancelling $a a^(-1)$ gives $w' = u v$. Note that $w' =_F(A) w$ and the length of $w'$ is shorter. Continuing inductively, we eventually arrive in the reduced case (note that $A$ is finite).
]
What about the conjugacy problem in free groups?
#definition[
    There is a natural action of $ZZ$ on $A^*$, given by cyclically permuting words: $
        1 . a_1 ... a_n = a_2 ... a_n a_1, quad a_i in A union A^(-1).
    $ The orbits of this action are called *cyclic words*.
]<def:cyclic-word>
#example[
    The cyclic word defined by $a b a^(-1) b^(-1)$ can be represented as $
        & med a & \
        b^(-1) & & b \
        & a^(-1) &
    $
]
#definition[
    If $u, v in A^*$ define the same cyclic word, we say that $u$ and $v$ are *cyclic conjugates*.
]<def:cyclic-conjugate>
#definition[
    $w in A^*$ is *cyclically reduced* if all its cyclic conjugates are reduced.
]<def:cyclically-reduced>
#example[
    $a b a^(-1) arrow.tilde b a^(-1) a =_F(A) b$. So $a b a^(-1)$ is reduced but not cyclically reduced.
]
#lemma[
    If $u, v in F(A)$ are cyclically reduced, then $u$ is conjugate to $v$ iff $u$ and $v$ are cyclic conjugates.
]<lem:cyclically-reduced-words-are-conjugate-iff-cyclic-conjugate>
#proofhints[
    - $<==$: straightforward.
    - $==>$: explain why we can assume $g in A union A^(-1)$.
]
#proof[
    $<==$: suppose $u = a_1 ... a_n$, $a_i in A union A^(-1)$. Then $v = a_k ... a_n (a_1 ... a_(k - 1))$ for some $k$. Let $g = a_1 ... a_(k - 1)$, then $u = g v g^(-1)$, as required.

    $==>$: suppose $u = g v g^(-1)$. By induction on the length of $g$, we may assume that $g in A union A^(-1)$. Since $u$ is cyclically reduced, $v$ decomposes as one of:
    - $v = g^(-1) v'$ or
    - $v = v' g$.
    In the first case, we obtain $u = v' g^(-1)$ and in the second case $u = g v'$. In either case, $u$ is a cyclic conjugate of $v$ as required.
]
#example("Conjugacy problem in free groups")[
    Consider $F(A)$ for $A$ finite. If $w in A^*$ is reduced but not cyclically reduced, then $w = a w' a^(-1)$ for some $a in A union A^(-1)$. Note that $w'$ is conjugate to $w$ and shorter than $w$. Therefore, continuing inductively, we may assume that $w$ is cyclically reduced.

    So @lem:cyclically-reduced-words-are-conjugate-iff-cyclic-conjugate solves the problem (since each word of finite length has a finite number of cyclic conjugates).
]

= Historical case study

We need to understand the state of topology in the early 20th century. Poincaré knew that 2D compact surfaces are classified by their homology groups. He wondered if the same could be true in dimension $3$.
#conjecture("Poincaré Conjecture (version 1)")[
    Let $M$ be a closed $3$-manifold. If $H_* (M) = cases(ZZ & "if" * = 0\, 3, 0 & "otherwise")$, then $M tilde.equiv S^3$. Such a $3$-manifold is called a *homology sphere*.
]<cng:poincare-v1>
#theorem("Poincaré")[
    There is a $3$-dimensional homology sphere $P$ such that $pi_1 (P) ->> A_5$ ($->>$ means surjects). In particular, $P tilde.equiv.not S^3$.
]
So the @cng:poincare-v1 is false and homology is not enough in dimension $3$.
#conjecture("Poincaré Conjecture (version 2)")[
    Let $M$ be a closed, connected $3$-manifold. If $pi_1 (M) tilde.equiv {e}$, then $M tilde.equiv S^3$.
]
This was proven in 2003 by Perelman.
#theorem("Dehn")[
    There are infinitely many pairwise non-homeomorphic homology spheres in dimension $3$.
]
Dehn's construction is as follows: let $K$ be the trefoil knot and $N = S^3 \\ N^o (K)$ where $N^o (K)$ is a small open tubular neighbourhood of $K$. We have $TT tilde.equiv partial N$. $pi_1 (N) = genrel(x, y, z | x^2 = y^3 = z)$. The homology sphere is $pi_1 (N)_("ab") = ZZ^2 \/ genrel((2, -3)) tilde.equiv ZZ$, the abelianisation of the fundamental group. In general, $
    H_* (N) = cases(ZZ quad & "if" * = 0\, 1, 0 & "otherwise").
$ It turns out that $pi_1 (TT) tilde.equiv ZZ^2 = genrel(x y, z) <= pi_1 (N)$. We have $
    H_1 (TT) tilde.equiv ZZ^2 quad & --> quad H_1 (N) tilde.equiv ZZ \
    x y quad & |-> quad 5 \
    z quad & |-> quad 6
$ We now build infinitely many manifolds using "Dehn filling". Let $U = D^2 times S^1$ be the solid sphere. For any homeomorphism $phi: partial U -> partial N$, define $M_phi = (U union.sq N) \/ {x tilde phi(x): x in partial U}$. By SVK theorem, if $g = phi_* (mu) in pi_1 (TT) <= pi_1 (N)$, then $pi_1 (M_phi) = pi_1 (N) \/ normalclosure(g)$ and $H_1 (M_phi) = ZZ \/ genrel([g])$.

So, to produce homology spheres, we need $[g] = plus.minus 1$ in $H_1 (N)$. If $g = (x y)^a z^b$ in $pi_1 (TT)$, then $[g] = 5a + 6b$. Dehn chooses $a = 6n + 5$, $b = -5n - 4$ for all $n in NN$. So we define $g_n = (x y)^(6n + 5) z^(-5n - 4)$. For these cases, $M_phi$ is a homology sphere:
- $H_0 (M_phi) tilde.equiv ZZ$
- $H_1 (M_phi) tilde.equiv {0}$
- $H_2 (M_phi) tilde.equiv {0}$ by Poincare duality
- $H_3 (M_phi) tilde.equiv ZZ$ by Poincare duality.

For $phi_n$ that sends $mu -> g_n = 5a + 6b$, write $M_n = M_(phi_n)$. Then $G_n := pi_1 (M_n) = genrel(x, y, z | x^2 = y^3 = z, (x y)^(6n + 5) = z^(5n + 4))$. To prove that the $M_n$ are pairwise distinct, we are left with the challenge of proving that $G_m tilde.equiv G_n ==> m = n$.

Also, note that if $g_n = g_m$, then $g_n tilde_"conj" g_m$ which implies $G_n tilde.equiv G_m$.

== Van Kampen diagrams

#definition[
    A map of cell complexes $Y -> X$ is called *combinatorial* if, for all $k$, and for every $k$-cell $e^k$ of $Y$, $f$ maps the interior of $e^k$ homeomorphically to the interior of a $k$-cell of $X$.
]
Consider a presentation $genrel(a_i | r_j) tilde.equiv G$ and let $X$ be the associated presentation complex.
#definition[
    A *(singular) disc diagram* is a compact contractible $2$-complex $D$ with an embedding $D arrow.hook RR^2$.
]
#definition[
    A disc diagram $D$ is said to be *over $X$* if it is equipped with a combinatorial map $D -> X$. Equivalently, each edge of $D$ is oriented and labelled by some $a_i$, so that the boundary of each $2$-cell reads some $r_j^(plus.minus 1)$, thought of as a cyclic word.
]