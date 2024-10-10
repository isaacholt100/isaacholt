#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

= Combinatorial methods

#definition[
    Let $G$ be an abelian group and $A, B subset.eq G$. The *sumset* of $A$ and $B$ is $
        A + B := {a + b: a in A, b in B}.
    $ The *difference set* of $A$ and $B$ is $
        A - B := {a - b: a in A, b in B}.
    $
]<def:sumset-and-difference-set>
#proposition[
    $max{|A|, |B|} <= |A + B| <= |A| dot |B|$.
]<prop:general-bound-on-sumset-size>
#proof[
    Trivial.
]
#example[
    Let $A = [n] = {1, ..., n}$. Then $A + A = {2, ..., 2n}$ so $|A + A| = 2|A| - 1$.
]
#lemma[
    Let $A subset.eq ZZ$ be finite. Then $|A + A| >= 2|A| - 1$ with equality iff $A$ is an arithmetic progression.
]<lem:lower-bound-on-integer-sumset>
#proof[
    - Let $A = {a_1, ..., a_n}$ with $a_i < a_(i + 1)$. Then $a_1 + a_1 < a_1 + a_2 < dots.c < a_1 + a_n < a_2 + a_n < dots.c < a_n + a_n$.
    - Note this is not the only choice of increasing sequence that works, in particular, so does $a_1 + a_1 < a_1 + a_2 < a_2 + a_2 < a_2 + a_3 < a_2 + a_4 < dots.c < a_2 + a_n < a_3 + a_n < dots.c < a_n + a_n$.
    - So when equality holds, all these sequences must be the same. In particular, $a_2 + a_i = a_1 + a_(i + 1)$ for all $i$.
]
#exercise[
    If $A, B subset.eq ZZ$, then $|A + B| >= |A| + |B| - 1$ with equality iff $A$ and $B$ are arithmetic progressions with the same common difference.
]
#example[
    Let $A, B subset.eq ZZ\/p$ for $p$ prime. If $|A| + |B| >= p + 1$, then $A + B = ZZ\/p$.
]
#proof[
    - $g in A + B$ iff $A sect (g - B) != emptyset$ where ($g - B = {g} - B$).
    - Let $g in ZZ\/p$, then use inclusion-exclusion on $|A sect (g - B)|$ to conclude result.
]
#theorem(name: "Cauchy-Davenport")[
    Let $p$ be prime, $A, B subset.eq ZZ\/p$ be non-empty. Then $
        |A + B| >= min{p, |A| + |B| - 1}.
    $
]<thm:cauchy-davenport>
#proof[
    - Assume $|A| + |B| <= p + 1$, and WLOG that $1 <= |A| <= |B|$ and $0 in A$ (by translation).
    - Use induction on $|A|$. $|A| = 1$ is trivial.
    - Let $|A| >= 2$ and let $0 != a in A$. Then since $p$ is prime, ${a, 2a, ..., p a} = ZZ\/p$.
    - There exists $m >= 0$ such that $m a in B$ but $(m + 1)a in.not B$. Let $B' = B - m a$, so $0 in B'$, $a in.not B'$ and $|B'| = |B|$.
    - $1 <= |A sect B'| < |A|$ (why?) so the inductive hypothesis applies to $A sect B'$ and $A union B'$.
    - Since $(A sect B') + (A union B') subset.eq A + B'$ (why?), we have $|A + B| = |A + B'| >= |(A sect B') + (A union B')| >= |A sect B'| + |A union B'| - 1 = |A| + |B| - 1$.
]
#exercise[
    Find a counterexample for Cauchy-Davenport for general abelian groups (e.g. $ZZ\/n$ for $n$ composite).
]
#example[
    Fix a small prime $p$ and let $V subset.eq FF_p^n$ be a subspace. Then $V + V = V$, so $|V + V| = |V|$. In fact, if $A subset.eq FF_p^n$ satisfies $|A + A| = |A|$, then $A$ is an affine subspace (a coset of a subspace).
]
#proof[
    If $0 in A$, then $A subset.eq A + A$, so $A = A + A$. General result follows by considering translation of $A$.
]
#example[
    Let $A subset.eq FF_p^n$ satisfy $|A + A| <= 3/2 |A|$. Then there exists a subspace $V subset.eq FF_p^n$ such that $|V| <= 3/2 |A|$ and $A$ is contained in a coset of $V$.
]
#proof[
    Exercise (sheet 1).
]


= Fourier-analytic techniques




= Probabilistic tools




= Further topics

