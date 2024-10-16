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
#proofhints[
    Consider two sequences in $A + A$ which are strictly increasing and of the same length.
]
#proof[
    - Let $A = {a_1, ..., a_n}$ with $a_i < a_(i + 1)$. Then $a_1 + a_1 < a_1 + a_2 < dots.c < a_1 + a_n < a_2 + a_n < dots.c < a_n + a_n$.
    - Note this is not the only choice of increasing sequence that works, in particular, so does $a_1 + a_1 < a_1 + a_2 < a_2 + a_2 < a_2 + a_3 < a_2 + a_4 < dots.c < a_2 + a_n < a_3 + a_n < dots.c < a_n + a_n$.
    - So when equality holds, all these sequences must be the same. In particular, $a_2 + a_i = a_1 + a_(i + 1)$ for all $i$.
]
#lemma[
    If $A, B subset.eq ZZ$, then $|A + B| >= |A| + |B| - 1$ with equality iff $A$ and $B$ are arithmetic progressions with the same common difference.
]
#proofhints[
    Similar to above, consider $4$ sequences in $A + B$ which are strictly increasing and of the same length.
]
#example[
    Let $A, B subset.eq ZZ\/p$ for $p$ prime. If $|A| + |B| >= p + 1$, then $A + B = ZZ\/p$.
]
#proofhints[
    Consider $A sect (g - B)$ for $g in ZZ\/p$.
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
#proofhints[
    - Assume $|A| + |B| < p + 1$, and WLOG that $1 <= |A| <= |B|$ and $0 in A$ (by translation).
    - Induct on $|A|$.
    - Let $a in A$, find $B'$ such that $0 in B'$, $a in.not B'$ and $|B'| = |B|$ (use fact that $p$ is prime).
    - Apply induction with $A sect B'$ and $A union B'$, while reasoning that $(A sect B') + (A union B') subset.eq A + B'$.
]
#proof[
    - Assume $|A| + |B| < p + 1$, and WLOG that $1 <= |A| <= |B|$ and $0 in A$ (by translation).
    - Use induction on $|A|$. $|A| = 1$ is trivial.
    - Let $|A| >= 2$ and let $0 != a in A$. Then since $p$ is prime, ${a, 2a, ..., p a} = ZZ\/p$.
    - There exists $m >= 0$ such that $m a in B$ but $(m + 1)a in.not B$ (why?). Let $B' = B - m a$, so $0 in B'$, $a in.not B'$ and $|B'| = |B|$.
    - $1 <= |A sect B'| < |A|$ (why?) so the inductive hypothesis applies to $A sect B'$ and $A union B'$.
    - Since $(A sect B') + (A union B') subset.eq A + B'$ (why?), we have $|A + B| = |A + B'| >= |(A sect B') + (A union B')| >= |A sect B'| + |A union B'| - 1 = |A| + |B| - 1$.
]
#example[
    Cauchy-Davenport does not hold general abelian groups (e.g. $ZZ\/n$ for $n$ composite): for example, let $A = B = {0, 2, 4} subset.eq ZZ\/6$, then $A + B = {0, 2, 4}$ so $|A + B| = 3 < min{6, |A| + |B| - 1}$.
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
#definition[
    Let $A, B subset.eq G$ be finite subsets of an abelian group $G$. The *Ruzsa distance* between $A$ and $B$ is $
        d(A, B) := log (|A - B|)/(sqrt(|A| dot |B|)).
    $
]
#lemma(name: "Ruzsa Triangle Inequality")[
    Let $A, B, C subset.eq G$ be finite. Then $
        d(A, C) <= d(A, B) + d(B, C).
    $
]<lem:ruzsa-triangle-inequality>
#proof[
    - Note that $|B| |A - C| <= |A - B| |B - C|$. Indeed, writing each $d in A - C$ as $d = a_d - c_d$ with $a_d in A$, $c_d in C$, the map $phi: B times (A - C) -> (A - B) times (B - C)$, $phi(b, d) = (a_d - b, b - c_d)$ is injective (why?).
    - Triangle inequality now follows from definition of Ruzsa distance.
]
#definition[
    The *doubling constant* of finite $A subset.eq G$ is $sigma(A) := |A + A|\/|A|$.
]<def:doubling-constant>
#definition[
    The *difference constant* of finite $A subset.eq G$ is $delta(A) := |A - A|\/|A|$.
]<def:difference-constant>
#remark[
    The Ruzsa triangle inequality shows that $
        log delta(A) = d(A, A) <= d(A, -A) + d(-A, A) = 2 log sigma(A).
    $ So $delta(A) <= sigma(A)^2$, i.e. $|A - A| <= |A + A|^2\/|A|$.
]
#notation[
    Let $A subset.eq G$, $ell, m in NN_0$. Then $
        ell A + m A := underbrace(A + dots.c + A, ell "times") underbrace(- A - dots.c - A, m "times")
    $ This is referred to as the *iterated sum and difference set*.
]
#theorem(name: "Plunnecke's Inequality")[
    Let $A, B subset.eq G$ be finite and $|A + B| <= K|A|$ for some $K >= 1$. Then $forall ell, m in NN_0$, $
        |ell B - m B| <= K^(ell + m) abs(A).
    $
]<thm:plunneckes-inequality>
#proof[
    - Choose $emptyset != A' subset.eq A$ which minimises $|A' + B|\/|A'|$. Let the minimum value by $K'$.
    - Then $|A' + B| = K' abs(A')$, $K' <= K$ and $forall A'' subset.eq A$, $|A'' + B| >= K' abs(A'')$.
    - Claim: for every finite $C subset.eq G$, $|A' + B + C| <= K' abs(A' + C)$:
        - Use induction on $abs(C)$. $abs(C) = 1$ is true by definition of $K'$.
        - Let claim be true for $C$, consider $C' = C union {x}$ for $x in.not C$.
        - $A' + B + C' = (A' + B + C) union ((A' + B + x) - (D + B + x))$, where $D = {a in A': a + B + x subset.eq A' + B + C}$.
        - By definition of $K'$, $abs(D + B) >= K' abs(D)$. Hence, $
            |A' + B + C| & <= |A' + B + C| + abs(A' + B + x) - abs(D + B + x) \
            & <= K' abs(A' + C) + K' abs(A') - K' abs(D) \
            & = K' (abs(A' + C) + abs(A') - |D|).
        $
        - Applying this argument a second time, write $A' + C' = (A' + C) union ((A' + x) - (E + x))$, where $E = {a in A': a + x in A' + C} subset.eq D$.
        - Finally, $
            abs(A' + C') & = abs(A' + C) + abs(A' + x) - abs(E + x) \
            & >= |A' + C| + |A'| - |D|.
        $
    - We first show that $forall m in NN_0$, $abs(A' + m B) <= (K')^m abs(A')$ by induction:
        - $m = 0$ is trivial, $m = 1$ is true by assumption.
        - Suppose $m - 1 >= 1$ is true. By the claim with $C = (m - 1) B$, we have $ abs(A' + m B) = |A' + B + (m - 1)B| <= K' abs(A' + (m - 1)B) <= (K')^m abs(A'). $
    - As in the proof of Ruzsa's triangle inequality, $forall ell, m in NN_0$, $ |A'| |ell B - m B| <= |A' + ell B| |A' + m B| <= (K')^ell abs(A') (K')^m abs(A') = (K')^(ell + m) abs(A')^2. $
]
#theorem(name: "Freiman-Ruzsa")[
    Let $A subset.eq FF_p^n$ and $abs(A + A) <= K abs(A)$. Then $A$ is contained in a subspace $H <= FF_p^n$ with $abs(H) <= K^2 p^(K^4) abs(A)$.
]<thm:freiman-ruzsa>


= Fourier-analytic techniques




= Probabilistic tools




= Further topics

