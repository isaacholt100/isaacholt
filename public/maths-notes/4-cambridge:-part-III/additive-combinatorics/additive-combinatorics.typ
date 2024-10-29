#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let Spec = math.op("Spec")

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
#theorem("Cauchy-Davenport")[
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
#lemma("Ruzsa Triangle Inequality")[
    Let $A, B, C subset.eq G$ be finite. Then $
        d(A, C) <= d(A, B) + d(B, C).
    $
]<lem:ruzsa-triangle-inequality>
#proofhints[
    Consider a certain map from $B times (A - C)$ to $(A - B) times (B - C)$.
]
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
#theorem("Plunnecke's Inequality")[
    Let $A, B subset.eq G$ be finite and $|A + B| <= K|A|$ for some $K >= 1$. Then $forall ell, m in NN_0$, $
        |ell B - m B| <= K^(ell + m) abs(A).
    $
]<thm:plunneckes-inequality>
#proofhints[
    - Let $A' subset.eq A$ minimise $abs(A' + B)\/abs(A')$ with value $K'$.
    - Show that for every finite $C subset.eq G$, $abs(A' + B + C) <= K' abs(A + C)$ by induction on $abs(C)$ (note two sets need to be written as disjoint unions here).
    - Show that $forall m in NN_0, abs(A' + m B) <= (K')^m abs(A')$ by induction.
    - Use Ruzsa triangle inequality to conclude result.
]
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
#theorem("Freiman-Ruzsa")[
    Let $A subset.eq FF_p^n$ and $abs(A + A) <= K abs(A)$. Then $A$ is contained in a subspace $H subset.eq FF_p^n$ with $abs(H) <= K^2 p^(K^4) abs(A)$.
]<thm:freiman-ruzsa>
#proofhints[
    - Let $X subset.eq 2A - A$ be of maximal size such that all $x + A$, $x in X$, are disjoint.
    - Use Plunnecke's inequality to obtain an upper bound on $abs(X) abs(A)$.
    - Show that $forall ell >= 2$, $ell A - A subset.eq (ell - 1)X + A - A$ by induction.
    - Let $H$ be subgroup generated by $A$. By writing $H$ as an infinite union, show that $H subset.eq Y + A - A$, where $Y$ is subgroup generated by $X$.
    - Find an upper bound for $abs(Y)$, conclude using Plunnecke inequality.
]
#proof[
    - Choose maximal $X subset.eq 2A - A$ such that the translates $x + A$ with $x in X$ are disjoint.
    - Such an $X$ cannot be too large: $forall x in X$, $x + A subset.eq 3A - A$, so by Plunnecke's inequality, since $abs(3A - A) <= K^4 abs(A)$, $
        abs(X) abs(A) = abs(union.big_(x in X) (x + A)) <= abs(3A - A) <= K^4 abs(A).
    $ Hence $abs(X) <= K^4$.
    - We next show that $2A - A subset.eq X + A - A$. Indeed, if, $y in 2A - A$ and $y in.not X$, then by maximality of $X$, then $(y + A) sect (x + A) != emptyset$ for some $x in X$. If $y in X$, then $y in X + A - A$.
    - It follows from above, by induction, that $forall ell >= 2$, $ell A - A subset.eq (ell - 1)X + A - A$: $ell A - A = A + (ell - 1)A - A subset.eq (ell - 2)X + 2A - A subset.eq (ell - 2)X + X + A - A = (ell - 1)X + A - A$.
    - Now, let $H subset.eq FF_p^n$ be the subgroup generated by $A$: $
        H = union.big_(ell >= 1) (ell A - A) subset.eq Y + A - A
    $ where $Y subset.eq FF_p^n$ is the subgroup generated by $X$.
    - Every element of $Y$ can be written as a sum of $abs(X)$ elements of $X$ with coefficients in ${0, ..., p - 1}$. Hence, $abs(Y) <= p^abs(X) <= p^(K^4)$.
    - Hence $abs(H) <= abs(Y) abs(A - A) <= p^(K^4) K^2 abs(A)$ by Plunnecke/Ruzsa triangle inequality.
]
#example[
    Let $A = V union R$, where $V subset.eq FF_p^n$ is a subspace with $dim(V) = d = n\/K$ satisfying $K << d << n - K$, and $R$ consists of $K - 1$ linearly independent vectors not in $V$. Then $abs(A) = abs(V union R) = abs(V) + abs(R) = p^(n\/K) + K - 1 approx p^(n\/K) = abs(V)$.

    Now $abs(A + A) = abs((V union R) + (V union R)) = abs(V union (V + R) union 2R) approx K abs(V) approx K abs(A)$ (since $V union (V + R)$ gives $K$ cosets of $V$). But any subspace $H subset.eq FF_p^n$ containing $A$ must have size at least $p^(n\/K + (K - 1)) approx abs(V) p^K$. Hence, the exponential dependence on $K$ in Freiman-Ruzsa is necessary.
]
#theorem("Polynomial Freiman-Ruzsa Theorem")[
    Let $A subset.eq FF_p^n$ be such that $abs(A + A) <= K abs(A)$. Then there exists a subspace $H subset.eq FF_p^n$ of size at most $C_1 (K) abs(A)$ such that for some $x in FF_p^n$, $
        abs(A sect (x + H)) >= abs(A)/(C_2 (K)),
    $ where $C_1 (K)$ and $C_2 (K)$ are polynomial in $K$.
]
#proof[
    Very difficult (took Green, Gowers and Tao to prove it).
]
#definition[
    Given $A, B subset.eq G$ for an abelian group $G$, the *additive energy* between $A$ and $B$ is $
        E(A, B) := abs({(a, a', b, b') in A times A times B times B: a + b = a' + b'}).
    $ *Additive quadruples* $(a, a', b, b')$ are those such that $a + b = a' + b'$. Write $E(A)$ for $E(A, A)$.
]
#example[
    Let $V subset.eq FF_p^n$ be a subspace. Then $E(V) = abs(V)^3$. On the other hand, if $A subset.eq ZZ\/p$ is chosen at random from $ZZ\/p$ (where each $a in ZZ\/p$ is included with probability $alpha > 0$), with high probability, $E(A) = alpha^4 p^3 = alpha abs(A)^3$.
]
#definition[
    For $A, B subset.eq G$, the *representation function* is $r_(A + B) (x) := abs({(a, b) in A times B: a + b = x}) = abs(A sect (x - B))$.
]
#lemma[
    Let $emptyset != A, B subset.eq G$ for an abelian group $G$. Then $
        E(A, B) >= (abs(A)^2 abs(B)^2)/abs(A plus.minus B).
    $
]
#proofhints[
    - Show that using Cauchy-Schwarz that $
        E(A, B) = sum_(x in G) r_(A + B)(x)^2 >= (sum_(x in G) r_(A + B)(x))^2 / abs(A + B).
    $
    - By using indicator functions, show that $sum_(x in G) r_(A + B)(x) = abs(A) abs(B)$.
]
#proof[
    Observe that $
        E(A, B) & = abs({(a, a', b, b') in A^2 times B^2: a + b = a' + b'}) \
        & = abs(union.big_(x in G) {(a, a', b, b') in A^2 times B^2: a + b = x "and" a' + b' = x}) \
        & = union.big_(x in G) abs({(a, a', b, b') in A^2 times B^2: a + b = x "and" a' + b' = x}) \
        & = sum_(x in G) r_(A + B) (x)^2 \
        & = sum_(x in A + B) r_(A + B) (x)^2 \
        & >= (sum_(x in A + B) r_(A + B) (x))^2/(abs(A + B)) quad "by Cauchy-Schwarz"
    $ But now $
        sum_(x in G) r_(A + B) (x) & = sum_(x in G) abs(A sect (x - B)) = sum_(x in G) sum_(y in G) indicator(A)(y) indicator(x - B) (y) \
        & = sum_(x in G) sum_(y in G) indicator(A)(y) indicator(B)(x - y) = abs(A) abs(B).
    $
    Note that the same argument works for $abs(A - B)$.
]
#corollary[
    If $abs(A + A) <= K abs(A)$, then $E(A) >= abs(A)^4 / abs(A + A) >= abs(A)^3 / K$. So if $A$ has small doubling constant, then it has large additive energy.
]
#proofhints[
    Trivial.
]
#proof[
    Trivial.
]
#example[
    The converse of the above lemma does not hold: e.g. let $G$ be a (class of) abelian group(s). Then there exist constants $theta, eta > 0$ such that for all $n$ large enough, there exists $A subset.eq G$ with $abs(A) >= n$ satisfying $E(A) >= eta abs(A)^3$, and $abs(A + A) >= theta abs(A)^2$.
]
#definition[
    Given $A subset.eq G$ and $gamma > 0$, let $P_gamma := {x in G: abs(A sect (x + A)) >= gamma abs(A)}$ be the set of *$gamma$-popular differences* of $A$.
]
#lemma[
    Let $A subset.eq G$ be finite such that $E(A) = eta abs(A)^3$ for some $eta > 0$. Then $forall c > 0$, there is a subset $X subset.eq A$ with $abs(X) >= eta/3 abs(A)$ such that for all $(16c)$-proportion of pairs $(a, b) in X^2$, $a - b in P_(c eta)$.
]
#proof[
    - We use a technique called "dependent random choice".
    - Let $U = {x in G: abs(A sect (x + A)) <= 1/2 eta abs(A)}$.
    - Then $sum_(x in U) abs(A sect (x + A))^2 <= 1/2 eta abs(A) sum_(x in G) abs(A sect (x + A)) = 1/2 eta abs(A)^3 = 1/2 E(A)$.
    - For $0 <= i <= ceil(log_2 eta^(-1))$, let $Q_i = {x in G: abs(A) \/ 2^(i + 1) < abs(A sect (x + A)) <= abs(A) \/ 2^i}$ and set $delta_i = eta^(-1) 2^(-2i)$.
    - Then $
        sum_(i = 0)^(ceil(log_2 eta^(-1))) delta_i abs(Q_i) & = sum_i abs(Q_i) / (eta 2^(2i)) \
        & = 1 / (eta abs(A)^2) sum_i abs(A)^2 / 2^(2i) abs(Q_i) \
        & = 1 / (eta abs(A)^2) sum_i abs(A)^2 / 2^(2i) sum_(x in.not U) indicator({abs(A) \/ 2^(i + 1) < abs(A sect (x + A)) <= abs(A) \/ 2^i}) \
        & >= 1 / (eta abs(A)^2) sum_(x in.not U) abs(A sect (x + A))^2 \
        & >= 1 / (eta abs(A)^2) dot 1/2 E(A) = 1/2 abs(A).
    $
    - Let $S = {(a, b) in A^2: a - b in.not P_(c eta)}$. Now $
        sum_i sum_((a, b) in S) abs((A - a) sect (A - b) sect Q_i) & <= sum_((a, b) in S) abs((A - a) sect (A - b)) \
        & = sum_((a, b) in S) abs(A sect (a - b + A)) \
        & <= sum_((a, b) in S) c eta abs(A) quad "by definition of" S \
        & = abs(S) c eta abs(A) \
        & <= c eta abs(A)^3 = 2 c eta abs(A)^2 dot 1/2 abs(A) \
        & <= 2 c eta abs(A)^2 sum_i delta_i abs(Q_i) quad "by above inequality".
    $
    - Hence $exists i_0$ such that $
        sum_((a, b) in S) abs((A - a) sect (A - b) sect Q_(i_0)) <= 2 c eta abs(A)^2 delta_(i_0) abs(Q_(i_0))
    $
    - Let $Q = Q_(i_0)$, $delta = delta_(i_0)$, $lambda = 2^(-i_0)$, so that $
        sum_((a, b) in S) abs((A - a) sect (A - b) sect Q) <= 2 c eta abs(A)^2 delta abs(Q)
    $
    - Given $x in G$, let $X(x) = A sect (x + A)$. Then $
        EE_(x in Q) abs(X(x)) = 1/abs(Q) sum_(x in Q) abs(A sect (x + A)) >= 1/2 lambda abs(A).
    $
    - Define $T(x) = {(a, b) in X(x)^2: a - b in P^(c eta)}$. Then $
        EE_(x in Q) abs(T(x)) & = EE_(x in Q) abs({(a, b) in (A sect (x + A))^2: a - b in.not P_(c eta)}) \
        & = 1/abs(Q) sum_(x in Q) abs({(a, b) in S: x in (A - a) sect (A - b)}) \
        & = 1/abs(Q) sum_((a, b) in S) abs((A - a) sect (A - b) sect Q) \
        & <= 1/abs(Q) 2 c eta abs(A)^2 delta abs(Q) = 2 c eta delta abs(A)^2 = 2c lambda^2 abs(A)^2.
    $
    - Therefore, $
        EE_(x in Q) (abs(X(x))^2 - (16c)^(-1) abs(T(x))) & >= (EE_(x in Q) abs(X(x)))^2 - (16c)^(-1) EE_(x in Q) abs(T(x)) "by C-S" \
        & >= (lambda/2)^2 abs(A)^2 - (16c)^(-1) 2 c lambda^2 abs(A)^2 \
        & = (lambda^2 / 4 - lambda^2 / 8) abs(A)^2 = lambda^2 / 8 abs(A)^2.
    $
    - So $exists x in Q$ such that $abs(X(x))^2 >= lambda^2 / 8 abs(A)^2$, so $abs(X) >= lambda / sqrt(8) abs(A) >= eta/3 abs(A)$ and $abs(T(x)) <= 16c abs(X)^2$.
]
#theorem("Balog-Szemerédi-Gowers, Schoen")[
    Let $A subset.eq G$ be finite such that $E(A) >= eta abs(A)^3$ for some $eta > 0$. Then there exists $A' subset.eq A$ with $abs(A') >= c_1 (eta) abs(A)$ such that $abs(A' + A') <= abs(A)\/c_2 (eta)$, where $c_1 (eta)$ and $c_2 (eta)$ are both polynomial in $eta$.
]
#proof[
    - The idea is to find $A' subset.eq A$ such that $forall a, b in A'$, $a - b$ has many representations as $(a_1 - a_2) + (a_3 - a_4)$ with each $a_i in A$.
    - Apply the above lemma with $c = 2^(-7)$ to obtain $X subset.eq A$ with $abs(X) >= eta/3 abs(A)$ such that for all but $1/8$ of pairs $(a, b) in X^2$, $a - b in P_(eta\/2^7)$. In particular, the bipartite graph $G = \(X union.sq X, \{(x, y) in X times X: x - y in P_(eta\/2^7)\}\)$ has at least $7/8 abs(X)^2$ edges.
    - Let $A' = {x in X: deg_G (x) >= 3/4 abs(X)}$. Clearly $abs(A') >= abs(X)\/8$.
    - For any $a, b in A'$, there are at least $abs(X)\/2$ elements $y in X$ such that $(a, y), (b, y) in E(G)$ (so $a - y, b - y in P_(eta\/2^7)$). Hence $a - b = (a - y) - (b - y)$ has at least $
        underbrace(eta/6 abs(A), "choices for" y) dot eta/2^7 abs(A) eta/2^7 abs(A) >= eta^3 / 2^17 abs(A)^3
    $ representations of the form $a_1 - a_2 - (a_3 - a_4)$ with each $a_i in A$.
    - It follows that $eta^3 / 2^17 abs(A)^3 abs(A' - A') <= abs(A)^4$, hence $abs(A' - A') <= 2^17 eta^(-3) abs(A) <= 2^22 eta^(-4) abs(A')$, and so $abs(A' + A') <= 2^44 eta^(-8) abs(A')$.
]


= Fourier-analytic techniques

In this chapter, assume that $G$ is a _finite_ abelian group.

#definition[
    The group $hat(G)$ of *characters* of $G$ is the group of homomorphisms $gamma: G -> CC^times$. In fact, $hat(G)$ is isomorphic to $G$.
]<def:group-characters>
#notation[
    Norm and inner product notation:
    - Write $
        norm(f)_q = norm(f)_(L^q (G)) & = (EE_(x in G) abs(f(x))^q)^(1\/q), \
        norm(hat(f))_q = norm(hat(f))_(ell^q (hat(G))) & = \(sum_(gamma in hat(G)) abs(hat(f)(gamma))^q\)^(1\/q), \
        gen(f, g)_(L^2 (G)) & = EE_(x in G) f(x) overline(g(x)), \
        gen(f, g)_(ell^2 (hat(G))) & = sum_(gamma in hat(G)) hat(f)(gamma) overline(hat(g)(gamma))
    $
    - If Fourier support of function is restricted to $Lambda subset.eq hat(G)$, write $norm(hat(f))_(ell^q (Lambda)) = (sum_(gamma in Lambda) abs(hat(f)(gamma))^q)^(1\/q)$.
]
#notation[
    Asymptotic notation:
    - Write $f(n) = O(g(n))$ if $
        exists C > 0: forall n in NN, quad abs(f(n)) <= C abs(g(n)).
    $
    - Write $f(n) = o(g(n))$ if $
        forall epsilon > 0, exists N in NN: forall n >= N, abs(f(n)) <= epsilon abs(g(n)),
    $ i.e. $lim_(n -> oo) f(n)/g(n) = 0$.
    - Write $f(n) = Omega(g(n))$ if $g(n) = O(f(n))$.
    - If the implied constant depends on a fixed parameter, this may be indicated by a subscript, e.g. $exp(p n^2) = O_p (exp(n^2))$.
]
#theorem("Hölder's Inequality")[
    Let $p, q in [1, oo]$ with $1/p + 1/q$, and $f in L^p (G)$, $g in L^q (G)$. Then $
        norm(f g)_1 <= norm(f)_p norm(g)_q.
    $
]
#theorem("Cauchy-Schwarz Inequality")[
    For $f, g in L^2 (G)$, we have $ gen(f, g)_(L^2 (G)) <= norm(f)_2 norm(g)_2. $ Note this is a special case of Hölder's inequality with $p = q = 2$.
]
#theorem("Young's Convolution Inequality")[
    Let $p, q, r in [1, oo]$, $1/p + 1/q = 1/r$, $f in L^p (G)$, $g in L^q (G)$. Then $
        norm(f * g)_r <= norm(f)_p norm(g)_q.
    $
]
#notation[
    $e(y)$ denotes the function $e^(2pi i y)$.
]
#example[
    - Let $G = FF_p^n$, then for any $gamma in hat(G)$, we have a corresponding character $gamma(x) = e((gamma . x) \/p)$.
    - If $G = ZZ\/N$, then any $gamma in hat(G)$ has a corresponding character $gamma(x) = e(gamma x \/ N)$.
]
#notation[
    Given a non-empty $B subset.eq G$ and $g: B -> CC$, write $EE_(x in B) g(x)$ for $1/abs(B) sum_(x in B) g(x)$. If $B = G$, we may simply write $EE$ instead of $EE_(x in B)$.
]
#lemma[
    For all $gamma in hat(G)$, $
        EE_(x in G) gamma(x) = cases(
            1 quad & "if" gamma = 1,
            0 & "otherwise"
        ).
    $ and for all $x in G$, $
        sum_(gamma in hat(G)) gamma(x) = cases(
            abs(G) quad & "if" x = 0,
            0 & "otherwise"
        ).
    $
]
#proofhints[
    - For $1 != gamma in hat(G)$, consider $y in G$ with $gamma(y) != 1$.
    - For $0 != x in G$, by considering $G\/gen(x)$, show by contradiction that there is $gamma in hat(G)$ with $gamma(x) != 1$.
]
#proof[
    The first case for both equations is trivial. Let $1 != gamma in hat(G)$. Then $exists y in G$ with $gamma(y) != 1$. So $
        gamma(y) EE_(z in G) gamma(z) & = EE_(z in G) gamma(y + z) \
        & = EE_(z' in G) gamma(z').
    $ Hence $EE_(z in G) gamma(z) = 0$.
    
    For second equation, given $0 != x in G$, there exists $gamma in hat(G)$ such that $gamma(x) != 1$, since otherwise $hat(G)$ would act trivially on $gen(x)$, hence would also be the dual group for $G\/gen(x)$, a contradiction.
]
#definition[
    Given $f: G -> CC$, define the *Fourier transform* of $f$ to be $
        hat(f): hat(G) & -> CC, \
        gamma & |-> EE_(x in G) f(x) overline(gamma(x)).
    $
]
#proposition[
    Let $f: G -> CC$. Then for all $x in G$, $
        f(x) = sum_(gamma in hat(G)) hat(f)(gamma) gamma(x).
    $
]
#proofhints[
    Straightforward.
]
#proof[
    We have $
        sum_(gamma in hat(G)) hat(f)(gamma) gamma(x) & = sum_(gamma in hat(G)) EE_(y in G) f(y) overline(gamma(y)) gamma(x) \
        & = EE_(y in G) f(y) sum_(gamma in hat(G)) gamma(x - y) \
        & = f(x)
    $ by the above lemma.
]
#definition[
    For $A subset.eq G$, the *indicator* (or *characteristic*) function of $A$ is $
        indicator(A): G & -> {0, 1}, \
        x & |-> cases(
            1 quad & "if" x in A,
            0 & "if" x in.not A
        ).
    $
]<def:indicator-function>
#definition[
    $hat(bb(1))_A (1) = EE_(x in G) indicator(A)(x) dot 1 = abs(A)\/abs(G)$ is the *density* of $A$ in $G$. This is often denoted by $alpha$.
]<def:density>
#definition[
    Given $emptyset != A subset.eq G$, the *characteristic measure* $mu_A: G -> [0, abs(G)]$ is defined by $
        mu_A (x) := alpha^(-1) indicator(A)(x).
    $ Note that $EE_(x in G) mu_A (x) = 1 = hat(mu)_A (1)$.
]<def:characteristic-measure>
#definition[
    The *balanced function* $f_A: G -> [-1, 1]$ of $A$ is given by $
        f_A (x) = indicator(A)(x) - alpha.
    $ Note that $EE_(x in G) f_A (x) = 0 = hat(f)_A (1)$.
]<def:balanced-function>
#example[
    Let $V <= FF_p^n$ be a subspace. Then for $t in hat(FF)_p^n$, $
        hat(bb(1))_V (t) & = EE_(x in FF_p^n) indicator(V)(x) e(-x . t \/ p) \
        & = abs(V)/p^n indicator(V^perp)(t).
    $ where $V^perp = \{t in hat(FF)_p^n: x . t = 0 quad forall x in V\}$ is the *annihilator* of $V$. Hence, $hat(bb(1))_V (t) = mu_(V^perp) (t)$.
]
#example[
    Let $R subset.eq G$ be such that each $x in G$ lies in $R$ independently with probability $1/2$. Then with high probability, $
        sup_(gamma != 1) abs(hat(bb(1))_R (gamma)) = O(sqrt((log abs(G))/abs(G))).
    $ This follows from Chernoff's inequality.
]
#theorem("Chernoff's Inequality")[
    Given complex-valued independent random variables $X_1, ..., X_n$ with mean $0$, for all $theta > 0$, we have $
        Pr[abs(sum_(i = 1)^n X_i) >= theta sqrt(sum_(i = 1)^n norm(X_i)_(L^oo (Pr))^2)] <= 4 exp(-theta^2 \/ 4).
    $
]<thm:chernoffs-inequality>
#example[
    Let $Q = {x in FF_p^n: x . x = 0}$ wiht $p > 2$. Then $abs(Q)\/p^n = 1/p + O(p^(-n\/2))$ and $sup_(t != 0) abs(hat(bb(1))_Q (t)) = O(p^(-n\/2))$.
]
#lemma("Plancherel's Identity")[
    Let $f, g: G -> CC$. Then we have
    - *Parseval's identity*: 
    - *Plancherel's identity*: $gen(f, g) = gen(hat(f), hat(g))$.
]
#proof[
    Exercise.
]
#corollary("Parseval's Identity")[
    For all $f, g: G -> CC$, $
        norm(f)_(L^2 (G))^2 = norm(hat(f))_(L^2 (hat(G)))^2.
    $
]
#proof[
    By Plancherel.
]
#definition[
    Let $rho > 0$ and $f: G -> CC$. The *$rho$-large Fourier spectrum* of $f$ is $
        Spec_rho (f) := {gamma in hat(G): abs(hat(f)(gamma)) >= rho norm(f)_1}.
    $
]<def:rho-large-fourier-spectrum>
#example[
    By the previous example, if $f = indicator(V)$ with $V <= FF_p^n$ a subspace, then for all $rho in (0, 1]$, $
        Spec_rho (indicator(V)) = {t in hat(FF)_p^n: abs(indicator(V)(t)) >= rho abs(V) / p^n} = V^perp
    $
]
#lemma[
    For all $rho > 0$, $
        abs(Spec_rho (f)) <= rho^(-2) norm(f)_2^2 / norm(f)_1^2
    $
]
#proofhints[
    Use Parseval's identity.
]
#proof[
    By Parseval's identity, $
        norm(f)_2^2 = norm(hat(f))_2^2 & = sum_(gamma in hat(G)) abs(hat(f)(gamma))^2 \
        & >= sum_(gamma in Spec_rho (f)) abs(hat(f)(gamma))^2 \
        & >= abs(Spec_rho (f)) (rho norm(f)_1)^2.
    $
]
#remark[
    In particular, if $f = indicator(A)$ for $A subset.eq G$, then $norm(f)_1 = alpha = abs(A) \/ abs(G) = norm(f)_2^2$. So $abs(Spec_rho (indicator(A))) <= rho^(-2) alpha^(-1)$.
]


= Probabilistic tools




= Further topics

