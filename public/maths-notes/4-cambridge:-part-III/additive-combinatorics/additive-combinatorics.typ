#import "../../template.typ": *
#let name-abbrvs = (
    "Cauchy-Schwarz Inequality": "Cauchy-Schwarz",
    "Parseval's Identity": "Parseval"
)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)

#let Spec = math.op("Spec")
#let codim = math.op("codim")
#let Re = math.op("Re")

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
    Let $A = {a_1, ..., a_n}$ with $a_i < a_(i + 1)$. Then $a_1 + a_1 < a_1 + a_2 < dots.c < a_1 + a_n < a_2 + a_n < dots.c < a_n + a_n$. Note this is not the only choice of increasing sequence that works, in particular, so does $a_1 + a_1 < a_1 + a_2 < a_2 + a_2 < a_2 + a_3 < a_2 + a_4 < dots.c < a_2 + a_n < a_3 + a_n < dots.c < a_n + a_n$. So when equality holds, all these sequences must be the same. In particular, $a_2 + a_i = a_1 + a_(i + 1)$ for all $i$.
]
#lemma[
    If $A, B subset.eq ZZ$, then $|A + B| >= |A| + |B| - 1$ with equality iff $A$ and $B$ are arithmetic progressions with the same step.
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
    Note that $g in A + B$ iff $A sect (g - B) != emptyset$ where ($g - B = {g} - B$). Let $g in ZZ\/p$, then use inclusion-exclusion on $|A sect (g - B)|$ to conclude result.
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
    Assume $|A| + |B| < p + 1$, and WLOG that $1 <= |A| <= |B|$ and $0 in A$ (by translation). We use induction on $|A|$. $|A| = 1$ is trivial. Let $|A| >= 2$ and let $0 != a in A$. Then since $p$ is prime, ${a, 2a, ..., p a} = ZZ\/p$. There exists $m >= 0$ such that $m a in B$ but $(m + 1)a in.not B$ (why?). Let $B' = B - m a$, so $0 in B'$, $a in.not B'$ and $|B'| = |B|$.
    
    Now $1 <= |A sect B'| < |A|$ (why?) so the inductive hypothesis applies to $A sect B'$ and $A union B'$. Since $(A sect B') + (A union B') subset.eq A + B'$ (why?), we have $|A + B| = |A + B'| >= |(A sect B') + (A union B')| >= |A sect B'| + |A union B'| - 1 = |A| + |B| - 1$.
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
    Note that $|B| |A - C| <= |A - B| |B - C|$. Indeed, writing each $d in A - C$ as $d = a_d - c_d$ with $a_d in A$, $c_d in C$, the map $phi: B times (A - C) -> (A - B) times (B - C)$, $phi(b, d) = (a_d - b, b - c_d)$ is injective (why?). The triangle inequality now follows from definition of Ruzsa distance.
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
    Choose $emptyset != A' subset.eq A$ which minimises $|A' + B|\/|A'|$. Let the minimum value by $K'$. Then $|A' + B| = K' abs(A')$, $K' <= K$ and $forall A'' subset.eq A$, $|A'' + B| >= K' abs(A'')$.

    We claim that for every finite $C subset.eq G$, $|A' + B + C| <= K' abs(A' + C)$:
    
    Use induction on $abs(C)$. $abs(C) = 1$ is true by definition of $K'$. Let claim be true for $C$, consider $C' = C union {x}$ for $x in.not C$. $A' + B + C' = (A' + B + C) union ((A' + B + x) - (D + B + x))$, where $D = {a in A': a + B + x subset.eq A' + B + C}$. By definition of $K'$, $abs(D + B) >= K' abs(D)$. Hence, $
        |A' + B + C| & <= |A' + B + C| + abs(A' + B + x) - abs(D + B + x) \
        & <= K' abs(A' + C) + K' abs(A') - K' abs(D) \
        & = K' (abs(A' + C) + abs(A') - |D|).
    $ Applying this argument a second time, write $A' + C' = (A' + C) union ((A' + x) - (E + x))$, where $E = {a in A': a + x in A' + C} subset.eq D$. Finally, $
        abs(A' + C') & = abs(A' + C) + abs(A' + x) - abs(E + x) \
        & >= |A' + C| + |A'| - |D|.
    $ This proves the claim.
    
    We now show that $forall m in NN_0$, $abs(A' + m B) <= (K')^m abs(A')$ by induction: $m = 0$ is trivial, $m = 1$ is true by assumption. Suppose it is true for $m - 1 >= 1$. By the claim with $C = (m - 1) B$, we have $
        abs(A' + m B) = |A' + B + (m - 1)B| <= K' abs(A' + (m - 1)B) <= (K')^m abs(A').
    $ As in the proof of Ruzsa's triangle inequality, $forall ell, m in NN_0$, $
        |A'| |ell B - m B| & <= |A' + ell B| |A' + m B| \
        & <= (K')^ell abs(A') (K')^m abs(A') \
        & = (K')^(ell + m) abs(A')^2.
    $
]
#theorem("Freiman-Ruzsa")[
    Let $A subset.eq FF_p^n$ and $abs(A + A) <= K abs(A)$. Then $A$ is contained in a subspace $H subset.eq FF_p^n$ with $abs(H) <= K^2 p^(K^4) abs(A)$.
]<thm:freiman-ruzsa>
#proofhints[
    - Let $X subset.eq 2A - A$ be of maximal size such that all $x + A$, $x in X$, are disjoint.
    - Use @thm:plunneckes-inequality to obtain an upper bound on $abs(X) abs(A)$.
    - Show that $forall ell >= 2$, $ell A - A subset.eq (ell - 1)X + A - A$ by induction.
    - Let $H$ be subgroup generated by $A$. By writing $H$ as an infinite union, show that $H subset.eq Y + A - A$, where $Y$ is subgroup generated by $X$.
    - Find an upper bound for $abs(Y)$, conclude using @thm:plunneckes-inequality.
]
#proof[
    Choose maximal $X subset.eq 2A - A$ such that the translates $x + A$ with $x in X$ are disjoint. Such an $X$ cannot be too large: $forall x in X$, $x + A subset.eq 3A - A$, so by @thm:plunneckes-inequality, since $abs(3A - A) <= K^4 abs(A)$, $
        abs(X) abs(A) = abs(union.big_(x in X) (x + A)) <= abs(3A - A) <= K^4 abs(A).
    $ Hence $abs(X) <= K^4$. We next show that $2A - A subset.eq X + A - A$. Indeed, if, $y in 2A - A$ and $y in.not X$, then by maximality of $X$, then $(y + A) sect (x + A) != emptyset$ for some $x in X$. If $y in X$, then $y in X + A - A$. It follows from above, by induction, that $forall ell >= 2$, $ell A - A subset.eq (ell - 1)X + A - A$: $
        ell A - A & = A + (ell - 1)A - A \
        & subset.eq (ell - 2)X + 2A - A \
        & subset.eq (ell - 2)X + X + A - A \
        & = (ell - 1)X + A - A.
    $ Now, let $H subset.eq FF_p^n$ be the subgroup generated by $A$: $
        H = union.big_(ell >= 1) (ell A - A) subset.eq Y + A - A
    $ where $Y subset.eq FF_p^n$ is the subgroup generated by $X$. Every element of $Y$ can be written as a sum of $abs(X)$ elements of $X$ with coefficients in ${0, ..., p - 1}$. Hence, $abs(Y) <= p^abs(X) <= p^(K^4)$. Finaly, $abs(H) <= abs(Y) abs(A - A) <= p^(K^4) K^2 abs(A)$ by @thm:plunneckes-inequality/@lem:ruzsa-triangle-inequality.
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
        & >= (sum_(x in A + B) r_(A + B) (x))^2/(abs(A + B)) quad #[by @thm:cauchy-schwarz]
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
    We use a technique called "dependent random choice". Let $U = {x in G: abs(A sect (x + A)) <= 1/2 eta abs(A)}$. Then $
        sum_(x in U) abs(A sect (x + A))^2 & <= 1/2 eta abs(A) sum_(x in G) abs(A sect (x + A)) \
        & = 1/2 eta abs(A)^3 = 1/2 E(A).
    $ For $0 <= i <= ceil(log_2 eta^(-1))$, let $Q_i = {x in G: abs(A) \/ 2^(i + 1) < abs(A sect (x + A)) <= abs(A) \/ 2^i}$ and set $delta_i = eta^(-1) 2^(-2i)$. Then $
        sum_(i = 0)^(ceil(log_2 eta^(-1))) delta_i abs(Q_i) & = sum_i abs(Q_i) / (eta 2^(2i)) \
        & = 1 / (eta abs(A)^2) sum_i abs(A)^2 / 2^(2i) abs(Q_i) \
        & = 1 / (eta abs(A)^2) sum_i abs(A)^2 / 2^(2i) sum_(x in.not U) indicator({abs(A) \/ 2^(i + 1) < abs(A sect (x + A)) <= abs(A) \/ 2^i}) \
        & >= 1 / (eta abs(A)^2) sum_(x in.not U) abs(A sect (x + A))^2 \
        & >= 1 / (eta abs(A)^2) dot 1/2 E(A) = 1/2 abs(A).
    $ Let $S = {(a, b) in A^2: a - b in.not P_(c eta)}$. Now $
        sum_i sum_((a, b) in S) abs((A - a) sect (A - b) sect Q_i) & <= sum_((a, b) in S) abs((A - a) sect (A - b)) \
        & = sum_((a, b) in S) abs(A sect (a - b + A)) \
        & <= sum_((a, b) in S) c eta abs(A) quad "by definition of" S \
        & = abs(S) c eta abs(A) \
        & <= c eta abs(A)^3 = 2 c eta abs(A)^2 dot 1/2 abs(A) \
        & <= 2 c eta abs(A)^2 sum_i delta_i abs(Q_i) quad "by above inequality".
    $ Hence $exists i_0$ such that $
        sum_((a, b) in S) abs((A - a) sect (A - b) sect Q_(i_0)) <= 2 c eta abs(A)^2 delta_(i_0) abs(Q_(i_0)).
    $ Let $Q = Q_(i_0)$, $delta = delta_(i_0)$, $lambda = 2^(-i_0)$, so that $
        sum_((a, b) in S) abs((A - a) sect (A - b) sect Q) <= 2 c eta abs(A)^2 delta abs(Q).
    $ Given $x in G$, let $X(x) = A sect (x + A)$. Then $
        EE_(x in Q) abs(X(x)) = 1/abs(Q) sum_(x in Q) abs(A sect (x + A)) >= 1/2 lambda abs(A).
    $ Define $T(x) = {(a, b) in X(x)^2: a - b in P^(c eta)}$. Then $
        EE_(x in Q) abs(T(x)) & = EE_(x in Q) abs({(a, b) in (A sect (x + A))^2: a - b in.not P_(c eta)}) \
        & = 1/abs(Q) sum_(x in Q) abs({(a, b) in S: x in (A - a) sect (A - b)}) \
        & = 1/abs(Q) sum_((a, b) in S) abs((A - a) sect (A - b) sect Q) \
        & <= 1/abs(Q) 2 c eta abs(A)^2 delta abs(Q) = 2 c eta delta abs(A)^2 = 2c lambda^2 abs(A)^2.
    $ Therefore, $
        EE_(x in Q) (abs(X(x))^2 - (16c)^(-1) abs(T(x))) & >= (EE_(x in Q) abs(X(x)))^2 - (16c)^(-1) EE_(x in Q) abs(T(x)) #[by @thm:cauchy-schwarz] \
        & >= (lambda/2)^2 abs(A)^2 - (16c)^(-1) 2 c lambda^2 abs(A)^2 \
        & = (lambda^2 / 4 - lambda^2 / 8) abs(A)^2 = lambda^2 / 8 abs(A)^2.
    $ So $exists x in Q$ such that $abs(X(x))^2 >= lambda^2 / 8 abs(A)^2$, so $abs(X) >= lambda / sqrt(8) abs(A) >= eta/3 abs(A)$ and $abs(T(x)) <= 16c abs(X)^2$.
]
#theorem("Balog-Szemerédi-Gowers, Schoen")[
    Let $A subset.eq G$ be finite such that $E(A) >= eta abs(A)^3$ for some $eta > 0$. Then there exists $A' subset.eq A$ with $abs(A') >= c_1 (eta) abs(A)$ such that $abs(A' + A') <= abs(A)\/c_2 (eta)$, where $c_1 (eta)$ and $c_2 (eta)$ are both polynomial in $eta$.
]
#proof[
    The idea is to find $A' subset.eq A$ such that $forall a, b in A'$, $a - b$ has many representations as $(a_1 - a_2) + (a_3 - a_4)$ with each $a_i in A$. Apply the above lemma with $c = 2^(-7)$ to obtain $X subset.eq A$ with $abs(X) >= eta/3 abs(A)$ such that for all but $1/8$ of pairs $(a, b) in X^2$, $a - b in P_(eta\/2^7)$. In particular, the bipartite graph $G = \(X union.sq X, \{(x, y) in X times X: x - y in P_(eta\/2^7)\}\)$ has at least $7/8 abs(X)^2$ edges.
    
    Let $A' = {x in X: deg_G (x) >= 3/4 abs(X)}$. Clearly $abs(A') >= abs(X)\/8$. For any $a, b in A'$, there are at least $abs(X)\/2$ elements $y in X$ such that $(a, y), (b, y) in E(G)$ (so $a - y, b - y in P_(eta\/2^7)$). Hence $a - b = (a - y) - (b - y)$ has at least $
        underbrace(eta/6 abs(A), "choices for" y) dot eta/2^7 abs(A) eta/2^7 abs(A) >= eta^3 / 2^17 abs(A)^3
    $ representations of the form $a_1 - a_2 - (a_3 - a_4)$ with each $a_i in A$. It follows that $eta^3 / 2^17 abs(A)^3 abs(A' - A') <= abs(A)^4$, hence $abs(A' - A') <= 2^17 eta^(-3) abs(A) <= 2^22 eta^(-4) abs(A')$, and so $abs(A' + A') <= 2^44 eta^(-8) abs(A')$.
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
]<thm:cauchy-schwarz>
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
]<lem:expectation-of-character-values>
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
]<def:finite-group-fourier-transform>
#proposition("Fourier Inversion Formula")[
    Let $f: G -> CC$. Then for all $x in G$, $
        f(x) = sum_(gamma in hat(G)) hat(f)(gamma) gamma(x).
    $
]<prop:fourier-inversion-formula>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        sum_(gamma in hat(G)) hat(f)(gamma) gamma(x) & = sum_(gamma in hat(G)) EE_(y in G) f(y) overline(gamma(y)) gamma(x) \
        & = EE_(y in G) f(y) sum_(gamma in hat(G)) gamma(x - y) \
        & = f(x)
    $ by @lem:expectation-of-character-values.
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
    $ where $V^perp = \{t in hat(FF)_p^n: x . t = 0 quad forall x in V\}$ is the *annihilator* of $V$. Hence, $hat(bb(1))_V = mu_(V^perp)$.
]<exa:fourier-transform-of-indicator-of-subspace-is-characteristic-measure-of-annihilator>
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
    Let $Q = {x in FF_p^n: x . x = 0}$ with $p > 2$. Then $abs(Q)\/p^n = 1/p + O(p^(-n\/2))$ and $sup_(t != 0) abs(hat(bb(1))_Q (t)) = O(p^(-n\/2))$.
]
#lemma("Plancherel's Identity")[
    For all $f, g: G -> CC$, $
        gen(f, g) = gen(hat(f), hat(g)).
    $
]<lem:plancherels-identity>
#proof[
    Exercise.
]
#corollary("Parseval's Identity")[
    For all $f, g: G -> CC$, $
        norm(f)_(L^2 (G))^2 = norm(hat(f))_(ell^2 (hat(G)))^2.
    $
]<crl:parsevals-identity>
#proofhints[
    Trivial from @lem:plancherels-identity.
]
#proof[
    By @lem:plancherels-identity.
]
#definition[
    Let $rho > 0$ and $f: G -> CC$. The *$rho$-large Fourier spectrum* of $f$ is $
        Spec_rho (f) := {gamma in hat(G): abs(hat(f)(gamma)) >= rho norm(f)_1}.
    $
]<def:rho-large-fourier-spectrum>
#example[
    Let $A subset.eq G$, then $norm(f)_1 = alpha = abs(A)\/abs(G)$, so $
        Spec_rho (indicator(A)) = {t in hat(FF)_p^n: abs(hat(bb(1))_V (t)) >= rho alpha}.
    $ In particular, if $V <= FF_p^n$ is a subspace, then by @exa:fourier-transform-of-indicator-of-subspace-is-characteristic-measure-of-annihilator, $Spec_rho (indicator(V)) = V^perp$ for all $rho in (0, 1]$.
]<exa:rho-large-spectrum-of-indicator-is-greater-than-rho-times-density>
#lemma[
    For all $rho > 0$, $
        abs(Spec_rho (f)) <= rho^(-2) norm(f)_2^2 / norm(f)_1^2
    $ In particular, if $f = indicator(A)$ for $A subset.eq G$, then $norm(f)_1 = alpha = abs(A) \/ abs(G) = norm(f)_2^2$. So $abs(Spec_rho (indicator(A))) <= rho^(-2) alpha^(-1)$.
]<lem:set-of-large-fourier-coefficients-is-small>
#proofhints[
    Use @crl:parsevals-identity.
]
#proof[
    By @crl:parsevals-identity, $
        norm(f)_2^2 = norm(hat(f))_2^2 & = sum_(gamma in hat(G)) abs(hat(f)(gamma))^2 \
        & >= sum_(gamma in Spec_rho (f)) abs(hat(f)(gamma))^2 \
        & >= abs(Spec_rho (f)) (rho norm(f)_1)^2.
    $
]
#definition[
    The *convolution* of $f, g: GG -> CC$ is $
        f * g: G & -> CC, \
        x & |-> EE_(y in G) f(y) g(x - y).
    $
]<def:convolution>
#example[
    Given $A, B subset.eq G$, $
        (indicator(A) * indicator(B))(x) & = EE_(y in G) indicator(A)(y) indicator(B)(x - y) \
        & = EE_(y in G) indicator(A)(y) indicator(x - B)(y) \
        & = EE_(y in G) indicator(A sect (x - B))(y) \
        & = abs(A sect (x - B)) / abs(G) = 1/abs(G) r_(A + B)(x).
    $ In particular, $supp(indicator(A) * indicator(B)) = A + B$.
]
#lemma[
    Given $f, g: G -> CC$, $
        forall gamma in hat(G), quad hat((f * g))(gamma) = hat(f)(gamma) hat(g)(gamma).
    $
]<lem:fourier-transform-of-convolution-is-product-of-fourier-transforms>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        hat((f * g))(gamma) & = EE_(x in G) (f * g)(x) overline(gamma(x)) \
        & = EE_(x in G) EE_(y in G) f(y) g(x - y) overline(gamma(x)) \
        & = EE_(u in G) EE_(y in G) f(y) g(u) overline(gamma(u + y)) quad (u = x - y) \
        & = EE_(u in G) EE_(y in G) f(y) g(u) overline(gamma(u)) overline(gamma(y)) \
        & = hat(f)(gamma) hat(g)(gamma).
    $
]
#example[
    $EE_(x + y = z + w) f(x) f(y) overline(f(z) f(w)) = norm(hat(f))_(ell^4 (hat(G)))^4$. In particular, $norm(hat(bb(1))_A)_(ell^4 (hat(G)))^4 = E(A) \/ abs(G)^3$ for any $A subset.eq G$.
]
#theorem("Bogolyubov's Lemma")[
    Let $A subset.eq FF_p^n$ be of density $alpha$. Then there exists a subspace $V <= FF_p^n$ with $codim(V) <= 2 alpha^(-2)$, such that $V subset.eq A + A - A - A$.
]<thm:bogolyubovs-lemma>
#proofhints[
    - Let $g = indicator(A) * indicator(A) * indicator(-A) * indicator(-A)$, reason that if $g(x) > 0$ for all $x in V$, then $V subset.eq 2A - 2A$.
    - Let $S = Spec_rho (indicator(A))$, with $rho$ for now unspecified.
    - Show that $g(x) = alpha^4 + sum_(t in S \\ {0}) abs(hat(bb(1))_A (t))^4 e(x . t \/ p) + sum_(t in.not S) abs(hat(bb(1))_A (t))^4 e(x . t \/ p)$.
    - Find an appropriate subspace $V$ from $S$, bound $g(x)$ from below in terms of $rho$, and use this to determine a suitable value for $rho$.
]
#proof[
    Observe $2A - 2A = supp(g)$ where $g = indicator(A) * indicator(A) * indicator(-A) * indicator(-A)$, so we want to find $V <= FF_p^n$ such that $g(x) > 0$ for all $x in V$. Let $S = Spec_rho (indicator(A))$ with $rho$ a constant to be specified later, and let $V = gen(S)^perp$. By @lem:set-of-large-fourier-coefficients-is-small, $codim(V) = dim gen(S) <= abs(S) <= rho^(-2) alpha^(-1)$. Fix $x in V$. Now $
        g(x) & = sum_(t in hat(FF)_p^n) hat(g)(t) e(x . t \/ p) \
        & = sum_(t in hat(FF)_p^n) abs(hat(bb(1))_A (t))^4 e(x . t \/ p) quad #[by @lem:fourier-transform-of-convolution-is-product-of-fourier-transforms] \
        & = alpha^4 + sum_(t != 0) abs(hat(bb(1))_A (t))^4 e(x . t \/ p) \
        & = alpha^4 + sum_(t in S \\ {0}) abs(hat(bb(1))_A (t))^4 e(x . t \/ p) + sum_(t in.not S) abs(hat(bb(1))_A (t))^4 e(x . t \/ p)
    $ Each term in the first sum is non-negative, since $forall t in S$, $x . t = 0$. The absolute value of the second sum is bounded above, by the triangle inequality, by $
        sum_(t in.not S) abs(hat(bb(1))_A (t))^4 & <= sup_(t in.not S) abs(hat(bb(1))_A (t))^2 sum_(t in.not S) abs(hat(bb(1))_A (t))^2 \
        & <= sup_(t in.not S) abs(hat(bb(1))_A (t))^2 sum_(t in hat(FF)_p^n) abs(hat(bb(1))_A (t))^2 \
        & <= (rho alpha)^2 norm(indicator(A))_2^2 = rho^2 alpha^3
    $ by @exa:rho-large-spectrum-of-indicator-is-greater-than-rho-times-density and @crl:parsevals-identity. Note the second sum must be real since all other terms in the equation are. So we have $g(x) >= alpha^4 - rho^2 alpha^3$. Thus, it is sufficient that $rho^2 alpha^3 <= alpha^4 / 2$, so set $rho = sqrt(a\/2)$. Hence $g(x) > 0$ (in fact, $g(x) >= alpha^4 / 2$) for all $x in V$, and $codim(V) <= 2alpha^(-2)$.
]
#example[
    The set $A = {x in FF_2^n: abs(x) >= n/2 + sqrt(n)/2}$ (where $|x|$ is number of $1$s in $x$) has density $>= 1/8$ but there is no coset $C$ of any subspace of codimension $sqrt(n)$ such that $C subset.eq A + A$. Hence, the $2A - 2A$ part of Bogolyubov's lemma is necessary: $2A$ is not sufficient.
]
#lemma[
    Let $A subset.eq FF_p^n$ have density $alpha$ with $sup_(t != 0) abs(hat(bb(1))_A (t)) >= rho alpha$ for some $rho > 0$. Then there exists a subspace $V <= FF_p^n$ with $codim(V) = 1$ and $x in FF_p^n$ such that $
        abs(A sect (x + V)) >= alpha(1 + rho/2) abs(V).
    $
]<lem:a-large-fourier-coefficient-implies-a-codimension-one-intersecting-subspace>
#proofhints[
    - Let $V = gen(t)^perp$ for some suitable $t$ (can determine later).
    - Define $a_j = abs(A sect (v_j + V))/abs(v_j + V) - alpha$ for each $j in [p]$, where $x . v_j = j$.
    - Show that $hat(bb(1))_A (t) = EE_(j in [p]) a_j e(-j\/p)$.
    - Show that $EE_(j in [p]) a_j + abs(a_j) >= rho alpha$.
]
#proof[
    Let $t != 0$ be such that $abs(hat(bb(1))_A (t)) >= rho alpha$ and let $V = gen(t)^perp$. Write $v_j + V = {x in FF_p^n: x . t = j}$ for $j in [p]$ for the $p$ distinct cosets of $V$. Then $
        hat(bb(1))_A (t) & = hat(f)_A (t) = EE_(x in FF_p^n) (indicator(A) (x) - alpha) e(-x . t \/ p) \
        & = EE_(j in [p]) EE_(x in v_j + V) (indicator(A)(x) - alpha)e(-j\/p) \
        & = EE_(j in [p]) (abs(A sect (v_j + V))/abs(v_j + V) - alpha) e(-j\/p) \
        & =: EE_(j in [p]) a_j e(-j\/p).
    $ By the triangle inequality, $EE_(j in [p]) abs(a_j) >= rho alpha$. Note that $EE_(j in [p]) a_j = 0$. So $EE_(j in [p]) a_j + abs(a_j) >= rho alpha$, so $exists j in [p]$ such that $a_j + abs(a_j) >= rho alpha$, hence $a_j >= rho alpha\/2$. So take $x = v_j$.
]
#notation[
    Given $f, g, h: G -> CC$, write $
        T_3 (f, g, h) = EE_(x, d in G) f(x) g(x + d) h(x + 2d).
    $
]
#notation[
    Given $A subset.eq G$, write $2 dot A = {2a: a in A}$. Note this is not the same as $2A = A + A$.
]
#lemma[
    Let $p >= 3$ and $A subset.eq FF_p^n$ be of density $alpha > 0$, such that $sup_(t != 0) abs(hat(bb(1))_A (t)) <= epsilon$. Then the number of $3$-APs in $A$ differs from $alpha^3 (p^n)^2$ by at most $epsilon (p^n)^2$.
]
#proofhints[
    - Express $T_3 (indicator(A), indicator(A), indicator(A))$ as an inner product of functions $FF_p^n -> CC$, rewrite as inner product of functions $hat(FF)_p^n -> CC$.
    - Find upper bound of the absolute value of a sub-sum of this inner product, using triangle inequality and Cauchy-Schwarz.
]
#proof[
    The number of $3$-APs in $A$ is $(p^n)^2$ multiplied by $
        T_3 (indicator(A), indicator(A), indicator(A)) & = EE_(x, d) indicator(A)(x) indicator(A)(x + d) indicator(A)(x + 2d) \
        & = EE_(x, y) indicator(A)(x) indicator(A)(y) indicator(A)(2y - x) \
        & = EE_y indicator(A)(y) EE_x indicator(A)(x) indicator(A)(2y - x) \
        & = EE_y indicator(A)(y) (indicator(A) * indicator(A))(2y) \
        & = gen(indicator(2 dot A), indicator(A) * indicator(A)).
    $ By @lem:plancherels-identity and @lem:fourier-transform-of-convolution-is-product-of-fourier-transforms, this is equal to $
        gen(hat(bb(1))_(2 dot A), hat(bb(1))_A^2) & = sum_(t in hat(FF)_p^n) hat(bb(1))_(2 dot A)(t) overline(hat(bb(1))_(A)(t))^2 \
        & = alpha^3 + sum_(t != 0) hat(bb(1))_(2 dot A)(t) overline(hat(bb(1))_A (t))^2
    $ But $
        abs(sum_(t != 0) hat(bb(1))_(2 dot A)(t) overline(hat(bb(1))_A (t))^2) & <= sup_(t != 0) abs(hat(bb(1))_A (t)) sum_(t != 0) abs(hat(bb(1))_(2 dot A)(t)) abs(hat(bb(1))_A (t)) \
        & <= epsilon sum_(t in hat(FF)_p^n) abs(hat(bb(1))_(2 dot A)(t)) abs(hat(bb(1))_A (t)) \
        & <= epsilon (sum_(t) abs(hat(bb(1))_(2 dot A)(t))^2 sum_(t) abs(hat(bb(1))_A (t))^2)^(1\/2) quad & #[by @thm:cauchy-schwarz] \
        & = epsilon norm(hat(bb(1))_(2 dot A))_2 norm(hat(bb(1))_A)_2 \
        & = epsilon dot alpha^2 <= epsilon & #[by @crl:parsevals-identity]. \
    $
]
#theorem("Meshulam")[
    Let $A subset.eq FF_p^n$ be a set containing no non-trivial $3$-APs. Then $abs(A) = O(p^n \/ log p^n)$, i.e. $alpha = O(1\/n)$.
]<thm:meshulam>
#proofhints[
    - Use similar proof as that of above lemma to show that $abs(T_3 (indicator(A), indicator(A), indicator(A)) - alpha^3) <= sup_(t != 0) abs(hat(bb(1))_A (t)) dot alpha$.
    - Reason that provided $p^n >= 2 alpha^(-2)$, we have $sup_(t != 0) abs(hat(bb(1))_A (t)) >= alpha^2 / 2$.
    - Use this to iteratively generate $A_1, V_1$, $A_2, V_2$, ....
    - Reason that each $A_i$ contains no non-trivial 3 APs.
    - Find an expression for maximum number of steps it takes for the density of the $A_i$ to increase from $2^k alpha$ to $2^(k + 1) alpha$ (in terms of $k$ and $alpha$). Use this to deduce an upper bound for the maximum number steps it takes for the density to reach $1$.
    - Find lower bound for $dim(V_m)$ where $V_m$ is the final $V_i$ in the sequence, use fact that iteration halted to deduce that $p^dim(V_m) <= 2 alpha^(-2)$.
    - Reason that we can assume $alpha >= sqrt(2) p^(-n \/ 4)$, and conclude that $alpha <= 16 n$.
]
#proof[
    By assumption, $T_3 (indicator(A), indicator(A), indicator(A)) = abs(A)\/(p^n)^2 = alpha\/p^n$ (there are $abs(A)$ trivial APs). By the proof of the above lemma, $
        abs(T_3 (indicator(A), indicator(A), indicator(A)) - alpha^3) <= sup_(t != 0) abs(hat(bb(1))_A (t)) dot alpha.
    $ So provided that $p^n >= 2alpha^(-2)$, we have $T_3 (indicator(A), indicator(A), indicator(A)) <= alpha^3 \/ 2$, so $abs(T_3 (indicator(A), indicator(A), indicator(A)) - alpha^3) >= alpha^3 \/ 2$, hence $
        sup_(t != 0) abs(hat(bb(1))_A (t)) >= alpha^2 / 2.
    $ So by @lem:a-large-fourier-coefficient-implies-a-codimension-one-intersecting-subspace with $rho = alpha/2$, there exists a subspace $V <= FF_p^n$ of codimension $1$ and $x in FF_p^n$ such that $abs(A sect (x + V)) >= (alpha + alpha^2 \/ 4) abs(V)$.
    
    We iterate this observation: let $A_0 = A$, $V_0 = FF_p^n$, $alpha_0 = abs(A_0) \/ abs(V_0)$. At this $i$-th step, we are given a set $A_(i - 1) subset.eq V_(i - 1)$ of density $alpha_(i - 1)$ with no non-trivial $3$-APs. Provided that $p^(dim(V_(i - 1))) >= 2 alpha_(i - 1)^(-2)$, there exists a subspace $V_i <= V_(i - 1)$ of codimension $1$ and $x_i in V_(i - 1)$ such that $
        abs((A - x_i) sect V_i) = abs(A sect (x_i + V_i)) >= (alpha_(i - 1) + alpha_(i - 1)^2 \/ 4) abs(V_i)
    $ So set $A_i = (A - x_i) sect V_i$. $A_i$ has density $alpha_i >= alpha_(i - 1) + alpha_(i - 1)^2 \/ 4$, and contains no non-trivial $3$-APs (since the translate $A - x_i$ contains no non-trivial $3$-APs). Through this iteration, the density increases:
    - from $alpha$ to $2 alpha$ in at most $alpha\/(alpha^2 \/ 4) = 4 alpha^(-1)$ steps,
    - from $2 alpha$ to $4 alpha$ in at most $(2 alpha)\/((2 alpha)^2 \/ 4) = 2 alpha^(-1)$ steps.
    - and so on, ...
    So the density reaches $1$ in at most $4 alpha^(-1) (1 + 1/2 + 1/4 + dots.c) = 8 alpha^(-1)$ steps. The iteration must end with $dim(V_i) >= n - 8 alpha^(-1)$, at which point we must have had $p^dim(V_i) < 2 alpha_(i - 1)^(-2) <= 2 alpha^(-2)$, or else we could have iterated again.

    But we may assume that $alpha >= sqrt(2) p^(-n\/4)$ (since otherwise we would be done), so $alpha^(-2) < 1/2 p^(n\/2)$, whence $p^(n - 8alpha^(-1)) <= p^(n\/2)$, i.e. $n/2 <= 8 alpha^(-1)$.
]
#remark[
    The current largest known subset of $FF_3^n$ containing no non-trivial $3$-APs has size $2.2202^n$.
]
#lemma[
    Let $A subset.eq [N]$ be of density $alpha > 0$ and contain no non-trivial $3$-APs, with $N > 50 alpha^(-2)$. Let $p$ be a prime with $p in [N\/3, 2N\/3]$, and write $A' = A sect [p] subset.eq ZZ\/p$. Then one of the following holds:
    + $sup_(t != 0) abs(hat(bb(1))_(A')(t)) >= alpha^2 \/ 10$ (where the Fourier coefficient is computed in $ZZ\/p$).
    + There exists an interval $J subset.eq [N]$ of length $>= N\/3$ such that $abs(A sect J) >= alpha(1 + alpha\/400) abs(J)$.
]
#proofhints[
    - Show that we can assume $abs(A') >= alpha(1 - alpha\/200) p$.
]
#proof[
    TODO: fill in details in proof.

    We may assume that $abs(A') = abs(A sect [p]) >= alpha(1 - alpha\/200) p$, since otherwise $abs(A sect [p + 1, N]) >= alpha N - (alpha(1 - alpha\/200) p) = alpha(N - p) + alpha^2 / 200 p >= (alpha + alpha^2 \/ 400)(N - p)$ since $p >= N\/3$, which implies case 2 with $J = [p + 1, N]$.

    Let $A'' = A' sect [p\/3, 2p\/3]$. Note that all $3$-APs of the form $(x, x + d, x + 2d) in A' times A'' times A''$ are in fact APs in $[N]$. If $abs(A' sect [p\/3])$ or $abs(A' sect [2p\/3, p])$ is at least $2/5 abs(A')$, then again we are in case 2. So we may assume that $abs(A'') >= abs(A')\/5$. Now as in above lemmas, we have $
        alpha'' / p = abs(A'') / p^2 = T_3 (indicator(A'), indicator(A''), indicator(A'')) = alpha' (alpha'')^2 + sum_(t) overline(hat(bb(1))_(A')(t) hat(bb(1))_(A'')(t)) hat(bb(1))_(2 dot A'')(t)
    $ where $alpha' = abs(A') \/ p$ and $alpha'' = abs(A'') \/ p$. So as before, $
        (alpha' alpha'') / 2 & <= sup_(t != 0) abs(indicator(A')(t)) dot alpha''
    $ provided that $alpha'' \/ p <= 1/2 alpha' (alpha'')^2$, i.e. $2 \/ p <= alpha' alpha''$ (check this inequality indeed holds). Hence, $sup_(t != 0) abs(hat(bb(1))_(A')(t)) >= (alpha' alpha'')/2 >= 1/2 alpha(1 - alpha\/200)^2 dot 2/5 >= alpha^2 \/ 10$. TODO: constants need to change somewhere here.
]
#lemma[
    Let $m in NN$, and let $phi: [m] -> ZZ\/p$ be given by $phi(x) = t x$ for some $t != 0$. For all $epsilon > 0$, there exists a partition of $[m]$ into progressions $P_i$ of length $ell_i in [epsilon sqrt(m)\/2, epsilon sqrt(m)]$, such that $
        forall i, quad "diam"(phi(P_i)) := max_(x, y in P_i) abs(phi(x) - phi(y)) <= epsilon p
    $ (where $abs(phi(x) - phi(y))$ views $phi(x), phi(y) in {0, ..., p - 1}$).
]
#proof[
    Let $u = floor(sqrt(m))$ and consider $0, t, ..., u t$. By the pigeonhole principle, there exists $0 <= v < w <= u$ such that $abs(w t - v t) = abs((w - v)t) <= p\/u$. Set $s = w - v$, so $abs(s t) <= p\/u$. Divide $[m]$ into residue classes $mod s$, each of which has size at least $m\/s >= m\/u$. But each residue class can be divided into APsof the form $a, a + s, ..., a + d s$ for some $epsilon u \/ 2 < d <= epsilon u$. The diameter of the image of each progression under $phi$ is $abs(d s t) <= d p \/ u <= epsilon u p \/ u = epsilon p$.
]
#lemma[
    Let $A subset.eq [N]$ be of density $alpha > 0$, let $p$ be prime with $p in [N\/3, 2N\/3]$, and write $A' = A sect [p] subset.eq ZZ\/p$. Suppose that $abs(hat(bb(1))_(A')(t)) >= alpha^2 \/ 20$ for some $t != 0$. Then there exists a progression $P subset.eq [N]$ of length at least $alpha^2 sqrt(N) \/ 500$ such that $abs(A sect P) >= alpha(1 + alpha\/80) abs(P)$.
]
#proof[
    Let $epsilon = alpha^2 \/ 40pi$ and use above lemma to partition $[p]$ into progressions $P_i$ of length $>= epsilon sqrt(p\/2) >= alpha^2 \/ 40pi sqrt(N \/ 3) / 2 >= alpha^ sqrt(N) \/ 500$, and $"diam"(phi(P_i)) <= epsilon p$. Fix one $x_i$ from each of the $P_i$. Then $
        alpha^2 / 20 & <= abs(hat(f)_(A')(t)) = 1/p sum_i sum_(x in P_i) f_(A')(x) e(- x t \/ p) \
        & = 1/p abs(sum_i sum_(x in P_i) f_(A')(x) e(-x i t \/ p) + sum_i sum_(x in P_i) f_(A')(x) (e(-x t \/ p) - e(-x i t \/ p))) \
        & <= 1/p sum_i abs(sum_(x in P_i) f_(A')(x)) + 1/p sum_i sum_(x in P_i) abs(f_(A')(x)) underbrace(abs(e(-x t \/ p) - e(-x i t \/ p)), <= 2pi epsilon "since" "diam"(phi(P_i)) <= epsilon p)
    $ So $
        sum_i abs(sum_(x in P_i) f_(A')(x)) >= alpha^2 / 40 p
    $ Since $f_(A')$ has mean zero, $
        sum_i (abs(sum_(x in P_i) f_(A')(x)) + sum_(x in P_i) f_(A')(x)) >= alpha^2 / 40 p
    $ hence $exists i$ such that $
        abs(sum_(x in P_i) f_(A')(x)) + sum_(x in P_i) f_(A')(x) >= alpha^2 / 80 abs(P_i)
    $ and so $
        sum_(x in P_i) f_(A')(x) >= alpha^2 / 160 abs(P_i).
    $
]
#definition[
    Let $Gamma subset.eq hat(G)$ and $rho > 0$. The *Bohr set* $B(Gamma, rho)$ is the set $
        B(Gamma, rho) = {x in G: abs(gamma(x) - 1)) < rho thick forall gamma in Gamma}.
    $ The *rank* of $B(Gamma, rho)$ is $abs(B(Gamma, rho))$, and is *width* (or *radius*) is $rho$.
]
#example[
    Let $G = FF_p^n$, then $B(Gamma, rho) = gen(Gamma)^perp$ for all sufficiently small $rho$. Here, the rank gives an upper bound on $codim(gen(Gamma)^perp)$.
]
#lemma[
    Let $Gamma subset.eq hat(G)$ and $abs(Gamma) = d$, and let $rho > 0$. Then $
        abs(B(Gamma, rho)) >= (rho / 8)^d abs(G).
    $
]
#proposition("Bogolyubov's Lemma for Finite Abelian Groups")[
    Let $A subset.eq G$ be of density $alpha > 0$. Then there exists $Gamma subset.eq hat(G)$ with $abs(Gamma) <= 2 alpha^(-2)$ such that $
        B(Gamma, 1/2) subset.eq A + A - (A + A).
    $
]
#proof[
    Recall that $
        (indicator(A) * indicator(A) * indicator(A) * indicator(A))(x) & = sum_(gamma in hat(G)) abs(hat(bb(1))_A (gamma))^4 gamma(x)
    $ Let $Gamma = Spec_(sqrt(alpha \/ 2))(indicator(A))$ and note that for $x in B(Gamma, 1 \/ 2)$ and $gamma in Gamma$, $Re(gamma(x)) > 0$. Hence, for $x in B(Gamma, 1 \/ 2)$, $
        Re (sum_(gamma in hat(G)) abs(hat(bb(1))_A (gamma))^4 gamma(x)) & = Re(sum_(gamma in Gamma)) abs(hat(bb(1))_A (gamma))^4 gamma(x)) + Re(sum_(x in.not Gamma)) abs(hat(bb(1))_A (gamma))^4 gamma(x))
    $ and $
        abs(Re(sum_(gamma in.not Gamma) abs(hat(bb(1))_A (gamma))^4 gamma(x)))) & <= sup_(gamma in.not Gamma) abs(hat(bb(1))_A (gamma))^2 sum_(gamma in.not Gamma) abs(hat(bb(1))_A (gamma))^2 \
        & <= (sqrt(alpha / 2) dot alpha)^2 dot alpha = alpha^4 / 2
    $ by Parseval.
]
#theorem("Roth")[
    Let $A subset.eq [N]$ be a set containing no non-trivial $3$-APs. Then $abs(A) = O(N\/ log log N)$.
]<thm:roth>
#proof[

]
#example("Behrend's Example")[
    There exists a set $A subset.eq [N]$ of size $abs(A) >= exp(-c sqrt(log N)) N$ containing no non-trivial $3$-APs.
]


= Probabilistic tools

All probability spaces here will be finite.

#theorem("Khintchine's Inequality")[
    Let $p in [2, oo)$. Let $X_1, ..., X_n$ be independent random variables such that $
        forall i in [n], quad PP(X_i = x_i) = PP(X_i = -x_i) = 1/2
    $ for some $x_1, ..., x_n in CC$. Then $
        norm(sum_(i = 1)^n X_i)_(L^p (PP)) = O(p^(1\/2) (sum_(i = 1)^n norm(X_i)_(L^2 (PP))^2)^(1\/2))
    $
]<thm:khintchines-inequality>
#proof[
    Since $L_p$ norms are nested, it suffices to prove in the case that $p = 2k$ for some $k in NN$. Write $X = sum_(i = 1)^n X_i$, and assume the quantity $sum_(i = 1)^n norm(X_i)_(L^oo (PP))^2 = sum_(i = 1)^n abs(x_i)^2 = sum_(i = 1)^n norm(X_i)_(L^2 (PP))^2$ is equal to $1$. By Chernoff's Inequality, $forall theta > 0$, $
        Pr(abs(X) >= theta) <= 4 exp(-theta^2 \/ 4),
    $ and so, since $integral_0^t P_X (s) dif s = Pr(abs(X) <= t)$, $
        norm(X)_(L^(2k)(Pr))^(2k) & = integral_0^oo t^(2k) P_X (t) dif t \
        & = integral_0^oo 2k t^(2k - 1) Pr(abs(X) >= t) dif t "by integration by parts" \
        & <= 8k integral_0^oo t^(2k - 1) exp(-t^2 \/ 4) dif t =: 8k I(k)
    $ We will show by induction on $k$ that $I(k) <= 2^(2k) (2k)^k \/ 4k$. Indeed, when $k = 1$, $
        integral_0^oo t exp(-t^2 \/ 4) dif t & = [-2 exp(-t^2 \/ 4)]_0^oo = 2 \
        & = 2^(2 dot 1) (2 dot 1)^1 \/ (4 dot 1)
    $ For $k > 1$, we integrate by parts to find that $
        I(k) & := integral_0^oo underbrace(t^(2k - 2), u) dot underbrace(t exp(-t^2 \/ 4), v') dif t \
        & = [t^(2k - 2) dot (-2 exp(-t^2 \/ 4))]_0^oo - integral_0^oo (2k - 2) t^(2k - 3) dot (-2 exp(-t^2 \/ 4)) dif t \
        & = 4(k - 1) integral_0^oo t^(2(k - 1) - 1) exp(-t^2 \/ 4) dif t \
        & = 4(k - 1) I(k - 1) \
        & <= (4(k - 1) 2^(2k - 1) (2(k - 1))^(k - 1)) / (4(k - 1)) "by induction hypothesis" \
        & <= (2^(2k) (2k)^k) / (4k).
    $
]
#corollary("Rudin's Inequality")[
    Let $Gamma subset.eq hat(FF)_2^n$ be a linearly independent set and let $p in [2, oo)$. Then $forall hat(f) in ell^2 (Gamma)$, $
        norm(sum_(gamma in Gamma) hat(f)(gamma) gamma)_(L^p (FF_2^n)) = O(sqrt(p) dot norm(hat(f))_(ell^2 (Gamma)))
    $
]<crl:rudins-inequality>
#proof[
    Exercise.
]
#corollary("Dual Rudin")[
    Let $Gamma subset.eq hat(FF)_2^n$ be a linearly independent set and let $p in (1, 2]$. Then $forall f in L^p (FF_2^n)$, $
        norm(hat(f))_(ell^2 (Gamma)) = O(sqrt(p / (p - 1)) dot norm(f)_(L^p (FF_2^n))).
    $
]<crl:dual-rudin>
#proof[
    Let $f in L^p (FF_2^n)$ and let $g(x) = sum_(gamma in Gamma) hat(f)(gamma) gamma(x)$, so $g = f|_(Gamma)$?. Then $
        norm(hat(f))_(ell^2 (Gamma))^2 & = sum_(gamma in Gamma) abs(hat(f)(gamma))^2 \
        & = gen(hat(f), hat(g))_(ell^2 (Gamma)) = gen(hat(f), hat(g))_(ell^2 (hat(FF)_2^n)) \
        & = gen(f, g)_(L^2 (FF_2^n)) quad & #[by @lem:plancherels-identity] \
        & <= norm(f)_(L^p (FF_2^n)) norm(g)_(L^q (FF_2^n)) quad & #[by Holder's inequality].
    $ where $1 \/ p + 1 \/ q = 1$. By @crl:rudins-inequality, $
        norm(g)_(L^q (FF_2^n)) & = O(sqrt(q) dot norm(hat(g))_(ell^2 (Gamma))) \
        & = O(sqrt(p / (p - 1)) dot norm(hat(f))_(ell^2 (Gamma))).
    $
]
Recall that given $A subset.eq FF_2^n$ of density $alpha > 0$, we have $abs(Spec_rho (indicator(A))) <= rho^(-2) alpha^(-1)$. This is the best possible bound as the example  of a subspace $A$ shows. However, in this case, the large spectrum is highly structured. 
#theorem("Special Case of Chang's Theorem")[
    Let $A subset.eq FF_2^n$ be of density of $alpha > 0$. Then $
        forall rho > 0, exists H <= hat(FF)_2^n: dim(H) = O(rho^(-2) log alpha^(-1)) "and" Spec_rho (indicator(A)) subset.eq H.
    $
]<thm:chang-special-case>
#proof[
    Let $Gamma subset.eq Spec_rho (indicator(A))$ be maximal linearly independent set. Let $H = gen(Spec_rho (indicator(A)))$. Clearly $dim(H) = abs(Gamma)$. By @crl:dual-rudin, $forall p in (1, 2]$, $
        (rho alpha)^2 abs(Gamma) <= sum_(gamma in Gamma) abs(hat(bb(1))_A (gamma))^2 = norm(hat(bb(1))_A)_(ell^2 (Gamma))^2 = O(p/(p - 1) norm(indicator(A))_(L^p (FF_2^n))^2) = O(p/(p - 1) alpha^(2 \/ p)).
    $ Hence, $abs(Gamma) <= O(rho^(-2) alpha^(-2) alpha^(2 \/ p) p/(p - 1))$. Setting $p = 1 + (log alpha^(-1))^(-1)$, we obtain $abs(Gamma) <= O(rho^(-2) alpha^(-2) (alpha^2 e^2)(log alpha^(-1) + 1)) = O(rho^(-2) log alpha^(-1))$.
]
#definition[
    Let $G$ be a finite abelian group. $S subset.eq G$ is *dissociated* if $sum_(s in S) epsilon_s s = 0$ with each $epsilon_s in {-1, 0, 1}$, then $epsilon_s = 0$ for all $s in S$.
]
#example[
    Clearly, if $G = FF_2^n$, then $S subset.eq G$ is dissociated iff $S$ is linearly independent.
]