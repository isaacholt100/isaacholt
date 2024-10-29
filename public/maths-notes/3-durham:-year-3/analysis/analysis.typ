#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

// FIND: - \*(\w+)\*: ([\s\S]*?)(?=\n-|\n\n)\n
// REPLACE: #$1[\n    $2\n]\n

#let indicator(arg) = $bb(1)_arg$
#let ip(a, b) = $angle.l #a, #b angle.r$

= The real numbers

== Conventions on sets and functions

#definition[
    For $f: X -> Y$, *preimage* of $Z subset.eq Y$ is $ f^(-1) (Z) := {x in X: f(x) in Z} $
]
#definition[
    $f: X -> Y$ *injective* if $ forall y in f(X), exists! x in X: y = f(x) $
]
#definition[
    $f: X -> Y$ *surjective* if $Y = f(X)$.
]
#proposition[
    Let $f: X -> Y$, $A, B subset.eq X$, then $ f(A sect B) & subset.eq f(A) sect f(B), \ f(A union B) & = f(A) union f(B), \ f(X) - f(A) & subset.eq f(X - A) $
]
#proposition[
    Let $f: X -> Y$, $C, D subset.eq Y$, then $ f^(-1)(C sect D) & = f^(-1) (C) sect f^(-1)(D), \ f^(-1)(C union D) & = f^(-1)(C) union f^(-1)(D), \ f^(-1)(Y - C) & = X - f^(-1)(C) $
]

== The real numbers

#definition[
    $a in RR$ is an *upper bound* of $E subset.eq RR$ if $forall x in E, x <= a$.
]
#definition[
    $c in RR$ is a *least upper bound (supremum)* of $E$, $c = sup(E)$, if $c <= a$ for every upper bound $a$.
]
#definition[
    $a in RR$ is an *lower bound* of $E subset.eq RR$ if $forall x in E, x >= a$.
]
#definition[
    $c in RR$ is a *greatest lower bound (infimum)*, $c = inf(E)$, if $c >= a$ for every lower bound $a$.
]
#theorem("Completeness axiom of the real numbers")[
    Every $E subset.eq RR$ with an upper bound has a least upper bound. Every $E subset.eq RR$ with a lower bound has a greatest lower bound.
]
#proposition("Archimedes' principle")[
    $ forall x in RR, exists n in NN: n > x $
]
#remark[
    Every non-empty subset of $NN$ has a minimum.
]
#proposition[
    $QQ$ is dense in $RR$: $ forall x < y in RR, exists r in QQ: r in (x, y) $
]

== Sequences, limits and series

#definition[
    $l in RR$ is *limit* of $(x_n)$ ($(x_n)$ converges to $l$) if $ forall epsilon > 0, exists N in NN: forall n >= N, quad |x_n - l| < epsilon $ A sequence *converges in $RR$ (is convergent)* if it has a limit $l in RR$. Limit $l = lim_(n -> oo) x_n$ is unique.
]
#definition[
    $(x_n)$ *tends to infinity* if $ forall K > 0, exists N in NN: forall n >= N, quad x_n > K $
]
#definition[
    *Subsequence* of $(x_n)$ is sequence $\(x_(n_j)\)$, $n_1 < n_2 < dots.h.c$.
]
#definition[
    *Limit inferior* of sequence $x_n$ is $ liminf_(n -> oo) x_n := sup_(n in NN) {inf_(m >= n) x_m} = lim_(n -> oo) (inf_(m >= n) x_m) $
]
#definition[
    *Limit superior* of sequence $x_n$ is $ limsup_(n -> oo) x_n := inf_(n in NN) {sup_(m >= n) x_m} = lim_(n -> oo) (sup_(m >= n) x_m) $
]
#proposition[
    Let $(x_n)$ bounded, $l in RR$. Then $l = limsup x_n$ iff both of the following hold:
    - $forall epsilon > 0, exists N in NN: forall n >= N, x_n < l + epsilon$.
    - $forall epsilon > 0, forall N in NN: exists n >= N: x_n > l - epsilon$.
]
#proposition[
    Let $(x_n)$ bounded, $l in RR$. Then $l = liminf x_n$ iff both of the following hold:
    - $forall epsilon > 0, exists N in NN: forall n >= N, x_n > l - epsilon$.
    - $forall epsilon > 0, forall N in NN: exists n >= N: x_n < l + epsilon$.
]
#theorem("Bolzano-Weierstrass")[
    Every bounded sequence has a convergent subsequence.
]
#proposition[
    Let $(x_n)$ bounded. There exists convergent subsequence with limit $limsup x_n$ and convergent subsequence with limit $liminf x_n$.
]
#proposition[
    Let $(x_n)$ bounded, then $(x_n)$ is convergent iff $limsup x_n = liminf x_n$.
]
#theorem("Monotone convergence theorem for sequences")[
    Monotone sequence converges in $RR$ or tends to either $oo$ or $-oo$.
]
#definition[
    $(x_n)$ is *Cauchy sequence* if $ forall epsilon > 0, exists N in NN: forall n, m >= N, quad |x_n - x_m| < epsilon $
]
#theorem[
    Every Cauchy sequence in $RR$ is convergent.
]

== Open and closed sets

#definition[
    $U subset.eq RR$ is *open* if $ forall x in U, exists epsilon > 0: (x - epsilon, x + epsilon) subset.eq U $
]
#proposition[
    Arbitrary unions of open sets are open. Finite intersections of open sets are open.
]
#definition[
    $x in RR$ is *point of closure (limit point)* for $E subset.eq RR$ if $ forall epsilon > 0, exists y in E: |x - y| < epsilon $ Equivalently, $x$ is point of closure of $E$ if every open interval containing $x$ contains a point of $E$.
]
#definition[
    *Closure* of $E$, $overline(E)$, is set of points of closure. Note $E subset.eq overline(E)$.
]
#definition[
    $F$ is *closed* if $F = overline(F)$.
]
#proposition[
    $overline(A union B) = overline(A) union overline(B)$. If $A subset B subset.eq RR$ then $overline(A) subset overline(B)$.
]
#proposition[
    For any set $E$, $overline(E)$ is closed, i.e. $overline(E) = overline(overline(E))$.
]
#proposition[
    $E subset.eq RR$ is closed iff $RR - E$ is open.
]
#proposition[
    Arbitrary intersections of closed sets are closed. Finite unions of closed sets are closed.
]
#definition[
    Collection $C$ of subsets of $RR$ *covers* (is a *covering* of) $F subset.eq RR$ if $F subset.eq union_(S in C) S$. If each $S$ in $C$ open, $C$ is *open covering*. If $C$ is finite, $C$ is *finite covering*.
]
#definition[
    Covering $C$ of $F$ *contains a finite subcover* if exists ${S_1, ..., S_n} subset.eq C$ with $F subset.eq union_(i = 1)^n S_i$ (i.e. a finite subset of $C$ covers $F$).
]
#definition[
    $F$ is *compact* if any open covering of $F$ contains a finite subcover.
]
#example[
    $RR$ is not compact, $[a, b]$ is compact.
]
#theorem("Heine Borel")[
    $F$ compact iff $F$ closed and bounded.
]

== Continuity, pointwise and uniform convergence of functions

#definition[
    Let $E subset.eq RR$. $f: E -> RR$ is *continuous at $a in E$* if $ forall epsilon > 0, exists delta > 0: forall x in E, |x - a| < delta ==> |f(x) - f(a)| < epsilon $ $f$ is *continuous* if continuous at all $y in E$.
]
#definition[
    $lim_(x -> a) f(x) = l$ if $ forall epsilon > 0, exists delta > 0: forall x in E, |x - a| < delta ==> |f(x) - l| < epsilon $
]
#proposition[
    $lim_(x -> a) f(x) = l$ iff for every sequence $(a_n)$ with $lim_(n -> oo) a_n = a$, $lim_(n -> oo) f(a_n) = l$.
]
#proposition[
    $f$ is continuous at $a in E$ iff $lim_(x -> a) f(x) = f(a)$ (and this limit exists).
]
#definition[
    $f: E -> RR$ is *uniformly continuous* if $ forall epsilon > 0, exists delta > 0: forall x, y in E, |x - y| < delta ==> |f(x) - f(y)| < epsilon $
]
#proposition[
    Let $F$ closed and bounded, $f: F -> RR$ continuous. Then $f$ is uniformly continuous.
]
#definition[
    Let $f_n: E -> RR$ sequence of functions, $f: E -> RR$. $(f_n)$ *converges pointwise* to $f$ if $ forall epsilon > 0, forall x in E, exists N in NN: forall n >= N, |f_n (x) - f(x)| < epsilon $ $(f_n)$ *converges uniformly* to $f$ is $ forall epsilon > 0, exists N in NN: forall n >= N, forall x in E, |f_n (x) - f(x)| < epsilon $
]
#theorem[
    Let $f_n: E -> RR$ sequence of continuous functions converging uniformly to $f: E -> RR$. Then $f$ is continuous.
]
#definition[
    $P = {x_0, ..., x_n}$ is *partition* of $[a, b]$ if $a = x_0 < dots.h.c < x_n = b$.
]
#definition[
    $f: [a, b] -> RR$ is *piecewise linear* if there exists partition $P = {x_0, ..., x_n}$ and $m_i, c_i in RR$ such that $ forall i in [n], forall x in \(x_(i - 1), x_i\), quad f(x) = m_i x + c_i $ $f$ is continuous on $[a, b] - P$.
]
#definition[
    $g: [a, b] -> RR$ is *step function* if there exists partition $P = {x_0, ..., x_n}$ and $m_i in RR$ such that $ forall i in [n], forall x in \(x_(i - 1), x_i\), quad g(x) = m_i $ $g$ is continuous on $[a, b] - P$.
]
#theorem[
    Let $f: E -> RR$ continuous, $E$ closed and bounded. Then there exist continuous piecewise linear $f_n$ with $f_n -> f$ uniformly, and step functions $g_n$ with $g_n -> f$ uniformly.
]
#definition[
    $f: E -> RR$ is *Lipschitz* if $ exists C > 0: forall x, y in E, quad |f(x) - f(y)| <= C|x - y| $
]
#definition[
    $f: E -> RR$ is *bi-Lipschitz* if $ exists C > 0: forall x, y in E, quad C^(-1)|x - y| <= |f(x) - f(y)| <= C|x - y| $
]

== The extended real numbers

#definition[
    *Extended reals* are $RR union {-oo, oo}$ with the order relation $-oo < oo$ and $forall x in RR, -oo < x < oo$. $oo$ is an upper bound and $-oo$ is a lower bound for every $x in RR$, so $sup(RR) = oo$, $inf(RR) = -oo$, $sup(nothing) = -oo$, $inf(nothing) = oo$.
    - Addition: $forall a in RR, a + oo = oo and a + (-oo) = -oo$. $oo + oo = oo - (-oo) = oo$. $oo - oo$ is undefined.
    - Multiplication: $forall a > 0, a dot.op oo = oo$, $forall a < 0, a dot.op oo = -oo$. Also $oo dot.op oo = oo$.
    - $limsup$ and $liminf$ are defined as $ limsup x_n := inf{sup{x_k: k >= n}: n in NN}, quad liminf x_n := sup{inf{x_k: k >= n}: n in NN} $
]
#definition[
    Extended real number $l$ is *limit* of $(x_n)$ if either
    - $forall epsilon > 0, exists N in NN: forall n >= N, |x_n - l| < epsilon$. Then $(x_n)$ *converges to $l$*. or
    - $forall Delta > 0, exists N in NN: forall n >= N, x_n > Delta$ (limit is $oo$) or
    - $forall Delta > 0, exists N in NN: forall n >= N, x_n < -Delta$ (limit is $-oo$).
    $(x_n)$ *converges in the extended reals* if it has a limit in the extended reals.
]

= Further analysis of subsets of $RR$

== Countability and uncountability

#definition[
    $A$ is *countable* if $A = nothing$, $A$ is finite or there is a bijection $phi: NN -> A$ (in which case $A$ is *countably infinite*). Otherwise $A$ is *uncountable*. *Enumeration* is bijection to $A$ from $[n]$ or $NN$.
]
#proposition[
    If there is surjection from countable set to $A$, or injection from $A$ to countable set, then $A$ is countable.
]
#proposition[
    Any subset of $NN$ is countable.
]
#proposition[
    $QQ$ is countable.
]
#proposition[
    If $(a_n)$ is a nonnegative sequence and $phi: NN -> NN$ is a bijection then $ sum_(n = 1)^infinity a_n = sum_(n = 1)^infinity a_(phi(n)) $
]
#proposition[
    If $\(a_(n, k)\)$ is a nonnegative sequence and $phi: NN -> NN times NN$ is a bijection then $ sum_(n = 1)^infinity sum_(k = 1)^infinity a_(n, k) = sum_(n = 1)^infinity a_(phi(n)) $
]
#definition[
    $f: X -> Y$ is *monotone* if $x >= y => f(x) >= f(y)$ or $x <= y => f(x) >= f(y)$.
]
#proposition[
    Let $f$ be monotone on $(a, b)$. Then it is discontinuous on a countable set.
]
#lemma[
    Set of sequences in ${0, 1}$, $\{(x_n)_(n in NN): forall n in NN, x_n in {0, 1}\}$ is uncountable.
]
#theorem[
    $RR$ is uncountable.
]

== The structure theorem for open sets

#definition[
    Collection ${A_i: i in I}$ of sets is *(pairwise) disjoint* if $n != m ==> A_n sect A_m = nothing$.
]
#theorem("Structure theorem for open sets")[
    Let $U subset.eq RR$ open. Then exists countable collection of disjoint open intervals ${I_n: n in NN}$ such that $U = union_(n in NN) I_n$.
]

== Accumulation points and perfect sets

#definition[
    $x in RR$ is *accumulation point* of $E subset.eq RR$ if $x$ is point of closure of $E - {x}$. Equivalently, $x$ is a point of closure if $ forall epsilon > 0, exists y in E: y != x and |x - y| < epsilon $ Equivalently, there exists a sequence of distinct $y_n in E$ with $y_n -> x$ as $n -> oo$.
]
#proposition[
    Set of accumulation points of $QQ$ is $RR$.
]
#proposition[
    Set of accumulation points $E'$ of $E$ is closed.
]
#definition[
    $E subset.eq RR$ is *isolated* if $ forall x in E, exists epsilon > 0: (x - epsilon, x + epsilon) sect E = {x} $
]
#proposition[
    $E$ is isolated iff it has no accumulation points.
]
#definition[
    Bounded set $E$ is *perfect* if it equals its set of accumulation points.
]
#theorem[
    Every non-empty perfect set is uncountable.
]

== The middle-third Cantor set

#proposition[
    Let ${F_n: n in NN}$ be collection of non-empty nested closed sets (so $F_(n + 1) subset.eq F_n$), one of which is bounded. Then $ sect.big_(n in NN) F_n != emptyset $
]
#definition[
    The *middle third Cantor set* is defined by:
    - Define $C_0 := [0, 1]$
    - Given $C_n = union_(i = 1)^(2^n) [a_i, b_i]$, $a_1 < b_1 < a_2 < dots.h.c < a_(2^n) < b_(2^n)$, with $|b_i - a_i| = 3^(-n)$, define $ C_(n + 1) := union_(i = 1)^(2^n) [a_i, a_i + 3^(-(n + 1))] union [b_i - 3^(-(n + 1)), b_i] $ which is a union of $2^(n + 1)$ disjoint intervals, with all differences in endpoints equalling $3^(-(n + 1))$.
    - The *middle third Cantor set* is $ C := sect.big_(n in NN_0) C_n $ Observe that if $a$ is an endpoint of an interval in $C_n$, it is contained in $C$.
]
#proposition[
    The middle third Cantor set is closed, non-empty and equal to its set of accumulation points. Hence it is perfect and so uncountable.
]
#definition[
    Let $k in NN - {1}$, $x in lr([0, 1))$. $0.a_1 a_2 ...$, $a_i in {0, ..., k - 1}$, is a *$k$-ary expansion* of $x$ if $ x = sum_(i in NN) a_i / k^i $
]
#remark[
    The $k$-ary expansion may not be unique, but there is a countable set $E subset.eq lr([0, 1))$ such that every $x in lr([0, 1)) - E$ has a unique $k$-ary expansion.
]
#remark[
    For every $x in C$, the ternary ($k = 3$) expansion of $x$ is unique and $ x = sum_(i in NN) a_i / 3^i, quad a_i in {0, 2} $ Moreover, every choice of sequence $(a_i)$, $a_i in {0, 2}$, gives $x = sum_(i in NN) a_i / 3^i in C$.
]
#definition[
    *Cantor-Lebesgue function*, $g: [0, 1] -> [0, 1]$, is defined by $ g(x) := cases(sum_(i in NN) (a_i\/2) / 2^i & "if" x = sum_(i in NN) a_i / 3^i \, a_i in {0, 2}, sup{g(y): y in C, y <= x} & "if" x in.not C) $ $g$ is a surjection, monotone and continuous.
]

== $G_delta, F_sigma$

#definition[
    $E subset.eq RR$ is *$G_delta$* if $E = sect_(n in NN) U_n$ with $U_n$ open.
]
#definition[
    $E subset.eq RR$ is *$F_sigma$* if $E = union_(n in NN) F_n$ with $F_n$ closed.
]
#lemma[
    Set of points where $f: RR -> RR$ is continuous is $G_delta$.
]

= Construction of Lebesgue measure

== Lebesgue outer measure

#definition[
    Let $I$ non-empty interval with endpoints $a = inf(I) in {-oo} union RR$ and $b = sup(I) in RR union {oo}$. The *length* of $I$ is $ ell(I) := b - a $ and set $ell(nothing) = 0$.
]
#definition[
    Let $A subset.eq RR$. *Lebesgue outer measure* of $A$ is infimum of all sums of lengths of intervals covering $A$: $ mu^*(A) := inf{sum_(k in NN) ell(I_k): A subset.eq union.big_(k in NN) I_k, I_k "intervals"} $ It satisfies *monotonicity*: $A subset.eq B ==> mu^*(A) <= mu^*(B)$.
]
#proposition[
    Outer measure is *countably subadditive*: $ mu^*(union.big_(k in NN) E_k) <= sum_(k in NN) mu^*(E_k) $ This implies *finite subadditivity*: $ mu^*(union.big_(k = 1)^n E_k) <= sum_(k = 1)^n mu^*(E_k) $
]
#lemma[
    We have $ mu^*(A) = inf{sum_(k in NN) ell(I_k): A subset union.big_(k in NN) I_k, I_k != nothing "open intervals"} $
]
#proposition[
    Outer measure of interval is its length: $mu^*(I) = ell(I)$.
]

== Measurable sets

#notation[
    $E^c = RR - E$.
]
#proposition[
    Let $E = (a, oo)$. Then $ forall A subset.eq RR, quad mu^*(A) = mu^*(A sect E) + mu^*(A sect E^c) $
]
#definition[
    $E subset.eq RR$ is *Lebesgue measurable* if $ forall A subset.eq RR, quad mu^*(A) = mu^*(A sect E) + mu^*(A sect E^c) $ Collection of such sets is $cal(F)_(mu^*)$.
]
#lemma("Excision Property")[
    Let $E$ Lebesgue measurable set with finite measure and $E subset.eq B$, then $ mu^*(B - E) = mu^*(B) - mu^*(E) $
]
#proposition[
    If $E_1, ..., E_n$ Lebesgue measurable then $union_(k = 1)^n E_k$ is Lebesgue measurable. If $E_1, ..., E_n$ disjoint then $ mu^*(A sect union.big_(k = 1)^n E_k) = sum_(k = 1)^n mu^*(A sect E_k) $ for any $A subset.eq RR$. In particular, for $A = RR$, $ mu^*(union.big_(k = 1)^n E_k) = sum_(k = 1)^n mu^*(E_k) $
]
#remark[
    Not every set is Lebesgue measurable.
]
#definition[
    Collection of subsets of $RR$ is an *algebra* if contains $nothing$ and closed under taking complements and finite unions: if $A, B in cal(A)$ then $RR - A, A union B in cal(A)$.
]
#remark[
    A union of a countable collection of Lebesgue measurable sets is also the union of a countable disjoint collection of Lebesgue measurable sets: if ${A_k}_(k in NN)$ is countable collection of Lebesgue measurable sets, then let $A_1 ' := A_1$ and for $k > 1$, define $ A_k ' := A_k - union_(i = 1)^(k - 1) A_i $ then ${A_k '}_(k in NN)$ is disjoint union of Lebesgue measurable sets and $union_(k in NN) A_k ' = union_(k in NN) A_k$.
]
#proposition[
    If $E$ is countable union of Lebesgue measurable sets, then $E$ is Lebesgue measurable. Also, if ${E_k}_(k in NN)$ is countable disjoint collection of Lebesgue measurable sets then $ mu (union.big_(k in NN) E_k) = sum_(k in NN) mu (E_k) $
]

== Abstract definition of a measure

#definition[
    Let $X subset.eq RR$. Collection of subsets of $cal(F)$ of $X$ is *$sigma$-algebra* if
    - $nothing in cal(F)$
    - $E in cal(F) ==> E^c in cal(F)$
    - If $forall k in NN, E_k in cal(F)$ then $union_(k in NN) E_k in cal(F)$.
]
#example[
    - Trivial examples are $cal(F) = {nothing, RR}$ and $cal(F) = cal(P)(RR)$.
    - Countable intersections of $sigma$-algebras are $sigma$-algebras.
]
#definition[
    Let $cal(F)$ $sigma$-algebra of $X$. $nu: cal(F) -> RR union {plus.minus oo}$ is *measure* satisfying
    - $nu(nothing) = 0$
    - $forall E in cal(F), nu(E) >= 0$
    - *Countable additivity*: if $E_1, E_2, ... in cal(F)$ are disjoint then $ nu(union.big_(k in NN) E_k) = sum_(k in NN) nu(E_k) $
    Elements of $cal(F)$ are *measurable* (as they are the only sets on which the measure $nu$ is defined).
]
#proposition[
    If $nu$ is measure then it satisfies:
    - *Monotonicity*: $A subset.eq B ==> nu(A) <= nu(B)$.
    - *Countable subadditivity*: $nu(union_(k in NN) E_k) <= sum_(k in NN) nu(E_k)$.
    - *Excision*: if $B$ has finite measure, then $A subset.eq B ==> nu(B - A) = nu(B) - nu(A)$.
]

== Lebesgue measure

#lemma[
    $F_(mu^*)$ is $sigma$-algebra and contains every interval.
]
#theorem("Carathéodory Extension")[
    Restriction of the $mu^*$ to $F_(mu^*)$ is a measure.
]
#theorem("Hahn extension theorem")[
    There exists unique measure $mu$ defined on $cal(F)_(mu^*)$ for which $mu(I) = ell(I)$ for any interval $I$.
]
#definition[
    The measure $mu$ of $mu^*$ restricted to $cal(F)_(mu^*)$ is the *Lebesgue measure*. It satisfies $mu(I) = ell(I)$ for any interval $I$ and is translation invariant.
]

== Sets of measure $0$

#proposition[
    Middle-third Cantor set is Lebesgue measurable and has Lebesgue measure $0$.
]
#proposition[
    Any countable set is Lebesgue measurable and has Lebesgue measure $0$.
]
#proposition[
    Any $E$ with $mu^*(E) = 0$ is Lebesgue measurable and has $mu(E) = 0$.
]
#lemma[
    Let $E$ Lebesgue measurable set with $mu(E) = 0$, then $forall E' subset.eq E$, $E'$ is Lebesgue measurable.
]

== Continuity of measure

#definition[
    Countable collection ${E_k}_(k in NN)$ is *ascending* if $forall k in NN, E_k subset.eq E_(k + 1)$ and *descending* if $forall k in NN, E_(k + 1) subset.eq E_k$.
]
#theorem[
    Every measure $m$ satisfies:
    - If ${A_k}_(k in NN)$ is ascending collection of measurable sets, then $ m(union.big_(k in NN) A_k) = lim_(k -> oo) m(A_k) $
    - If ${B_k}_(k in NN)$ is descending collection of measurable sets and $m(B_1) < oo$, then $ m(sect.big_(k in NN) B_k) = lim_(k -> oo) m(B_k) $
]

== An approximation result for Lebesgue measure

#definition[
    *Borel $sigma$-algebra* $cal(B)(RR)$ is smallest $sigma$-algebra containing all intervals: for any other $sigma$-algebra $cal(F)$ containing all intervals, $cal(B)(RR) subset.eq cal(F)$. $ cal(B)(RR) := sect.big {cal(F): cal(F) " " sigma "-algebra containing all intervals"} $ $E in cal(B)(RR)$ is *Borel* or *Borel measurable*.
]
#lemma[
    All open subsets of $RR$, closed subsets of $RR$, $G_delta$ sets and $F_sigma$ sets are Borel.
]
#proposition[
    The following are equivalent:
    - $E$ is Lebesgue measurable
    - $forall epsilon > 0, exists "open" G: E subset.eq G and mu^*(G - E) < epsilon$
    - $forall epsilon > 0, exists "closed" F: F subset.eq E and mu^*(E - F) < epsilon$
    - $exists G in G_delta: E subset.eq G and mu^*(G - E) = 0$
    - $exists F in F_sigma: F subset.eq E and mu^*(E - F) = 0$
]

= Measurable functions

== Definition of a measurable function

#proposition[
    Let $f: RR -> RR$. $f$ continuous iff $forall "open" U subset.eq RR, f^(-1)(U) subset.eq RR$ is open.
]
#lemma[
    Let $f: E -> RR union {plus.minus oo}$ with $E$ Lebesgue measurable. The following are equivalent:
    - $forall c in RR, {x in E: f(x) > c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) >= c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) < c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) <= c}$ is Lebesgue measurable.
    The same statement holds for Borel measurable sets.
]
#definition[
    $f: E -> RR union {plus.minus oo}$ is *(Lebesgue) measurable* if it satisfies any of the above properties and if $E$ is Lebesgue measurable. $f$ being *Borel measurable* is defined similarly.
]
#corollary[
    If $f$ is Lebesgue measurable then for every $B in cal(B)(RR)$, $f^(-1)(B)$ is measurable. In particular, if $f$ is Lebesgue measurable, preimage of any interval is measurable.
]
#definition[
    *Indicator function* on set $A$, $indicator(A): RR -> {0, 1}$, is $ indicator(A)(x) := cases(1 & "if" x in A, 0 & "if" x in.not A) $
]
#definition[
    $phi: RR -> RR$ is *simple (measurable) function* if $phi$ is measurable function that has finite codomain.
]

== Fundamental aspects of measurable functions

#definition[
    Let $E subset.eq F subset.eq RR$, let $f: F -> RR$. *Restriction* $f_E$ is function with domain $E$ and for which $forall x in E, f_E (x) = f(x)$.
]
#definition[
    Real-valued function which is increasing or decreasing is *monotone*.
]
#definition[
    Sequence $(f_n)$ on domain $E$ is increasing if $f_n <= f_(n + 1)$ on $E$ for all $n in NN$.
]
#example[
    Continuous functions are measurable.
]
#definition[
    For $f_1: E -> RR, ..., f_n: E -> RR$, define $ max{f_1, ..., f_n}(x) := max{f_1 (x), ..., f_n (x)} $ $min{f_1, ..., f_n}$ is defined similarly.
]
#proposition[
    For finite family ${f_k}_(k = 1)^n$ of measurable functions with common domain $E$, $max{f_1, ..., f_n}$ and $min{f_1, ..., f_n}$ are measurable.
]
#definition[
    For $f: E -> RR$, functions $|f|, f^+, f^-$ defined on $E$ are $ |f|(x) := max{f(x), -f(x)}, quad f^+ (x) := max{f(x), 0}, quad f^- (x) := max{-f(x), 0} $
]
#corollary[
    If $f$ measurable on $E$, so are $|f|$, $f^+$ and $f^-$.
]
#proposition[
    Let $f: E -> RR union {plus.minus oo}$. For measurable $D subset.eq E$, $f$ measurable on $E$ iff restrictions of $f$ to $D$ and $E - D$ are measurable.
]
#theorem[
    Let $f, g: E -> RR$ measurable.
    - *Linearity*: $forall alpha, beta in RR, alpha f + beta g$ is measurable.
    - *Products*: $f g$ is measurable.
]
#proposition[
    Let $f_n: E -> RR union {plus.minus oo}$ be sequence of measurable functions that converges pointwise to $f: E -> RR union {plus.minus oo}$. Then $f$ is measurable.
]
#lemma("Simple approximation lemma")[
    Let $f: E -> RR$ measurable and bounded, so $exists M >= 0: forall x in E, |f|(x) < M$. Then $forall epsilon > 0$, there exist simple measurable functions $phi_epsilon, psi_epsilon: E -> RR$ such that $ forall x in E, quad phi_epsilon (x) <= f(x) <= psi_epsilon (x) and 0 <= psi_epsilon (x) - phi_epsilon (x) < epsilon $
]
#theorem("Simple approximation theorem")[
    Let $f: E -> RR union {plus.minus oo}$, $E$ measurable. Then $f$ is measurable iff there exists sequence $(phi_n)$ of simple functions on $E$ which converge pointwise on $E$ to $f$ and satisfy $ forall n in NN, forall x in E, |phi_n|(x) <= |f|(x) $ If $f$ is nonnegative, $(phi_n)$ can be chosen to be increasing.
]
#definition[
    Let $f, g: E -> RR union {plus.minus oo}$. Then $f = g$ *almost everywhere* if ${x in E: f(x) != g(x)}$ has measure $0$.
]
#proposition[
    Let $f_1, f_2, f_3: E -> RR union {plus.minus oo}$ measurable. If $f_1 = f_2$ almost everywhere and $f_2 = f_3$ almost everywhere then $f_1 = f_3$ almost everywhere.
]
#remark[
    Lebesgue measurable functions can be modified arbitrarily on a set of measure $0$ without affecting measurability.
]
#proposition[
    Let $f_n: E -> RR union {plus.minus oo}$ sequence of measurable functions, $f: E -> RR union {plus.minus oo}$ measurable. Set of points where $(f_n)$ converges pointwise to $f$ is measurable.
]
#proposition[
    Let $f, g: E -> RR union {plus.minus oo}$ measurable and finite almost everywhere on $E$.
    - *Linearity*: $forall alpha, beta in RR$, there exists function equal to $alpha f + beta g$ almost everywhere on $E$ (any such function is measurable).
    - *Products*: there exists function equal to $f g$ almost everywhere on $E$ (any such function is measurable).
]
#definition[
    Sequence of functions $(f_n)$ with domain $E$ *converge in measure* to $f$ if $(f_n)$ and $f$ are finite almost everywhere and $ forall epsilon > 0, quad mu({x in E: |f_n (x) - f(x)| > epsilon}) -> 0 "as" n -> oo $
]

= The Lebesgue integral

== The integral of a simple measurable function

#definition[
    Let $phi$ be real-valued function taking finitely many values $alpha_1 < dots.h.c < alpha_n$, then *standard representation* of $phi$ is $ phi = sum_(i = 1)^n alpha_i bb(1)_(A_i), quad A_i = phi^(-1)({alpha_i}) $
]
#lemma[
    Let $phi = sum_(i = 1)^m beta_i indicator(B_i)$, $B_i$ disjoint measurable collection, $beta_i in RR$, then $phi$ is simple measurable. If $phi$ takes value $0$ outside a set of finite measure then $ sum_(i = 1)^n alpha_i mu(A_i) = sum_(i = 1)^m beta_i mu(B_i) $ where $A_i$ in standard representation.
]
#definition[
    Let $phi$ be simple nonnegative measurable function or simple measurable function taking value $0$ outside set of finite measure. *Integral* of $phi$ with respect to $mu$ is $ integral phi = sum_(i = 1)^n alpha_i mu(A_i) $ where $phi = sum_(i = 1)^n alpha_i bb(1)_(A_i)$ is standard representation. Here, use convention $0 dot.op oo = 0$. For measurable $E subset.eq RR$, define $ integral_E phi = integral indicator(E) phi $
]
#example[
    - Let $phi_2 = indicator([0, 2]) + indicator([1, 3]) = indicator(lr([0, 1) union lr((2, 3]))) + 2 indicator([1, 2])$ so $integral phi_2 = 4$.
    - Let $phi_3 = indicator(RR)$, then $integral phi_3 = 1 dot.op oo = oo$.
    - Let $phi_4 = bb(1)_((0, oo)) + (-1) indicator((-oo, 0))$. This can't be integrated.
    - Let $phi_5 = indicator((-1, 0)) + (-1) indicator((0, 1))$, then $integral phi_5 = 0$.
]
#lemma[
    Let $B_1, ..., B_m$ be measurable sets, $beta_1, ..., beta_m in RR - {0}$. Then $phi = sum_(i = 1)^m beta_i indicator(B_i)$ is simple measurable function. Also, $ mu(union.big_(i = 1)^m B_i) < oo ==> sum_(i = 1)^n alpha_i mu(A_i) = sum_(i = 1)^m beta_i mu(B_i) $ where $A_i$ in standard representation.
]
#proposition[
    Let $phi, psi$ be simple measurable functions:
    - If $phi, psi$ take value $0$ outside a set of finite measure, then $forall alpha, beta in RR$, $ integral (alpha phi + beta psi) = alpha integral phi + beta integral psi $
    - If $phi, psi$ nonnegative, then $forall alpha, beta >= 0$, $ integral (alpha phi + beta psi) = alpha integral phi + beta integral psi $
    - *Monotonicity*: $ 0 <= phi <= psi ==> 0 <= integral phi <= integral psi $
]
#corollary[
    Let $phi$ nonnegative simple function, then $ integral phi = sup{integral psi: 0 <= psi <= phi, thick psi "simple measurable"} $
]
#lemma[
    Let $phi$ simple measurable nonnegative function. $phi$ takes value $0$ outside a set of finite measure iff $integral phi < oo$. Also, $integral phi = oo$ iff there exist $alpha > 0$, measurable $A$ with $mu(A) = oo$ and $forall x in A, phi(x) >= alpha$.
]
#lemma[
    Let ${E_n}$ be ascending collection of measurable sets, $union_(n in NN) E_n = RR$. Let $phi$ be simple nonnegative measurable function. Then $ integral_(E_n) phi -> integral phi quad "as" n -> oo $
]

== The integral of a nonnegative function

#notation[
    Let $cal(M)^+$ denote collection of nonnegative measurable functions $f: RR -> RR_(>= 0) union {oo}$.
]
#definition[
    *Support* of measurable function $f$ with domain $E$ is $"supp"(f) := {x in E: f(x) != 0}$.
]
#definition[
    Let $f in cal(M)^+$. *Integral of $f$ with respect to $mu$* is $ integral f := sup{integral phi: 0 <= phi <= f, phi "simple measurable"} in RR union {oo} $ For measurable set $E$, define $ integral_E f := integral indicator(E) f $
]
#proposition("Monotonicity")[
    Let $f, g$ measurable, nonnegative. If $g <= f$ then $integral g <= integral f$. Let $E, F$ measurable. If $E subset.eq F$ then $integral_E f <= integral_F f$.
]
#theorem("Monotone convergence theorem")[
    Let $(f_n)$ be sequence in $cal(M)^+$. If $(f_n)$ is increasing on measurable set $E$ and converges pointwise to $f$ on $E$ then $ integral_E f_n -> integral_E f quad "as" n -> oo $
]
#corollary[
    Restriction of integral to nonnegative functions is linear: $forall f, g in cal(M)^+$, $forall alpha >= 0$, $ integral (f + g) & = integral f + integral g \ integral alpha f & = alpha integral f $
]
#lemma("Fatou's Lemma")[
    Let $(f_n)$ be sequence in $cal(M)^+$, then $ integral liminf_(n -> oo) f_n <= liminf_(n -> oo) integral f_n $
]
#lemma[
    Let $(f_n) subset cal(M)^+$, then $ integral sum_(n in NN) f_n = sum_(n in NN) integral f_n $
]
#proposition("Chebyshev's inequality")[
    Let $f$ be nonnegative measurable function on $E$. Then $ forall lambda > 0, quad mu({x in E: f(x) >= lambda}) <= 1/lambda integral_E f $
]
#proposition[
    Let $f$ be nonnegative measurable function on $E$. Then $ integral_E f = 0 <==> f = 0 "almost everywhere on" E $
]

== Integration of measurable functions

#notation[
    Let $cal(M)$ denote set of measurable functions.
]
#definition[
    $f in cal(M)^+$ is *integrable* if $integral f < oo$. By Chebyshev's inequality, if $f$ is integrable, then $f$ is finite almost everywhere.
]
#definition[
    Let $f: RR -> RR union {plus.minus oo}$ measurable function. $f$ is *integrable* if $integral f^+$ and $integral f^-$ are finite. In this case, for any measurable set $E$, define $ integral_E f := integral_E f^+ - integral_E f^- $ Note that if $f$ integrable then $f^+ - f^-$ is well-defined.
]
#proposition[
    If $f = f_1 - f_2$, $f_1, f_2 in cal(M)^+$, $f_1, f_2$ integrable, then $ integral f^+ - integral f^- = integral f_1 - integral f_2 $
]
#definition[
    $f in cal(M)$ is *integrable over $E$* ($E$ is measurable) if $integral_E f^+$ and $integral_E f^-$ are finite (i.e. $f dot.op indicator(E)$ is integrable).
]
#theorem[
    $f in cal(M)$ is integrable iff $|f|$ is integrable. If $f$ integrable, then $ abs(integral f) <= integral abs(f) $
]
#corollary[
    Let $f, g in cal(M)$, $|f| <= |g|$. If $g$ integrable then $|f|$ is integrable, and $integral |f| <= integral |g|$.
]
#example[
    $sin$ is not integrable over $RR$, but is integrable over $[0, 2pi]$, since $|f_([0, 2pi])| <= indicator([0, 2pi])$.
]
#theorem("Linearity of Integration")[
    Let $f, g in cal(M)$ integrable. Then $f + g$ is integrable and $forall alpha in RR$, $alpha f$ is integrable. The integral is linear: $ integral (f + g) & = integral f + integral g \ integral alpha f & = alpha integral f $
]
#theorem("Dominated Convergence Theorem")[
    Let $(f_n)$ be sequence of integrable functions. If there exists an integrable $g$ with $forall n in NN, |f_n| <= g$, and $f_n -> f$ pointwise almost everywhere then $f$ is integrable and $ integral f = lim_(n -> oo) integral f_n $
]

== Integrability: Riemann vs Lebesgue

#proposition[
    Let $f$ bounded function on bounded measurable domain $E$. Then $f$ is measurable and $integral_E |f| < oo$ iff $ sup{integral_E phi: phi <= f, phi "simple measurable"} = inf{integral_E psi: f <= psi: psi "simple measurable"} $ (If $f$ satisfies either condition then $integral_E f$ is equal to the two above expressions).
]
#definition[
    Bounded function $f$ is *Lebesgue integrable* if it satisfies either of the equivalences in the above proposition.
]
#definition[
    Let $P = {x_0, ..., x_n}$ partition of $[a, b]$, $f: [a, b] -> RR$ bounded. *Lower and upper Darboux sums* for $f$ with respect to $P$ are $ L(f, P) := sum_(i = 1)^n m_i (x_i - x_(i - 1)), quad U(f, P) := sum_(i = 1)^n M_i (x_i - x_(i - 1)) $ where $ m_i := inf{f(x): x in (x_(i - 1), x_i)}, quad M_i := sup{f(x): x in (x_(i - 1), x_i)} $ If $P subset.eq Q$ ($Q$ is a *refinement of $P$*), then $ L(f, P) <= L(f, Q) <= U(f, Q) <= U(f, P) $
]
#definition[
    *Lower and upper Riemann integrals* of $f$ over $[a, b]$ are $ underline(cal(I))_a^b (f) & := sup{L(f, P): P "partition of" [a, b]} \ overline(cal(I))_a^b (f) & := inf{U(f, P): P "partition of" [a, b]} $
]
#definition[
    Let $f: [a, b] -> RR$ bounded, then $f$ is *Riemann integrable* ($f in cal(R)$), if $ underline(cal(I))_a^b (f) = overline(cal(I))_a^b (f) $ and common value $cal(I)_a^b (f) = integral_a^b f(x) dif x$ is *Riemann integral* of $f$.
]
#remark[
    Let $g: [a, b] -> RR$ step function with discontinuities at $P = {x_0, ..., x_n}$, so $g = sum_(i = 1)^n alpha_i indicator((x_(i - 1), x_i))$ almost everywhere. So $g$ is simple measurable and $ L(g, P) = sum_(i = 1)^n alpha_i (x_i - x_(i - 1)) = U(g, P) = integral g = cal(I)_a^b (g) $ Hence for any bounded $f: [a, b] -> RR$, $ underline(cal(I))_a^b (f) & = sup{integral phi: phi <= f, phi "step function"}, \ overline(cal(I))_a^b (f) & = inf{integral psi: f <= psi, psi "step function"} $
]
#theorem[
    Let $f: [a, b] -> RR$ bounded, $a, b != plus.minus oo$. If $f$ Riemann integrable over $[a, b]$ then $f$ Lebesgue integrable over $[a, b]$ and the two integrals are equal.
]
#theorem[
    Let $f: [a, b] -> RR$ bounded, $a, b != plus.minus oo$. Then $f$ is Riemann integrable on $[a, b]$ iff $f$ is continuous on $[a, b]$ except on a set of measure zero.
]
#lemma[
    Let $(phi_n)$, $(psi_n)$ be sequences of functions, all integrable over $E$, $(phi_n)$ increasing on $E$, $(psi_n)$ decreasing on $E$. Let $f: E -> RR$ with $ forall n in NN, phi_n <= f <= psi_n "on" E, quad lim_(n -> oo) integral_E (psi_n - phi_n) = 0 $ Then $phi_n, psi_n -> f$ pointwise almost everywhere on $E$, $f$ is integrable over $E$ and $ lim_(n -> oo) integral_E phi_n = lim_(n -> oo) integral_E psi_n = integral_E f $
]
#definition[
    For partition $P = {x_0, ..., x_n}$, *gap* of $P$ is $ "gap"(P) := max{|x_i - x_(i - 1)|: i in {1, ..., n}} $
]
#lemma[
    Let $f: [a, b] -> RR$, $E subset.eq [a, b]$ be set where $f$ is continuous. Let $(P_n)$ be sequence of partitions of $[a, b]$ with $P_(n + 1) subset.eq P_n$ and $"gap"(P_n) -> 0$ as $n -> oo$. Let $phi_n, psi_n: [a, b] -> RR$ step functions with $ phi_n (x) := inf{f(x): x in (x_(i - 1), x_i)}, quad psi_n (x) := sup{f(x): x in (x_(i - 1), x_i)} $ for $P_n = {x_0, ..., x_n}$. Then $forall x in E - union_(n in NN) P_n$, $ phi_n (x), psi_n (x) -> f(x) quad "as" n -> oo $
]
#definition[
    Let $f: lr((a, b]) -> RR$, $-oo <= a < b < oo$, $f$ bounded and Riemann integrable on all closed bounded sub-intervals of $lr((a, b])$. If $ lim_(t -> a, t > a) cal(I)_t^b (f) $ exists then this is defined as the *improper Riemann integral* $cal(I)_a^b (f)$. Similar definitions exist for $f: (a, b) -> RR$ and $f: lr([a, b)) -> RR$.
]
#note[
    Improper Riemann integral may exist without function being Lebesgue integral.
]
#proposition[
    If $f$ is integrable, the improper Riemann integral is equal to the Lebesgue integral whenever the former exists.
]
#definition[
    Let $alpha: [a, b] -> RR$ monotonically increasing (and so bounded). For partition $P = {x_0, ..., x_n}$ of $[a, b]$ and bounded $f: [a, b] -> RR$, define $ L(f, P, alpha) := sum_(i = 1)^n m_i (alpha(x_i) - alpha(x_(i - 1))), quad U(f, P, alpha) := sum_(i = 1)^n M_i (alpha(x_i) - alpha(x_(i - 1))) $ where $m_i := inf{f(x): x in (x_(i - 1), x_i)}$, $M_i := sup{f(x): x in (x_(i - 1), x_i)}$. Then $f$ is *integrable with respect to $alpha$*, $f in cal(R)(alpha)$, if $ inf{U(f, P, alpha): P "partition of" [a, b]} = sup{L(f, P, alpha): P "partition of" [a, b]} $ and the common value $integral_a^b f dif alpha$ is the *Riemann-Stieltjes integral* of $f$ with respect to $alpha$.
]
#proposition[
    Let $f: (a, b) -> RR$, then set of points where $f$ is differentiable is measurable.
]
#remark[
    If $alpha: [0, 1] -> [a, b]$ bijection, then $ integral_0^1 f compose alpha dif alpha = integral_a^b f(x) dif x $
]
#proposition[
    Let $alpha$ be monotonically increasing and differentiable with $alpha' in cal(R)$. Then $g in cal(R)(alpha)$ iff $g alpha' in cal(R)$, and in that case, $ integral_a^b g dif alpha = integral_a^b g(x) alpha'(x) dif x $
]
#remark[
    When $g = 1$, this says $integral_a^b 1 dif alpha = alpha(b) - alpha(a) = integral alpha'(x) dif x$, similar to the fundamental theorem of calculus.
]

= Lebesgue spaces

== Normed linear spaces

#definition[
    Let $X$ be *complex linear space* (vector space over $CC$). $norm(dot.op): X -> RR_(>=0)$ is *norm on $X$* if
    - $forall x in X, norm(x) = 0 <==> x = 0$.
    - $forall x in X, forall lambda in CC, norm(lambda x) = |lambda| norm(x)$.
    - $forall x, y in X, norm(x + y) <= norm(x) + norm(y)$.
    $X$ equipped with norm $norm(dot.op)$, $(X, norm(dot.op))$, is called *complex normed linear space*.
]
#example[
    - $norm(x) = sqrt(x overline(x))$ is norm on $CC$.
    - Let $C[a, b]$ denote linear space of continuous real-valued functions on $[a, b]$. Then $ norm(f)_max := max{|f(x)|: x in [a, b]} $ is norm on $C[a, b]$.
]
#proposition[
    Norm induces metric on $X$: $d(x, y) = norm(x - y)$.
]
#definition[
    Let $(X, norm(dot.op))$ be normed linear space.
    - Sequence $(f_n)$ in $X$ is *Cauchy sequence* in $X$ if $ forall epsilon > 0, exists N in NN: forall n, m >= N, quad norm(f_n - f_m) < epsilon $
    - Sequence $(f_n)$ in $X$ *converges in $X$*, $norm(f_n - f) -> 0$ as $n -> oo$, if $ exists f in X: forall epsilon > 0, exists N in NN: forall n >= N, quad norm(f_n - f) < epsilon $
    - $(X, norm(dot.op))$ is *complete* if every Cauchy sequence converges in $X$.
    - *Banach space* is complete normed linear space.
]
#proposition[
    Let $(X, norm(dot.op))$ be normed linear space.
    - If $(x_n)$ converges in $X$, $(x_n)$ is Cauchy sequence in $X$.
    - Let $(x_n)$ be Cauchy sequence in $X$. If $(x_n)$ has convergent subsequence in $X$ then $(x_n)$ converges in $X$.
]

== Lebesgue spaces $L^p$, $p in lr([1, oo))$

#definition[
    Let $p in lr([1, oo))$, $E subset.eq RR$.
    - Linear space $L^p (E)$ is defined as $ L^p (E) := {f: E -> CC: f "is measurable and" integral_E |f|^p < oo} \/ tilde.equiv $ where $f tilde.equiv g$ iff $f = g$ almost everywhere: $ f tilde.equiv g <==> exists F subset.eq E: mu(F) = 0 and forall x in E - F, f(x) = g(x) $
    - Define $norm(dot.op)_(L^p): L^p (E) -> RR$ as $ norm(f)_(L^p) := (integral_E |f|^p)^(1\/p) $
]
#remark[
    - We often consider space $L^p (E)$ of real-valued measurable functions $f: E -> RR$ such that $integral_E |f|^p < oo$.
    - For $f: E -> CC$, $f = f_1 + i f_2$, $f$ is measurable iff $f_1: E -> RR$ and $f_2: E -> RR$ are measurable. Also, $ integral_E |f|^p < oo <==> (integral_E |f_1|^p < oo and integral_E |f_2|^p < oo) $
]
#example[
    Let $E = RR$, $f(x) = indicator(RR - QQ)(x) + i indicator(QQ)(x)$ and $g(x) = 1$. Then $mu(QQ) = 0$ so $f tilde.equiv g$.
]
#proposition[
    Let $(f_n), (g_n)$ sequences of measurable functions, $forall n in NN, f_n tilde.equiv g_n$, $lim_(n -> oo) f_n = f$ and $lim_(n -> oo) g_n = g$. Then $f tilde.equiv g$.
]
#definition[
    $p, q in RR$ are *conjugate exponents* if $p > 1$ and $1/p + 1/q = 1$.
]
#lemma("Young's inequality")[
    Let $p, q$ conjugate exponents, then $ forall A, B in RR_(>=0), quad A B <= A^p / p + B^q / q $ with equality iff $A^p = B^q$.
]
#lemma("Hölder's inequality")[
    Let $p, q$ conjugate exponents. If $f in L^p (E)$, $g in L^q (E)$, then $ integral_E |f g| <= norm(f)_(L^p) norm(g)_(L^q) $
]
#corollary([Cauchy-Schwarz inequality for $L^2 (E)$])[
    If $f, g in L^2 (E)$, then $ abs(integral_E f overline(g)) <= integral_E |f g| <= norm(f)_(L^2) norm(g)_(L^2) $
]
#lemma("Minkowski's inequality")[
    Let $p in lr([1, oo))$. If $f, g in L^p (E)$ then $f + g in L^p (E)$ and $ norm(f + g)_(L^p) <= norm(f)_(L^p) + norm(g)_(L^p) $
]
#theorem[
    For $p in lr([1, oo))$, $\(L^p (E), norm(dot.op)_(L^p)\)$ is normed linear space.
]
#proposition[
    Let $1 <= p < q < oo$. If $mu(E) < oo$ then $L^q (E) subset.eq L^p (E)$ and $ norm(f)_(L^p) <= mu(E)^(1/p - 1/q) norm(f)_(L^q) $
]
#remark[
    - Convergence in $L^p$ is also called convergence in the mean of order $p$.
    - This notion of convergence is different to pointwise convergence, uniform convergence and convergence in measure.
]
#theorem("Riesz-Fischer")[
    For $p in lr([1, oo))$, $\(L^p (E), norm(dot.op)_(L^p)\)$ is complete.
]<riesz-fischer>

== Lebesgue space $L^oo$

#definition[
    - Let $f: E -> CC$ measurable. $f$ is *essentially bounded* if $ exists M >= 0: |f(x)| <= M quad "almost everywhere on" E $
    - $L^oo (E)$ is collection of equivalence classes of essentially bounded functions where $f tilde.equiv g$ iff $f = g$ almost everywhere.
    - For $f in L^oo (E)$, define $ norm(f)_(L^oo) := "ess" sup |f| := inf{M in RR: mu({x in E: |f(x)| > M}) = 0} $
]
#proposition[
    - $0 <= |f(x)| <= norm(f)_(L^oo)$ almost everywhere.
    - $norm(f)_(L^oo)$ is norm on $L^oo (E)$.
    - If $f in L^1 (E)$, $g in L^oo (E)$, then $ integral_E |f g| <= norm(f)_(L^1) norm(g)_(L^oo) $
]
#proposition[
    Let $(f_n)$ sequence of functions in $L^oo (E)$. Then $(f_n)$ converges to $f in L^oo (E)$ iff there exists $G subset.eq E$ with $mu(G) = 0$ and $(f_n)$ converges to $f$ uniformly on $E - G$.
]
#theorem[
    $\(L^oo (E), norm(dot.op)_(L^oo)\)$ is complete.
]
#remark[
    If $mu(E) < oo$, then $L^oo (E) subset L^p (E)$ for $p in lr([1, oo))$ and $ norm(f)_(L^p) <= mu(E)^(1\/p) norm(f)_(L^oo) $ since $ norm(f)_(L^p)^p = integral_E |f|^p <= integral_E norm(f)_(L^oo)^p dot.op indicator(E) = norm(f)_(L^oo)^p mu(E) $
]

== Approximation and separability

#definition[
    Let $(X, norm(dot.op))$ be normed linear space. Let $F subset.eq G subset.eq X$. $F$ is *dense in $G$* if $ forall g in G, forall epsilon > 0, exists f in F: quad norm(f - g) < epsilon $
]
#proposition[
    - $F$ is dense in $G$ iff for every $g in G$, there exists sequence $(f_n)$ in $F$ such that $lim_(n -> oo) f_n = g$ in $X$.
    - For $F subset.eq G subset.eq H subset.eq X$, if $F$ dense in $G$ and $G$ dense in $H$, then $F$ dense in $H$.
]
#proposition[
    Let $p in [1, oo]$. Then subspace of simple functions in $\(L^p (E), norm(dot.op)_(L^p)\)$ is dense in $\(L^p (E), norm(dot.op)_(L^p)\)$.
]
#definition[
    $psi: RR -> RR$ is *step function* if it can be written as $ psi = sum_(k = 1)^N tilde(a)_k indicator((a_k, b_k)) $ where the intervals $(a_k, b_k)$ are disjoint.
]
#proposition[
    Let $[a, b]$ be bounded, $p in [1, oo)$. Then subspace of step functions on $[a, b]$ is dense in $\(L^p ([a, b]), norm(dot.op)_(L^p)\)$.
]
#definition[
    Normed linear space $(X, norm(dot.op))$ is *separable* if there exists countable, dense subset $X' subset.eq X$.
]
#example[
    $RR$ is separable, since $QQ$ is countable and dense in $RR$.
]
#theorem[
    Let $E subset.eq RR$ measurable, $p in [1, oo)$. Then $\(L^p (E), norm(dot.op)_(L^p)\)$ is separable. In particular, step functions are dense in $L^p (E)$ for $p in [1, oo)$.
]
#proposition[
    Let $epsilon > 0$, $f in L^p (E)$, $p in [1, oo)$. There exists continuous $g in L^p (E)$ such that $norm(f - g)_(L^p) < epsilon$.
]
#remark[
    Linear space of continuous functions that vanish outside bounded set is dense in $\(L^p (E), norm(dot.op)_(L^p)\)$ for $p in [1, oo)$.
]
#remark[
    Differentiable functions are also dense in $\(L^p (E), norm(dot.op)_(L^p)\)$ for $p in [1, oo)$.
]
#remark[
    Step functions and continuous functions are not dense in $\(L^oo (E), norm(dot.op)_(L^oo)\)$.
]
#example[
    In general, $\(L^oo (E), norm(dot.op)_(L^oo)\)$ is not separable. Let $[a, b]$ be bounded, $a != b$. Assume there is countable ${f_n: n in NN}$ which is dense in $\(L^oo ([a, b]), norm(dot.op)_(L^oo)\)$. Then for every $x in [a, b]$, can choose $g(x) in NN$ such that $ norm(indicator([a, x]) - f_(g(x)))_(L^oo) < 1/2 $ Also, for $x_1 <= x_2$, $ norm(indicator([a, x_1]) - indicator([a, x_2]))_(L^oo) = cases(1 & quad "if" a <= x_1 < x_2 <= b, 0 & quad "if" x_1 = x_2) $ and $ norm(indicator([a, x_1]) - indicator([a, x_2]))_(L^oo) & <= norm(indicator([a, x_1]) - f_(g(x_1)))_(L^oo) + norm(f_(g(x_1)) - f_(g(x_2)))_(L^oo) + norm(f_(g(x_2)) - indicator([a, x_2]))_(L^oo) \ & < 1 + norm(f_(g(x_1)) - f_(g(x_2)))_(L^oo) $ If $g(x_1) = g(x_2)$ then $norm(indicator([a, x_1]) - indicator([a, x_2]))_(L^oo) = 0$ so $g: [a, b] -> NN$ is injective. But $NN$ is countable and $[a, b]$ is not countable: contradiction.
]

== Riesz representation theorem for $L^p (E)$, $p in [1, oo)$

#definition[
    Let $X$ be linear space. $T: X -> RR$ is *linear functional* if $ forall f, g in X, forall a, b in RR, quad T(a f + b g) = a T(f) + b T(g) $ Any linear combination of linear functionals is linear, so set of linear functionals on linear space is also linear space.
]
#definition[
    Let $(X, norm(dot.op))$ be normed linear space. $T: X -> RR$ is *bounded functional* if $ exists M >= 0: forall f in X, quad |T(f)| <= M norm(f) $ *Norm* of $T$, $norm(T)_*$, is the smallest such $M$.
]
#remark[
    For bounded linear functional $T$ on normed linear space $(X, norm(dot.op))$, $ |T(f) - T(g)| <= norm(T)_* norm(f - g) $ This gives the following continuity property: if $f_n -> f in X$, then $T(f_n) -> T(f)$.
]
#example[
    Let $E subset.eq RR$ measurable, $p in [1, oo)$, $q$ conjugate to $p$. Let $h in L^q (E)$. Define $T: L^p (E) -> RR$ by $ T(f) = integral_E h dot.op f $ By Holder's inequality, $ |T(f)| = abs(integral_E h f) <= integral_E abs(h f) <= norm(h)_(L^q) norm(f)_(L^p) $ So $T$ is bounded linear functional.
]
#remark[
    We can write $norm(dot.op)_*$ as $ norm(T)_* := inf{M in RR: forall f in X, |T(f)| <= M norm(f)} = sup{|T(f)|: f in X, norm(f) <= 1} $
]
#definition[
    *Dual space* of $X$, $X^*$, is set of bounded linear functionals on $X$ with norm $norm(dot.op)_*$.
]
#proposition[
    Let $(X, norm(dot.op))$ be normed linear space, then dual space of $X$ is linear space with norm $norm(dot.op)_*$.
]
#remark[
    Bounded linear functional is special case of *bounded linear transformation* between normed spaces. $T: X -> Y$ is bounded linear transformation if $T(a f + b g) = a T(f) + b T(g)$ and $exists M >= 0: norm(T(f))_Y <= M norm(f)_X$.
]
#proposition[
    Let $E subset.eq RR$ measurable, $p in [1, oo)$, $q$ conjugate to $p$, $h in L^q (E)$. Define $T: L^p (E) -> RR$ by $ T(f) = integral_E h f $ Then $norm(T)_* = norm(h)_(L^q)$.
]
#theorem([Riesz representation theorem for $L^p$])[
    Let $p in [1, oo)$, $q$ conjugate to $p$, $E subset.eq RR$ measurable. For $h in L^q (E)$, define bounded linear functional $R_h: L^p (E) -> RR$ by $ R_h (f) = integral_E h f $ Then for every bounded linear functional $T: L_p (E) -> RR$, there is unique $h in L^q (E)$ such that $ R_h = T quad and quad norm(T)_* = norm(h)_(L^q) $
]
#theorem[
    Let $[a, b]$ be non-degenerate, bounded interval, $p in [1, oo)$, $q$ conjugate to $p$. If $T$ is bounded linear functional on $L^p ([a, b])$ then there exists $h in L^q ([a, b])$ such that $ T(f) = integral_a^b h f $ 
]

= Hilbert spaces

== Inner product spaces

#definition[
    Let $H$ be complex linear space. *Inner product* on $H$ is function $ip(dot.op, dot.op): H times H -> CC$ such that $forall a, b in CC, forall x, y, z in H$,
    - *Linear in first variable*: $ip(a x + b y, z) = a ip(x, z) + b ip(y, z)$.
    - *Conjugate symmetric*: $ip(x, y) = overline(ip(y, x))$.
    - *Positive*: $x != 0 ==> ip(x, x) in (0, oo)$
    - $ip(x, x) = 0 <==> x = 0$.
    These imply that $ip(0, x) = 0$ and inner product is conjugate linear in second variable: $ip(z, a x + b y) = overline(a) ip(z, x) + overline(b) ip(z, y)$.
]
#example[
    - $RR^n$ has inner product $ip(x, y) = sum_(i = 1)^n x_i y_i$.
    - $CC^n$ has inner product $ip(x, y) = sum_(i = 1)^n x_i overline(y_i)$.
    - Inner product induces metric on $H$: $ d(x, y) = ip(x - y, x - y)^(1\/2) $
]
#definition[
    Complex linear space $H$ with inner product $ip(dot.op, dot.op)$ is called *pre-Hilbert space* or *inner product space*.
]
#definition[
    Let $H$ inner product space. For $x in H$, define the norm $ norm(x) = sqrt(ip(x, x)) $
]
#proposition[
    $norm(x plus.minus y)^2 = norm(x)^2 plus.minus 2 "Re"(ip(x, y)) + norm(y)^2$.
]
#theorem("Cauchy-Schwarz inequality")[
    Let $(H, ip(dot.op, dot.op))$ be pre-Hilbert space. Then $ forall x, y in H, quad |ip(x, y)| <= norm(x) norm(y) $ with equality iff $x$ and $y$ linearly dependent.
]
#theorem("Parallelogram Identity")[
    A normed linear space $X$ is an inner product space with norm derived from the inner product (i.e. $norm(dot.op) = sqrt(ip(dot.op, dot.op))$) iff $ forall x, y in X, quad norm(x + y)^2 + norm(x - y)^2 = 2 norm(x)^2 + 2 norm(y)^2 $
]
#definition[
    Let $(X, ip(dot.op, dot.op)_X)$, $(Y, ip(dot.op, dot.op)_Y)$ be inner product spaces.
    - An inner product on $X times Y$ is $ ip((x_1, y_1), (x_2, y_2))_(X times Y) = ip(x_1, x_2)_X + ip(y_1, y_2)_Y $
    - The associated norm on $X times Y$ is $ norm((x, y))_(X times Y) = sqrt(ip((x, y), (x, y))_(X times Y)) = sqrt(norm(x)_X^2 + norm(y)_Y^2) $
]
#theorem[
    Let $X$ inner product space, $x_n -> x$, $y_n -> y$ in $X$. Then $ip(x_n, y_n)_X -> ip(x, y)_X$.
]
#proof[
    Use $|ip(x_n, y_n) - ip(x, y)| = |ip(x_n - x, y_n) + ip(x, y_n) - ip(x, y_n) + ip(x, y_n - y)|$ and Cauchy-Schwarz, reverse triangle inequality to show $norm(y_n) -> norm(y)$.
]
#proposition[
    The norm and inner product are continuous.
]

== Hilbert spaces

#definition[
    Hilbert space is inner product space which is complete with respect to norm induced by inner product.
]
#example[
    $RR^n$ with standard inner product is Hilbert space.
]
#example[
    Define inner product on $L^2 (E)$ $ ip(f, g)_(L^2) := integral_E f overline(g) $ Induced norm is the $L^2$ norm. So by Riesz-Fischer theorem, $\(L^2 (E), ip(dot.op, dot.op)_(L^2)\)$ is Hilbert space.
]
#definition[
    Let $H$ Hilbert space with inner product $ip(dot.op, dot.op)$.
    - $x, y in H$ are *orthogonal*, $x perp y$ if $ip(x, y) = 0$.
    - $A, B subset.eq H$ are *orthogonal*, $A perp B$ if $forall x in A, forall y in B, quad x perp y$.
    - *Orthogonal complement* of $A subset.eq H$ is $ A^perp := {x in H: forall y in A, thick thick x perp y} $
]
#theorem("Pythagorean Theorem")[
    If $x_1, ..., x_n in H$, $x_i perp x_j$ for $i != j$, then $ norm(sum_(i = 1)^n x_i)^2 = sum_(i = 1)^n norm(x_i)^2 $
]
#proof[
    Use linearity of inner product and orthogonal condition.
]
#theorem[
    Let $H$ Hilbert space, $A subset.eq H$, then $A^perp$ is closed subspace of $H$.
]
#proof[
    - Subspace:
        - For $y, z in A^perp$, $lambda, mu in CC$, show $forall x in A$, $lambda y + mu z in A^perp$.
    - Closed:
        - Show if $(y_n) subset.eq A^perp$, $y_n -> y$, then $y in A^perp$:
            - Let $x in A$, then show $|ip(x, y)| -> 0$ by squeezing, triangle inequality and Cauchy-Schwarz.
]
#theorem("Projection")[
    Let $M$ closed subspace of Hilbert space $H$.
    - For every $x in H$, there exists unique closest point $y in M$: $ forall x in H, exists! y in M: quad norm(x - y) = min{norm(x - z): z in M} $ We say $y$ is "the best approximation" to $x$ in $M$.
    - The point $y in M$ closest to $x in H$ is unique element of $M$ such that $(x - y) perp M$.
]
#proof[
    - Let $d = inf{norm(x - z): z in M}$. Show that $exists y in M: norm(x - y) = d$:   
        - There is sequence $(y_n) subset M$ with $norm(x - y_n) -> d$. Show that $(y_n)$ is Cauchy:
            - $norm(y_m - y_n)^2 + norm(2x - y_m - y_n)^2 = 2 norm(x - y_m)^2 + 2 norm(x - y_n)^2$ by parallelogram identity.
            - $(y_m + y_n)/2 in M$, so $norm(2x - y_m - y_n) >= 2d$.
        - Deduce that $y_n -> y in M$ and $norm(x - y) -> d$ by squeezing.
    - Uniqueness of $y$:
        - Let $norm(x - y) = d = norm(x - y')$.
        - By parallelogram identity, $2 norm(x - y)^2 + 2 norm(x - y')^2 = norm(2x - y - y')^2 + norm(y - y')^2$.
        - Use that $(y + y')/2 in M$ to show $norm(y - y') = 0$.
    - To show $z = x - y perp M$:
        - For $w in M$, write $ip(z, w) = |ip(z, w)| lambda$ where $lambda = e^(i theta)$, set $u = lambda w$.
        - Define $f(t) = norm(z + t u)^2$, show $t = 0$ is minimum of $f$ and so $0 = f'(0)$, hence $z in M^perp$.
    - To show uniqueness of $z$:
        - Show for $y, y' in M$ such that $x - y perp M$ and $x - y' perp M$, then $ip(y - y', w) = 0$ for any $w in M$. Set $w = y - y'$ to give $y = y'$.
]
#definition[
    *Direct sum* of subspaces $M$ and $N$ of linear space is $ M xor N := {y + z: y in M, z in N} $
]
#corollary[
    If $M$ closed subspace of Hilbert space $H$, then $H = M xor M^perp$.

    For all $x in H$, $x$ can be written uniquely as $x = y + z$ where $y$ is best approximation to $x$ in $M$ and $z = x - y perp M$.
]
#proof[
    By above theorem.
]
#definition[
    Let $H$ Hilbert space. ${u_alpha}_(alpha in I)$ is *orthonormal* if it is *orthogonal*: $u_alpha perp u_beta$ for $alpha != beta$, and *normalised*: $forall alpha in I, norm(u_alpha) = 1$.
]
#definition[
    Let $X$ Banach space, ${x_alpha in X: alpha in I}$ be indexed set where $I$ is countable or uncountable.
    - For each finite $J subset.eq I$, define *partial sum* as $ S_J := sum_(alpha in J) x_alpha $
    - Unordered sum of ${x_alpha in X: alpha in I}$ *converges unconditionally* to $x in X$, written $x = sum_(alpha in I) x_alpha$, if $forall epsilon > 0$, there exists finite $J subset.eq I$ such that $norm(S_K - x) < epsilon$ for every finite $J subset.eq K subset.eq I$.
    - Unordered sum $sum_(alpha in I) x_alpha$ is *Cauchy* if $forall epsilon > 0$, there exists finite $J subset.eq I$ such that $norm(S_L) < epsilon$ for every finite $L subset.eq I - J$. Note that $ norm(S_L) = norm(sum_(alpha in L union J) x_alpha - sum_(alpha in J) x_alpha) $
    - Unordered sum of ${x_alpha in X: alpha in I}$ *converges absolutely* if $sum_(alpha in I) norm(x_alpha)$ converges unconditionally in $RR$.
]
#proposition[
    Unordered sum in Banach space converges unconditionally iff it is Cauchy.
]<unordered-sum-converges-iff-cauchy>
#definition[
    Let ${c_alpha: alpha in I} subset.eq [0, oo]$. Define $ sum_(alpha in I) c_alpha = sup{sum_(alpha in J) c_alpha: J subset.eq I, J "finite"} $
]
#proposition[
    Let ${c_alpha: alpha in I} subset.eq [0, oo]$, $K = {alpha in I: c_alpha > 0}$. If $sum_(alpha in I) c_alpha < oo$, then $K$ is countable.
]
#theorem("Bessel's inequality")[
    Let $U = {u_alpha: alpha in I}$ orthonormal in Hilbert space $H$. Then $ forall x in H, quad sum_(alpha in I) |ip(x, u_alpha)|^2 <= norm(x)^2 $ In particular, $forall x in H$, ${alpha in I: ip(x, u_alpha) != 0}$ is countable.
]
#proof[
    - Prove for any finite $J subset.eq I$, then take supremum on LHS.
    - Show that $ norm(x - sum_(alpha in J) ip(x, u_alpha) u_alpha) = norm(x)^2 - sum_(alpha in J) |ip(x, u_alpha)|^2 $ using equation 2.2 and Pythagorean theorem.
]
#theorem[
    If $U = {u_alpha: alpha in I}$ is orthonormal subset of Hilbert space $H$ then the following are equivalent:
    - If $forall alpha in I, ip(x, u_alpha) = 0$, then $x = 0$.
    - $forall x in H$, $x = sum_(alpha in I) ip(x, u_alpha) u_alpha$ where sum converges unconditionally in $H$ and only has countably many non-zero terms.
    - *Parseval's identity*: $ forall x in H, quad norm(x)^2 = sum_(alpha in I) |ip(x, u_alpha)|^2 $
]<parseval>
#proof[
    - (i) $==>$ (ii): let ${alpha_j: j in NN}$ be set of indices where $ip(x, u_(alpha_j)) != 0$. Show the partial sums of $sum_(j in NN) ip(x, u_(alpha_j)) u_(alpha_j)$ are Cauchy using Pythagorean theorem and so show converges.
    - Set $ y = x - sum_(j in NN) ip(x, u_(alpha_j)) u_(alpha_j) $ and show $ip(y, u_alpha) = 0$.
    - (ii) $==>$ (iii): let $epsilon > 0$. Use definition of unconditional convergence of $x$ and Pythagorean theorem to show $norm(x)^2 - sum_(alpha in I) |ip(x, u_alpha)|^2 < epsilon$.
]
#definition[
    Orthonormal subset $U = {u_alpha: alpha in I}$ of Hilbert space $H$ is *complete* if it satisfies any of the conditions in @parseval. An *orthonormal basis* of $H$ is a complete orthonormal subset of $H$.
]
#definition[
    $U$ is *maximal orthonormal set* if $forall V subset.eq H$ such that $U subset.neq V$, $V$ is not orthonormal.
]
#lemma[
    $U$ is maximal orthonormal set iff it is an orthonormal basis.
]<maximal-orthonormal-iff-basis>
#remark[
    For orthonormal basis ${u_alpha: alpha in NN}$, representation $x = sum_(alpha in NN) c_alpha u_alpha$ is unique (consider $ip(x - x, u_beta) = lim_(n -> oo) ip(sum_(alpha = 1)^n (c_alpha - d_alpha) u_alpha, u_beta)$).
]
#theorem[
    Every Hilbert space $H$ has orthonormal basis. If $V subset.eq H$ is orthonormal set, then $H$ has orthonormal basis containing $V$.
]
#proof[
    - Assume $H != {0}$. Use partial ordering $subset.eq$.
    - Let ${U_alpha: alpha in I}$ be totally ordered collection of orthonormal sets. Find upper bound of ${U_alpha: alpha in I}$ which is orthonormal.
    - Show result using @zorn and @maximal-orthonormal-iff-basis.
    - To show orthonormal sets $V$ can be extended to orthonormal bases, use same argument on family of all orthonormal subsets of $H$ containing $V$.
]
#definition[
    A set $X$ is *partially ordered* if it is equipped with relation $<=$ satisfying:
    - *Reflexivity*: $forall x in X, x <= x$.
    - *Transitivity*: $(x <= y and y <= z) ==> x <= z$.
    - *Anti-symmetry*: $(x <= y and y <= x) ==> x = y$.
    $X$ is *totally ordered* if partially ordered and $forall x, y in X$, either $x <= y$ or $y <= x$.
]
#definition[
    Let $X$ totally ordered set with relation $<=$. $x in X$ is *upper bound* for $Y subset.eq X$ if $forall y in Y, y <= x$. $x in X$ is *maximal* if $forall y in X$, $x <= y ==> y = x$.
]
#example[
    Let $X$ be non-empty collection of sets. Then $subset.eq$ is partial ordering on $X$. $A in X$ is upper bound for $X' subset.eq X$ if every set in $X'$ is subset of $A$. $M in X$ is maximal if it is not proper subset of any set in $X$.
]
#theorem("Zorn's Lemma")[
    A partially ordered set $X$ that has upper bounds for its totally ordered subsets has a maximal element.
]<zorn>
#proposition[
    Hilbert space is separable iff it has countable orthonormal basis.
]
#proof[
    - $==>$: let $U = {u_n: n in NN}$ countable, dense in $H$. Recursively discard any $u_n$ in linear span of $u_1, ..., u_(n - 1)$ to obtain linearly independent set $V = {v_n: n in NN}$ whose linear span is dense in $H$. Applying Gram-Schmidt, set $ w_1 = v_1 / norm(v_1), ..., w_(n + 1) = c_(n + 1) (v_(n + 1) - sum_(k = 1)^n ip(w_k, v_(n + 1) w_k)) $ where $c_n in CC$ chosen so that $norm(w_n) = 1$. ${w_n: n in NN}$ is countable orthonormal basis.
    - $<==$: let ${w_n: n in NN}$ be orthonormal basis, show that $ S_m = {sum_(k = 1)^m c_k w_k: c_k in QQ + i QQ} $ is countable and $union_(m in NN) S_m$ dense in $H$.
]
#theorem("Riesz Representation Theorem for Hilbert Spaces")[
    Let $H$ Hilbert space with inner product $ip(dot.op, dot.op)$, $T: H -> RR$ bounded linear functional. Then $ exists! y in H: forall x in H, quad T(x) = ip(x, y) $ Note RHS gives bounded linear functional by Cauchy-Schwarz.
]
#proof[
    - Existence:
        - Show $N = {x in H: T(x) = 0}$ is closed subspace of $H$, use that $H = N xor N^perp$.
        - Assume $N^perp$ contains $v$ with $norm(v) = 1$. For $x in H$, define $u = T(x) v - T(v) x$.
        - Show that $ip(u, v) = 0$, deduce a value for $y$ from this.
    - Uniqueness: straightforward.
]

= Convergence of Fourier series

#note[
    We can view $f: [-pi, pi] -> CC$ as being $2pi$-periodic by extending it on the real line.
]
#definition[
    $m$-th *partial Fourier sum* of $2pi$-periodic integrable function $f: [-pi, pi] -> CC$ is given by $ (S_m f)(x) = sum_(k = -m)^m a_k (f) e^(i k x) $ where $ a_k (f) = 1/(2 pi) integral_(-pi)^pi f(y) e^(-i k y) dif y $ are *Fourier coefficients* of $f$.
]
#definition[
    Let $f, g: [-pi, pi] -> CC$ be $2pi$-periodic integrable functions. *Convolution* $f * g$ is $ (f * g)(x) = 1/(2pi) integral_(-pi)^pi f(y) g(x - y) dif y $
]
#proposition[
    Let $f, g, h: [-pi, pi] -> CC$ be $2pi$-periodic integrable functions, $c in CC$. Then $*$ satisfies:
    - *Commutativity*: $f * g = g * f$.
    - *Distributivity*: $f * (g + h) = (f * g) + (f * h)$.
    - *Homogeneity*: $(c f) * g = c(f * g) = f * (c g)$.
    - *Associativity*: $(f * g) * h = f * (g * h)$.
]

== Pointwise convergence of Fourier series via Dirichlet kernel

#definition[
    Let $m in NN_0$. The *$m$-th Dirichlet kernel* is $ D_m (x) := sum_(k = -m)^m e^(i k x) $
]
#proposition[
    - $D_m$ is trigonometric polynomial of degree $m$ with coefficients equal to $1$ for $k in [-m, m]$ and $0$ otherwise.
    - $D_m$ is real-valued and $2pi$-periodic.
    - $ 1/(2pi) integral_(-pi)^pi D_m (x) dif x = 1 $
]<dirichlet-kernel-properties>
#proposition[
    Let $f: [-pi, pi] -> CC$ be $2pi$-periodic integrable function. Then $ (D_m * f)(x)= sum_(k = -m)^m a_k (f) e^(i k x) = (S_m f)(x) $ where $a_k (f) = 1/(2pi) integral_(-pi)^pi f(y) e^(-i k y) dif y$.
]
#proposition[
    $ D_m (x) = sin((m + 1/2) x)/sin(x/2) $
]<dirichlet-kernel-explicit>
#remark[
    RHS in @dirichlet-kernel-explicit has removable singularity at $x = 0$, and $D_m (0) = 2m + 1$. Applying l'Hopital's rule to RHS gives $ lim_(x -> 0) sin((m + 1/2) x)/sin(x/2) = 2m + 1 $
]
#theorem("Riemann-Lebesgue Lemma")[
    Let $E subset.eq RR$ measurable, $f in L^1 (E)$. Then $ lim_(n -> oo) integral_E f(x) sin(n x) = lim_(n -> oo) integral_E f(x) cos(n x) = lim_(n -> oo) integral_E f(x) e^(-i n x) = 0 $
]
#proof[
    - First consider when $f(x) = indicator((a, b))(x)$. Define $I_j = ((2pi j)/n, (2pi(j + 1))/n)$, so integral of $sin(n x)$ over each $I_j$ is $0$.
    - Write $ (a, b) = L union union.big_(j = 1)^N I_j union R $ so that $"length"(L), "length"(R) < (2pi)/n$.
    - Show that $ abs(integral_E f(x) sin(n x)) < (4pi)/n $
    - Deduce the $sin$ result for step functions.
    - Use that step functions are dense in $L^1$ to show $sin$ result for $f in L^1 (E)$ by writing $f = (f - psi) + psi$ and finally take $limsup$.
    - Same argument works for $cos$.
    - Conclude $exp$ result.
]
#theorem[
    Let $f in L^1 ([-pi, pi])$ be $2pi$-periodic, assume $f$ differentiable at $b in [-pi, pi]$. Then $
        f(b) = lim_(m -> oo) 1/(2pi) integral_(-pi)^pi f(y) D_m (b - y) dif y = lim_(m -> oo) (f * D_m)(b) = lim_(m -> oo) S_m f (b)
    $
]
#proof[
    - First assume $b = 0$. Let $0 < epsilon < 1$, show that $f(y)\/sin(y\/2)$ is integrable on $[epsilon, pi]$ and show $ lim_(m -> oo) integral_epsilon^pi f(y)/sin(y/2) sin((m + 1/2)y) dif y = 0 $ Conclude the same for $integral_(-pi)^(-epsilon)$.
    - Write $f(y) = f(0) + s(y)$ and split the integral $integral_(-pi)^pi$ as such.
    - Use @dirichlet-kernel-properties and split integral of $s(y)$ to show $ lim_(m -> oo) 1/(2pi) integral_(-pi)^pi f(y) D_m (y) dif y = f(0) + lim_(m -> oo) 1/(2pi) integral_(-epsilon)^epsilon s(y) D_m (y) dif y $
    - Use differentiability at $0$ to show for $epsilon$ small and $y in [-epsilon, epsilon]$, $|s(y)| <= C|y|$.
    - Show that $|x|\/|sin(x)| <= 2$ for $x$ small (for $cos(x) >= 1/2$) by considering $g(x) = 2 sin(x) - x$, and then that $ 0 <= abs(lim_(m -> oo) 1/(2pi) integral_(-epsilon)^epsilon s(y) D_m (y) dif y) <= (4 C epsilon)/pi $
    - Conclude the result for $b = 0$.
    - To show for $b in [-pi, pi]$, define $G(y) = f(b - y)$ and use commutativity of convolution.
]

== Uniform convergence of Cesàro mean Fourier series via Fejér kernel

#definition[
    Let $x in RR$, $N in NN$. *Fejér kernel* is $ F_N (x) = 1/N sum_(m = 0)^(N - 1) D_m (x) = 1/N sum_(m = 0)^(N - 1) sum_(k = -m)^m e^(i k x) $
]
#proposition[
    - $ 1/(2pi) integral_(-pi)^pi F_N (x) dif x = 1 $
    - $ F_N (x) = 1/N (sin(N x\/2)/sin(x\/2))^2 $
    - Fejér kernel is non-negative, so $ F_N (x) = |F_N (x)| ==> integral_(-pi)^pi |F_N (x)| dif x = 2pi $
    - For $epsilon > 0$ and $epsilon < |x| < pi$, there exists $C_epsilon > 0$ such that $(sin(x\/2))^(-2) <= C_epsilon$, hence $ integral_epsilon^pi |F_N (x)| dif x = 1/N integral_epsilon^pi abs(sin(N x\/2)/sin(x\/2))^2 dif x <= 1/N integral C_epsilon <= (pi C_epsilon) / N -> 0 quad "as" N -> oo $ and similarly for $-pi < x < -epsilon$.
]<fejer-kernel-properties>
#definition[
    The *$N$-th Cesàro mean* is the average of the first $N$ partial Fourier sums of $f$: $ 1/N sum_(m = 0)^(N - 1) (S_m f)(x) $
]
#proposition[
    Let $f: [-pi, pi] -> CC$ integrable, then convolution of $f$ with Fejér kernel is the Cesàro mean: $ (f * F_N)(x) = 1/N sum_(m = 0)^(N - 1) (S_m f)(x) $
]
#theorem[
    Let $f: [-pi, pi] -> CC$ continuous and $2pi$-periodic, then $ forall x in [-pi, pi], quad f(x) = lim_(N -> oo) (f * F_N)(x) = lim_(N -> oo) 1/N sum_(m = 0)^(N - 1) (S_m f)(x) $ and the convergence is uniform.
]<fejer-convolution-approximation>
#proof[
    - Reason that $f$ is bounded: $|f| <= B$ on $[-pi, pi]$.
    - Let $rho > 0$. Show that $forall x, y in [-pi, pi]$, for some $epsilon > 0$, $|y| < epsilon ==> |f(x - y) - f(x)| < rho$.
    - Show that $ & |(f * F_N)(x) - f(x)| \ & <= 1/(2pi) (integral_(-pi)^(-epsilon) + integral_epsilon^pi) |F_N (y)| |f(x - y) - f(x)| dif y + 1/(2pi) integral_(-epsilon)^epsilon |F_N (y)| |f(x - y) - f(x)| dif y $
    - Show that first terms of RHS tend to zero as $N -> oo$.
    - Show last term on RHS is $< rho$.
    - Conclude the result.
]
#remark[
    - By above theorem, any $2pi$-periodic continuous function on $[-pi, pi]$ can be uniformly approximated by trigonometric polynomials, i.e. if $epsilon > 0$, then there exists trigonometric polynomial $p$ such that $forall x in [-pi, pi], |f(x) - p(x)| < epsilon$.
    - This is analogue of Weierstrass Approximation Theorem for $2pi$-periodic functions. Weierstrass Approximation Theorem states that for continuous function $f: [a, b] -> RR$ and $epsilon > 0$, there exists polynomial $p$ such that $forall x in [a, b]$, $|f(x) - p(x)| < epsilon$.
    - Continuous functions are dense in $L^p ([a, b])$ for $p in [1, oo)$. Let $epsilon > 0$, $f in L^p ([a, b])$ and $g: [a, b] -> RR$ continuous such that $norm(f - g)_(L^p) < epsilon$. By Weierstrass Approximation Theorem, there exists polynomial $tilde(p)$ such that $ forall x in [a, b], quad |g(x) - tilde(p)(x)| < epsilon/(b - a)^(1\/p) $ Hence $ integral_a^b |g(x) - tilde(p)(x)|^p < epsilon^p quad "i.e." quad norm(g - tilde(p))_(L^p) < epsilon $ Hence by Minkowski's inequality, $norm(f - tilde(p))_(L^p) < 2epsilon$. Hence polynomials are dense in $L^p ([a, b])$ for $p in [1, oo)$.
    - *Note*: for $p = oo$, any continuous function in $L^oo ([a, b])$ can be approximated by polynomials, but continuous functions are not dense in $L^oo ([a, b])$.
    - Similarly, trigonometric polynomials are dense in $L^p ([-pi, pi])$ for $p in [1, oo)$.
]

== Mean convergence of Fourier series in $L^2 ([-pi, pi])$

#notation[
    Define an inner product on $L^2 ([-pi, pi])$ by $ ip(f, g) = 1/(2pi) integral_([-pi, pi]) f overline(g) $ and denote $norm(dot) = sqrt(ip(dot, dot))$. $(L^2 ([-pi, pi]), ip(dot, dot))$ is Hilbert space by Riesz-Fischer.

    For $k in ZZ$, $x in [-pi, pi]$, let $phi_k (x) = e^(i k x)$, then for $2pi$-periodic integrable function $f: [-pi, pi] -> CC$, $ a_k (f) = ip(f, phi_k), quad S_N f (x) = sum_(k = -N)^N ip(f, phi_k) phi_k $
]
#lemma[
    Let $f in L^2 ([-pi, pi])$ be $2pi$-periodic, define $ cal(P)_N = {sum_(k = -n)^n c_k phi_k: c_k in CC, n <= N} $ Then:
    - ${phi_n: n in ZZ}$ is orthonormal in $L^2 ([-pi, pi])$ with respect to $ip(dot, dot)$.
    - $forall p in cal(P)_N$, $f - S_N f$ is orthogonal to $p$.
    - $forall N >= 0$, $forall p in cal(P)_N$, $ norm(f - S_N f) <= norm(f - p) $ with equality iff $p = S_N f$.
]<fourier-projection>
#proof[
    - Show $1/(2pi) integral_([-pi, pi]) phi_m overline(phi_n) = 0 = delta_(m n)$ (justify use of Riemann integral).
    - Show that $(f - S_N f) perp phi_m$ for each $|m| <= N$ to show $(f - S_N f) perp p$ for $p in cal(P)_N$.
    - Write $f - p = f - S_N f + S_N f - sum_(k = -N)^N c_k phi_k$, use Pythagoras.
]
#remark[
    Above lemma is projection result, i.e. $S_N f$ is best approximation to $f$ in $cal(P)_N$.
]
#theorem[
    Let $f in L^2 ([-pi, pi])$ be $2pi$-periodic function. Then Fourier series for $f$ converges to $f$ in $(L^2 ([-pi, pi]), norm(dot))$, i.e. $ lim_(N -> oo) norm(S_N f - f) = 0 $
]
#proof[
    - First show if $g: [-pi, pi] -> CC$ continuous, then $norm(S_N g - G) -> 0$ as $N -> oo$.
        - Let $epsilon > 0$, then for some $M$, there exists $p in cal(P)_M$ such that $ forall x in [-pi, pi], quad |g(x) - p(x)| < epsilon $
        - Use that $g(x) = lim_(N -> oo) (g * F_N)(x)$ and $g * F_(M + 1) in cal(P)_M$.
        - Deduce that $norm(g - p)^2 < epsilon^2$.
        - Show if $M <= N$ then $norm(g - S_N g) <= norm(g - p) < epsilon$, conclude result for continuous functions.
    - Let $f in L^2 ([-pi, pi])$, $epsilon > 0$. Using that continuous functions are dense in $L^2 ([-pi, pi])$, there is $g: [-pi, pi] -> CC$ such that $norm(f - g) < epsilon$.
    - Since $g$ continuous, for large enough $M$, $norm(S_M g - g) < epsilon$ by above.
    - Use triangle inequality, the fact that $N >= M ==> S_M g in cal(P)_N$ and projection theorem to conclude the result.
]
#lemma[
    ${phi_n: n in ZZ}$ is orthonormal basis of $(L^2 ([-pi, pi])$ with respect to inner product $ ip(f, g) = 1/(2pi) integral_([-pi, pi]) f overline(g) $
]
#proof[
    - Note that $(L^2 ([-pi, pi]), ip(dot, dot))$ is Hilbert space.
    - Show Parseval's identity holds.
    - Write $f = f - S_N f + S_N f$, use projection theorem, Pythagorean theorem and orthonormality of ${phi_n: n in ZZ}$ to show $ norm(f)^2 = norm(f - S_N f)^2 + sum_(k = -N)^N |ip(f, phi_k)|^2 $
    - Take limit as $N -> oo$ to conclude result.
]