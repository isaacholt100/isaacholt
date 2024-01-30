#import "../../template.typ": template
#show: template

#let indicator(arg) = $bb(1)_arg$

= The real numbers

== Conventions on sets and functions

- *Definition*: for $f: X -> Y$, *preimage* of $Z subset.eq Y$ is $ f^(-1) (Z) := {x in X: f(x) in Z} $
- *Definition*: $f: X -> Y$ *injective* if $ forall y in f(X), exists! x in X: y = f(x) $
- *Definition*: $f: X -> Y$ *surjective* if $Y = f(X)$.
- *Proposition*: let $f: X -> Y$, $A, B subset.eq X$, then $ f(A sect B) & subset.eq f(A) sect f(B), \ f(A union B) & = f(A) union f(B), \ f(X) - f(A) & subset.eq f(X - A) $
- *Proposition*: let $f: X -> Y$, $C, D subset.eq Y$, then $ f^(-1)(C sect D) & = f^(-1) (C) sect f^(-1)(D), \ f^(-1)(C union D) & = f^(-1)(C) union f^(-1)(D), \ f^(-1)(Y - C) & = X - f^(-1)(C) $

== The real numbers

- *Definition*: $a in RR$ is an *upper bound* of $E subset.eq RR$ if $forall x in E, x <= a$.
- *Definition*: $c in RR$ is a *least upper bound (supremum)* of $E$, $c = sup(E)$, if $c <= a$ for every upper bound $a$.
- *Definition*: $a in RR$ is an *lower bound* of $E subset.eq RR$ if $forall x in E, x >= a$.
- *Definition*: $c in RR$ is a *greatest lower bound (supremum)*, $c = inf(E)$, if $c >= a$ for every upper bound $a$.
- *Completeness axiom of the real numbers*: every $E subset.eq RR$ with an upper bound has a least upper bound. Every $E subset.eq RR$ with a lower bound has a greatest lower bound.
- *Archimedes' principle*: $ forall x in RR, exists n in NN: n > x $
- *Remark*: every non-empty subset of $NN$ has a minimum.
- *Proposition*: $QQ$ is dense in $RR$: $ forall x < y in RR, exists r in QQ: r in (x, y) $

== Sequences, limits and series

- *Definition*: $l in RR$ is *limit* of $(x_n)$ ($(x_n)$ converges to $l$) if $ forall epsilon > 0, exists N in NN: forall n >= N, quad |x_n - l| < epsilon $ A sequence *converges in $RR$ (is convergent)* if it has a limit $l in RR$. Limit $l = lim_(n -> oo) x_n$ is unique.
- *Definition*: $(x_n)$ *tends to infinity* if $ forall K > 0, exists N in NN: forall n >= N, quad x_n > K $
- *Definition*: *subsequence* of $(x_n)$ is sequence $\(x_(n_j)\)$, $n_1 < n_2 < dots.h.c$.
- *Definition*: *limit inferior* of sequence $x_n$ is $ liminf_(n -> oo) x_n := lim_(n -> oo) (inf_(m >= n) x_m) = sup_(n in NN) inf_(m >= n) x_m $
- *Definition*: *limit superior* of sequence $x_n$ is $ limsup_(n -> oo) x_n := lim_(n -> oo) (sup_(m >= n) x_m) = inf_(n in NN) sup_(m >= n) x_m $
- *Proposition*: let $(x_n)$ bounded, $l in RR$. The following are equivalent:
    - $l = limsup x_n$.
    - $forall epsilon > 0, exists N in NN: forall n >= N, x_n < l + epsilon$.
    - $forall epsilon > 0, forall N in NN: exists n in NN: x_n > l - epsilon$.
- *Proposition*: let $(x_n)$ bounded, $l in RR$. The following are equivalent:
    - $l = liminf x_n$.
    - $forall epsilon > 0, exists N in NN: forall n >= N, x_n > l - epsilon$.
    - $forall epsilon > 0, forall N in NN: exists n in NN: x_n < l + epsilon$.
- *Theorem (Bolzano-Weierstrass)*: every bounded sequence has a convergent subsequence.
- *Proposition*: let $(x_n)$ bounded. There exists convergent subsequence with limit $limsup x_n$ and convergent subsequence with limit $liminf x_n$.
- *Proposition*: let $(x_n)$ bounded, then $(x_n)$ is convergent iff $limsup x_n = liminf x_n$.
- *Monotone convergence theorem for sequences*: monotone sequence converges in $RR$ or tends to either $oo$ or $-oo$.
- *Definition*: $(x_n)$ is *Cauchy sequence* if $ forall epsilon > 0, exists N in NN: forall n, m >= N, quad |x_n - x_m| < epsilon $
- *Theorem*: every Cauchy sequence in $RR$ is convergent.

== Open and closed sets

- *Definition*: $U subset.eq RR$ is *open* if $ forall x in U, exists epsilon > 0: (x - epsilon, x + epsilon) subset.eq U $
- *Proposition*: arbitrary unions of open sets are open. Finite intersections of open sets are open.
- *Definition*: $x in RR$ is *point of closure (limit point)* for $E subset.eq RR$ if $ forall epsilon > 0, exists y in E: |x - y| < epsilon $ Equivalently, $x$ is point of closure of $E$ if every open interval containing $x$ contains another point of $E$.
- *Definition*: *closure* of $E$, $overline(E)$, is set of points of closure. Note $E subset.eq overline(E)$.
- *Definition*: $F$ is *closed* if $F = overline(F)$.
- *Proposition*: $overline(A union B) = overline(A) union overline(B)$. If $A subset B subset.eq RR$ then $overline(A) subset overline(B)$.
- *Proposition*: for any set $E$, $overline(E)$ is closed, i.e. $overline(E) = overline(overline(E))$.
- *Proposition*: let $E subset.eq RR$. The following are equivalent:
    - $E$ is closed.
    - $RR - E$ is open.
- *Proposition*: arbitrary intersections of closed sets are closed. Finite unions of closed sets are closed.
- *Definition*: collection $C$ of subsets of $RR$ *covers* (is a *covering* of) $F subset.eq RR$ if $F subset.eq union_(S in C) S$. If each $S$ in $C$ open, $C$ is *open covering*. If $C$ is finite, $C$ is *finite covering*.
- *Definition*: covering $C$ of $F$ *contains a finite subcover* if exists ${S_1, ..., S_n} subset.eq C$ with $F subset.eq union_(i = 1)^n S_i$ (i.e. a finite subset of $C$ covers $F$).
- *Definition*: $F$ is *compact* if any open covering of $F$ contains a finite subcover.
- *Example*: $RR$ is not compact, $[a, b]$ is compact.
- *Heine-Borel theorem*: $F$ compact iff $F$ closed and bounded.

== Continuity, pointwise and uniform convergence of functions

- *Definition*: let $E subset.eq RR$. $f: E -> RR$ is *continuous at $a in E$* if $ forall epsilon > 0, exists delta > 0: forall x in E, |x - a| < delta ==> |f(x) - f(a)| < epsilon $ $f$ is *continuous* if continuous at all $y in E$.
- *Definition*: $lim_(x -> a) f(x) = l$ if $ forall epsilon > 0, exists delta > 0: forall x in E, |x - a| < delta ==> |f(x) - l| < epsilon $
- *Proposition*: $lim_(x -> a) f(x) = l$ iff for every sequence $(a_n)$ with $lim_(n -> oo) a_n = a$, $lim_(n -> oo) f(a_n) = l$.
- *Proposition*: $f$ is continuous at $a in E$ iff $lim_(x -> a) f(x) = f(a)$ (and this limit exists).
- *Definition*: $f: E -> RR$ is *uniformly continuous* if $ forall epsilon > 0, exists delta > 0: forall x, y in E, |x - y| < delta ==> |f(x) - f(y)| < epsilon $
- *Proposition*: let $F$ closed and bounded, $f: F -> RR$ continuous. Then $f$ is uniformly continuous.
- *Definition*: let $f_n: E -> RR$ sequence of functions, $f: E -> RR$. $(f_n)$ *converges pointwise* to $f$ if $ forall epsilon > 0, forall x in E, exists N in NN: forall n >= N, |f_n (x) - f(x)| < epsilon $ $(f_n)$ *converges uniformly* to $f$ is $ forall epsilon > 0, exists N in NN: forall n >= N, forall x in E, |f_n (x) - f(x)| < epsilon $
- *Theorem*: let $f_n: E -> RR$ sequence of continuous functions converging uniformly to $f: E -> RR$. Then $f$ is continuous.
- *Definition*: $P = {x_0, ..., x_n}$ is *partition* of $[a, b]$ if $a = x_0 < dots.h.c < x_n = b$.
- *Definition*: $f: [a, b] -> RR$ is *piecewise linear* if there exists partition $P = {x_0, ..., x_n}$ and $m_i, c_i in RR$ such that $ forall i in [n], forall x in \(x_(i - 1), x_i\), quad f(x) = m_i x + c_i $ $f$ is continuous on $[a, b] - P$.
- *Definintion*: $g: [a, b] -> RR$ is *step function* if there exists partition $P = {x_0, ..., x_n}$ and $m_i in RR$ such that $ forall i in [n], forall x in \(x_(i - 1), x_i)\), quad g(x) = m_i $ $g$ is continuous on $[a, b] - P$.
- *Theorem*: let $f: E -> RR$ continuous, $E$ closed and bounded. Then there exist continuous piecewise linear $f_n$ with $f_n -> f$ uniformly, and step functions $g_n$ with $g_n -> f$ uniformly.
- *Definition*: $f: E -> RR$ is *Lipschitz* if $ exists C > 0: forall x, y in E, quad |f(x) - f(y)| <= C|x - y| $
- *Definition*: $f: E -> RR$ is *bi-Lipschitz* if $ exists C > 0: forall x, y in E, quad C^(-1)|x - y| <= |f(x) - f(y)| <= C|x - y| $

== The extended real numbers

- *Definition*: *extended reals* are $RR union {-oo, oo}$ with the order relation $-oo < oo$ and $forall x in RR, -oo < x < oo$. $oo$ is an upper bound and $-oo$ is a lower bound for every $x in RR$, so $sup(RR) = oo$, $inf(RR) = -oo$.
    - Addition: $forall a in RR, a + oo = oo and a + (-oo) = -oo$. $oo + oo = oo - (-oo) = oo$. $oo - oo$ is undefined.
    - Multiplication: $forall a > 0, a dot.op oo = oo$, $forall a < 0, a dot.op oo = -oo$. Also $oo dot.op oo = oo$.
    - $limsup$ and $liminf$ are defined as $ limsup x_n := inf_(n in NN) {sup_(k >= n) x_k}, quad liminf x_n := sup_(n in NN) {inf_(k >= n) x_k} $
- *Definition*: extended real number $l$ is *limit* of $(x_n)$ if either
    - $forall epsilon > 0, exists N in NN: forall n >= N, |x_n - l| < epsilon$. Then $(x_n)$ *converges to $l$*. or
    - $forall Delta > 0, exists N in NN: forall n >= N, x_n > Delta$ (limit is $oo$) or
    - $forall Delta > 0, exists N in NN: forall n >= N, x_n < -Delta$ (limit is $-oo$).
    $(x_n)$ *converges in the extended reals* if it has a limit in the extended reals.

= Further analysis of subsets of $RR$

== Countability and uncountability

- *Definition*: $A$ is *countable* if $A = nothing$, $A$ is finite or there is a bijection $phi: NN -> A$ (in which case $A$ is *countably infinite*). Otherwise $A$ is *uncountable*. *Enumeration* is bijection from $A$ to $[n]$ or $NN$.
- *Proposition*: if surjection from countable set to $A$, or injection from $A$ to countable set, then $A$ is countable.
- *Proposition*: any subset of $NN$ is countable.
- *Proposition*: $QQ$ is countable.
- *Proposition*: show that if $(a_n)$ is a nonnegative sequence and $phi: NN -> NN$ is a bijection then $ sum_(n = 1)^infinity a_n = sum_(n = 1)^infinity a_(phi(n)) $
- *Proposition*: show that if $\(a_(n, k)\)$ is a nonnegative sequence and $phi: NN -> NN times NN$ is a bijection then $ sum_(n = 1)^infinity sum_(n = 1)^infinity a_(n, k) = sum_(n = 1)^infinity a_(phi(n)) $
- *Definition*: $f: X -> Y$ is *monotone* if $x >= y => f(x) >= f(y)$ or $x <= y => f(x) >= f(y)$.
- *Proposition*: let $f$ be monotone on $(a, b)$. Then it is discountinuous on a countable set.
- *Lemma*: set of sequences in ${0, 1}$, $\{(x_n)_(n in NN): forall n in NN, x_n in {0, 1}\}$ is uncountable.
- *Theorem*: $RR$ is uncountable.

== The structure theorem for open sets

- Collection ${A_i: i in I}$ of sets is *(pairwise) disjoint* if $n != m ==> A_n sect A_m = nothing$.
- *Structure theorem for open sets*: let $U subset.eq RR$ open. Then exists countable collection of disjoint open intervals ${I_n: n in NN}$ such that $U = union_(n in NN) I_n$.

== Accumulation points and perfect sets

- *Definition*: $x in RR$ is *accumulation point* of $E subset.eq RR$ if $x$ is point of closure of $E - {x}$. Equivalently, $x$ is a point of closure if $ forall epsilon > 0, exists y in E: y != x and |x - y| < epsilon $ Equivalently, there exists a sequence of distinct $y_n in E$ with $y_n -> x$ as $n -> oo$.
- *Proposition*: set of accumulation points of $QQ$ is $RR$.
- *Proposition*: set of accumulation points $E'$ of $E$ is closed.
- *Definition*: $E subset.eq RR$ is *isolated* if $ forall x in E, exists epsilon > 0: (x - epsilon, x + epsilon) sect E = {x} $
- *Proposition*: $E$ is isolated iff it has no accumulation points.
- *Definition*: bounded set $E$ is *perfect* if it equals its set of accumulation points.
- *Theorem*: every non-empty perfect set is uncountable.

== The middle-third Cantor set

- *Proposition*: let ${F_n: n in NN}$ be collection of non-empty nested closed sets (so $F_(n + 1) subset.eq F_n$), one of which is bounded. Then $ sect.big_(n in NN) F_n != emptyset $
- *Definition*: the *middle third Cantor set* is defined by:
    - Define $C_0 := [0, 1]$
    - Given $C_n = union_(i = 1)^(2^n) [a_i, b_i]$, $a_1 < b_1 < a_2 < dots.h.c < a_(2^n) < b_(2^n)$, with $|b_i - a_i| = 3^(-n)$, define $ C_(n + 1) := union_(i = 1)^(2^n) [a_i, a_i + 3^(-(n + 1))] union [b_i - 3^(-(n + 1)), b_i] $ which is a union of $2^(n + 1)$ disjoint intervals, with all differences in endpoints equalling $3^(-(n + 1))$.
    - The *middle third Cantor set* is $ C := sect.big_(n in NN) C_n $ Observe that if $a$ is an endpoint of an interval in $C_n$, it is contained in $C$.
- *Proposition*: the middle third Cantor set is closed, non-empty and equal to its set of accumulation points. Hence it is perfect and so uncountable.
- *Definition*: let $k in NN - {1}$, $x in lr([0, 1))$. $0.a_1 a_2 ...$, $a_i in {0, ..., k - 1}$, is a *$k$-ary expansion* of $x$ if $ x = sum_(i in NN) a_i / k^i $
- *Remark*: the $k$-ary expansion may not be unique, but there is a countable set $E subset.eq lr([0, 1))$ such that every $x in lr([0, 1)) - E$ has a unique $k$-ary expansion.
- *Remark*: for every $x in C$, the ternary ($k = 3$) expansion of $x$ is unique and $ x = sum_(i in NN) a_i / 3^i, quad a_i in {0, 2} $ Moreover, every choice of sequence $(a_i)$, $a_i in {0, 2}$, gives $x = sum_(i in NN) a_i / 3^i in C$.
- *Definition*: *Cantor-Lebesgue function*, $g: [0, 1] -> [0, 1]$, is defined by $ g(x) := cases(sum_(i in NN) (a_i\/2) / 2^i & "if" x = sum_(i in NN) a_i / 3^i \, a_i in {0, 2}, sup{f(y): y in C, y <= x} & "if" x in.not C) $ $g$ is a surjection, monotone and continuous.

== $G_delta, F_sigma$

- *Definition*: $E subset.eq RR$ is *$G_delta$* if $E = sect_(n in NN) U_n$ with $U_n$ open.
- *Definition*: $E subset.eq RR$ is *$F_sigma$* if $E = union_(n in NN) F_n$ with $F_n$ closed.
- *Lemma*: set of points where $f: RR -> RR$ is continuous is $G_delta$.

= Construction of Lebesgue measure

== Lebesgue outer measure

- *Definition*: let $I$ non-empty interval with endpoints $a = inf(I) in {-oo} union RR$ and $b = sup(I) in RR union {oo}$. The *length* of $I$ is $ ell(I) := b - a $ and set $ell(nothing) = 0$.
- *Definition*: let $A subset.eq RR$. *Lebesgue outer measure* of $A$ is infimum of all sums of lengths of intervals covering $A$: $ mu^*(A) := inf{sum_(k in NN) ell(I_k): A subset.eq union.big_(k in NN) I_k, I_k "intervals"} $ It satisfies *monotonicity*: $A subset.eq B ==> mu^*(A) <= mu^*(B)$.
- *Proposition*: outer measure is *countably subadditive*: $ mu^*(union.big_(k in NN) E_k) <= sum_(k in NN) mu^*(E_k) $ This implies *finite subadditivity*: $ mu^*(union.big_(k = 1)^n E_k) <= sum_(k = 1)^n mu^*(E_k) $
- *Lemma*: we have $ mu^*(A) = inf{sum_(k in NN) ell(I_k): A subset union.big_(k in NN) I_k, I_k != nothing "open intervals"} $
- *Proposition*: outer measure of interval is its length: $mu^*(I) = ell(I)$.

== Measurable sets

- *Notation*: $E^c = RR - E$.
- *Proposition*: let $E = (a, oo)$. Then $ forall A subset.eq RR, quad mu^*(A) = mu^*(A sect E) + mu^*(A sect E^c) $
- *Definition*: $E subset.eq RR$ is *Lebesgue measurable* if $ forall A subset.eq RR, quad mu^*(A) = mu^*(A sect E) + mu^*(A sect E^c) $ Collection of such sets is $cal(F)_(mu^*)$.
- *Lemma (excision property)*: let $E$ Lebesgue measurable set with finite measure and $E subset.eq B$, then $ mu^*(B - E) = mu^*(B) - mu^*(E) $
- *Proposition*: if $E_1, ..., E_n$ Lebesgue measurable then $union_(k = 1)^n E_k$ is Lebesgue measurable. If $E_1, ..., E_n$ disjoint then $ mu^*(A sect union.big_(k = 1)^n E_k) = sum_(k = 1)^n mu^*(A sect E_k) $ for any $A subset.eq RR$. In particular, for $A = RR$, $ mu^*(union.big_(k = 1)^n E_k) = sum_(k = 1)^n mu^*(E_k) $
- *Remark*: not every set is Lebesgue measurable.
- *Definition*: collection of subsets of $RR$ is an *algebra* if contains $nothing$ and closed under taking complements and finite unions: if $A, B in cal(A)$ then $RR - A, A union B in cal(A)$.
- *Remark*: a union of a countable collection of Lebesgue measurable sets is also the union of a countable disjoint collection of Lebesgue measurable sets: if ${A_k}_(k in NN)$ is countable collection of Lebesgue measurable sets, then let $A_1' := A_1$ and for $k > 1$, define $ A_k' := A_k - union_(i = 1)^(k - 1) A_i $ then ${A_k'}_(k in NN)$ is disjoint union of Lebesgue measurable sets.
- *Proposition*: if $E$ is countable union of Lebesgue measurable sets, then $E$ is Lebesgue measurable. Also, if ${E_k}_(k in NN)$ is countable disjoint collection of Lebesgue measurable sets then $ mu^* (union.big_(k in NN) E_k) = sum_(k in NN) mu^* (E_k) $

== Abstract definition of a measure

- *Definition*: let $X subset.eq RR$. Collection of subsets of $cal(F)$ of $X$ is *$sigma$-algebra* if
    - $nothing in cal(F)$
    - $E in cal(F) ==> E^c in cal(F)$
    - $E_1, ..., E_n in cal(F) ==> union_(k in NN) E_k in cal(F)$.
- *Example*:
    - Trivial examples are $cal(F) = {nothing, RR}$ and $cal(F) = cal(P)(RR)$.
    - Countable intersections of $sigma$-algebras are $sigma$-algebras.
- *Definition*: let $cal(F)$ $sigma$-algebra of $X$. $nu: cal(F) -> RR union {plus.minus oo}$ is *measure* satisfying
    - $nu(nothing) = 0$
    - $forall E in cal(F), nu(E) >= 0$
    - *Countable additivity*: if $E_1, E_2, ... in cal(F)$ are disjoint then $ nu(union.big_(k in NN) E_k) = sum_(k in NN) nu(E_k) $
    Elements of $cal(F)$ are *measurable* (as they are the only sets on which the measure $nu$ is defined).
- *Proposition*: if $nu$ is measure then it satisfies:
    - *Monotonicity*: $A subset.eq B ==> nu(A) <= nu(B)$.
    - *Countable subadditivity*: $nu(union_(k in NN) E_k) <= sum_(k in NN) nu(E_k)$.
    - *Excision*: if $A$ has finite measure, then $A subset.eq B ==> m(B - A) = m(B) - m(A)$.

== Lebesgue measure

- *Lemma*: $F_(mu^*)$ is $sigma$-algebra and contains every interval.
- *Theorem (Carathéodory extension)*: restriction of the $mu^*$ to $F_(mu^*)$ is a measure.
- *Hahn extension theorem*: there exists unique measure $mu$ defined on $cal(F)_(mu^*)$ for which $mu(I) = ell(I)$ for any interval $I$.
- *Definition*: the measure $mu$ of $mu^*$ restricted to $cal(F)_(mu^*)$ is the *Lebesgue measure*. It satisfies $mu(I) = ell(I)$ for any interval $I$ and is translation invariant.

== Sets of measure $0$

- *Proposition*: middle-third Cantor set is Lebesgue measurable and has Lebesgue measure $0$.
- *Proposition*: any countable set is Lebesgue measurable and has Lebesgue measure $0$.
- *Proposition*: any $E$ with $mu^*(E) = 0$ is Lebesgue measurable and has $mu(E) = 0$.
- *Lemma*: let $E$ Lebesgue measurable set with $mu(E) = 0$, then $forall E' subset.eq E$, $E'$ is Lebesgue measurable.

== Continuity of measure

- *Definition*: countable collection ${E_k}_(k in NN)$ is *ascending* if $forall k in NN, E_k subset.eq E_(k + 1)$ and *descending* if $forall k in NN, E_(k + 1) subset.eq E_k$.
- *Theorem*: every measure $m$ satisfies:
    - If ${A_k}_(k in NN)$ is ascending collection of measurable sets, then $ m(union.big_(k in NN) A_k) = lim_(k -> oo) m(A_k) $
    - If ${B_k}_(k in NN)$ is descending collection of measurable sets and $m(B_1) < oo$, then $ m(sect.big_(k in NN) B_k) = lim_(k -> oo) m(B_k) $

== An approximation result for Lebesgue measure

- *Definition*: *Borel $sigma$-algebra* $cal(B)(RR)$ is smallest $sigma$-algebra containing all intervals: for any other $sigma$-algebra $cal(F)$ containing all intervals, $cal(B)(RR) subset.eq cal(F)$. $ cal(B)(RR) := sect.big {cal(F): cal(F) " " sigma "-algebra containing all intervals"} $ $E in cal(B)(RR)$ is *Borel* or *Borel measurable*.
- *Lemma*: all open subsets of $RR$, closed subsets of $RR$, $G_delta$ sets and $F_sigma$ sets are Borel.
- *Proposition*: the following are equivalent:
    - $E$ is Lebesgue measurable
    - $forall epsilon > 0, exists "open" G: E subset.eq G and mu^*(G - E) < epsilon$
    - $forall epsilon > 0, exists "closed" F: F subset.eq E and mu^*(E - F) < epsilon$
    - $exists G in G_delta: E subset.eq G and mu^*(G - E) = 0$
    - $exists F in F_sigma: F subset.eq E and mu^*(E - F) = 0$

= Measurable functions

== Definition of a measurable function

- *Proposition*: let $f: RR -> RR$. $f$ continuous iff $forall "open" U subset.eq RR, f^(-1)(U) subset.eq RR$ is open.
- *Lemma*: let $f: E -> RR union {plus.minus oo}$ with $E$ Lebesgue measurable. The following are equivalent:
    - $forall c in RR, {x in E: f(x) > c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) >= c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) < c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) <= c}$ is Lebesgue measurable.
    The same statement holds for Borel measurable sets.
- *Definition*: $f: E -> RR union {plus.minus oo}$ is *(Lebesgue) measurable* if it satisfies any of the above properties and if $E$ is Lebesgue measurable. $f$ being *Borel measurable* is defined similarly.
- *Corollary*: if $f$ is measurable then for every $B in cal(B)(RR)$, $f^(-1)(B)$ is measurable. In particular, if $f$ is measurable, preimage of any interval is measurable.
- *Definition*: *indicator function* on set $A$, $indicator(A): RR -> {0, 1}$, is $ indicator(A)(x) := cases(1 & "if" x in A, 0 & "if" x in.not A) $
- *Definition*: $phi: RR -> RR$ is *simple (measurable) function* if $phi$ is measurable function that has finite codomain.

== Fundamental aspects of measurable functions

- *Definition*: let $E subset.eq F subset.eq RR$, let $f: F -> RR$. *Restriction* $f_E$ is function with domain $E$ and for which $forall x in E, f_E (x) = f(x)$.
- *Definition*: real-valued function which is increasing or decreasing is *monotone*.
- *Definition*: sequence $(f_n)$ on domain $E$ is increasing if $f_n <= f_(n + 1)$ on $E$ for all $n in NN$.
- *Example*: continuous functions are measurable.
- *Definition*: for $f_1: E -> RR, ..., f_n: E -> RR$, define $ max{f_1, ..., f_n}(x) := max{f_1 (x), ..., f_n (x)} $ $min{f_1, ..., f_n}$ is defined similarly.
- *Proposition*: for finite family ${f_k}_(k = 1)^n$ of measurable functions with common domain $E$, $max{f_1, ..., f_n}$ and $min{f_1, ..., f_n}$ are measurable.
- *Definition*: for $f: E -> RR$, functions $|f|, f^+, f^-$ defined on $E$ are $ |f|(x) := max{f(x), -f(x)}, quad f^+ (x) := max{f(x), 0}, quad f^- (x) := max{-f(x), 0} $
- *Corollary*: if $f$ measurable on $E$, so are $|f|$, $f^+$ and $f^-$.
- *Proposition*: let $f: E -> RR union {plus.minus oo}$. For measurable $D subset.eq E$, $f$ measurable on $E$ iff restrictions of $f$ to $D$ and $E - D$ are measurable.
- *Theorem*: let $f, g: E -> RR$ measurable.
    - *Linearity*: $forall alpha, beta in RR, alpha f + beta g$ is measurable.
    - *Products*: $f g$ is measurable.
- *Proposition*: let $f_n: E -> RR union {plus.minus oo}$ be sequence of measurable functions that converges pointwise to $f: E -> RR union {plus.minus oo}$. Then $f$ is measurable.
- *Simple approximation lemma*: let $f: E -> RR$ measurable and bounded, so $exists M >= 0: forall x in E, |f|(x) < M$. Then $forall epsilon > 0$, there exist simple measurable functions $phi_epsilon, psi_epsilon: E -> RR$ such that $ forall x in E, quad phi_epsilon (x) <= f(x) <= psi_epsilon (x) and 0 <= psi_epsilon (x) - phi_epsilon (x) < epsilon $
- *Simple approximation theorem*: let $f: E -> RR union {plus.minus oo}$, $E$ measurable. Then $f$ is measurable iff there exists sequence $(phi_n)$ of simple functions on $E$ which converge pointwise on $E$ to $f$ and satisfy $ forall n in NN, forall x in E, |phi_n|(x) <= |f|(x) $ If $f$ is nonnegative, $(phi_n)$ can be chosen to be increasing.
- *Definition*: let $f, g: E -> RR union {plus.minus oo}$. Then $f = g$ *almost everywhere* if ${x in E: f(x) != g(x)}$ has measure $0$.
- *Proposition*: let $f_1, f_2, f_3: E -> RR union {plus.minus oo}$ measurable. If $f_1 = f_2$ almost everywhere and $f_2 = f_3$ almost everywhere then $f_1 = f_3$ almost everywhere.
- *Remark*: Lebesgue measurable functions can be modified arbitrarily on a set of measure $0$ without affecting measurability.
- *Proposition*: let $f_n: E -> RR union {plus.minus oo}$ sequence of measurable functions, $f: E -> RR union {plus.minus oo}$ measurable. Set of points where $(f_n)$ converges pointwise to $f$ is measurable.
- *Proposition*: let $f, g: E -> RR union {plus.minus oo}$ measurable and finite almost everywhere on $E$.
    - *Linearity*: $forall alpha, beta in RR$, there exists function equal to $alpha f + beta g$ almost everywhere on $E$ (any such function is measurable).
    - *Products*: there exists function equal to $f g$ almost everywhere on $E$ (any such function is measurable).
- *Definition*: sequence of functions $(f_n)$ with domain $E$ *converge in measure* to $f$ if $(f_n)$ and $f$ are finite almost everywhere and $ forall epsilon > 0, quad mu({x in E: |f_n (x) - f(x)| > epsilon}) -> 0 "as" n -> oo $

= The Lebesgue integral

== The integral of a simple measurable function

- *Definition*: let $phi$ be real-valued function taking finitely many values $alpha_1 < dots.h.c < alpha_n$, then *standard representation* of $phi$ is $ phi = sum_(i = 1)^n alpha_i bb(1)_(A_i), quad A_i = phi^(-1)({alpha_i}) $
- *Lemma*: let $phi = sum_(i = 1)^m beta_i indicator(B_i)$, $B_i$ disjoint measurable collection, $beta_i in RR$, then $phi$ is simple measurable. If $phi$ takes value $0$ outside a set of finite measure then $ sum_(i = 1)^n alpha_i mu(A_i) = sum_(i = 1)^m beta_i mu(B_i) $ where $A_i$ in standard representation.
- *Definition*: let $phi$ be simple nonnegative measurable function or simple measurable function taking value $0$ outside set of finite measure. *Integral* of $phi$ with respect to $mu$ is $ integral phi = sum_(i = 1)^n alpha_i mu(A_i) $ where $phi = sum_(i = 1)^n alpha_i bb(1)_(A_i)$ is standard representation. Here, use convention $0 dot.op oo = 0$. For measurable $E subset.eq RR$, define $ integral_E phi = integral indicator(E) phi $
- *Example*:
    - Let $phi_2 = indicator([0, 2]) + indicator([1, 3]) = indicator(lr([0, 1) union lr((2, 3]))) + 2 indicator([1, 2])$ so $integral phi_2 = 4$.
    - Let $phi_3 = indicator(RR)$, then $integral phi_3 = 1 dot.op oo = oo$.
    - Let $phi_4 = bb(1)_((0, oo)) + (-1) indicator((-oo, 0))$. This can't be integrated.
    - Let $phi_5 = indicator((-1, 0)) + (-1) indicator((0, 1))$.
- *Lemma*: let $B_1, ..., B_m$ be measurable sets, $beta_1, ..., beta_m in RR - {0}$. Then $phi = sum_(i = 1)^m beta_i indicator(B_i)$ is simple measurable function. Also, $ mu(union.big_(i = 1)^m B_i) < oo ==> sum_(i = 1)^n alpha_i mu(A_i) = sum_(i = 1)^m beta_i mu(B_i) $ where $A_i$ in standard representation.
- *Proposition*: let $phi, psi$ be simple measurable functions:
    - If $phi, psi$ take value $0$ outside a set of finite measure, then $forall alpha, beta in RR$, $ integral (alpha phi + beta psi) = alpha integral phi + beta integral psi $
    - If $phi, psi$ nonnegative, then $forall alpha, beta >= 0$, $ integral (alpha phi + beta psi) = alpha integral phi + beta integral psi $
    - *Monotonicity*: $ 0 <= phi <= psi ==> 0 <= integral phi <= integral psi $
- *Corollary*: let $phi$ nonnegative simple function, then $ integral phi = sup{integral psi: 0 <= psi <= phi, thick psi "simple measurable"} $
- *Lemma*: let $phi$ simple measurable nonnegative function. $phi$ takes value $0$ outside a set of finite measure iff $integral phi < oo$. Also, $integral phi = oo$ iff there exist $alpha > 0$, measurable $A$ with $mu(A) = oo$ and $forall x in A, phi(x) >= alpha$.
- *Lemma*: let ${E_n}$ be ascending collection of measurable sets, $union_(n in NN) E_n = RR$. Let $phi$ be simple nonnegative measurable function. Then $ integral_(E_n) phi -> integral phi quad "as" n -> oo $

== The integral of a nonnegative function

- *Notation*: let $cal(M)^+$ denote collection of nonnegative measurable functions $f: RR -> RR_(>= 0) union {oo}$.
- *Definition*: *support* of measurable function $f$ with domain $E$ is $"supp"(f) := {x in E: f(x) != 0}$.
- *Definition*: let $f in cal(M)^+$. *Integral of $f$ with respect to $mu$* is $ integral f := sup{integral phi: 0 <= phi <= f, phi "simple measurable"} in RR union {oo} $ For measurable set $E$, define $ integral_E f := integral indicator(E) f $
- *Proposition*: let $f, g$ measurable. If $g <= f$ then $integral g <= integral f$. Let $E, F$ measurable. If $E subset.eq F$ then $integral_E f <= integral_F f$.
- *Monotone convergence theorem*: let $(f_n)$ be sequence in $cal(M)^+$. If $(f_n)$ is increasing on measurable set $E$ and converges pointwise to $f$ on $E$ then $ integral_E f_n -> integral_E f quad "as" n -> oo $
- *Corollary*: restriction of integral to nonnegative functions is linear: $forall f, g in cal(M)^+$, $forall alpha >= 0$, $ integral (f + g) & = integral f + integral g \ integral alpha f & = alpha integral f $
- *Fatou's lemma*: let $(f_n)$ be sequence in $cal(M)^+$, then $ integral liminf_(n -> oo) f_n <= liminf_(n -> oo) integral f_n $
- *Lemma*: let $(f_n) subset cal(M)^+$, then $ integral sum_(n in NN) f_n = sum_(n in NN) integral f_n $
- *Proposition (Chebyshev's inequality)*: let $f$ be nonnegative measurable function on $E$. Then $ forall lambda > 0, quad mu({x in E: f(x) >= lambda}) <= 1/lambda integral_E f $
- *Proposition*: let $f$ be nonnegative measurable function on $E$. Then $ integral_E f = 0 <==> f = 0 "almost everywhere on" E $

== Integration of measurable functions

- *Notation*: let $cal(M)$ denote set of measurable functions.
- *Definition*: $f in cal(M)^+$ is *integrable* if $integral f < oo$.
- *Definition*: let $f: RR -> RR union {plus.minus oo}$ measurable function. $f$ is *integrable* if $integral f^+$ and $integral f^-$ are finite. In this case, for any measurable set $E$, define $ integral_E f := integral_E f^+ - integral_E f^- $ Note that if $f$ integrable then $f^+ - f^-$ is well-defined.
- *Proposition*: if $f = f_1 - f_2$, $f_1, f_2 in cal(M)^+$, $f_1, f_2$ integrable, then $ integral f^+ - integral f^- = integral f_1 - integral f_2 $
- *Definition*: $f in cal(M)$ is *integrable over $E$* ($E$ is measurable) if $integral_E f^+$ and $integral_E f^-$ are finite (i.e. $f dot.op indicator(E)$ is integrable).
- *Theorem*: $f in cal(M)$ is integrable iff $|f|$ is integrable. If $f$ integrable, then $ abs(integral f) <= integral abs(f) $
- *Corollary*: let $f, g in cal(M)$, $|f| <= |g|$. If $g$ integrable then $|f|$ is integrable, and $integral |f| <= integral |g|$.
- *Example*: $sin$ is not integrable over $RR$, but is integrable over $[0, 2pi]$, since $|f_([0, 2pi])| <= indicator([0, 2pi])$.
- *Theorem (Linearity of Integration)*: let $f, g in cal(M)$ integrable. Then $f + g$ is integrable and $forall alpha in RR$, $alpha f$ is integrable. The integral is linear: $ integral (f + g) & = integral f + integral g \ integral alpha f & = alpha integral f $
- *Dominated Convergence Theorem*: let $(f_n)$ be sequence of integrable functions. If there exists an integrable $g$ with $forall n in NN, |f_n| <= g$, and $f_n -> f$ pointwise almost everywhere then $f$ is integrable and $ integral f = lim_(n -> oo) integral f_n $

== Integrability: Riemann vs Lebesgue

- *Proposition*: let $f$ bounded function on bounded measurable domain $E$. Then $f$ is measurable and $integral_E |f| < oo$ iff $ sup{integral_E phi: phi <= f, phi "simple measurable"} = inf{integral_E psi: f <= psi: psi "simple measurable"} $ (If $f$ satisfies either condition then $integral_E f$ is equal to the two above expressions).
- *Definition*: bounded function $f$ is *Lebesgue integrable* if it satisfies either of the equivalences in the above proposition.
- *Definition*: let $P = {x_1, ..., x_n}$ partition of $[a, b]$, $f: [a, b] -> RR$ bounded. *Lower and upper Darboux sums* for $f$ with respect to $P$ are $ L(f, P) := sum_(i = 1)^n m_i (x_i - x_(i - 1)), quad U(f, P) := sum_(i = 1)^n M_i (x_i - x_(i - 1)) $ where $ m_i := inf{f(x): x in (x_(i - 1), x_i)}, quad M_i := sup{f(x): x in (x_(i - 1), x_i)} $ If $P subset.eq Q$ ($Q$ is a *refinement of $P$*), then $ L(f, P) <= L(f, Q) <= U(f, Q) <= U(f, P) $
- *Definition*: *lower and upper Riemann integrals* of $f$ over $[a, b]$ are $ underline(cal(I))_a^b (f) & := sup{L(f, P): P "partition of" [a, b]} \ overline(cal(I))_a^b (f) & := inf{U(f, P): P "partition of" [a, b]} $
- *Definition*: let $f: [a, b] -> RR$ bounded, then $f$ is *Riemann integrable* ($f in cal(R)$), if $ underline(cal(I))_a^b (f) = overline(cal(I))_a^b (f) $ and common value $cal(I)_a^b (f) = integral_a^b f(x) dif x$ is *Riemann integral* of $f$.
- Let $g: [a, b] -> RR$ step function with discontinuities at $P = {x_0, ..., x_n}$, so $g = sum_(i = 1)^n alpha_i indicator((x_(i - 1), x_i))$ almost everywhere. So $g$ is simple measurable and $ L(g, P) = sum_(i = 1)^n alpha_i (x_i - x_(i - 1)) = U(g, P) = integral g = cal(I)_a^b (g) $ Hence for any bounded $f: [a, b] -> RR$, $ underline(cal(I))_a^b (f) & = sup{integral phi: phi <= f, phi "step function"}, \ overline(cal(I))_a^b (f) & = inf{integral psi: f <= psi, psi "step function"} $
- *Theorem*: let $f: [a, b] -> RR$ bounded, $a, b != plus.minus oo$. If $f$ Riemann integrable over $[a, b]$ then $f$ Lebesgue integrable over $[a, b]$ and the two integrals are equal.
- *Theorem*: let $f: [a, b] -> RR$ bounded, $a, b != plus.minus oo$. Then $f$ is Riemann integrable on $[a, b]$ iff $f$ is continuous on $[a, b]$ except on a set of measure zero.
- *Lemma*: let $(phi_n)$, $(psi_n)$ be sequences of functions, all integrable over $E$, $(phi_n)$ increasing on $E$, $(psi_n)$ decreasing on $E$. Let $f: E -> RR$ with $ forall n in NN, phi_n <= f <= psi_n "on" E, quad lim_(n -> oo) integral_E (psi_n - phi_n) = 0 $ Then $phi_n, psi_n -> f$ pointwise almost everywhere on $E$, $f$ is integrable over $E$ and $ lim_(n -> oo) integral_E phi_n = lim_(n -> oo) integral_E psi_n = integral_E f $
- *Definition*: for partition $P = {x_0, ..., x_n}$, *gap* of $P$ is $ "gap"(P) := max{|x_i - x_(i - 1)|: i in {1, ..., n}} $
- *Lemma*: let $f: [a, b] -> RR$, $E subset.eq [a, b]$ be set where $f$ is continuous. Let $(P_n)$ be sequence of partitions of $[a, b]$ with $P_(n + 1) subset.eq P_n$ and $"gap"(P_n) -> 0$ as $n -> oo$. Let $phi_n, psi_n: [a, b] -> RR$ step functions with $ phi_n (x) := inf{f(x): x in (x_(i - 1), x_i)}, quad psi_n (x) := sup{f(x): x in (x_(i - 1), x_i)} $ for $P_n = {x_0, ..., x_n}$. Then $forall x in E - union_(n in NN) P_n$, $ phi_n (x), psi_n (x) -> f(x) quad "as" n -> oo $
- *Definition*: let $f: lr((a, b]) -> RR$, $-oo <= a < b < oo$, $f$ bounded and Riemann integrable on all closed bounded sub-intervals of $lr((a, b])$. If $ lim_(t -> a, t > a) cal(I)_t^b (f) $ exists then this is defined as the *improper Riemann integral* $cal(I)_a^b (f)$. Similar definitions exist for $f: (a, b) -> RR$ and $f: lr([a, b)) -> RR$.
- *Note*: improper Riemann integral may exist without function being Lebesgue integral.
- *Proposition*: if $f$ is integrable, the improper Riemann integral is equal to the Lebesgue integral whenever the former exists.
- *Definition*: let $alpha: [a, b] -> RR$ monotonically increasing (and so bounded). For partition $P = {x_0, ..., x_n}$ of $[a, b]$ and bounded $f: [a, b] -> RR$, define $ L(f, P, alpha) := sum_(i = 1)^n m_i (alpha(x_i) - alpha(x_(i - 1))), quad U(f, P, alpha) := sum_(i = 1)^n M_i (alpha(x_i) - alpha(x_(i - 1))) $ where $m_i := inf{f(x): x in (x_(i - 1), x_i)}$, $M_i := sup{f(x): x in (x_(i - 1), x_i)}$. Then $f$ is *integrable with respect to $alpha$*, $f in cal(R)(alpha)$, if $ inf{U(f, P, alpha): P "partition of" [a, b]} = sup{L(f, P, alpha): P "partition of" [a, b]} $ and the common value $integral_a^b f dif alpha$ is the *Riemann-Stieltjes integral* of $f$ with respect to $alpha$.
- *Proposition*: let $f: (a, b) -> RR$, then set of points where $f$ is differentiable is measurable.
- *Remark*: if $alpha: [0, 1] -> [a, b]$ bijection, then $ integral_0^1 f compose alpha dif alpha = integral_a^b f(x) dif x $
- *Proposition*: let $alpha$ be monotonically increasing and differentiable with $alpha' in cal(R)$. Then $g in cal(R)(alpha)$ iff $g alpha' in cal(R)$, and in that case, $ integral_a^b g dif alpha = integral_a^b g(x) alpha'(x) dif x $
- *Remark*: when $g = 1$, this says $integral_a^b 1 dif alpha = alpha(b) - alpha(a) = integral alpha'(x) dif x$, similar to the fundamental theorem of calculus.

= Lebesgue spaces

== Normed linear spaces

- *Definition*: let $X$ be *complex linear space* (vector space over $CC$). $norm(dot.op): X -> RR_(>=0)$ is *norm on $X$* if
    - $forall x in X, norm(x) = 0 <==> x = 0$.
    - $forall x in X, forall lambda in CC, norm(lambda x) = |lambda| norm(x)$.
    - $forall x, y in X, norm(x + y) <= norm(x) + norm(y)$.
    $X$ equipped with norm $norm(dot.op)$, $(X, norm(dot.op))$, is called *complex normed linear space*.
- *Example*:
    - $norm(x) = sqrt(x overline(x))$ is norm on $CC$.
    - Let $C[a, b]$ denote linear space of continuous real-valued functions on $[a, b]$. Then $ norm(f)_max := max{|f(x)|: x in [a, b]} $ is norm on $C[a, b]$.
- *Proposition*: norm induces metric on $X$: $d(x, y) = norm(x - y)$.
- *Definition*: let $(X, norm(dot.op))$ be normed linear space.
    - Sequence $(f_n)$ in $X$ is *Cauchy sequence* in $X$ if $ forall epsilon > 0, exists N in NN: forall n, m >= N, quad norm(f_n - f_m) < epsilon $
    - Sequence $(f_n)$ in $X$ *converges in $X$*, $norm(f_n - f) -> 0$ as $n -> oo$, if $ exists f in X: forall epsilon > 0, exists N in NN: forall n >= N, quad norm(f_n - f) < epsilon $
    - $(X, norm(dot.op))$ is *complete* if every Cauchy sequence converges in $X$.
    - *Banach space* is complete normed linear space.
- *Proposition*: let $(X, norm(dot.op))$ be normed linear space.
    - If $(x_n)$ converges in $X$, $(x_n)$ is Cauchy sequence in $X$.
    - Let $(x_n)$ be Cauchy sequence in $X$. If $(x_n)$ has convergent subsequence in $X$ then $(x_n)$ converges in $X$.

== Lebesgue spaces $L^p$, $p in lr([1, oo))$

- *Definition*: let $p in lr([1, oo))$, $E subset.eq RR$.
    - Linear space $L^p (E)$ is defined as $ L^p (E) := {f: E -> CC: f "is measurable and" integral_E |f|^p < oo} \/ tilde.equiv $ where $f tilde.equiv g$ iff $f = g$ almost everywhere: $ f tilde.equiv g <==> exists F subset.eq E: mu(F) = 0 and forall x in E - F, f(x) = g(x) $
    - Define $norm(dot.op)_(L^p): L^p (E) -> RR$ as $ norm(f)_(L^p) := (integral_E |f|^p)^(1\/p) $
- *Remark*:
    - We often consider space $L^p (E)$ of real-valued measurable functions $f: E -> RR$ such that $integral_E |f|^p < oo$.
    - For $f: E -> CC$, $f = f_1 + i f_2$, $f$ is measurable iff $f_1: E -> RR$ and $f_2: E -> RR$ are measurable. Also, $ integral_E |f|^p < oo <==> (integral_E |f_1|^p < oo and integral_E |f_2|^p < oo) $
- *Example*: let $E = RR$, $f(x) = indicator(RR - QQ)(x) + i indicator(QQ)(x)$ and $g(x) = 1$. Then $mu(QQ) = 0$ so $f tilde.equiv g$.
- *Proposition*: let $(f_n), (g_n)$ sequences of measurable functions, $forall n in NN, f_n tilde.equiv g_n$, $lim_(n -> oo) f_n = f$ and $lim_(n -> oo) g_n = g$. Then $f tilde.equiv g$.
- *Definition*: $p, q in RR$ are *conjugate exponents* if $p > 1$ and $1/p + 1/q = 1$.
- *Lemma (Young's inequality)*: let $p, q$ conjugate exponents, then $ forall A, B in RR_(>=0), quad A B <= A^p / p + B^q / q $ with equality iff $A^p = B^q$.
- *Lemma (Hölder's inequality)*: let $p, q$ conjugate exponents. If $f in L^p (E)$, $g in L^q (E)$, then $ integral_E |f g| <= norm(f)_(L^p) norm(g)_(L^q) $
- *Corollary (Cauchy-Schwarz inequality for $L^2 (E)$)*: if $f, g in L^2 (E)$, then $ abs(integral_E f overline(g)) <= integral_E |f g| <= norm(f)_(L^2) norm(g)_(L^2) $
- *Lemma (Minkowski's inequality)*: let $p in lr([1, oo))$. If $f, g in L^p (E)$ then $f + g in L^p (E)$ and $ norm(f + g)_(L^p) <= norm(f)_(L^p) + norm(g)_(L^p) $
- *Theorem*: for $p in lr([1, oo))$, $\(L^p (E), norm(dot.op)_(L^p)\)$ is normed linear space.
- *Proposition*: let $1 <= p < q < oo$. If $mu(E) < oo$ then $L^q (E) subset.eq L^p (E)$ and $ norm(f)_(L^p) <= mu(E)^(1/p - 1/q) norm(f)_(L^q) $
- *Remark*:
    - Convergence in $L^p$ is also called convergence in the mean of order $p$.
    - This notion of convergence is different to pointwise convergence, uniform convergence and convergence in measure.
- *Riesz-Fischer theorem*: for $p in lr([1, oo))$, $\(L^p (E), norm(dot.op)_(L^p)\)$ is complete.

== Lebesgue space $L^oo$

- *Definition*:
    - Let $f: E -> CC$ measurable. $f$ is *essentially bounded* if $ exists M >= 0: |f(x)| <= M quad "almost everywhere on" E $
    - $L^oo (E)$ is collection of equivalence classes of essentially bounded functions where $f tilde.equiv g$ iff $f = g$ almost everywhere.
    - For $f in L^oo (E)$, define $ norm(f)_(L^oo) := "ess" sup |f| := inf{M in RR: mu({x in E: |f(x)| > M}) = 0} $
- *Proposition*:
    - $0 <= |f(x)| <= norm(f)_(L^oo)$ almost everywhere.
    - $norm(f)_(L^oo)$ is norm on $L^oo (E)$.
    - If $f in L^1 (E)$, $g in L^oo (E)$, then $ integral_E |f g| <= norm(f)_(L^1) norm(g)_(L^oo) $
- *Proposition*: let $(f_n)$ sequence of functions in $L^oo (E)$. Then $(f_n)$ converges to $f in L^oo (E)$ iff there exists $G subset.eq E$ with $mu(G) = 0$ and $(f_n)$ converges to $f$ uniformly on $E - G$.
- *Theorem*: $\(L^oo (E), norm(dot.op)_(L^oo)\)$ is complete.
- *Remark*: if $mu(E) < oo$, then $L^oo (E) subset L^p (E)$ for $p in lr([1, oo))$ and $ norm(f)_(L^p) <= mu(E)^(1\/p) norm(f)_(L^oo) $ since $ norm(f)_(L^p)^p = integral_E |f|^p <= integral_E norm(f)_(L^oo)^p dot.op indicator(E) = norm(f)_(L^oo)^p mu(E) $

== Approximation and separability

- *Definition*: let $(X, norm(dot.op))$ be normed linear space. Let $F subset.eq G subset.eq X$. $F$ is *dense in $G$* if $ forall g in G, forall epsilon > 0, exists f in F: quad norm(f - g) < epsilon $
- *Proposition*:
    - $F$ is dense in $G$ iff for every $g in G$, there exists sequence $(f_n)$ in $F$ such that $lim_(n -> oo) f_n = g$ in $X$.
    - For $F subset.eq G subset.eq H subset.eq X$, if $F$ dense in $G$ and $G$ dense in $H$, then $F$ dense in $H$.
- *Proposition*: let $p in [1, oo]$. Then subspace of simple functions in $\(L^p (E), norm(dot.op)_(L^p)\)$ is dense in $\(L^p (E), norm(dot.op)_(L^p)\)$.
- *Definition*: $psi: RR -> RR$ is *step function* if it can be written as $ psi = sum_(k = 1)^N tilde(a)_k indicator((a_k, b_k)) $ where the intervals $(a_k, b_k)$ are disjoint.
- *Proposition*: let $[a, b]$ be bounded, $p in [1, oo)$. Then subspace of step functions on $[a, b]$ is dense in $\(L^p ([a, b]), norm(dot.op)_(L^p)\)$.
- *Definition*: normed linear space $(X, norm(dot.op))$ is *separable* if there exists countable, dense subset $X' subset.eq X$.
- *Example*: $RR$ is separable, since $QQ$ is countable and dense in $RR$.
- *Theorem*: let $E subset.eq RR$ measurable, $p in [1, oo)$. Then $\(L^p (E), norm(dot.op)_(L^p)\)$ is separable.
- *Proposition*: let $epsilon > 0$, $f in L^p (E)$, $p in [1, oo)$. There exists continuous $g in L^p (E)$ such that $norm(f - g)_(L^p) < epsilon$.
- *Remark*: linear space of continuous functions that vanish outside bounded set is dense in $\(L^p (E), norm(dot.op)_(L^p)\)$ for $p in [1, oo)$.
- *Remark*: differentiable functions are also dense in $\(L^p (E), norm(dot.op)_(L^p)\)$ for $p in [1, oo)$.
- *Remark*: step functions and continuous functions are not dense in $\(L^oo (E), norm(dot.op)_(L^oo)\)$.
- *Example*: in general, $\(L^oo (E), norm(dot.op)_(L^oo)\)$ is not separable. Let $[a, b]$ be bounded, $a != b$. Assume there is countable ${f_n: n in NN}$ which is dense in $\(L^oo ([a, b]), norm(dot.op)_(L^oo)\)$. Then for every $x in [a, b]$, can choose $g(x) in NN$ such that $ norm(indicator([a, x]) - f_(g(x)))_(L^oo) < 1/2 $ Also, $ norm(indicator([a, x_1]) - indicator([a, x_2]))_(L^oo) = cases(1 & quad "if" a <= x_1 < x_2 <= b, 0 & quad "if" x_1 = x_2) $ and $ norm(indicator([a, x_1]) - indicator([a, x_2]))_(L^oo) & <= norm(indicator([a, x_1]) - f_(g(x_1)))_(L^oo) + norm(f_(g(x_1)) - f_(g(x_2)))_(L^oo) + norm(f_(g(x_2)) - indicator([a, x_2]))_(L^oo) \ & < 1 + norm(f_(g(x_1)) - f_(g(x_2)))_(L^oo) $ If $g(x_1) = g(x_2)$ then $norm(indicator([a, x_1]) - indicator([a, x_2]))_(L^oo) = 0$ so $g: [a, b] -> NN$ is injective. But $NN$ is countable and $[a, b]$ is not countable: contradiction.

== Riesz representation theorem for $L^p (E)$, $p in [1, oo)$

- *Definition*: let $X$ be linear space. $T: X -> RR$ is *linear functional* if $ forall f, g in X, forall a, b in RR, quad T(a f + b g) = a T(f) + b T(g) $ Any linear combination of linear functionals is linear, so set of linear functionals on linear space is also linear space.
- *Definition*: let $(X, norm(dot.op))$ be normed linear space. $T: X -> RR$ is *bounded functional* if $ exists M >= 0: forall f in X, quad |T(f)| <= M norm(f) $ *Norm* of $T$, $norm(T)_*$, is the smallest such $M$.
- *Remark*: for bounded linear functional $T$ on normed linear space $(X, norm(dot.op))$, $ |T(f) - T(g)| <= norm(T)_* norm(f - g) $ This gives the following continuity property: if $f_n -> f in X$, then $T(f_n) -> T(f)$.
- *Example*: let $E subset.eq RR$ measurable, $p in [1, oo)$, $q$ conjugate to $p$. Let $h in L^q (E)$. Define $T: L^p (E) -> RR$ by $ T(f) = integral_E h dot.op f $ By Holder's inequality, $ |T(f)| = abs(integral_E h f) <= integral_E abs(h f) <= norm(h)_(L^q) norm(f)_(L^p) $ So $T$ is bounded linear functional.