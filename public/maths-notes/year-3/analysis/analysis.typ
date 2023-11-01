#import "../../template.typ": template
#show: template

== Integration and measure

- Dirichlet's function: $f: [0, 1] -> RR$, $ f(x) = cases(1 & " if" x in QQ, 0 & " otherwise") $

= The real numbers

- $a in RR$ is an *upper bound* of $E subset.eq RR$ if $forall x in E, x <= a$.
- $c in RR$ is a *least upper bound (supremum)* if $c <= a$ for every upper bound $a$.
- $a in RR$ is an *lower bound* of $E subset.eq RR$ if $forall x in E, x >= a$.
- $c in RR$ is a *greatest lower bound (supremum)* if $c >= a$ for every upper bound $a$.
- *Completeness axiom of the real numbers*: every subset $E$ with an upper bound has a least upper bound. Every subset $E$ with a lower bound has a greatest lower bound.
- *Archimedes' principle*: $ forall x in RR, exists n in NN: n > x $
- Every non-empty subset of $NN$ has a minimum.
- *The rationals are dense in the reals*: $ forall x < y in RR, exists r in QQ: r in (x, y) $

== Conventions on sets and functions

- For $f: X -> Y$, *preiamge* of $Z subset.eq Y$ is $ f^(-1) (Z) := {x in X: f(x) in Z} $
- $f: X -> Y$ *injective* if $ forall y in f(X), exists! x in X: y = f(x) $
- $f: X -> Y$ *surjective* if $Y = f(X)$.
- *Limit inferior* of sequence $x_n$: $ liminf_(n -> oo) x_n := lim_(n -> oo) (inf_(m >= n) x_m) = sup_(n >= 0) inf_(m >= n) x_m $
- *Limit superior* of sequence $x_n$: $ limsup_(n -> oo) x_n := lim_(n -> oo) (sup_(m >= n) x_m) = inf_(n >= 0) sup_(m >= n) x_m $

== Open and closed sets

- $U subset.eq RR$ is *open* if $ forall x in U, exists epsilon: (x - epsilon, x + epsilon) subset.eq U $
- Arbitrary unions of open sets are open.
- Finite intersections of open sets are open.
- $x in RR$ is *point of closure (limit point)* for $E subset.eq RR$ if $ forall delta > 0, exists y in E: |x - y| < delta $ Equivalently, $x$ is point of closure if every open interval containing $x$ contains another point of $E$.
- *Closure* of $E$, $overline(E)$, is set of points of closure.
- $F$ is *closed* if $F = overline(F)$.
- If $A subset B subset.eq RR$ then $overline(A) subset overline(B)$.
- $overline(A union B) = overline(A) union overline(B)$.
- For any set $E$, $overline(E)$ is closed.
- Let $E subset.eq RR$. The following are equivalent:
    - $E$ is closed.
    - $RR - E$ is open.
- Arbitrary intersections of closed sets are closed. Finite unions of closed sets are closed.
- *Definition*: collection $C$ of subsets of $RR$ *covers* (is a *covering* of) $F subset.eq RR$ if $F subset.eq union_(S in C) S$. If each $S$ in $C$ open, $G$ is *open covering*. If $C$ is finite, $C$ is *finite cover*.
- Covering $C$ of $F$ *contains a finite subcover* if exists ${S_1, ..., S_n} subset.eq C$ with $F subset.eq union_(i = 1)^n S_i$ (i.e. a finite subset of $C$ covers $F$). $F$ is *compact* if any open covering $U$ contains a finite subcover.
- *Example*: $RR$ is not compact, $[a, b]$ is compact.
- *Heine-Borel theorem*: if $F subset RR$ closed and bounded then any open covering of $F$ has finite subcovering (so $F$ is compact). If $F$ compact then $F$ closed and bounded.

== The extended real numbers

- *Definition*: *extended reals* are $RR union {-oo, oo}$ with the order relation $-oo < oo$ and $forall x in RR, -oo < x < oo$. $oo$ is an upper bound and $-oo$ is a lower bound for every $x in RR$, so $sup(RR) = oo$, $inf(RR) = -oo$.
    - Addition: $forall a in RR, a + oo = oo and a + (-oo) = -oo$. $oo + oo = oo - (-oo) = oo$. $oo - oo$ is undefined.
    - Multiplication: $forall a in RR_(>0), a dot.op oo = oo$, $forall a in RR_(<0), a dot.op = -oo$. $oo dot.op oo = oo$ and $0 dot.op oo = oo$.
    - $limsup$ and $liminf$ are defined as $ limsup x_n := inf_(n in NN) {sup_(k >= n) x_k}, quad liminf x_n := sup_(n in NN) {inf_(k >= n) x_k} $
- *Definition*: extended real number $l$ is *limit* of $(x_n)$ if either
    - $forall epsilon > 0, exists N in NN: forall n >= N, |x_n - l| < epsilon$. Then $(x_n)$ *converges to $l$*. or
    - $forall Delta > 0, exists N in NN: forall n >= N, x_n > Delta$ (limit is $oo$) or
    - $forall Delta > 0, exists N in NN: forall n >= N, x_n < -Delta$ (limit is $-oo$).
    $(x_n)$ *converges in the extended reals* if it has a limit in the extended reals.

= Further analysis of subsets of $RR$

TODO: up to here, check that all notes are made from these topics

== Countability and uncountability

- $A$ is *countable* if $A = nothing$, $A$ is finite or there is a bijection $phi: NN -> A$ (in which case $A$ is *countably infinite*). Otherwise $A$ is *uncountable*. $phi$ is called an *enumeration*.
- If surjection from $NN$ to $A$, or injection from $A$ to $NN$, then $A$ is countable.
- Examples of countable sets:
    - $NN$ ($phi(n) = n$)
    - $2 NN$ ($phi(n) = 2n$)
- $QQ$ is countable.
- *Exercise (todo)*: show that $NN^k$ is countable for any $k in NN$.
- *Exercise (todo)*: show that if $a_n$ is a nonnegative sequence and $phi: NN -> NN$ is a bijection then $ sum_(n = 1)^infinity a_n = sum_(n = 1)^infinity a_(phi(n)) $
- *Exercise (todo)*: show that if $a_(n, k)$ is a nonnegative sequence and $phi: NN times NN -> NN$ is a bijection then $ sum_(n = 1)^infinity sum_(n = 1)^infinity a_(n, k) = sum_(n = 1)^infinity a_(phi(n)) $
- $f: X -> Y$ is *monotone* if $x >= y => f(x) >= f(y)$ or $x <= y => f(x) >= f(y)$.
- Let $f$ be monotone on $(a, b)$. Then it is discountinuous on a countable set.
- Set of sequences in ${0, 1}$, $\{((x_n))_(n in NN): forall n in NN, x_n in {0, 1}\}$ is uncountable.
- *Theorem*: $RR$ is uncountable.

== The structure theorem for open sets

- Collection ${A_i: i in I}$ of sets is *(pairwise) disjoint* if $n != m ==> A_n sect A_m = nothing$.
- *Structure theorem for open sets*: let $U subset.eq RR$ open. Then exists countable collection of disjoint open intervals ${I_n: n in NN}$ such that $U = union_(n in NN) I_n$.

== Accumulation points and perfect sets

- $x in RR$ is *accumulation point* of $E subset.eq RR$ if $x$ is point of closure of $E - {x}$. Equivalently, $x$ is a point of closure if $ forall delta > 0, exists y in E: y != x and |x - y| < delta $ Equivalently, there exists a sequence of distinct $y_n in E$ with $y_n -> x$ as $n -> oo$.
- *Exercise*: set of accumulation points of $QQ$ is $RR$.
- $E subset.eq RR$ is *isolated* if $ forall x in E, exists epsilon > 0: (x - epsilon, x + epsilon) sect E = {x} $
- *Proposition*: set of accumulation points $E'$ of $E$ is closed.
- Bounded set $E$ is *perfect* if it equals its set of accumulation points.
- *Exercise (todo)*: what is the set of accumulation points of an isolated set?
- Every non-empty perfect set is uncountable.

== The middle-third Cantor set

- *Middle third Cantor set*:
    - Define $C_0 := [0, 1]$
    - Given $C_n = union_(i = 1)^(2^n) [a_i, b_i]$, $a_i < b_1 < a_2 < dots.h.c$, with $|b_i - a_i| = 3^(-n)$, define $ C_(n + 1) := union_(i = 1)^(2^n) [a_i, a_i + 3^(-(n + 1))] union [b_i - 3^(-(n + 1)), b_i] $ which is a union of $2^(n + 1)$ disjoint intervals, with difference in endpoints equalling $3^(-(n + 1))$.
    - The *middle third Cantor set* is $ C := union.big_(n in NN) C_n $ Observe that if $a$ is an endpoint of an interval in $C_n$, it is contained in $C$.
- *Proposition*: the middle third Cantor set is closed, non-empty and equal to its set of accumulation points. Hence it is perfect and uncountable.

== $G_s, F_sigma$

- Set $E$ is *$G_delta$* if $E = sect_(n in NN) U_n$ with $U_n$ open.
- Set $E$ is *$F_sigma$* if $E = union_(n in NN) F_n$ with $F_n$ closed.
- *Lemma*: set of points where $f: RR -> RR$ is continuous is $G_delta$.

= Construction of Lebesgue measure

== Lebesgue outer measure

- *Definition*: let $I$ non-empty interval with endpoints $a = inf(I) in {-oo} union RR$ and $b = sup(I) in RR union {oo}$. The *length* of $I$ is $ ell(I) := b - a $ and set $ell(nothing) = 0$.
- *Example*: if $I = lr((-oo, b]) = lr((-oo, a]) union [a, b]$ then $ell(I) = oo = ell(lr(-oo, a])) + ell([a, b])$
- *Definition*: let $A subset.eq RR$. *Lebesgue outer measure* of $A$ is infimum of all sums of lengths of intervals covering $A$: $ mu^*(A) := inf{sum_(k = 1)^oo ell(I_k): A subset.eq union.big_(k = 1)^oo I_k, I_k "intervals"} $ It satisfies *monotonicity*: $A subset.eq B ==> mu^*(A) <= mu^*(B)$.
- *Proposition*: outer measure is *countably subadditive*: if ${E_k}_(k = 1)^oo$ is any countable collection of sets then $ mu^*(union.big_(k = 1)^oo E_k) <= sum_(k = 1)^oo mu^*(E_k) $
- *Lemma*: we have $ mu^*(A) = inf{sum_(k = 1)^oo ell(I_k): A subset union.big_(k = 1)^oo I_k, I_k != nothing "open intervals"} $
- Lebesgue outer measure of interval is its length: $mu^*(I) = ell(I)$.

== Measurable sets

- *Notation*: $E^c = RR - E$.
- *Proposition*: let $E = (a, oo)$. Then $ forall A subset.eq RR, quad mu^*(A sect E) + mu^*(A sect E^c) $
- *Definition*: $E subset.eq RR$ is *Lebesgue measurable* if $ forall A subset.eq RR, mu^*(A) = mu^*(A sect E) + mu^*(A sect E^c) $ Collection of such sets is $cal(F)_(mu^*)$.
- *Lemma (excision property)*: let $E$ Lebesgue measurable set with finite measure and $E subset.eq B$, then $ mu^*(B - E) = mu^*(B) - mu^*(E) $
- *Remark*: not every set is Lebesgue measurable.
- *Definition*: collection of subsets of $RR$ is an *algebra* if contains $nothing$ and closed under taking complements and finite unions: if $A, B in cal(A)$ then $RR - A, A union B in cal(A)$.
- *Remark*: if a union of a countable collection of Lebesgue measurable sets is also the union of a countable disjoint collection of Lebesgue measurable sets: if ${A_k}_(k = 1)^oo$ is countable collection of Lebesgue measurable sets, then let $A_1' = A_1$ and for $k > 1$, define $ A_k' = A_k - union_(i = 1)^(k - 1) A_i $ then ${A_k'}_(k = 1)^oo$ is disjoint union of Lebesgue measurable sets.
- *Proposition*: if $E_1, ..., E_n$ Lebesgue measurable then $union_(k = 1)^n E_k$ is Lebesgue measurable. If $E_1, ..., E_n$ disjoint then $ mu^*(A sect union.big_(k = 1)^n E_k) = sum_(k = 1)^n mu^*(A sect E_k) $ for any $A subset.eq RR$. In particular, for $A = RR$, $ mu^*(union.big_(k = 1)^n E_k) = sum_(k = 1)^n mu^*(E_k) $
- *Proposition*: if $E$ is countable union of Lebesgue measurable sets, then $E$ is Lebesgue measurable. Also, if ${E_k}_(k in NN)$ is countable disjoint collection of Lebesgue measurable sets then $ mu^* (union.big_(k = 1)^oo E_k) = sum_(k = 1)^oo mu^* (E_k) $

== Abstract definition of a measure

- *Definition*: let $X subset.eq RR$. Collection of subsets of $cal(F)$ of $X$ is *$sigma$-algebra* if
    - $nothing in F$
    - $E in F ==> E^c in F$
    - $E_1, ..., E_n in F ==> union_(k = 1)^oo E_k in cal(F)$.
- *Example*:
    - Trivial examples are $cal(F) = {nothing, RR}$ and $cal(F) = cal(P)(RR)$.
    - Arbitrary intersections of $sigma$-algebras are $sigma$-algebras.
- *Definition*: let $cal(F)$ $sigma$-algebra of $X$. $nu: cal(F) -> RR union {plus.minus oo}$ is *measure* satisfying
    - $nu(nothing) = 0$
    - $forall E in cal(F), nu(E) >= 0$
    - *Countable additivity*: if $E_1, E_2, ... in cal(F)$ are disjoint then $ nu(union.big_(k = 1)^oo E_k) = sum_(k = 1)^oo nu(E_k) $
    Elements of $cal(F)$ are *measurable* (as they are the only sets on which the measure $nu$ is defined).
- *Proposition*: if $nu$ is measure then it satisfies:
    - *Monotonicity*: $A subset.eq B ==> nu(A) <= nu(B)$.
    - *Countable subadditivity*: $nu(union_(k in NN) E_k) <= sum_(k in NN) nu(E_k)$.
    - *Excision*: if $A$ has finite measure, then $A subset.eq B ==> m(B - A) = m(B) - m(A)$.

== Lebesgue measure

- *Lemma*: the Lebesgue measurable sets form a $sigma$-algebra and contain every interval.
- *Theorem (Caratheodory extension)*: the restriction of the outer measure $mu^*$ to the $sigma$-algebra of Lebesgue measurable sets is a measure.
- *Definition*: the measure $mu$ of $mu^*$ restricted to $cal(F)_(mu^*)$ is the *Lebesgue measure*. It satisfies $mu(I) = ell(I)$ for any interval $I$ and is translation invariant.
- *Hahn extension theorem*: there exists unique measure $mu$ defined on $cal(F)_(mu^*)$ for which $mu(I) = ell(I)$ for any interval $I$.

== Sets of measure $0$

- *Exercise (todo)*: middle-third Cantor set is Lebesgue measurable and has Lebesgue measure $0$.
- *Exercise (todo)*: any countable set is Lebesgue measurable and has Lebesgue measure $0$.
- *Exercise (todo)*: any $E$ with $mu^*(E) = 0$ is Lebesgue measurable and has $mu(E) = 0$.
- *Lemma*: let $E$ Lebesgue measurable set with $mu(E) = 0$, then $forall E' subset.eq E$, $E'$ is Lebesgue measurable.

== An approximation result for Lebesgue measure

- *Definition*: *Borel $sigma$-algebra* $cal(B)(RR)$ is smallest $sigma$-algebra containing all intervals: for any other $sigma$-algebra $cal(F)$ containing all intervals, $cal(B)(RR) subset cal(F)$. $ cal(B)(RR) = sect.big {cal(F): cal(F) " " sigma "-algebra containing all intervals"} $ $E in cal(B)(RR)$ is *Borel* or *Borel measurable*.
- Every open subset of $RR$, every closed subset of $RR$, every $G_delta$ set, every $F_sigma$ set is Borel.
- *Proposition*: the following are equivalent:
    - $E$ is Lebesgue measurable
    - $forall epsilon > 0, exists "open" G: E subset.eq G and mu^*(G - E) < epsilon$
    - $forall epsilon > 0, exists "closed" F: F subset.eq E and mu^*(E - F) < epsilon$
    - $exists G in G_delta: E subset.eq G and mu^*(G - E) = 0$
    - $exists F in F_sigma: F subset.eq E and mu^*(E - F) = 0$

= Measurable functions

== Definition of a measurable function

- *Lemma*: let $f: E -> RR union {plus.minus oo}$ with $E$ Lebesgue measurable. The following are equivalent:
    - $forall c in RR, {x in E: f(x) > c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) >= c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) < c}$ is Lebesgue measurable.
    - $forall c in RR, {x in E: f(x) <= c}$ is Lebesgue measurable.
- *Definition*: $f: E -> RR$ is *(Lebesgue) measurable* if it satisfies any one of the above properties.