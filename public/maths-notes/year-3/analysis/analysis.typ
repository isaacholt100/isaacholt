#import "../../template.typ": template
#show: template

#let indicator(arg) = $bb(1)_arg$

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
- *Definition*: $f: E -> RR$ is *bi-Lipschitz* if $ exists C > 0: forall x, y in E, quad C^(-1)|x - y| <= |f(x) - f(y)| <= C|x - y| $

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

- *Proposition*: let ${F_n: n in N}$ be collection of non-empty nested closed sets, one of which is bounded, so $F_(n + 1) subset.eq F_n$. Then $ sect.big_(n in NN) F_n != emptyset $
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

== Continuity of measure

- *Definition*: countable collection ${E_k}_(k = 1)^oo$ is *ascending* if $forall k in NN, E_k subset.eq E_(k + 1)$ and *descending* if $forall k in NN, E_(k + 1) subset.eq E_k$.
- *Theorem*: every measure $m$ satisfies:
    - If ${A_k}_(k = 1)^oo$ is ascending collection of measurable sets, then $ m(union.big_(k = 1)^oo A_k) = lim_(k -> oo) m(A_k) $
    - If ${B_k}_(k = 1)^oo$ is descending collection of measurable sets and $m(B_1) < oo$, then $ m(sect.big_(k = 1)^oo B_k) = lim_(k -> oo) m(B_k) $

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
- *Definition*: $f: E -> RR$ is *(Lebesgue) measurable* if it satisfies any one of the above properties and if $E$ is Lebesgue measurable.
- *Proposition*: let $f: RR -> RR$. $f$ continuous iff $forall "open" U subset.eq, f^(-1)(U) subset.eq RR$ is open.
- *Definition*: *indicator function* on set $A$, $bb(1)_A: RR -> {0, 1}$ is $ bb(1)_A (x) := cases(1 & "if" x in A, 0 & "if" x in.not A) $
- *Definition*: $phi: RR -> RR$ is *simple (measurable) function* if $phi$ is measurable function that has finite codomain.
- *Definition*: sequence of functions $(f_n)$ with domain $E$ *converge in measure* to $f$ if $ forall epsilon > 0, quad mu({x in E: |f_n (x) - f(x)| > epsilon}) -> 0 "as" n -> oo $

== Fundamental aspects of measurable functions

- *Definition*: let $E subset.eq F subset.eq RR$, let $f: F -> RR$. *Restriction* $f_E$ is function with domain $E$ and for which $forall x in E, f_E (x) = f(x)$.
- *Definition*: real-valued function which is increasing or decreasing is *monotone*.
- *Definition*: sequence $(f_n)$ on domain $E$ is increasing if $f_n <= f_(n + 1)$ on $E$ for all $n in NN$.
- *Example*: continuous functions are measurable.
- *Definition*: for $f_1: E -> RR, ..., f_n: E -> RR$, $max {f_1, ..., f_n}: E -> RR$ is $ max{f_1, ..., f_n}(x) = max{f_1 (x), ..., f_n (x)} $ $min{f_1, ..., f_n}$ is defined similarly.
- *Proposition*: for finite family ${f_k}_(k = 1)^n$ of measurable functions with common domain $E$, $max{f_1, ..., f_n}$ and $min{f_1, ..., f_n}$ are measurable.
- *Definition*: for $f: E -> RR$, functions $|f|, f^+, f^-$ defined on $E$ are $ |f|(x) := max{f(x), -f(x)}, quad f^+ (x) := max{f(x), 0}, quad f^- (x) := max{-f(x), 0} $
- *Corollary*: if $f$ measurable on $E$, so are $|f|$, $f^+$ and $f^-$.
- *Proposition*: let $f: E -> RR union {plus.minus oo}$. For measurable $D subset.eq E$, $f$ measurable on $E$ iff restrictions of $f$ to $D$ and $E - D$ are measurable.
- *Theorem*: let $f, g$ real-valued measurable functions with domain $E$.
    - *Linearity*: $forall alpha, beta in RR, alpha f + beta g$ is measurable.
    - *Products*: $f g$ is measurable.
- *Proposition*: let $(f_n)$ be sequence of measurable functions on $E$ that converges pointwise to $f$ on $E$. Then $f$ is measurable.
- *Simple approximation lemma*: let $f: E -> RR$ measurable and bounded, so $exists M >= 0: forall x in E, |f|(x) < M$. Then $forall epsilon > 0$, there exist simple measurable functions $phi_epsilon, psi_epsilon: E -> RR$ such that $ forall x in E, phi_epsilon (x) <= f(x) <= psi_epsilon (x) and 0 <= psi_epsilon (x) - phi_epsilon (x) < epsilon $
- *Definition*: let $f, g: E -> RR union {plus.minus oo}$. Then $f = g$ *almost everywhere* if ${x in E: f(x) != g(x)}$ has measure $0$.
- *Proposition*: let $f_1, f_2, f_3: E -> RR union {plus.minus oo}$ measurable. If $f_1 = f_2$ almost everywhere and $f_2 = f_3$ almost everywhere then $f_1 = f_3$ almost everywhere.
- Let $f, g: E -> RR union {plus.minus oo}$ finite almost everywhere on $E$. Let $D_f$ and $D_g$ be sets for which $f$ and $g$ are finite. Then $f + g$ is finite and well-defined on $D_f sect D_g$ and complement of $D_f sect D_g$ has measure $0$.
- *Remark*: Lebesgue measurable functions can be modified arbitrarily on a set of measure $0$ without affecting measurability.
- *Simple approximation theorem*: let $f: E -> RR union {plus.minus oo}$, $E$ measurable. Then $f$ is measurable iff there exists sequence $(phi_n)$ of simple functions on $E$ which converge pointwise on $E$ to $f$ and satisfy $ forall n in NN, forall x in E, |phi_n (x)| <= |f|(x) $ If $f$ is nonnegative, $(phi_n)$ can be chosen to be increasing.

= The Lebesgue integral

== The integral of a simple measurable function

- *Definition*: let $phi$ be real-valued function taking finitely many values $alpha_1 < dots.h.c < alpha_n$, then *standard representation* of $phi$ is $ phi = sum_(i = 1)^n alpha bb(1)_(A_i), quad A_i = phi^(-1)({alpha_i}) $
- *Lemma*: let $phi = sum_(i = 1)^m beta_i indicator(B_i)$, $B_i$ disjoint mesauble collection, $beta_i in RR$, then $phi$ is simple measurable. If $phi$ takes values $0$ outside a finite set then $ sum_(i = 1)^n alpha_i mu(A_i) = sum_(i = 1)^m beta_i mu(B_i) $ where $A_i$ in standard representation.
- *Definition*: let $phi$ be simple nonnegative measurable function. *Integral* of $phi$ with respect to $mu$ is $ integral phi = sum_(i = 1)^n alpha_i mu(A_i) $ where $phi = sum_(i = 1)^n alpha_i bb(1)_(A_i)$ is the standard representation. Here we use the convention $0 dot.op oo = 0$.
- *Example*:
    - Let $phi_2 = indicator([0, 2]) + indicator([1, 3]) = indicator(lr([0, 1) union lr((2, 3]))) + 2 indicator([1, 2])$ so $integral phi_2 = 4$.
    - Let $phi_3 = indicator(RR)$, then $integral phi_3 = 1 dot.op oo = oo$.
    - Let $phi_4 = bb(1)_((0, oo)) + (-1) indicator((-oo, 0))$. This can't be integrated.
    - Let $phi_5 = indicator((-1, 0)) + (-1) indicator((0, 1))$.
- *Lemma*: let $B_1, ..., B_m$ be collection of measurable sets, $beta_1, ..., beta_m in RR - {0}$. Then $phi = sum_(i = 1)^m beta_i indicator(B_i)$ is simple measurable function. If measurable of $union_(i = 1)^m B_i$ is finite, then $ sum_(i = 1)^n alpha_i mu(A_i) = sum_(i = 1)^m beta_i mu(B_i) $ where $A_i$ in standard representation.
- *Proposition (linearity and monotonicity of integration for simple funtions)*: let $phi, psi$ be simple measurable functions:
    - If $phi, psi$ take value $0$ outside a set of finite measure, then $forall alpha, beta in RR$, $ integral (alpha phi + beta psi) = alpha integral phi + beta integral psi $
    - $ 0 <= phi <= psi ==> 0 <= integral phi <= integral psi $
- *Corollary*: let $phi$ nonnegative simple function, then $ integral phi = sup{integral psi: 0 <= psi <= phi, thick psi "simple measurable"} $
- *Lemma*: let $phi$ simple measurable nonnegative function. $phi$ takes value $0$ outside a set of finite measure iff $integral phi < oo$. Also, $integral phi = oo$ iff there exist $alpha > 0$, measurable $A$ with $mu(A) = oo$ with $phi(x) >= alpha$ on $A$.
- *Lemma*: let ${E_n}$ be ascending collection of measurable sets, $union_(n = 1)^oo E_n = RR$. Let $phi$ be simple nonnegative measurable function. Then $ integral_(E_n) phi -> integral phi quad "as" n -> oo $

== The integral of a nonnegative function

- *Notation*: let $cal(M)^+$ denote collection of nonnegative measurable functions $f: RR -> RR_(>= 0) union {oo}$.
- *Definition*: *support* of measurable function $f$ with domain $E$ is ${x in E: f(x) != 0}$.
- *Definition*: let $f in cal(M)^+$. *Integral of $f$ with respect to $mu$* is $ integral f := sup{integral phi: 0 <= phi <= f, phi "simple measurable"} in RR union {oo} $ For measurable set $E$, define $ integral_E f := integral indicator(E) f $
- *Proposition*: let $f, g$ measurable. If $g <= f$ then $integral g <= integral f$. Let $E, F$ measurable. If $E subset.eq F$ then $integral_E f <= integral_F f$.
- *Monotone convergence theorem*: let $(f_n)$ be sequence in $cal(M)^+$. If $(f_n)$ is increasing on measurable set $E$ and converges pointwise to $f$ on $E$ then $ integral_E f_n -> integral_E f quad "as" n -> oo $
- *Corollary*: restriction of integral to nonnegative functions is linear: $forall f, g in cal(M)^+$, $forall alpha >= 0$, $ integral (f + g) & = integral f + integral g \ integral alpha f & = alpha integral f $
- *Fatou's lemma*: let $(f_n)$ be sequence in $cal(M)^+$, then $ integral liminf_(n -> oo) f_n <= liminf_(n -> oo) integral f_n $
- *Lemma*: let $(f_n) subset cal(M)^+$, then $ integral sum_(n = 1)^oo f_n = sum_(n = 1)^oo integral f_n $
- *Proposition (Chebyshev's inequality)*: let $f$ be nonnegative measurable function on $E$. Then $ forall lambda > 0, quad mu({x in E: f(x) >= lambda}) <= 1/lambda integral_E f $
- *Proposition*: let $f$ be nonnegative measurable function on $E$. Then $ integral_E f = 0 <==> f = 0 "almost everywhere on" E $

== Integration of measurable functions

- *Notation*: let $cal(M)$ denote set of measurable functions.
- *Definition*: $f in cal(M)^+$ is *integrable* if $integral f < oo$.
- *Definition*: let $f: RR -> RR union {plus.minus oo}$ measurable function. $f$ is *integrable* if $integral f^+$ and $integral f^-$ are finite. In this case, for any measurable set $E$, define $ integral_E f := integral_E f^+ - integral_E f^- $ If $f$ integrable then $f^+ - f^-$ is well-defined.
- *Definition*: $f in cal(M)$ is *integrable over $E$* ($E$ is measurable) if $integral_E f^+$ and $integral_E f^-$ are finite (i.e. $f dot.op indicator(E)$ is integrable).
- *Theorem*: $f in cal(M)$ is integrable iff $|f|$ is integrable. If $f$ integrable, then $ abs(integral f) <= integral abs(f) $
- *Corollary*: let $f, g in cal(M)$, $|f| <= |g|$. If $g$ integrable then $|f|$ is integrable, and $integral |f| <= integral |g|$.
- *Theorem (Linearity of Integration)*: let $f, g$ integrable. Then $f + g$ is integrable and $forall alpha in RR$, $alpha f$ is integrable. The integral is linear: $ integral (f + g) & = integral f + integral g \ integral alpha f & = alpha integral f $
- *Dominated Convergence Theorem*: let $(f_n)$ be sequence of integrable functions. If there exists an integrable $g$ with $forall n in NN, |f_n| <= g$, and $f_n -> f$ pointwise almost everywhere then $f$ is integrable and $ integral f = lim_(n -> oo) integral f_n $
- *Example*: $sin$ is not integrable over $RR$, but is integrable over $[0, 2pi]$, since $|f_([0, 2pi])| <= indicator([0, 2pi])$.