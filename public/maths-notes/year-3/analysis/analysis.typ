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