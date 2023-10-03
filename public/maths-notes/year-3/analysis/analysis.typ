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

== Open and closed sets

- $U subset.eq RR$ is *open* if $ forall x in U, exists epsilon: (x - epsilon, x + epsilon) subset.eq U $
- Arbitrary unions of open sets are open.
- Finite intersections of open sets are open.
- $x in E subset.eq RR$ is *point of closure* if $ forall delta > 0, exists y in E: |x - y| < delta $ Equivalently, $x$ is point of closure if every open interval containing $x$ contains another point of $E$.
- *Closure* of $E$, $overline(E)$, is set of points of closure.
- If $A subset B subset.eq RR$ then $overline(A) subset overline(B)$. *Exercise (todo)*: prove this.
- $overline(A union B) = overline(A) union overline(B)$.

= Further analysis of subsets of $RR$

TODO: up to here, check that all notes are made from these topics

== Countability and uncountability

- $A$ is *countable* if $A = nothing$, $A$ is finite or there is a bijection $phi: NN -> A$ (in which case $A$ is *countably infinite*). Otherwise $A$ is *uncountable*. $phi$ is called an *enumeration*.
- Examples of countable sets:
    - $NN$ ($phi(n) = n$)
    - $2 NN$ ($phi(n) = 2n$)
- *Exercise (todo)*: show that any subset of $NN$ is countable.
- *Exercise (todo)*: show that if there is an injection from $A$ to $NN$, or if there is a surjection from $NN$ to $A$, then $A$ is countable.
- $QQ$ is countable.
- *Exercise (todo)*: show that $NN^k$ is countable for any $k in NN$.
- *Exercise (todo)*: show that if $a_n$ is a nonnegative sequence and $phi: NN -> NN$ is a bijection then $ sum_(n = 1)^infinity a_n = sum_(n = 1)^infinity a_(phi(n)) $
- *Exercise (todo)*: show that if $a_(n, k)$ is a nonnegative sequence and $phi: NN times NN -> NN$ is a bijection then $ sum_(n = 1)^infinity sum_(n = 1)^infinity a_(n, k) = sum_(n = 1)^infinity a_(phi(n)) $
- $f: X -> Y$ is *monotone* if $x >= y => f(x) >= f(y)$ or $x <= y => f(x) >= f(y)$.
- Let $f$ be monotone on $(a, b)$. Then it is discountinuous on a countable set.
- Set of sequences in ${0, 1}$, $\{((x_n))_(n in NN): forall n in NN, x_n in {0, 1}\}$ is uncountable.
- $RR$ is uncountable.

TODO: problem sheet one