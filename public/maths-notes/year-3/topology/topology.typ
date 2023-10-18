#import "../../template.typ": template
#show: template

#let powset(X) = $cal(P)(X)$

= Metric spaces

== Metrics

- *Metric space*: $(X, d)$, $X$ is set, $d: X times X -> [0, infinity)$ is *metric* satisfying:
    - $d(x, y) = 0 <==> x = y$
    - *Symmetry*: $d(x, y) = d(y, x)$
    - *Triangle inequality*: $d(x, y) <= d(x, z) + d(z, y)$
- Examples of metrics:
    - $p$-adic metric: $ d_p (x, y) = (sum_(i = 1)^n |x_i - y_i|^p)^(1/p) $
    - Extension of the $p$-adic metric: $ d_infinity (x, y) = max{|x_i - y_i|: i in [n]} $
    - Metric of $C([a, b])$: $ d(f, g) = sup{|f(x) - g(x)|: x in [a, b]} $
    - Discrete metric: $ d(x, y) = cases(0 & "if" x = y, 1 & "if" x != y) $
- *Open ball of radius $r$ around $x$*: $ B(x; r) = {y in X: d(x, y) < r} $
- *Closed ball of radius $r$ around $x$*: $ D(x; r) = {y in X: d(x, y) <= r} $

== Open and closed sets

- $U subset.eq X$ is *open* if $ forall x in U, exists epsilon > 0: B(x; epsilon) subset U $
- $A subset.eq X$ is *closed* if $X - A$ is open.
- Sets can be neither closed nor open, or both.
- Any singleton ${x} in RR$ is closed and not open.
- Let $X$ be metric space, $x in N subset.eq X$. $N$ is *neighbourhood* of $x$ if $ exists "open " V subset.eq X: x in V subset.eq N $
- *Corollary*: let $x in X$, then $N subset.eq X$ neighbourhood of $x$ iff $exists epsilon > 0: x in B(x; epsilon) subset.eq N$.
- *Proposition*: open balls are open, closed balls are closed.
- *Lemma*: let $(X, d)$ metric space.
    - $X$ and $nothing$ are both open and closed.
    - Arbitrary unions of open sets are open.
    - Finite intersections of open sets are open.
    - Finite unions of closed sets are closed.
    - Arbitrary intersections of closed sets are closed.


== Continuity

- *Sequence* in $X$: $a: NN -> X$, written $(a_n)_(n in NN)$.
- $(a_n)$ converges to $a$ if $ forall epsilon > 0, exists n_0 in NN: forall n >= n_0, d(a, a_n) < epsilon $
- *Proposition*: let $X, Y$ metric spaces, $a in X$, $f: X -> Y$. The following are equivalent
    - $forall epsilon > 0, exists delta > 0: d_X (a, x) < delta ==> d_Y (f(a), f(x)) < epsilon$.
    - For every sequence $(a_n)$ in $X$ with $a_n -> a$, $f(a_n) -> f(a)$.
    - For every open $U subset.eq Y$ with $f(a) in U$, $f^(-1) (U)$ is a neighbourhood of $a$.
If $f$ satisfies these, it is *continuous at $a$*.
- $f$ *continuous* if continuous at every $a in X$.
- *Proposition*: $f: X -> Y$ continuous iff $f^(-1)(U)$ open for every open $U subset.eq Y$.

= Topological spaces

== Topologies

- *Power set* of $X$: $cal(P)(X) := {A: A subset.eq X}$.
- *Topology* on set $X$ is $tau subset.eq cal(P)(X)$ with:
    - $nothing in tau$, $X in tau$.
    - If $forall i in I, U_i in tau$, then $ union.big_(i in I) U_i in tau $
    - $U_1, U_2 in tau ==> U_1 sect U_2 in tau$ (this is equivalent to $U_1, ..., U_n in tau ==> sect_(i in [n]) U_i in tau$).
- $(X, tau)$ is *topological space*. Elements of $tau$ are *open* subsets of $X$.
- $A subset.eq X$ *closed* if $X - A$ is open.
- Let $X$ be a set. Then $tau = powset(X)$ is the *discrete topology* on $X$.
- $tau = {nothing, X}$ is the *indiscrete topology* on $X$.
- *Examples*:
    - For metric space $(M, d)$, find the open sets. Let $tau_d subset.eq cal(P)(M)$ exactly contain these open sets. Then $(M, tau_d)$ is a topological space. The metric $d$ *induces* the topology $tau_d$.
    - Let $X = NN_0$ and $tau = {nothing} union {U subset.eq X: X - U "is finite"}$.
- *Proposition*: for topological space $X$:
    - $X$ and $nothing$ are closed
    - Arbitrary intersections of closed sets are closed
    - Finite unions of closed sets are closed
- *Proposition*: for topological space $(X, tau)$ and $A subset.eq X$, the *induced (subspace) topology on $A$* $ tau_A = {A sect U: U in tau} $ is a topology on $A$.
- *Example*: let $X = RR$ with standard topology induced by metrix $d(x, y) = |x - y|$. Let $A = [1, 5]$. Then $lr([1, 3)) = A sect (0, 3)$ and $[1, 5] = A sect (0, 6)$ are open in $A$.
- *Example*: consider $RR$ with standard topology $tau$. Then
    - $tau_ZZ$ is the discrete topology on $ZZ$.
    - $tau_QQ$ is not the discrete topology on $QQ$.
- *Proposition*: the metrics $d_p$ for $p in lr([1, oo))$ and $d_oo$ all induce the same topology on $RR^n$.
- *Definition*: $(X, tau)$ is *Hausdorff* if $ forall x != y in X, exists U, V in tau: U sect V = nothing and x in U, y in V $
- *Lemma*: any metric space $(M, d)$ is Hausdorff.
- *Example*: let $|X| >= 2$ with the indiscrete topology. Then $X$ is not Hausdorff, since $tau = {X, nothing}$ and if $x != y in X$, the only open set containing $x$ is $X$ (same for $y$). But $X sect X = X != nothing$.
- *Furstenberg's topology on $ZZ$*: define $U subset.eq ZZ$ to be open if $ forall a in U, exists 0 != d in ZZ: a + d ZZ =: {a + d n: n in ZZ} subset.eq U $
- Furstenberg's topology is Hausdorff.

== Continuity

- *Definition*: let $X, Y$ topological spaces.
    - $f: X -> Y$ is *continuous* if $ forall V "open in" Y, f^(-1) (V) "open in" X $
    - $f$ is *continuous at $a in X$* if $ forall V "open in" Y, f(a) in V, exists U "open in" X: a in U subset.eq f^(-1) (V) $
- *Lemma*: $f: X -> Y$ continuous iff $f$ continuous at every $a in X$. (Key idea for proof: $union_(a in f^(-1) (V)) U_a subset.eq f^(-1) (V) = union_(a in f^(-1) (V)) {a} subset.eq union_(a in f^(-1) (V)) U_a$)
- *Example*: inclusion $i: (A, tau_A) -> (X, tau_X)$, $A subset.eq X$, is always continuous.