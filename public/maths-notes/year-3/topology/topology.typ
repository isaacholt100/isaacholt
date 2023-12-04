#import "../../template.typ": template
#show: template

#let powset(X) = $cal(P)(X)$
#let inv(x) = $#x^(-1)$
#let vd(v) = $bold(#v)$
#let ideal(..gens) = $angle.l #gens.pos().join(",") angle.r$

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
    - For metric space $(M, d)$, find the open sets with respect to metric $d$. Let $tau_d subset.eq cal(P)(M)$ exactly contain these open sets. Then $(M, tau_d)$ is a topological space. The metric $d$ *induces* the topology $tau_d$.
    - Let $X = NN_0$ and $tau = {nothing} union {U subset.eq X: X - U "is finite"}$.
- *Proposition*: for topological space $X$:
    - $X$ and $nothing$ are closed
    - Arbitrary intersections of closed sets are closed
    - Finite unions of closed sets are closed
- *Proposition*: for topological space $(X, tau)$ and $A subset.eq X$, the *induced (subspace) topology on $A$* $ tau_A = {A sect U: U in tau} $ is a topology on $A$.
- *Example*: let $X = RR$ with standard topology induced by metric $d(x, y) = |x - y|$. Let $A = [1, 5]$. Then $lr([1, 3)) = A sect (0, 3)$ and $[1, 5] = A sect (0, 6)$ are open in $A$.
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
- *Lemma*: a composition of continuous functions is continuous.
- *Lemma*: let $f: X -> Y$ be function between topological spaces. Then $f$ is continuous iff $ forall A "closed in" Y, quad f^(-1) (A) "closed in" X $
- *Remark*: we can use continuous functions decide that sets are open or closed.
- *Definition*: *$n$-sphere* is $ S^n := {(x_1, ..., x_(n + 1)) in RR^(n + 1): sum_(i = 1)^n x_i^2 = 1} $
- *Example*: in the standard topology, the $n$-sphere is a closed subset of $RR^(n + 1)$. (Consider the preimage of ${1}$ which is closed in $RR$).
- Can consider set of square matrices $M_(n, n) (RR) tilde.equiv RR^(n^2)$ and give it the standard topology.
- *Example*:
    - Note $ det(A) = sum_(sigma in "sym"(n)) ("sgn"(sigma) product_(i = 1)^n a_(i, sigma(i))) $ is a polynomial in the entries of $A$ so is continuous function from $M_n (RR)$ to $RR$.
    - $"GL"_n (RR) = {A in M_n (RR): det(A) != 0} = det^(-1) (RR - {0})$ is open.
    - $"SL"_n (RR) = {A in M_n (RR): det(A) = 1} = det^(-1) ({1})$ is closed.
    - $O(n) = {A in M_n (RR): A A^T = I}$ is closed - consider $f_(i, j) (A) = (A A^T)_(i, j)$ then $ O(n) = sect.big_(1 <= i, j <= n) (f_(i, j))^(-1) ({delta_(i, j)}) $
    - $"SO"(n) = O(n) sect "SL"_n (RR)$ is closed.
- *Definition*: for $X, Y$ topological spaces, $h: X -> Y$ is *homeomorphism* if $h$ is bijective, continuous and $h^(-1)$ is continuous. $X$ and $Y$ are *homeomorphic*. A homeomorphism gives bijection between $tau_X$ and $tau_Y$ which satisfies $ h(A sect B) = h(A) sect h(B), quad h(A union B) = h(A) union h(B) $
- *Example*: in standard topology, $(0, 1)$ is homeomorphic to $RR$. (Consider $f: (-pi/2, pi/2) -> (-oo, oo)$, $f = tan$, $g: (0, 1) -> (-pi/2, pi/2)$, $g(x) = pi (x - 1/2)$ and $f compose g$).
- *Example*: $RR$ with standard topology $tau_"st"$ is not homoeomorphic to $RR$ with the discrete topology $tau_d$. (Consider $h^(-1) ({a}) = {h^(-1) (a)}$, ${a} in tau_"st"$ but ${h^(-1) (a)} in.not tau_"st"$).
- *Example*: let $X = RR union {overline(0)}$. Define $f_0: RR -> X$, $f_0(a) = a$ and $f_(overline(0)): RR -> X$, $f_(overline(0))(a) = a$ for $a != 0$, $f_(overline(0))(0) = overline(0)$. Topology on $X$ has $A subset.eq X$ open iff $f_0^(-1)(A)$ and $f_(overline(0))^(-1)(A)$ open. Every point in $X$ lies in open set: for $a in.not {0, overline(0)}$, $a in (a - (|a|)/2, a + (|a|)/2)$ and both pre-images of this are same open interval, for $0$, set $U_0 = (-1, 0) union {0} union (0, 1) subset.eq X$ then $f_0^(-1) (U_0) = (-1, 1)$ and $f_(underline(0))^(-1) (U_0) = (-1, 0) union (0, 1)$ are both open. For $overline(0)$, set $U_(overline(0)) = (-1, 0) union {overline(0)} union (0, 1) subset.eq X$, then $f_(overline(0))^(-1)(U_(overline(0))) = (-1, 1)$ and $f_0^(-1)(U_(overline(0))) = (-1, 0) union (0, 1)$ are both open. So $U_0$ and $U_(overline(0))$ both open in $X$. $X$ is not Hausdorff since any open sets containing $0$ and $overline(0)$ must contain "open intervals" such as $U_0$ and $U_(overline(0))$.
- *Example (Furstenberg's proof of infinitude of primes)*: since $a + d ZZ$ is infinite, any nonempty finite set is not open, so any set with finite complement is not closed. For fixed $d$, sets $d ZZ$, $1 + d ZZ, ..., (d - 1) + d ZZ$ partition $ZZ$. So the complement of each is the union of the rest, so each is open and closed. Every $n in ZZ - {-1, 1}$ is prime or product of primes, so $ZZ - {-1, 1} = union_(p "prime") p ZZ$, but finite unions of closed sets are closed, and since $ZZ - {-1, 1}$ has finite complement, the union must be infinite.

= Limits, bases and products

== Limit points, interiors and closures

- *Definition*: for topological space $X$, $x in X$, $A subset.eq X$:
    - *Open neighbourhood of $x$* is open set $N$, $x in N$.
    - $x in X$ is *limit point* of $A$ if every open neighbourhood $N$ of $x$ satisfies $ (N - {x}) sect A != nothing $
- *Corollary*: $x$ is not limit point of $A$ iff exists neighbourhood $N$ of $x$ with $ A sect N = cases({x} & "if" x in A, nothing & "if" x in.not A) $
- *Example*: let $X = RR$ with standard topology.
    - $0 in X$, then $(-1\/2, 1\/2)$ is open neighbourhood of $0$.
    - If $U subset.eq X$ open, $U$ is open neighbourhood for any $x in U$.
    - Let $A = {1/n: n in ZZ - {0}}$, then only limit point in $A$ is $0$.
- *Definition*: let $A subset.eq X$.
    - *Interior* of $A$ is largest open set contained in $A$: $ A^circle.small = union.big_(U "open" \ U subset.eq A) U $
    - *Closure* of $A$ is smallest closed set containing $A$: $ overline(A) = sect.big_(F "closed" \ A subset.eq F) $ If $A^circle.small = X$, $A$ is *dense* in $X$.
- *Lemma*:
    - $overline(X - A) = X - A^circle.small$
    - $overline(A) = X - (X - A)^circle.small$
- *Example*:
    - Let $QQ subset RR$ with standard topology. Then $QQ^circle.small = nothing$ and $overline(QQ) = RR$ (since every nonempty open set in $RR$ contains rational and irrational numbers).
- *Lemma*: $overline(A) = A union L$ where $L$ is the set of limit points of $A$.
- *Dirichlet prime number theorem*: let $a, d$ coprime, the set $a + d ZZ$ contains infinitely many primes.
- *Example*: let $A$ be the set of primes in $ZZ$ with the Furstenberg topology. By the above lemma, we only need to find the limit points in $ZZ - A$ to find $overline(A)$. $10 ZZ$ is an open neighbourhood of $0$ for $0$ inside $ZZ - A$. For $a in.not {-1, 0, 1}$, $a + 10a ZZ$ is an open neighbourhood of $a$. These sets have no primes so the corresponding points are not limit points of $A$. For $plus.minus 1$, any open neighbourhood of $1$ contains a set $plus.minus 1 + d ZZ$ for some $d != 0$, but by the Dirichlet prime number theorem, this set contains at least one prime. So $overline(A) = A union {plus.minus 1}$.
- *Lemma*:
    - Let $A subset.eq M$ for metric space $M$. If $x$ is limit point of $A$ then exists sequence $x_n$ in $A$ such that $lim_(n -> oo) x_n = x$.
    - If $x in M - A$ and exists sequence $x_n$ in $A$ with $lim_(n -> oo) x_n = x$ then $x$ is limit point of $A$.

== Bases

- *Definition*: a *basis* for topology $tau$ on $X$ is collection $cal(B) subset.eq tau$ such that $ forall U in tau, U = union.big_(b in cal(B)) b $ (every open $U$ is a union of sets in $B$).
- *Example*:
    - For metric space $(M, d)$, $cal(B) = {B(x; r): x in M, r > 0}$ is basis for the induced topology. (Since if $U$ open, $U = union_(u in U) {u} subset.eq union_(u in U) B(u, r_u) subset.eq U$.)
    - In $RR^n$ with standard topology, $cal(B) = {B(q; 1\/m): q in QQ^n, m in NN}$ is a *countable* basis. (Find $m in NN$ such that $1/m < r/2$ and $q in QQ^n$ such that $q in B(p; 1/m)$, then $B(q; 1/m) subset.eq B(p; r) subset.eq U$ using the triangle inequality).
- *Theorem*: let $f: X -> Y$ be map between topological spaces. The following are equivalent:
    - $f$ is continuous.
    - If $cal(B)$ is basis for topology $tau$ on $Y$ then $f^(-1)(B)$ is open for every $B in cal(B)$.
    - $forall A subset.eq X, f\(overline(A)\) subset.eq overline(f(A))$.
    - $forall V subset.eq Y, overline(f^(-1)(V)) subset.eq f^(-1)\(overline(V)\)$.
    - $f^(-1)(C)$ closed for any closed set $C subset.eq Y$.
- *Theorem*: let $X$ be a set and collection $cal(B) subset.eq cal(P)(X)$ be such that:
    - $forall x in X, exists B in cal(B): x in B$
    - If $x in B_1 sect B_2$ with $B_1, B_2 in cal(B)$, then $exists B_3 in cal(B): x in B_3 subset.eq B_1 sect B_2$.
    Then there is unique topology $tau_(cal(B))$ on $X$ for which $cal(B)$ is a basis. We say $cal(B)$ *generates* $tau_(cal(B))$.

== Product topologies

- *Definition*: *Cartesian product* of topological spaces $X, Y$ is $X times Y := {(x, y): x in X, y in Y}$. We give it the *product topology* which is generated by $cal(B)_(X times Y) := {U times V: U in tau_X, V in tau_Y}$.
- *Example*:
    - Let $X = Y = RR$, then product topology is same as standard topology on $RR^2$.
    - Let $X = Y = S^1$, then $X times Y = T^2 = S^1 times S^1$ is the $2$-torus.
- *Definition*: if $tau_1 subset.eq tau_2$, then $tau_1$ is *smaller* than $tau_2$ ($tau_2$ is *larger* than $tau_1$).
- *Definition*: for topological spaces $X, Y$, *projection maps* $pi_X: X times Y -> X$ and $pi_Y: X times Y -> Y$ are $ pi_X (x, y) = x, quad pi_Y (x, y) = y $
- *Proposition*: for $X times Y$ with product topology,
    - $pi_X$ and $pi_Y$ are continuous.
    - $pi_X$ and $pi_Y$ map open sets to open sets.
    - Product topology is smallest topology for which $pi_X$ and $pi_Y$ are continuous.
- *Proposition*: let $X, Y, Z$ topological spaces, then $f: Z -> X times Y$ (with product topology on $X times Y$) continuous iff both $pi_X compose f: Z -> X$ and $pi_Y compose f: Z -> Y$ are continuous.
- *Exercise (todo)*: prove above proposition.
- *Example*: let $f: X -> RR^n$, $pi_i: RR^n -> RR$, $pi_i (x) = x_i$, $f_i = pi_i compose f$, then $f$ is continuous iff all $f_i$ are continuous.
- *Proposition*: let $X, Y$ nonempty topological spaces. Then $X times Y$ is Hausdorff iff $X$ and $Y$ are both Hausdorff.

= Connectedness

== Clopen sets and examples

- *Definition*: let $X$ topological space, then $A subset.eq X$ is *clopen* if $A$ is open and closed.
- *Definition*: $X$ is *connected* if the only clopen sets in $X$ are $X$ and $nothing$.
- *Example*:
    - $RR$ with standard topology is connected.
    - $QQ$ with induced topology from $RR$ is not connected (consider $L = QQ sect \(-oo, sqrt(2)\)$ and $QQ - L = QQ sect \(sqrt(2), oo\)$).
    - The connected subsets of $RR$ are the intervals.
- $A subset.eq RR$ is an interval iff $forall x, y in A, x < z < y ==> z in A$.
- *Example*:
    - $X = {0, 1}$ with discrete topology is not connected (${1}$ and ${0}$ both open so both closed).
    - $X = {0, 1}$ with $tau = {nothing, {1}, {0, 1}}$ is connected.
    - $ZZ$ with Furstenberg topology is not connected.
- *Theorem (continuity preserves connectedness)*: if $h: X -> Y$ continuous and $X$ connected, then $h(X) subset.eq Y$ is connected.
- *Corollary*: if $h: X -> Y$ is homeomorphism and $X$ is connected then $Y$ is connected.
- *Theorem*: let $X$ topological space. The following are equivalent:
    - $X$ is connected.
    - $X$ cannot be written as disjoint union of two non-empty sets.
    - There exists no continuous surjective function from $X$ to a discrete space with more than one point.
- *Example*:
    - $"GL"_n (RR)$ is not connected (since $det: "GL"_n (RR) -> RR - {0}$ is continuous and surjective and $RR - {0} = (-oo, 0) union (0, oo)$).
    - $O(n)$ is not connected.
    - $(0, 1)$ is connected (since $RR tilde.equiv (0, 1)$ and $RR$ is connected).
    - $X = lr((0, 1])$ and $Y = (0, 1)$ are not homeomorphic (if they are, then $lr((0, 1])$ is connected since $(0, 1)$ is).
- *Definition*: let $A = B union C$, $B sect C = emptyset$, then $B$ and $C$ are *complementary subsets* of $A$.
- *Remark*: if $B$ and $C$ are open in $A$, then $B$ and $C$ are clopen in $A$. So if $B, C != emptyset$ then $A$ is not connected.

== Constructing more connected sets, components, path-connectedness

- *Proposition*: let $X$ topological space, $Z subset.eq X$ connected. If $Z subset.eq Y subset.eq overline(Z)$ then $Y$ is connected. In particular, with $Y = overline(Z)$, the closure of a connected set is connected.
- *Proposition*: let $A_i subset.eq X$ connected, $i in I$, $A_i sect A_j != emptyset$ and $union_(i in I) A_i = X$. Then $X$ is connected.
- *Theorem*: if $X$ and $Y$ are connected then $X times Y$ is connected.
- *Example*:
    - $RR^n$ is connected.
    - $B^n = {x in RR^n: d_2 (0, x) < 1}$ ($B^n$ is homeomorphic to $RR^n$).
    - $D^n = {x in RR^n: d_2 (0, x) <= 1} = overline(B^n)$ is connected.
- *Example*:
    - $forall n >= 1$, $S^n$ is connected.
    - $forall n >= 1$, $T^n := (S^1)^n$ is connected.
- *Definition*: *component* of topological space $X$ is maximal connected subset of $X$.
- *Proposition*: in a topological space $X$:
    - Every $p in X$ is in a unique component.
    - If $C_1 != C_2$ are components, then $C_1 sect C_2 = emptyset$.
    - $X$ is the union of its components.
    - Every component is closed in $X$.
- *Example*:
    - If $X$ connected, then its only component is itself.
    - If $X$ discrete, then each singleton in $tau_X$ is a component.
    - In $QQ$ with induced standard topology from $RR$, every singleton is a component.
- *Definition*: *path* in topological space $X$ is continuous function $gamma: [0, 1] -> X$. $gamma$ is said to be path from $gamma(0)$ to $gamma(1)$.
- *Definition*: $X$ is *path-connected* if for every $p, q in X$, there is a path from $p$ to $q$.
- *Proposition*: every path-connected topological space is connected.
- *Example*: let $ Z = {(x, sin(1\/x)) in RR^2: 0 < x <= 1} $ $Z$ is path-connected, as a path from $(x_1, sin(1\/x_1))$ to $(x_2, sin(1\/x_2))$ is given by $ gamma(t) = (x_1 + (x_2 - x_1)t, sin(1/(x_1 + (x_2 - x_1)t))) $ So then $Z$ is connected by the above proposition, and since the closure of a connected set is connected, $overline(Z)$ is connected. 

    Every point $(0, y)$, $y in [-1, 1]$ is a limit point of $Z$. Assume $overline(Z)$ is path-connected. Then there is a path $gamma: [0, 1] -> overline(Z)$ from $(0, 0)$ to $(1, sin(1))$. Since $(pi_X compose gamma)(0) = 0$ and $(pi_X compose gamma)(1) = 1$ and $pi_X compose gamma$ is continuous, by the Intermediate Value Theorem, $exists t_1 in [0, 1]: (pi_X compose gamma)(t_1) = 2\/pi$. By IVT again, $exists t_2 in [0, t_1]: (pi_X compose gamma)(t_2) = 2/(2pi)$. We obtain a strictly decreasing sequence $(t_n) subset.eq [0, 1]$ where $(pi_X compose gamma)(t_n) = 2/(n pi)$ which is bounded below by $0$, so must converge with limit $t^*$.
    
    Now $pi_Y compose gamma$ is continuous, so $lim_(n -> oo) (pi_Y compose gamma)(t_n) = (pi_Y compose gamma)(t^*)$. But $(pi_Y compose gamma)(t_n) = sin((n pi)/2)$, and as $n -> oo$, this oscillates between $-1$ and $1$ and does not converge, so contradiction.

= Compactness

- *Definition*: let $X$ topological space, *cover* is collection $(U_i)_(i in I)$ of subsets of $X$ with $ union.big_(i in I) U_i = X $ If every $U_i$ is open, it is an *open cover*. If $J subset.eq I$, then $(U_i)_(i in J)$ is a *subcover* of $(U_i)_(i in I)$ if it is also a cover.
- *Definition*: $X$ is *compact* if every open cover of $X$ admits a finite subcover.
- *Example*:
    - If $X$ is finite then $X$ is compact.
    - $RR$ is not compact.
    - If $X$ infinite with $tau = {U subset.eq X: X - U "is finite"} union emptyset$, then $X$ is compact.
- *Proposition*: let $X$ have topology with basis $cal(B)$. Then $X$ is compact iff every cover $(B_i)_(i in I)$ of $X$, $B_i in cal(B)$, admits a finite subcover of $X$.
- *Remark*: to determine compactness of $Y subset.eq X$, consider open covers $Y = union_(i in I) (U_i sect y)$ for $U_i$ open in $X$, which is equivalent to $Y subset.eq union_(i in I) U_i$.
- *Example*: $[0, 1]$ is compact.
- *Proposition*: if $f: X -> Y$ continuous, $X$ compact, then $f(X)$ is compact.
- *Proposition*: if $X$ compact, $A subset.eq X$ closed in $X$, then $A$ is compact.
- *Theorem*: if $X$ is Hausdorff and $A subset.eq X$ is compact then $A$ is closed.
- *Corollary*: if $X$ compact, $Y$ is Hausdorff, $f: X -> Y$ continuous bijection, then $f$ is homeomorphism.
- *Theorem*: if $X$, $Y$ compact, then $X times Y$ is compact.
- *Definition*: $S subset.eq RR^n$ is *bounded* if $ exists r in R: S subset.eq B(0; r) $
- *Theorem (Heine-Borel)*: $A subset.eq RR^n$ is compact iff it is closed and bounded.
- *Example*:
    - $S^n$ is compact.
    - $T^n$ is compact.
    - $X = {vd(x) in RR^3: x_1^2 + x_2^2 - x_3^3 = 1}$ is not compact, since $forall n in NN$, $\(n, 0, \(n^2 - 1\)^(1\/3) \) in X$, so $X subset.eq.not B(n)$, so is unbouded, so not compact by Heine-Borel.
- *Corollary*: let $f: X -> RR$, $X$ compact, $f$ continuous. Then $f$ attains its maximum and minimum.
- *Theorem (Bolzano-Weierstrass)*: an infinite subset $A$ of a compact space $X$ has a limit point in $X$.

= Quotient spaces

- Let $X$ topologial space, $tilde$ equivalence relation on $X$. Write $X\/tilde$ for the set of equivalence classes of $tilde$: for $x in X$, $ [x] := {y in X: y tilde x}, quad X\/tilde thick := {[x]: x in X} $ There is a surjective map $pi: X -> X\/tilde$, $pi(x) = [x]$.
- *Example*: let $X = RR^3$, define equivalence relation $ (x_1, y_1, z_1) tilde (x_2, y_2, z_2) <=> z_1 = z_2 $ Then $pi(a, b, c) = [(a, b, c)] = {(x, y, z) in RR^3: z = c}$. The elements of $RR^3\/tilde$ are horizontal planes.
- *Definition*: let $X$ topological space, $tilde$ equivalence relation on $X$. Then $X\/tilde$ is given *quotient topology* defined by $ U subset.eq X\/tilde "open" <==> pi^(-1)(U) "open in" X $
- *Proposition*: the quotient topology defines a topology on $X\/tilde$.
- *Proposition*: the topology on $X\/tilde$ is the largest such that $pi$ is continuous.
- *Proposition*: let $X$ topology space with equivalence relation $tilde$, $Y$ topology space. Then $f: X\/tilde thick -> Y$ continuous iff $f compose pi: X -> Y$ is continuous.
- *Example*: in $RR$, let $x tilde y <==> x - y in ZZ$. Define $exp: RR -> S^1 subset.eq CC$, $exp(t) = e^(2pi i t)$) and $overline(exp): RR\/tilde thick -> S^1$, $overline(exp)([t]) = exp(t)$. Then $ [s] = [t] <==> s - t = k in ZZ <==> overline(exp)(s) = e^(2pi i k) e^(2pi i t) = e^(2pi i t) = overline(exp)(t) $ Hence $overline(exp)$ is well-defined and injective, and is surjective since $exp$ is. Also, $overline(exp)$ is continuous since $exp = overline(exp) compose pi$ is. $R^2$ is a metric space and so is Hausdorff, so $S^1 subset RR^2$ with the induced topology is Hausdorff. Now e.g. $pi([-10, 10]) = RR\/tilde$, $[-10, 10]$ is compact and $pi$ continuous so $RR\/tilde$ is compact. Since $overline(exp)$ is a continuous bijection, these three properties imply $overline(exp)$ is a homeomorphism. Hence $RR\/tilde thick tilde.equiv S^1$.
- *Definition*: let $A subset.eq X$, define $x tilde y <==> x = y$ or $x, y in A$. Then define $X\/A := X\/tilde$.
- *Example*: $S^n tilde.equiv D^n \/ S^(n - 1)$. Any point in $D^n$ can be written as $t dot.op phi$, $t in [0, 1]$, $phi in S^(n - 1)$. Define $ f: D^n -> S^n, quad f(t dot.op phi) & = (cos(pi t), phi sin(pi t)) in RR times RR^n = RR^(n + 1) \ ==> f(0 dot.op phi) & = (1, vd(0)), thick f(1\/2 dot.op phi) = (0, phi), thick f(1 dot.op phi) = (-1, 0) $ Define $overline(f): D^n \/ S^(n - 1) -> S^n$, $overline(f)([t dot.op phi]) = f(t dot.op phi)$. If $t_1 dot.op phi_1 != t_2 dot.op phi_2$, then $ [t_1 dot.op phi_1] = [t_2 dot.op phi_2] <==> t_1 dot.op phi_1, t_2 dot.op phi_2 in S^(n - 1) & <==> t_1 = t_2 = 1 \ & <==> f(t_1 dot.op phi_1) = (-1, vd(0)) = f(t_2 dot.op phi_2) \ & <==> overline(f)([t_1 dot.op phi_1]) = overline(f)([t_2 dot.op phi_2]) $

= Topological groups

== Examples

- *Definition*: a *topological group* $G$ is Hausdorff space $G$ which is also a group such that $ circle.filled.small: G times G -> G, thick thick circle.filled.small (g, h) = g h quad "and" quad i: G -> G, thick thick i(g) = g^(-1) $ are continuous.
- *Example*:
    - $RR^n$ with addition is a topological group.
    - $"GL"_n (RR)$ with multiplication and its subgroups $O(n)$ and $"SO"(n)$ are topological groups.
- *Proposition*:
    - Any group with the discrete topology is a topological group.
    - Any subgroup of a topological group is also a topological group.
- *Example*:
    - $CC - {0}$ with multiplication has topological subgroup $S^1 subset CC - {0}$.
    - Define *quaternions* as $HH := ideal(1, i, j, k)$, with topology taken from $RR^4$. $HH - {0}$ is a multiplicative group with $S^3$ a topological subgroup. For $q = a + b i + c j + d k in HH$, $a, b, c, d in RR$, we have $i j := k$, $j k := i$, $k i := j$, $j i := -k$, $k j := -i$, $i k := -j$. For $q != 0$, $ q^(-1) = (a - b i - c j - d k)/(a^2 + b^2 + c^2 + d^2) $
    - Note however that $S^2$ is not a topological group.
- *Definition*: for topological group $G$, $x in G$, define *left translation by $x$* as $ L_x: G -> G, quad L_x (g) := x g $ Similarly, *right translation by $x$* is $ R_x: G -> G, quad R_x (g) := g x $
- *Proposition*: $L_x$ has inverse $(L_x)^(-1) = L_(x^(-1))$ and is a homeomorphism. Similarly for $R_x$.
- *Notation*: a specified inclusion $G limits(arrow.hook)^x G times G$ is the map $G -> {x} times G$ composed with the inclusion map ${x} times G -> G times G$. (similarly for $G times {x}$).
- *Proposition*: Let $G$ topological group, $K$ the component containing identity of $G$. Then $K$ is a normal subgroup.