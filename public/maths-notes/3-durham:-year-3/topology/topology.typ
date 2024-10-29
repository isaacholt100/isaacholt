#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

// FIND: - \*(\w+)\*: ([\s\S]*?)(?=\n-|\n\n)\n
// REPLACE: #$1[\n    $2\n]\n

#let powset(X) = $cal(P)(X)$
#let inv(x) = $#x^(-1)$
#let vd(v) = $bold(#v)$
#let ideal(..gens) = $angle.l #gens.pos().join(",") angle.r$
#let St = $op("St")$
#let int = $op("int")$

= Metric spaces

== Metrics

#definition[
    *Metric space* is $(X, d)$, $X$ is set, $d: X times X -> [0, infinity)$ is *metric* satisfying:
    - $d(x, y) = 0 <==> x = y$
    - *Symmetry*: $d(x, y) = d(y, x)$
    - *Triangle inequality*: $d(x, y) <= d(x, z) + d(z, y)$
]
#example[
    - $p$-adic metric: for $p in lr([1, oo))$ $ d_p (x, y) = (sum_(i = 1)^n |x_i - y_i|^p)^(1/p) $
    - Extension of the $p$-adic metric: $ d_infinity (x, y) = max{|x_i - y_i|: i in [n]} $
    - Metric of $C([a, b])$: $ d(f, g) = sup{|f(x) - g(x)|: x in [a, b]} $
    - Discrete metric: $ d(x, y) = cases(0 & "if" x = y, 1 & "if" x != y) $
]
#definition[
    *Open ball of radius $r$ around $x$*: $ B(x; r) := {y in X: d(x, y) < r} $
]
#definition[
    *Closed ball of radius $r$ around $x$*: $ D(x; r) := {y in X: d(x, y) <= r} $
]

== Open and closed sets

#definition[
    $U subset.eq X$ is *open* if $ forall x in U, exists epsilon > 0: B(x; epsilon) subset.eq U $
]
#definition[
    $A subset.eq X$ is *closed* if $X - A$ is open.
]
#note[
    It is possible for sets to be neither closed nor open, or both closed and open.
]
#example[
    With standard metric on $RR$, any singleton ${x} in RR$ is closed and not open (same holds for $RR^n$).
]
#definition[
    Let $X$ be metric space, $x in N subset.eq X$. $N$ is *neighbourhood* of $x$ if $ exists "open " V subset.eq X: x in V subset.eq N $
]
#corollary[
    Let $x in X$, then $N subset.eq X$ neighbourhood of $x$ iff $exists epsilon > 0: x in B(x; epsilon) subset.eq N$.
]
#proposition[
    Open balls are open, closed balls are closed.
]
#lemma[
    Let $(X, d)$ metric space.
    - $X$ and $nothing$ are both open and closed.
    - Arbitrary unions of open sets are open.
    - Finite intersections of open sets are open.
    - Finite unions of closed sets are closed.
    - Arbitrary intersections of closed sets are closed.
]
#example[
    If $X$ has discrete metric, any $A subset.eq X$ is open and closed.
]

== Continuity

#definition[
    - *Sequence* in $X$ is $a: NN_0 -> X$, written $\(a_n\)_(n in NN)$.
    - $(a_n)$ *converges to $a$*, $lim_(n -> oo) a_n = a$, if $ forall epsilon > 0, exists n_0 in NN: forall n >= n_0, d(a, a_n) < epsilon $
]
#proposition[
    Let $X, Y$ metric spaces, $a in X$, $f: X -> Y$. The following are equivalent:
    - $forall epsilon > 0, exists delta > 0: forall x in X, d_X (a, x) < delta ==> d_Y (f(a), f(x)) < epsilon$.
    - For every sequence $(a_n)$ in $X$ with $a_n -> a$, $f(a_n) -> f(a)$.
    - For every open $U subset.eq Y$ with $f(a) in U$, $f^(-1) (U)$ is a neighbourhood of $a$.
    If $f$ satisfies these, it is *continuous at $a$*.
]
#definition[
    $f$ *continuous* if continuous at every $a in X$.
]
#proposition[
    $f: X -> Y$ continuous iff $f^(-1)(U)$ open for every open $U subset.eq Y$.
]
#example[
    Let $d$ be discrete metric, $d_2$ be $2$-adic metric.
    - Any $f: (X, d) -> (RR, d_2)$ is continuous.
    - $id: (RR, d_2) -> (RR, d)$ is not continuous.
]

= Topological spaces

== Topologies

#definition[
    *Power set* of $X$: $cal(P)(X) := {A: A subset.eq X}$.
]
#definition[
    *Topology* on set $X$ is $tau subset.eq cal(P)(X)$ with:
    - $nothing in tau$, $X in tau$.
    - *Closure under arbitrary unions*: if $forall i in I, U_i in tau$, then $ union.big_(i in I) U_i in tau $
    - *Closure under finite intersections*: $U_1, U_2 in tau ==> U_1 sect U_2 in tau$ (this is equivalent to $U_1, ..., U_n in tau ==> sect.big_(i in [n]) U_i in tau$).
    $(X, tau)$ is *topological space*. Elements of $tau$ are *open* subsets of $X$. $A subset.eq X$ *closed* if $X - A$ is open.
]
#definition[
    $tau = powset(X)$ is the *discrete topology* on $X$.
]
#definition[
    $tau = {nothing, X}$ is the *indiscrete topology* on $X$.
]
#example[
    - For metric space $(M, d)$, let $tau_d$ exactly contain sets which are open with respect to $d$. Then $(M, tau_d)$ is a topological space. $d$ *induces* topology $tau_d$.
    - Let $X = NN_0$ and $tau = {nothing} union {U subset.eq X: X - U "is finite"}$, then $(X, tau)$ is topological space.
]
#proposition[
    For topological space $X$:
    - $X$ and $nothing$ are closed
    - Arbitrary intersections of closed sets are closed
    - Finite unions of closed sets are closed
]
#proposition[
    For topological space $(X, tau)$ and $A subset.eq X$, the *induced (subspace) topology on $A$* $ tau_A = {A sect U: U in tau} $ is a topology on $A$.
]
#example[
    Let $X = RR$ with standard topology induced by metric $d(x, y) = |x - y|$. Let $A = [1, 5]$. Then $lr([1, 3)) = A sect (0, 3)$ and $[1, 5] = A sect (0, 6)$ are open in $A$.
]
#example[
    Consider $RR$ with standard topology $tau$. Then
    - $tau_ZZ$ is the discrete topology on $ZZ$.
    - $tau_QQ$ is not the discrete topology on $QQ$.
]
#proposition[
    Metrics $d_p$ for $p in lr([1, oo))$ and $d_oo$ all induce same topology on $RR^n$, called the *standard topology* on $RR^n$.
]
#definition[
    $(X, tau)$ is *Hausdorff* if $ forall x != y in X, exists U, V in tau: U sect V = nothing and x in U, y in V $
]
#lemma[
    Any metric space $(M, d)$ with topology induced by $d$ is Hausdorff.
]
#example[
    Let $|X| >= 2$ with indiscrete topology. Then $X$ is not Hausdorff, since $tau = {X, nothing}$ and if $x != y in X$, only open set containing $x$ is $X$ (same for $y$). But $X sect X = X != nothing$.
]
#definition[
    *Furstenberg's topology on $ZZ$*: define $U subset.eq ZZ$ to be open if $ forall a in U, exists 0 != d in ZZ: a + d ZZ := {a + d n: n in ZZ} subset.eq U $
]
#proposition[
    Furstenberg's topology is Hausdorff.
]

== Continuity

#definition[
    Let $X, Y$ topological spaces.
    - $f: X -> Y$ is *continuous* if $ forall V "open in" Y, f^(-1) (V) "open in" X $
    - $f$ is *continuous at $a in X$* if $ forall V "open in" Y "with" f(a) in V, exists U "open in" X: a in U subset.eq f^(-1) (V) $
]
#lemma[
    $f: X -> Y$ continuous iff $f$ continuous at every $a in X$. (Key idea for proof: $union_(a in f^(-1) (V)) U_a subset.eq f^(-1) (V) = union_(a in f^(-1) (V)) {a} subset.eq union_(a in f^(-1) (V)) U_a$)
]
#example[
    Inclusion $i: (A, tau_A) -> (X, tau_X)$, $A subset.eq X$, is always continuous.
]
#lemma[
    Compositions of continuous functions are continuous.
]
#lemma[
    Let $f: X -> Y$ be function between topological spaces. Then $f$ is continuous iff $ forall A "closed in" Y, quad f^(-1) (A) "closed in" X $
]
#remark[
    We can use continuous functions to decide that sets are open or closed.
]
#definition[
    *$n$-sphere* is $ S^n := {(x_1, ..., x_(n + 1)) in RR^(n + 1): sum_(i = 1)^(n + 1) x_i^2 = 1} $
]
#example[
    In the standard topology, the $n$-sphere is a closed subset of $RR^(n + 1)$. (Consider the preimage of ${1}$ which is closed in $RR$).
]
#example[
    - Can consider set of square matrices $M_(n, n) (RR) tilde.equiv RR^(n^2)$ and give it the standard topology.
    - Note $ det(A) = sum_(sigma in "sym"(n)) ("sgn"(sigma) product_(i = 1)^n a_(i, sigma(i))) $ is a polynomial in the entries of $A$ so is continuous function from $M_n (RR)$ to $RR$.
    - $"GL"_n (RR) = {A in M_n (RR): det(A) != 0} = det^(-1) (RR - {0})$ is open.
    - $"SL"_n (RR) = {A in M_n (RR): det(A) = 1} = det^(-1) ({1})$ is closed.
    - $O(n) = {A in M_n (RR): A A^T = I}$ is closed: $f_(i, j) (A) = \(A A^T\)_(i, j)$ is continuous and $ O(n) = sect.big_(1 <= i, j <= n) \(f_(i, j)\)^(-1) \(\{delta_(i, j)\}\) $
    - $"SO"(n) = O(n) sect "SL"_n (RR)$ is closed.
]
#definition[
    For $X, Y$ topological spaces, $h: X -> Y$ is *homeomorphism* if $h$ is bijective, continuous and $h^(-1)$ is continuous. $X$ and $Y$ are *homeomorphic*, $X tilde.equiv Y$. $h$ induces bijection between $tau_X$ and $tau_Y$ which commutes with unions and intersections.
]
#proposition[
    Compositions of homeomorphisms are homeomorphisms.
]
#example[
    In standard topology, $(0, 1)$ is homeomorphic to $RR$. (Consider $f: (-pi/2, pi/2) -> (-oo, oo)$, $f = tan$, $g: (0, 1) -> (-pi/2, pi/2)$, $g(x) = pi (x - 1/2)$ and $f compose g$).
]
#example[
    $RR$ with standard topology $tau_"st"$ is not homoeomorphic to $RR$ with the discrete topology $tau_d$. (Consider $h^(-1) ({a}) = {h^(-1) (a)}$, ${a} in tau_d$ but ${h^(-1) (a)} in.not tau_"st"$).
]
#example[
    Let $X = RR union \{overline(0)\}$. Define $f_0: RR -> X$, $f_0(a) = a$ and $f_(overline(0)): RR -> X$, $f_(overline(0))(a) = a$ for $a != 0$, $f_(overline(0))(0) = overline(0)$. Topology on $X$ has $A subset.eq X$ open iff $f_0^(-1)(A)$ and $f_(overline(0))^(-1)(A)$ open. Every point in $X$ lies in open set: for $a in.not \{0, overline(0)\}$, $a in \(a - (|a|)/2, a + (|a|)/2\)$ and both pre-images of this are same open interval, for $0$, set $U_0 = (-1, 0) union {0} union (0, 1) subset.eq X$ then $f_0^(-1) (U_0) = (-1, 1)$ and $f_(underline(0))^(-1) (U_0) = (-1, 0) union (0, 1)$ are both open. For $overline(0)$, set $U_(overline(0)) = (-1, 0) union {overline(0)} union (0, 1) subset.eq X$, then $f_(overline(0))^(-1)(U_(overline(0))) = (-1, 1)$ and $f_0^(-1)(U_(overline(0))) = (-1, 0) union (0, 1)$ are both open. So $U_0$ and $U_(overline(0))$ both open in $X$. $X$ is not Hausdorff since any open sets containing $0$ and $overline(0)$ must contain "open intervals" such as $U_0$ and $U_(overline(0))$.
]
#example("Furstenberg's proof of infinitude of primes")[
    Since $a + d ZZ$ is infinite, any nonempty finite set is not open, so any set with finite complement is not closed. For fixed $d$, sets $d ZZ$, $1 + d ZZ, ..., (d - 1) + d ZZ$ partition $ZZ$. So the complement of each is the union of the rest, so each is open and closed. Every $n in ZZ - {-1, 1}$ is prime or product of primes, so $ZZ - {-1, 1} = union.big_(p "prime") p ZZ$, but finite unions of closed sets are closed, and since $ZZ - {-1, 1}$ has finite complement, the union must be infinite.
]

= Limits, bases and products

== Limit points, interiors and closures

#definition[
    For topological space $X$, $x in X$, $A subset.eq X$:
    - *Open neighbourhood of $x$* is open set $N$, $x in N$.
    - $x$ is *limit point* of $A$ if every open neighbourhood $N$ of $x$ satisfies $ (N - {x}) sect A != nothing $
]
#corollary[
    $x$ is not limit point of $A$ iff exists neighbourhood $N$ of $x$ with $ A sect N = cases({x} & "if" x in A, nothing & "if" x in.not A) $
]
#example[
    Let $X = RR$ with standard topology.
    - $0 in X$, then $(-1\/2, 1\/2)$ is open neighbourhood of $0$.
    - If $U subset.eq X$ open, $U$ is open neighbourhood for any $x in U$.
    - Let $A = {1/n: n in ZZ - {0}}$, then only limit point in $A$ is $0$.
]
#definition[
    Let $A subset.eq X$.
    - *Interior* of $A$ is largest open set contained in $A$: $ A^circle.small := union.big_(U "open" \ U subset.eq A) U $
    - *Closure* of $A$ is smallest closed set containing $A$: $ overline(A) := sect.big_(F "closed" \ A subset.eq F) F $ If $overline(A) = X$, $A$ is *dense* in $X$.
]
#lemma[
    - $overline(X - A) = X - A^circle.small$
    - $overline(A) = X - (X - A)^circle.small$
]
#example[
    Let $QQ subset RR$ with standard topology. Then $QQ^circle.small = nothing$ and $overline(QQ) = RR$ (since every nonempty open set in $RR$ contains rational and irrational numbers).
]
#lemma[
    $overline(A) = A union L$ where $L$ is the set of limit points of $A$.
]
#theorem("Dirichlet prime number theorem")[
    Let $a, d$ coprime, then $a + d ZZ$ contains infinitely many primes.
]
#example[
    Let $A$ be set of primes in $ZZ$ with Furstenberg topology. By above lemma, only need to find  limit points in $ZZ - A$ to find $overline(A)$. $10 ZZ$ is an open neighbourhood of $0$ for $0$ inside $ZZ - A$. For $a in.not {-1, 0, 1}$, $a + 10a ZZ$ is an open neighbourhood of $a$. These sets have no primes so the corresponding points are not limit points of $A$. For $plus.minus 1$, any open neighbourhood of $plus.minus 1$ contains a set $plus.minus 1 + d ZZ$ for some $d != 0$, but by the Dirichlet prime number theorem, this set contains at least one prime. So $overline(A) = A union {plus.minus 1}$.
]
#lemma[
    - Let $A subset.eq M$ for metric space $M$. If $x$ is limit point of $A$ then exists sequence $x_n$ in $A$ such that $lim_(n -> oo) x_n = x$.
    - If $x in M - A$ and exists sequence $x_n$ in $A$ with $lim_(n -> oo) x_n = x$ then $x$ is limit point of $A$.
]

== Bases

#definition[
    A *basis* for topology $tau$ on $X$ is collection $cal(B) subset.eq tau$ such that $ forall U in tau, exists B subset.eq cal(B): U = union.big_(b in B) b $ (every open $U$ is a union of sets in $B$).
]
#example[
    - For metric space $(M, d)$, $cal(B) = {B(x; r): x in M, r > 0}$ is basis for the induced topology. (Since if $U$ open, $U = union_(u in U) {u} subset.eq union_(u in U) B(u, r_u) subset.eq U$.)
    - In $RR^n$ with standard topology, $cal(B) = {B(q; 1\/m): q in QQ^n, m in NN}$ is a *countable* basis. (Find $m in NN$ such that $1/m < r/2$ and $q in QQ^n$ such that $q in B(p; 1/m)$, then $B(q; 1/m) subset.eq B(p; r) subset.eq U$ using the triangle inequality).
]
#theorem[
    Let $f: X -> Y$ be map between topological spaces. The following are equivalent:
    - $f$ is continuous.
    - If $cal(B)$ is basis for topology $tau$ on $Y$ then $f^(-1)(B)$ is open for every $B in cal(B)$.
    - $forall A subset.eq X, f\(overline(A)\) subset.eq overline(f(A))$.
    - $forall V subset.eq Y, overline(f^(-1)(V)) subset.eq f^(-1)\(overline(V)\)$.
    - $f^(-1)(C)$ closed for any closed set $C subset.eq Y$.
]
#theorem[
    Let $X$ be a set and collection $cal(B) subset.eq cal(P)(X)$ be such that:
    - $forall x in X, exists B in cal(B): x in B$
    - If $x in B_1 sect B_2$ with $B_1, B_2 in cal(B)$, then $exists B_3 in cal(B): x in B_3 subset.eq B_1 sect B_2$.
    Then there is unique topology $tau_(cal(B))$ on $X$ for which $cal(B)$ is a basis. We say $cal(B)$ *generates* $tau_(cal(B))$. We have $tau_B = {union_(i in I) B_i: B_i in cal(B), I "indexing set"}$.
]

== Product topologies

#definition[
    *Cartesian product* of topological spaces $X, Y$ is $X times Y := {(x, y): x in X, y in Y}$. We give it the *product topology* which is generated by $cal(B)_(X times Y) := {U times V: U in tau_X, V in tau_Y}$.
]
#example[
    - Let $X = Y = RR$, then product topology is same as standard topology on $RR^2$.
    - Let $X = Y = S^1$, then $X times Y = T^2 = S^1 times S^1$ is the *$2$-torus*. *$n$-torus* is defined for $n >= 3$ by $ T^n := S^1 times T^(n - 1) $
]
#definition[
    If $tau_1 subset.eq tau_2$ are topologies, then $tau_1$ is *smaller* than $tau_2$ ($tau_2$ is *larger* than $tau_1$).
]
#definition[
    For topological spaces $X, Y$, *projection maps* $pi_X: X times Y -> X$ and $pi_Y: X times Y -> Y$ are $ pi_X (x, y) = x, quad pi_Y (x, y) = y $
]
#proposition[
    For $X times Y$ with product topology,
    - $pi_X$ and $pi_Y$ are continuous.
    - $pi_X$ and $pi_Y$ map open sets to open sets.
    - Product topology is smallest topology for which $pi_X$ and $pi_Y$ are continuous.
]
#proposition[
    Let $X, Y, Z$ topological spaces, then $f: Z -> X times Y$ (with product topology on $X times Y$) continuous iff both $pi_X compose f: Z -> X$ and $pi_Y compose f: Z -> Y$ are continuous.
]
#example[
    Let $f: X -> RR^n$, $pi_i: RR^n -> RR$, $pi_i (x) = x_i$, $f_i = pi_i compose f$, then $f$ is continuous iff all $f_i$ are continuous.
]
#proposition[
    Let $X, Y$ nonempty topological spaces. Then $X times Y$ with product topology is Hausdorff iff $X$ and $Y$ are both Hausdorff.
]

= Connectedness

== Clopen sets and examples

#definition[
    Let $X$ topological space, then $A subset.eq X$ is *clopen* if $A$ is open and closed.
]
#definition[
    $X$ is *connected* if the only clopen sets in $X$ are $X$ and $nothing$.
]
#example[
    - $RR$ with standard topology is connected.
    - $QQ$ with induced topology from $RR$ is not connected (consider $L = QQ sect \(-oo, sqrt(2)\)$ and $QQ - L = QQ sect \(sqrt(2), oo\)$).
    - The connected subsets of $RR$ are the intervals.
]
#definition[
    $A subset.eq RR$ is an interval iff $forall x, y in A, forall z in RR, x < z < y ==> z in A$.
]
#example[
    - $X = {0, 1}$ with discrete topology is not connected (${1}$ and ${0}$ both open so both closed).
    - $X = {0, 1}$ with $tau = {nothing, {1}, {0, 1}}$ is connected.
    - $ZZ$ with Furstenberg topology is not connected.
]
#theorem("continuity preserves connectedness")[
    If $h: X -> Y$ continuous and $X$ connected, then $h(X) subset.eq Y$ is connected.
]
#corollary[
    If $h: X -> Y$ is homeomorphism and $X$ is connected then $Y$ is connected.
]
#theorem[
    Let $X$ topological space. The following are equivalent:
    - $X$ is connected.
    - $X$ cannot be written as disjoint union of two non-empty open sets.
    - There exists no continuous surjective function from $X$ to a discrete space with more than one point.
]
#example[
    - $"GL"_n (RR)$ is not connected (since $det: "GL"_n (RR) -> RR - {0}$ is continuous and surjective and $RR - {0} = (-oo, 0) union (0, oo)$).
    - $O(n)$ is not connected.
    - $(0, 1)$ is connected (since $RR tilde.equiv (0, 1)$ and $RR$ is connected).
    - $X = lr((0, 1])$ and $Y = (0, 1)$ are not homeomorphic (consider $h(1) = p in Y$).
]
#definition[
    Let $A = B union C$, $B sect C = emptyset$, then $B$ and $C$ are *complementary subsets* of $A$.
]
#remark[
    If complementary $B$ and $C$ open in $A$, then $B$ and $C$ clopen in $A$. So if $B, C != emptyset$ then $A$ not connected.
]

== Constructing more connected sets, components, path-connectedness

#proposition[
    Let $X$ topological space, $Z subset.eq X$ connected. If $Z subset.eq Y subset.eq overline(Z)$ then $Y$ is connected. In particular, with $Y = overline(Z)$, the closure of a connected set is connected.
]
#proposition[
    Let $A_i subset.eq X$ connected, $i in I$, $A_i sect A_j != emptyset$ and $union_(i in I) A_i = X$. Then $X$ is connected.
]
#theorem[
    If $X$ and $Y$ are connected then $X times Y$ is connected.
]
#example[
    - $RR^n$ is connected.
    - $B^n = {x in RR^n: d_2 (0, x) < 1}$ is connected ($B^n$ is homeomorphic to $RR^n$).
    - $D^n = {x in RR^n: d_2 (0, x) <= 1} = overline(B^n)$ is connected.
]
#example[
    - $forall n in NN$, $S^n$ is connected.
    - $forall n in NN$, $T^n$ is connected.
]
#definition[
    *Component* of topological space $X$ is maximal connected subset of $X$.
]
#proposition[
    In a topological space $X$:
    - Every $p in X$ is in a unique component.
    - If $C_1 != C_2$ are components, then $C_1 sect C_2 = emptyset$.
    - $X$ is the union of its components.
    - Every component is closed in $X$.
]
#example[
    - If $X$ connected, then its only component is itself.
    - If $X$ discrete, then each singleton in $tau_X$ is a component.
    - In $QQ$ with induced standard topology from $RR$, every singleton is a component.
]
#definition[
    *Path* in topological space $X$ is continuous function $gamma: [0, 1] -> X$. $gamma$ is said to be path from $gamma(0)$ to $gamma(1)$.
]
#definition[
    $X$ is *path-connected* if for every $p, q in X$, there is a path from $p$ to $q$.
]
#proposition[
    Every path-connected topological space is connected.
]
#example[
    Let $ Z = {(x, sin(1\/x)) in RR^2: 0 < x <= 1} $ $Z$ is path-connected, as a path from $(x_1, sin(1\/x_1))$ to $(x_2, sin(1\/x_2))$ is given by $ gamma(t) = (x_1 + (x_2 - x_1)t, sin(1/(x_1 + (x_2 - x_1)t))) $ So then $Z$ is connected by the above proposition, and since the closure of a connected set is connected, $overline(Z)$ is connected. 
]

    Every point $(0, y)$, $y in [-1, 1]$ is a limit point of $Z$. Assume $overline(Z)$ is path-connected. Then there is a path $gamma: [0, 1] -> overline(Z)$ from $(0, 0)$ to $(1, sin(1))$. Since $(pi_X compose gamma)(0) = 0$ and $(pi_X compose gamma)(1) = 1$ and $pi_X compose gamma$ is continuous, by the Intermediate Value Theorem, $exists t_1 in [0, 1]: (pi_X compose gamma)(t_1) = 2\/pi$. By IVT again, $exists t_2 in [0, t_1]: (pi_X compose gamma)(t_2) = 2/(2pi)$. We obtain a strictly decreasing sequence $(t_n) subset.eq [0, 1]$ where $(pi_X compose gamma)(t_n) = 2/(n pi)$ which is bounded below by $0$, so must converge with limit $t^*$.
    
    Now $pi_Y compose gamma$ is continuous, so $lim_(n -> oo) (pi_Y compose gamma)(t_n) = (pi_Y compose gamma)(t^*)$. But $(pi_Y compose gamma)(t_n) = sin((n pi)/2)$, and as $n -> oo$, this oscillates between $-1$ and $1$ and does not converge, so contradiction.

= Compactness

#definition[
    Let $X$ topological space, *cover* of $X$ is collection $\(U_i\)_(i in I)$ of subsets of $X$ with $ union.big_(i in I) U_i = X $ If every $U_i$ is open, it is an *open cover*. If $J subset.eq I$, then $\(U_i\)_(i in J)$ is a *subcover* of $\(U_i\)_(i in I)$ if it is also a cover.
]
#definition[
    $X$ is *compact* if every open cover of $X$ admits a finite subcover.
]
#example[
    - If $X$ is finite then $X$ is compact.
    - $RR$ is not compact.
    - If $X$ infinite with $tau = {U subset.eq X: X - U "is finite"} union {emptyset}$, then $X$ is compact.
]
#proposition[
    Let $X$ have topology with basis $cal(B)$. Then $X$ is compact iff every cover $\(B_i\)_(i in I)$ of $X$, $B_i in cal(B)$, admits a finite subcover of $X$.
]
#remark[
    To determine compactness of $Y subset.eq X$ with induced topology, consider open covers $Y = union_(i in I) (U_i sect Y)$ for $U_i$ open in $X$, which is equivalent to $Y subset.eq union_(i in I) U_i$.
]
#example[
    $[0, 1]$ is compact.
]
#proposition[
    If $f: X -> Y$ continuous, $X$ compact, then $f(X)$ is compact.
]
#proposition[
    If $X$ compact, $A subset.eq X$ closed in $X$, then $A$ is compact.
]
#theorem[
    If $X$ is Hausdorff and $A subset.eq X$ is compact then $A$ is closed.
]
#corollary[
    If $X$ compact, $Y$ is Hausdorff, $f: X -> Y$ continuous bijection, then $f$ is homeomorphism.
]
#theorem[
    If $X$, $Y$ compact, then $X times Y$ is compact.
]
#definition[
    $S subset.eq RR^n$ is *bounded* if $ exists r in RR: S subset.eq B(0; r) $
]
#theorem("Heine-Borel")[
    $A subset.eq RR^n$ is compact iff it is closed and bounded.
]
#example[
    - $S^n$ is compact.
    - $T^n$ is compact.
    - $X = {vd(x) in RR^3: x_1^2 + x_2^2 - x_3^3 = 1}$ is not compact, since $forall n in NN$, $\(n, 0, \(n^2 - 1\)^(1\/3) \) in X$, so $X subset.eq.not B(n)$, so is unbounded, so not compact by Heine-Borel.
]
#corollary[
    Let $f: X -> RR$, $X$ compact, $f$ continuous. Then $f$ attains its maximum and minimum.
]
#theorem("Bolzano-Weierstrass")[
    An infinite subset $A$ of a compact space $X$ has a limit point in $X$.
]

= Quotient spaces

#definition[
    Let $X$ topological space, $tilde$ equivalence relation on $X$. Write $X\/tilde$ for the set of equivalence classes of $tilde$: for $x in X$, $ [x] := {y in X: y tilde x}, quad X\/tilde thick := {[x]: x in X} $ There is a surjective map, the *quotient map*, $pi: X -> X\/tilde$, $pi(x) = [x]$.
]
#example[
    Let $X = RR^3$, define equivalence relation $ (x_1, y_1, z_1) tilde (x_2, y_2, z_2) <=> z_1 = z_2 $ Then $pi(a, b, c) = [(a, b, c)] = {(x, y, z) in RR^3: z = c}$. Elements of $RR^3\/tilde$ are horizontal planes.
]
#definition[
    Let $X$ topological space, $tilde$ equivalence relation on $X$. Then $X\/tilde$ is given *quotient topology* defined by $ U subset.eq X\/tilde "open" <==> pi^(-1)(U) "open in" X $
]
#proposition[
    Quotient topology defines a topology on $X\/tilde$.
]
#proposition[
    Quotient topology on $X\/tilde$ is largest such that $pi$ is continuous.
]
#proposition[
    Let $X$ topological space with equivalence relation $tilde$, $Y$ topological space. Then $f: X\/tilde thick -> Y$ continuous iff $f compose pi: X -> Y$ is continuous.
]
#example[
    In $RR$, let $x tilde y <==> x - y in ZZ$. Define $exp: RR -> S^1 subset.eq CC$, $exp(t) = e^(2pi i t)$ and $overline(exp): RR\/tilde thick -> S^1$, $overline(exp)([t]) = exp(t)$. Then $ [s] = [t] <==> s - t = k in ZZ <==> overline(exp)(s) = e^(2pi i k) e^(2pi i t) = e^(2pi i t) = overline(exp)(t) $ Hence $overline(exp)$ is well-defined and injective, and is surjective since $exp$ is. Also, $overline(exp)$ is continuous since $exp = overline(exp) compose pi$ is. $RR^2$ is a metric space and so is Hausdorff, so $S^1 subset RR^2$ with the induced topology is Hausdorff. Now e.g. $pi([-10, 10]) = RR\/tilde$, $[-10, 10]$ is compact and $pi$ continuous so $RR\/tilde$ is compact. Since $overline(exp)$ is a continuous bijection, these three properties imply $overline(exp)$ is a homeomorphism. Hence $RR\/tilde thick tilde.equiv S^1$.
]
#definition[
    Let $A subset.eq X$, define $x tilde y <==> x = y$ or $x, y in A$. Then define $X\/A := X\/tilde$.
]
#example[
    $S^n tilde.equiv D^n \/ S^(n - 1)$. Any point in $D^n$ can be written as $t dot.op phi$, $t in [0, 1]$, $phi in S^(n - 1)$. Define $ f: D^n -> S^n, quad f(t dot.op phi) &:= (cos(pi t), phi sin(pi t)) in RR times RR^n = RR^(n + 1) \ ==> f(0 dot.op phi) & = (1, vd(0)), thick f(1\/2 dot.op phi) = (0, phi), thick f(1 dot.op phi) = (-1, 0) $ Define $overline(f): D^n \/ S^(n - 1) -> S^n$, $overline(f)([t dot.op phi]) = f(t dot.op phi)$. If $t_1 dot.op phi_1 != t_2 dot.op phi_2$, then $ [t_1 dot.op phi_1] = [t_2 dot.op phi_2] <==> t_1 dot.op phi_1, t_2 dot.op phi_2 in S^(n - 1) & <==> t_1 = t_2 = 1 \ & <==> f(t_1 dot.op phi_1) = (-1, vd(0)) = f(t_2 dot.op phi_2) \ & <==> overline(f)([t_1 dot.op phi_1]) = overline(f)([t_2 dot.op phi_2]) $ $f$ is surjective, so $overline(f)$ is also. Now $overline(f) compose pi = f$ which is continuous, so by above proposition, $overline(f)$ is continuous. $S^n subset RR^(n + 1)$ is Hausdorff, $D^n subset RR^n$ is closed and bounded so is compact by Heine-Borel, and so $D^n \/ S^(n - 1)$ is compact (since $pi$ continuous). Also, $f$ is a continuous bijection. These imply that $overline(f)$ is homeomorphism.
]

= Topological groups

== Examples

#definition[
    A *topological group* $G$ is Hausdorff space which is also a group such that $ circle.filled.small: G times G -> G, thick thick circle.filled.small (g, h) = g h quad "and" quad i: G -> G, thick thick i(g) = g^(-1) $ are continuous.
]
#example[
    - $RR^n$ with addition is topological group.
    - $"GL"_n (RR)$ with multiplication and its subgroups $O(n)$ and $"SO"(n)$ are topological groups (each entry in $A B$ is sum of products of entries of $A$ and $B$, so matrix multiplication is continuous, matrix inversion also continuous).
]
#proposition[
    - Any group with discrete topology is topological group.
    - Any subgroup of topological group is also topological group.
]
#example[
    - $CC - {0}$ with multiplication has topological subgroup $S^1 subset CC - {0}$.
    - Define *quaternions* as vector space $HH := ideal(1, i, j, k)$, with topology taken from $RR^4$. $HH - {0}$ is a multiplicative group with $S^3$ a topological subgroup. For $q = a + b i + c j + d k in HH$, $a, b, c, d in RR$, we have $i j := k$, $j k := i$, $k i := j$, $j i := -k$, $k j := -i$, $i k := -j$. For $q != 0$, $ q^(-1) = (a - b i - c j - d k)/(a^2 + b^2 + c^2 + d^2) $
    - Note however that $S^2$ is not a topological group.
]
#definition[
    For topological group $G$, $x in G$, define *left translation by $x$* as $ L_x: G -> G, quad L_x (g) := x g $ Similarly, *right translation by $x$* is $ R_x: G -> G, quad R_x (g) := g x $
]
#proposition[
    $L_x$ has inverse $(L_x)^(-1) = L_(x^(-1))$ and is homeomorphism. Similarly for $R_x$.
]
#notation[
    A specified inclusion $G limits(arrow.hook)^x G times G$ is the map $G -> {x} times G$ composed with the inclusion map ${x} times G -> G times G$. (similarly for $G times {x}$).
]
#proposition[
    Let $G$ topological group, $K$ the component containing identity of $G$. Then $K$ is normal subgroup of $G$.
]
#example[
    $O(n)$ is not connected, but $"SO"(n)$ is connected and contains $I_n$, so is a normal subgroup of $O(n)$
]

== Actions, orbits, orbit spaces

#definition[
    *Action* of group $G$ on topological space $X$ is map $circle.filled.small: G times X -> X$ such that $forall g, h in G$, $forall x in X$,
    - $(h g) circle.filled.small x = h circle.filled.small (g circle.filled.small x)$.
    - $1 circle.filled.small x = x$.
    - $g: X -> X$ defined by $g(x) = g circle.filled.small x$ is continous. Note: $g$ has inverse map $g^(-1)$ which is also continuous, so both are homeomorphisms.
]
#definition[
    *Action* of topological group $G$ on topological space $X$ is continuous map $circle.filled.small: G times X -> X$ such that $forall g, h in G$, $forall x in X$,
    - $(h g) circle.filled.small x = h circle.filled.small (g circle.filled.small x)$.
    - $1 circle.filled.small x = x$.
]
#remark[
    For the above definition, the condition $g(x) = g circle.filled.small x$ being continuous isn't required since $g$ is the composition of continuous maps: $ X limits(arrow.hook)^g G times X limits(-->)^circle.filled.small X, quad x -> (g, x) -> g circle.filled.small x $
]
#example[
    - Trivial action: $(g, x) |-> g circle.filled.small x = x$, so $circle.filled.small = pi_X$.
    - Let $G = "GL"_n (RR)$, $X = RR^n$, let the action be matrix multiplication: $(A, vd(x)) -> A circle.filled.small vd(x) = A vd(x)$. This induces an action of subgroups $O(n)$ or $"SO"(n)$ on $X = RR^n$.
    - Let $H$ subgroup of topological group $G$, *left translation action* of $H$ on $G$ is $circle.filled.small: H times G -> G$, $h circle.filled.small g = h g$. Equivalently, $phi(h) = L_h$.
    - Let $N$ normal subgroup of topological group $G$, *conjugation action* of $G$ on $N$ is $circle.filled.small: G times N -> N$, $g circle.filled.small n = g n g^(-1)$.
]
#definition[
    Let $G$ act on topological space $X$, define equivalence relation $tilde$ on $X$ by $ x tilde y <==> exists g in G: g(x) := g circle.filled.small x = y $ An equivalence class for this relation is an *orbit*, denoted $G x$. *Orbit space*, $X\/G$, is quotient space $X\/tilde$. Action is *transitive* if $X\/G$ is a singleton.
]
#example[
    - If $G$ acts trivially, every orbit is singleton and $X\/G = X$.
    - $RR^n\/"GL"_n (RR)$ contains two points and has neither discrete nor indiscrete topology.
    - Action of $O(n)$ on $S^(n - 1)$ is transitive for $n in NN$. Action of $"SO"(n)$ on $S^(n - 1)$ is transitive for $n >= 2$.
]
#lemma[
    If connected topological group $G$ acts on topological space $X$, then the orbits are connected in $X$.
]
#theorem[
    Let $G$ connected topological group act on topological space $X$. If $X\/G$ is connected, then $X$ is connected.
]
#notation[
    Define specified inclusion $i_1: M_n (RR) limits(arrow.hook)^1 M_(n + 1) (RR)$ by $A -> mat(1, 0; 0, A)$. So $M_n (RR)$ can be regarded as subspace of $M_(n + 1) (RR)$.
]
#proposition[
    - Using the inclusion $limits(arrow.hook)^1$, $"SO"(n)$ is subgroup of $"SO"(n + 1)$.
    - Viewing these as topological groups, if subgroup $"SO"(n)$ acts on $"SO"(n + 1)$, orbit space is $"SO"(n + 1)\/"SO"(n) tilde.equiv S^n$.
]
#corollary[
    The topological group $"SO"(n)$ is connected for $n in NN$.
]

#import "@preview/cetz:0.2.0": canvas
#import "@preview/cetz:0.2.0"

#let polygon(points, labels: (), show-vertices: true, color: black, centre: (0, 0), ..other) = {
    let circ = circle
    let c = centre
    let (cx, cy) = (0, 0)
    import cetz.draw: *
    // translate(x: centre.at(0), y: centre.at(1))
    for (x, y) in points {
        (cx, cy) = (cx + x, cy + y)
    }
    (cx, cy) = (cx / points.len(), cy / points.len())
    // (cx, cy) = (cx + c.at(0), cy + c.at(1))
    // circle((cx, cy), radius: 0.1)
    // let (cx, cy) = centre
    points.push(points.first())
    cetz.draw.merge-path(..other, stroke: color + 1.5pt, {
    // translate(x: centre.at(0), y: centre.at(1))
        for i in range(points.len() - 1) {
            let (x1, y1) = points.at(i)
            let (x2, y2) = points.at(i + 1)
            cetz.draw.line((x1 + c.at(0), y1 + c.at(1)), (x2 + c.at(0), y2 + c.at(1)))
        }
    })
    for i in range(points.len() - 1) {
        if show-vertices {
            let (x, y) = points.at(i)
            circle((x + c.at(0), y + c.at(1)), radius: 0.05, fill: color, stroke: none)
        }
        if labels.len() > 0 {
            let (x, y) = points.at(i)
            let (dx, dy) = (x - cx, y - cy)
            let anchor = (x + dx / 6, y + dy / 6)
            cetz.draw.content((anchor.at(0) + c.at(0), anchor.at(1) + c.at(1)), circ(fill: none, stroke: none, inset: 0.2em)[#labels.at(i)])
        }
    }
}

#let ngon(n, centre: (0, 0), radius: 1, show-vertices: true, color: black, ..other) = {
    let top = (radius, 0)
    let points = ()
    for i in range(n) {
        let x = top.at(0) * calc.cos(2*calc.pi*i/n) - top.at(1) * calc.sin(2*calc.pi*i/n)
        let y = top.at(0) * calc.sin(2*calc.pi*i/n) + top.at(1) * calc.cos(2*calc.pi*i/n)
        points.push((x, y))
    }
    return polygon(points, centre: centre, show-vertices: show-vertices, color: color, ..other)
}

= Introduction

#notation[
    Let $I = [0, 1]$.
]
#definition[
    *Closed $n$-disc* is $ D^n := {vd(x) in RR^n: norm(x) <= 1} $
]
#definition[
    *Open $n$-disc* is $ E^n := {vd(x) in RR^n: norm(x) < 1} $
]
#definition[
    *$n$-sphere* is $ S^n := {vd(x) in RR^(n + 1): norm(x) = 1} $
]
#definition[
    *Cylinder* is $S^1 times I$.
]
#definition[
    The *$2$-torus (torus)* can be defined as $TT := S^1 times S^1$ or $TT := (I times I) \/ tilde$ where $ forall x in I, (x, 0) tilde (x, 1), quad forall y in I, (0, y) tilde (1, y) $
]
#definition[
    *Klein bottle* is given by $KK := (I times I) \/ tilde$ where $ forall x in I, (x, 0) tilde (x, 1), quad forall y in I, (0, y) tilde (1, 1 - y) $
]
#definition[
    *Map* is continuous $f: X -> Y$ where $X, Y$ are topological spaces.
]

= Simplicial complexes

== Simplicial complexes and triangulations

#definition[
    Let $v_0, ..., v_n in RR^N$, $n <= N$.
    - $v_0, ..., v_n$ are in *general position* if ${v_1 - v_0, ..., v_n - v_0}$ are linearly independent.
    - *Convex hull* of $v_0, ..., v_n$ is set of all *convex linear combinations* of $v_0, ..., v_n$: $ ideal(v_0, ..., v_n) := {sum_(i = 0)^n lambda_i v_i: sum_(i = 0)^n lambda_i = 1, forall i in {0, ..., n}, lambda_i >= 0 } $
    - An *$n$-simplex*, $sigma^n = ideal(v_0, ..., v_n)$, is convex hull of $v_0, ..., v_n$ in general position. The *vertices* $v_0, ..., v_n$ *span* $sigma^n$ and $sigma^n$ is *$n$-dimensional*.
]
#example[
    - $0$-simplex is a point.
    - $1$-simplex is a closed line segment.
    - $2$-simplex is closed triangle including its interior.
    - $3$-simplex is closed tetrahedron including its interior.
]
#definition[
    If $sigma^n = ideal(v_0, ..., v_n)$ is $n$-simplex and ${i_0, ..., i_r} subset.eq {0, ..., n}$, then $ideal(v_(i_0), ..., v_(i_r))$ is $r$-simplex and $ideal(v_(i_0), ..., v_(i_r)) subset.eq sigma^n$. Any such sub-simplex is called *$r$-face* of $sigma^n$. A *proper face* is an $(n - 1)$-face. The *$i$th face* of $sigma^n$ is the $(n - 1)$-simplex $ideal(v_0, ..., v_(i - 1), v_(i + 1), ..., v_n)$.
]
#definition[
    A *finite simplicial complex* $K subset RR^N$ is finite union of simplices in $RR^N$ such that
    - If $sigma^n$ is simplex in $K$ and $tau^r$ is $r$-face of $sigma^n$, then $tau^r$ is simplex in $K$.
    - If $sigma_1^n$ and $sigma_2^m$ are simplices in $K$ with $sigma_1^n sect sigma_2^m != nothing$, then there exists $r in {0, ..., min(n, m)}$ and $r$-simplex $tau^r$ in $K$ such that $tau^r$ is $r$-face of both $sigma_1^n$ and $sigma_2^m$ and $sigma_1^n sect sigma_2^m = tau^r$.
    *Dimension* of $K$ is maximum value of $n$ for which there is an $n$-simplex in $K$.
]
#remark[
    A finite simplicial complex $K subset RR^N$ is a topological space when equipped with subspace topology from $RR^N$.
]
#remark[
    Second condition implies that two simplices can meet in at most one common face (this is important when considering quotient topologies and identifying edges with each other). It also implies that any set of $n$ vertices defines either only one or no $n$-simplices in $K$.
]
#definition[
    *Triangulation* of topological space $X$ is homeomorphism $h: X -> K$ for some finite simplicial complex $K$. We say $K$ *triangulates* $X$. $X$ is *triangulable* if it has at least one triangulation.
]
#remark[
    If a triangulation exists, it is not unique.
]
#example[
    The black and blue figures are simplicial complexes that triangulate $S^1$:
#canvas(length: 2cm, {
    ngon(3, radius: 0.7, stroke: 1.5pt)
    ngon(4, radius: 0.7, centre: (3, 0), color: blue)
})
]

== Simplicial maps

#definition[
    A map $f: K -> L$ between finite simplicial complexes $K$ and $L$ is *simplicial* if
    - For every vertex $v$ of $K$, $f(v)$ is a vertex of $L$.
    - If $sigma = ideal(v_0, ..., v_n)$ is simplex $sigma$ in $K$, $f(sigma)$ is simplex of $L$ with vertices $f(v_0), ..., f(v_n)$, where map $f|_sigma$ is defined linearly as $ f(sum_(i = 0)^n lambda_i v_i) = sum_(i = 0)^n lambda_i f(v_i) $
]
#remark[
    Vertices $f(v_0), ..., f(v_n)$ of simplex $f(sigma)$ may not be distinct, so $f(sigma)$ may be simplex of lower dimension than $sigma$.
]
#remark[
    For triangulations $h_X: X -> K_X$ and $h_Y: Y -> K_Y$ of topological spaces $X$ and $Y$, a simplicial map $f: K_X -> K_Y$ induces a map $F: X -> Y$ by $F = h_Y^(-1) compose f compose h_X$.
]
#example[
    $F: S^1 -> S^1$, $F(e^(i pi t)) = e^(2 i pi t)$ is the *2 times* map. Let $f: K_1 -> K_2$, $f(v_i) = w_(i mod 3)$, $f$ is simplicial map. Then $F$ is induced by $f$, where $K_1$ and $K_2$ are as below:
#canvas(length: 2cm, {
    ngon(6, centre: (0, 0), labels: ($v_0$, $v_1$, $v_2$, $v_3$, $v_4$, $v_5$))
    ngon(3, centre: (3, 0), labels: ($w_0$, $w_1$, $w_2$))
})
]

== Barycentric subdivision and simplicial approximation

#definition[
    *Barycentre* of $sigma^k = ideal(v_0, ..., v_k) subset RR^N$ is $ overline(sigma^k) = 1/(k + 1) (v_0 + dots.h.c + v_k) in RR^N $
]
#example[
    - Barycentre of $0$-simplex is itself.
    - Barycentre of $1$-simplex is midpoint of the line.
// #canvas(length: 2cm, {
//     ngon(3, centre: (0, 0))
//     cetz.draw.circle((0, 0), radius: 0.05, stroke: none, fill: red)
// })
]
#definition[
    Let $K subset RR^N$ be finite simplicial complex. *First barycentric subdivision* of $K$ is the simplicial complex $K^((1))$ such that:
    - The vertices of $K^((1))$ are the barycentres $overline(sigma^k)$ for every simplex $sigma^k$ in $K$.
    - The vertices $overline(sigma^(k_0)), ..., overline(sigma^(k_m)) in K^((1))$ span an $m$-simplex in $K^((1))$ if the original simplices $sigma^(k_0), ..., sigma^(k_m)$ in $K$ are (up to relabelling) strictly nested: $ sigma^(k_0) lt.curly dots.h.c lt.curly sigma^(k_m) $ where $sigma^i lt.curly sigma^j$ iff $sigma^i$ is $i$-face of $sigma^j$ with $i < j$ (thus $k_0 < dots.h.c < k_m$).
]
#definition[
    The $r$th barycentric subdivision of $K$ is defined inductively for $r > 1$ by $K^((r)) := (K^((r - 1)))^((1))$.
]
#proposition[
    Let $K$ be finite simplicial complex.
    - If $K$ is triangulation of topological space $X$, then so is $K^((r))$ for all $r in NN$.
    - Each simplex in $K^((1))$ is contained in a simplex of $K$.
    - If $dim(K) = n$, then length of longest $1$-simplex in $K^((1))$ is at most $n\/(n + 1)$ times length of longest $1$-simplex in $K$.
]
#theorem("Simplicial approximation theorem")[
    For each $i in {1, 2}$, let $h_i: X_i -> K_i$ be triangulation of topological space $X_i$ by finite simplicial complex $K_i$. Let $f: X_1 -> X_2$ be map. Then $forall epsilon > 0$ there exist $n, m in NN$ and a simplicial map $s: K_1^((n)) -> K_2^((m))$ such that for $F := h_2 compose f compose h_1^(-1)$, $ s tilde.eq F quad "and" quad forall x in K_1, quad |F(x) - s(x)| < epsilon $
]

= Surfaces

== Surfaces

#definition[
    Let $S$ be Hausdorff, compact, connected topological space.
    - $S$ is *surface* if for all $x in S$, there exists $U subset.eq S$ such that $x in U$ and $U tilde.equiv E^2$ or $U tilde.equiv E^2 sect (RR times RR_(>=0)) =: E^2 sect RR_+^2$.
    - *Boundary* of $S$, $diff S$, is set of all $x in S$ such that there is not a $U subset.eq S$ with $x in U$ and $U tilde.equiv E^2$.
    - *Interior* of $S$ is $"int"(S) := S - diff S$.
    - $S$ is *closed surface* if $diff S = emptyset$ ($S$ is *locally Euclidean of dimension 2*).
    - $S$ is *surface with boundary* if $diff S != emptyset$. Surface with boundary is closed surface from which interiors of finite number of pairwise disjoint closed discs have been removed.
]
#definition[
    Let $K$ be finite simplicial complex, $x in K$. *Open star* of $x$ in $K$, $"St"(x, K)$, is union of ${x}$ and interiors of all simplices containing $x$.
]
#example[
    Let $K$ be 2d finite simplicial complex, $x in K$.
    - If there exists a $2$-simplex $sigma^2 subset.eq K$ such that $x in "int"(sigma^2)$, then $St(x, K) = int(sigma^2) tilde.equiv E^2$.
    - If there exists a $1$-simplex $sigma^1 subset.eq K$ such that $x in int(sigma^1)$, then $ St(x, K) = int(sigma^1) union {int(sigma^2): sigma^1 "is face of" sigma^2 subset.eq K, sigma^2 "is 2-simplex"} $ Here, $St(x, K) tilde.equiv E^2$ iff there are exactly two $2$-simplices meeting along $sigma^1$.
    - If $x in K$ is vertex, then $ St(x, K) = {x} & union {int(sigma^1): x "vertex of" sigma^1 subset.eq K, sigma^1 "is 1-simplex"} \ & union {int(sigma^2): x "vertex of" sigma^2 subset.eq K, sigma^2 "is 2-simplex"} $ Here $St(x, K) tilde.equiv E^2$ iff $x$ is vertex of $n >= 3$ $2$-simplices, and along any of its edges containing $x$, each of these $2$-simplices meets precisely one other $2$-simplex (from the remaining $n - 1$).
]
#lemma[
    Let $M$ be topological space triangulated by connected, finite simplicial complex $K$. Then $M$ is closed surface iff $ forall x in K, quad St(x, K) tilde.equiv E^2 $ and the ways that this can happen are as listed above, with exactly two $2$-simplices meeting along each $1$-simplex.
]
#remark[
    If $h: M -> K$ is triangulation of topological space $M$ and $dim(K) != 2$, then $M$ is not closed surface. It is enough to check the open star condition (in above example) at all vertices of $K$: if there is $x in K$ such that $St(x, K) tilde.equiv.not E^2$, then there exists vertex $v$ of $K$ such that $St(v, K) tilde.equiv.not E^2$.
]
#corollary[
    Let $X$ topological space, triangulated by connected finite simplicial complex $K$, $dim(K) = 2$. Then $X$ is closed surface iff for every vertex $v in K$, $St(v, K) tilde.equiv E^2$.
]
#remark[
    This means $X$ is closed surface if open star of every vertex of triangulation of $X$ is homeomorphic to union of two copies of $E^2 sect RR_+^2$ glued along the parts of their boundaries that are contained in $E^2 sect RR_+^2$.
]
#remark[
    If we remove an edge from the open star of a vertex, and this produces a disjoint union of open sets, the original space cannot be a surface, since removing a segment from $E^2$ yields a connected space and removing a segment from $E^2 sect RR_+^2$ yields either a connected space or a disjoint union of two non-open sets.
]
#definition[
    *Real projective plane* is closed surface arising from identifying the edges of the unit square with the following: $ PP := (I times I)\/tilde, quad (x, 0) tilde (1 - x, 1), quad (0, y) tilde (1, 1 - y) $ It may also be defined as quotient of $S^2$ by identifying diametrically opposite points: $ PP = S^2 \/ tilde, quad forall x in S^2, quad x tilde -x $
]

== Orientations on surfaces

#definition[
    An *orientation on $RR^2$* is choice of direction in which to travserse circles around the origin. There are exactly two choices.
]
#definition[
    *Simple closed curve* in topological space is subspace homeomorphic to circle, i.e. connected curve with no self-intersections and ends where it begins.
]
#definition[
    Surface $S$ is *orientable* if for all $x in int(S)$, any choice of local orientation at $x$ is preserved after translation along any simple closed curve in $int(S)$ containing $x$. $S$ is *non-orientable* if there exists $x in int(S)$ and simple closed curve $C subset.eq int(S)$ through $x$ such that translation along $C$ reverses any choice of local orientation at $x$. Every surface is either orientable or non-orientable.
]
#remark[
    Orientability or non-orientability respectively correspond to the surface having two sides or one side.
]
#example[
    $S^2, TT$ are orientable. Mobius band and Klein bottle are non-orientable.
]
#lemma[
    $S$ is non-orientable iff it contains subspace homeomorphic to Mobius band.
]
#theorem[
    Let $S_1, S_2$ be homeomorphic surfaces. $S_1$ is orientable iff $S_2$ is orientable.
]
#remark[
    $2$-simplex can be given orientation by drawing a direction around it (anticlockwise or clockwise) or by drawing direction around its boundary. A $2$-simplex can be oriented in 2 ways, which can be represented by ordering of the vertices: $ideal(v_0, v_1, v_2)$, $ideal(v_1, v_2, v_0)$ and $ideal(v_2, v_0, v_1)$ represent same orientation, $ideal(v_1, v_0, v_2)$ represents different orientation.
]
#definition[
    Let $K$ finite simplicial complex that triangulates surface $S$ such that all $2$-simplices in $K$ are oriented.
    - The orientations of two $2$-simplices in $K$ which share an edge are *compatible* if they induce opposite orientations on the shared edge.
    - $K$ is *$Delta$-orientable* if there exists choice of orientations on its $2$-simplices such that any two $2$-simplices which share an edge have compatible orientations. Such a choice, if it exists, is a *$Delta$-orientation* on $K$.
]
#theorem[
    Surface is orientable iff one (and so every) finite simplicial complex which triangulates it is $Delta$-orientable.
]

== Constructions on surfaces

#definition[
    For surfaces $S_1, S_2$, their *connected sum*, $S_1 \# S_2$, is obtained by removing the interiors of one small open disc from interior of each surface, and identifying the two newly formed boundary circles. If $S_1, S_2$ oriented, directions around the boundary circles induced by the respective orientations must be identified such that the directions are opposite to each other. Then $S_1 \# S_2$ inherits an orientation which agrees (upon restriction) with those of the original surfaces $S_1$ and $S_2$.
]
#proposition[
    - Since $S_1$, $S_2$ connected, it does not matter which two open discs are removed, the result is the same up to homeomorphism.
    - $\#$ is commutative and associative.
    - $S^2$ is the identity for $\#$ operation: $M \# S^2 tilde.equiv M$.
]
#definition[
    For $g in NN_0$, *closed orientable surface of genus $g$ ($g$-holed torus)* is $ M_g = S^2 \# underbrace(T \# dots.h.c \# T, g "times") $
]
#example[
    The Klein bottle is given by $KK tilde.equiv PP \# PP$.
]
#definition[
    *Adding handle* to surface $S$ is as follows: remove two open discs from $S$. Attach the ends of cylinder $S^1 times I$ to the resulting boundary circles. If $S$ (and cylinder) are oriented, require that the two resulting boundary circles are glued to those of the cylinder with opposite orientations, which ensures the new surface is still oriented. But if $S$ is not orientable, this doesn't matter, as all possible results are homeomorphic.
]
#example[
    - $S^2$ with handle added is homeomorphic to the torus.
    - $S^2$ with $g$ handles added is homeomorphic to $M_g$.
    - $M_n$ with handle added is homeomorphic to $M_(n + 1)$.
]
#definition[
    *Attaching a cross cap (Mobius band)* to surface $S$ is as follows: remove open disc from $S$, and identify resulting boundary circle with boundary circle of Mobius band. Attaching a cross-cap always makes the surface non-orientable.
]
#example[
    Adding cross-cap to $S^2$ gives real projective plane $PP$.
]
#remark[
    Connected sums of surfaces, surfaces with handles and surfaces with cross caps are always surfaces.
]

= Homotopy and the fundamental group

== Homotopy

#definition[
    The *stereographic projection* is the bijection $ phi: S^n - (0, ..., 0, 1) -> RR^n, quad (y_1, ..., y_(n + 1)) |-> (y_1/(1 - y_(n + 1)), ..., y_n/(1 - y_(n + 1))) $
]
#definition[
    Let $X, Y$ topological spaces. *Homotopy* between maps $f: X -> Y$ and $g: X -> Y$ is map $H: X times [0, 1] -> Y$ with $ forall x in X, quad H(x, 0) = f(x) and H(x, 1) = g(x) $ $f$ and $g$ are *homotopic*, $f tilde.eq g$, if there is a homotopy between them. We can think of homotopy as "path of maps" starting at $f: X -> Y$ and ending at $g: X -> Y$: for $t in [0, 1]$, define $h_t: X -> Y$, $h_t (x) = H(x, t)$, which varies continuously from $f$ at $t = 0$ to $g$ at $t = 1$.
]
#example[
    Let $f, g: RR -> RR$ maps, then $ H: RR times [0, 1] -> RR, quad (x, t) |-> (1 - t) f(x) + t g(x) $ is homotopy between $f$ and $g$.
]

#import "@preview/cetz:0.2.0": canvas, plot

#let f(x) = (x - 2) * (x - 1) * (x + 3)
#let g(x) = -(x + 3) * (x - 0.5) * (x - 2.5) + 10

#figure(canvas(length: 1cm, {
    plot.plot(
        axis-style: "school-book",
        size: (12, 6),
        x-tick-step: none,
        // x-ticks: ((-2, $-2$), (4, $4$)),
        y-tick-step: none,
        // y-ticks: ((2, $2$), (-4, $-4$)),
        {plot.add(
            style: (stroke: red + 2pt),
            domain: (-3, 3), x => f(x),
            // mark: "o",
            label: $ f(x) $
        )
        plot.add(
            style: (stroke: blue + 2pt),
            domain: (-3, 3), x => g(x),
            label: $ g(x) $
        )
        plot.add(
            style: (stroke: color.mix((red, 30%), (blue, 70%)) + 2pt),
            domain: (-3, 3), x => f(x) * (1 - 0.7) + g(x) * 0.7,
            label: $ 0.3 f(x) + 0.7 g(x) $
        )
        plot.add(
            style: (stroke: color.mix((red, 80%), (blue, 20%)) + 2pt),
            domain: (-3, 3), x => f(x) * (1 - 0.2) + g(x) * 0.2,
            label: $ 0.8 f(x) + 0.2 g(x) $
        )}
    )
}))
#example[
    Consider $S^1 subset CC$, so $S^1 = {e^(i pi s): s in [0, 2)}$. Let $a: S^1 -> S^1$ be the *antipodal map*, $a(e^(i pi s)) = -e^(i pi s)$. Then $a tilde.eq id$, with homotopy given by $H: S^1 times I -> S^1$, $H(e^(i pi s)) = e^(i pi (s + t))$.
]
#lemma[
    Homotopy is equivalence relation between maps.
]
#definition[
    Map $f: X -> Y$ is *null homotopic* if it is homotopic to a constant map, i.e. to map $c: X -> Y$ with $c(x) = y_0$, $y_0 in Y$ fixed.
]
#example[
    Identity map $id_(D^2): D^2 -> D^2$ is null homotopic: let $c: D^2 -> D^2$, $c(x) = 0$. Consider $H: D^2 times [0, 1] -> D^2$, $H(x, t) = (1 - t)x$, then $H$ is homotopy between $id_(D^2)$ and $c$, since $H$ is continuous and $H(x, 0) = x = id_(D^2)(x)$, $H(x, 1) = 0 = c(x)$.
]
#definition[
    Map $f: X -> Y$ is *homotopy equivalence* if there exists a map $g: Y -> X$ (a *homotopy inverse*) such that $g compose f tilde.eq id_X$ and $f compose g tilde.eq id_Y$. $X$ and $Y$ are *homotopy equivalent*, $X tilde.eq Y$ if there exists homotopy equivalence between them. If $X tilde.eq Y$, we say they have the same *homotopy type*.
]
#theorem[
    Homotopy equivalence is equivalence relation on topological spaces.
]
#example[
    Let $P = {vd(p)}$ be the one point space, then $D^2 tilde.eq P$: let $f: D^2 -> P$, $f(x) = vd(p)$, $g: P -> D^2$, $g(vd(p)) = 0$. Then $f compose g = id_P tilde.eq id_P$. Now $forall x in D^2$, $(g compose f) (x) = 0$ so $g compose f tilde.eq id_(D^2)$ as $g compose f$ is constant map.
]
#definition[
    Topological space $X$ is *contractible* if it is homotopy equivalent to a one-point space.
]
#example[
    Let $X$ topological space. The *cone on $X$* is $ C X = (X times [0, 1])\/tilde $ where $tilde$ identifies all points of the form $(x, 0)$ with each other, i.e. it collapses the end $X times {0}$ to a single point. We have $D^n tilde.equiv C S^(n - 1)$.
]
#proposition[
    For all topological spaces $X$, the cone $C X$ is contractible.
]
#example[
    For a finite simplicial complex $K subset RR^N$, $C K subset RR^(N + 1)$ has vertices equal to vertices of $K$ together with $P = (0, ..., 0, 1) in RR^(N + 1)$. Simplices in $C K$ of dimension $>= 1$ are those in $K$ together with all simplices $ideal(v_0, ..., v_r, P)$ where $ideal(v_0, ..., v_r)$ is simplex in $K$.
]
#lemma[
    Every contractible space is path connected.
]
#lemma[
    If $X$ and $Y$ are homeomorphic, they are homotopy equivalent (converse does not hold).
]
#definition[
    - It is useful to assume that every topological space $X$ has a particular distinguished *base point* $x_0 in X$.
    - We then require that all maps and homotopies between spaces map base points to base points.
    - The pair $(X, x_0)$ is a *based space*.
    - If $K$ is finite simplicial complex and $v_0$ is vertex of $K$, then $(K, v_0)$ is *pointed*.
    - A *based map* $f: (X, x_0) -> (Y, y_0)$ is a map $X -> Y$ and satisfies $f(x_0) = y_0$.
    - A *based homotopy* $H: (X, x_0) times [0, 1] -> (Y, y_0)$ between based maps $f, g: (X, x_0) -> (Y, y_0)$ is homotopy $H: X times [0, 1] -> Y$ with $forall t in [0, 1]$, $H(x_0, t) = y_0$.
    - All results shown for homotopies are true for based homotopies.
]

== The fundamental group

#remark[
    We consider circle $S^1$ as unit circle in $CC$ and give it base point $1$.
]
#definition[
    A *loop* in based space $(X, x_0)$ is based map $ lambda: (S^1, 1) -> (X, x_0) $ Equivalently, a loop in $(X, x_0)$ is path in $X$ beginning and ending at $x_0$: $ lambda: [0, 1] -> (X, x_0), quad lambda(0) = lambda(1) = x_0 $ Two loops $lambda, mu: [0, 1] -> (X, x_0)$ are homotopic if there exists based homotopy between them, i.e. if there is map $ & H: [0, 1] times [0, 1] -> X, \ forall s in I, quad & H(s, 0) = lambda(s), \ forall s in I, quad & H(s, 1) = mu(s), \ forall t in I, quad & H(0, t) = H(1, t) = x_0 $ This corresponds with $lambda$ being continuously deformed into $mu$.
]
#remark[
    It is useful to represent based homotopy $H$ between $lambda$ and $mu$ on the unit square. Bottom edge corresponds to $lambda$, top edge corresponds to $mu$, right and left edges are mapped entirely to $x_0$. Horizontal line drawn across unit square represents loop in $(X, x_0)$ and homotopy $H$ describes path of loops from $lambda$ to $mu$. Vertical line describes path traced from $lambda(s)$ to $mu(s)$ under $H$.
]
#figure(canvas(length: 2cm, {
    import cetz.draw: *
    cetz.draw.rect((0, 0), (1, 1), name: "my-rect")
    set-style(mark: (end: ">"))
    line((0, 0), (1/2 + 0.1, 0))
    line((0, 1), (1/2 + 0.1, 1))

    content("my-rect.center", box(fill: white)[$H$], anchor: "center")
    content("my-rect.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("my-rect.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("my-rect.north", padding: -1.2em, box(fill: white)[$lambda$], anchor: "north")
    content("my-rect.south", padding: -1.2em, box(fill: white)[$mu$], anchor: "south")
}))
#definition[
    *Homotopy class* of loop $lambda$ in $(X, x_0)$ is $ [lambda] := {mu: mu "loop in" (X, x_0), mu tilde.eq lambda} $ *Fundamental group* of $(X, x_0)$ is set of homotopy classes of loops in $(X, x_0)$: $ pi_1 (X, x_0) := {[lambda]: lambda "loop in" (X, x_0)} $ with group operation $*$ defined by $ *: pi_1 (X, x_0) times pi_1 (X, x_0) & -> pi_1 (X, x_0), \ ([lambda_1], [lambda_2]) -> [lambda_1 * lambda_2] $ where *concatenation (product)* of $lambda_1$ and $lambda_2$ is the loop in $(X, x_0)$ given by $ lambda_1 * lambda_2: [0, 1] & -> X, \ s & |-> cases(lambda_1 (2s) & "if" 0 <= s <= 1/2, lambda_2 (2s - 1) & "if" 1/2 <= s <= 1) $ Group identity is $e: [0, 1] -> X$, $e(s) = x_0$, inverse of loop $lambda$ is $overline(lambda): s |-> lambda(1 - s)$, then $[overline(lambda)] = [lambda]^(-1)$ (equivalently, define $[lambda]^(-1) = [lambda compose w]$ where $w: [0, 1] -> [0, 1]$, $w(s) = 1 - s$).
]
#remark[
    Group operation $*$ is well defined, since if $lambda_1 tilde.eq mu_1$ by homotopy $H_1$, $lambda_2 tilde.eq mu_2$ by homotopy $H_2$, then $lambda_1 * lambda_2 tilde.eq mu_1 * mu_2$ by homotopy $H$ where $ H(s, t) = cases(H_1 (2s, t) & "if" 0 <= s <= 1/2, H_2 (2s - 1, t) & "if" 1/2 <= s <= 1) $
]
#figure(canvas(length: 2cm, {
    import cetz.draw: *
    cetz.draw.rect((0, 0), (1, 1), name: "H_1")
    cetz.draw.rect((2, 0), (3, 1), name: "H_2")
    cetz.draw.rect((4, 0), (4.5, 1), name: "H")
    cetz.draw.rect((4.5, 0), (5, 1), name: "I")
    set-style(mark: (end: ">"))
    line((0, 0), (1/2 + 0.1, 0))
    line((0, 1), (1/2 + 0.1, 1))
    line((2, 0), (2 + 1/2 + 0.1, 0))
    line((2, 1), (2 + 1/2 + 0.1, 1))
    line((4, 0), (4 + 1/4 + 0.1, 0))
    line((4, 1), (4 + 1/4 + 0.1, 1))
    line((4.5, 0), (4.5 + 1/4 + 0.1, 0))
    line((4.5, 1), (4.5 + 1/4 + 0.1, 1))

    content("H_1.center", box(fill: white)[$H_1$], anchor: "center")
    content("H_1.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("H_1.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("H_1.north", padding: -1.2em, box(fill: white)[$lambda_1$], anchor: "north")
    content("H_1.south", padding: -1.2em, box(fill: white)[$mu_1$], anchor: "south")

    content("H_2.center", box(fill: white)[$H_2$], anchor: "center")
    content("H_2.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("H_2.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("H_2.north", padding: -1.2em, box(fill: white)[$lambda_2$], anchor: "north")
    content("H_2.south", padding: -1.2em, box(fill: white)[$mu_2$], anchor: "south")

    content("H.center", box(fill: white)[$H_1$], anchor: "center")
    content("H.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("H.north", padding: -1.2em, box(fill: white)[$lambda_1$], anchor: "north")
    content("H.south", padding: -1.2em, box(fill: white)[$mu_1$], anchor: "south")

    content("I.center", box(fill: white)[$H_2$], anchor: "center")
    content("I.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("I.north", padding: -1.2em, box(fill: white)[$lambda_2$], anchor: "north")
    content("I.south", padding: -1.2em, box(fill: white)[$mu_2$], anchor: "south")
}))
Associativity between $(lambda * mu) * kappa$ and $(lambda * (mu * kappa))$ is shown by homotopy diagram with $(lambda * mu) * kappa$ at bottom and $lambda * (mu * kappa)$ at top. At any intermediate time, path traverses $lambda$ at between 2 and 4 times speed, and correspondingly adjusts speed of $kappa$ to finish path at $t = 1$. $mu$ is traversed at 4 times speed at all times.
#figure(canvas(length: 3cm, {
    import cetz.draw: *
    cetz.draw.rect((0, 0), (1, 1), name: "my-rect")
    line((1/4, 0), (1/2, 1))
    line((1/2, 0), (3/4, 1))
    set-style(mark: (end: ">"))
    line((0, 0), (1/8 + 0.07, 0), name: "l1")
    line((0, 1), (1/4 + 0.07, 1), name: "l2")
    line((1/4, 0), (1/4 + 1/8 + 0.07, 0), name: "l3")
    line((1/2, 1), (1/2 + 1/8 + 0.07, 1), name: "l4")
    line((1/2, 0), (1/2 + 1/4 + 0.07, 0), name: "l5")
    line((3/4, 1), (3/4 + 1/8 + 0.07, 1), name: "l6")

    content("l1.end", padding: 0.4em, box(fill: white)[$lambda$], anchor: "north-east")
    content("l2.end", padding: 0.4em, box(fill: white)[$lambda$], anchor: "south-east")
    content("l3.end", padding: 0.4em, box(fill: white)[$mu$], anchor: "north-east")
    content("l4.end", padding: 0.4em, box(fill: white)[$mu$], anchor: "south-east")
    content("l5.end", padding: 0.4em, box(fill: white)[$kappa$], anchor: "north-east")
    content("l6.end", padding: 0.4em, box(fill: white)[$kappa$], anchor: "south-east")

    content("my-rect.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("my-rect.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
}))
Can show identity $e(s) = x_0$ satisfies $[lambda] * [e] = [e] * [lambda] = [lambda]$ with diagrams
#figure(canvas(length: 3cm, {
    import cetz.draw: *
    rect((0, 0), (1, 1), name: "el")
    rect((2, 0), (3, 1), name: "le")
    line((1/2, 0), (1, 1))
    line((2 + 1/2, 0), (2, 1))
    set-style(mark: (end: ">"))
    line((0, 0), (1/4 + 0.07, 0), name: "l1")
    line((0, 0), (3/4 + 0.07, 0), name: "l2")
    line((0, 1), (1/2 + 0.07, 1))
    line((2, 0), (2 + 1/4 + 0.07, 0), name: "l3")
    line((2, 0), (2 + 3/4 + 0.07, 0), name: "l4")
    line((2, 1), (2 + 1/2 + 0.07, 1))

    content("l1.end", padding: 0.4em, box(fill: white)[$lambda$], anchor: "north-east")
    content("l2.end", padding: 0.4em, box(fill: white)[$e$], anchor: "north-east")
    content("l3.end", padding: 0.4em, box(fill: white)[$e$], anchor: "north-east")
    content("l4.end", padding: 0.4em, box(fill: white)[$lambda$], anchor: "north-east")

    content("el.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("el.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("el.north", padding: -1.2em, box(fill: white)[$lambda$], anchor: "north")

    content("le.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("le.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("le.north", padding: -1.2em, box(fill: white)[$lambda$], anchor: "north")
}))
Can show that $[lambda] * \[overline(lambda)\] = \[overline(lambda)\] * [lambda] = e$ by
#figure(canvas(length: 3cm, {
    import cetz.draw: *
    rect((0, 0), (1, 1), name: "el")
    rect((2, 0), (3, 1), name: "le")
    line((1/2, 0), (1, 1))
    line((1/2, 0), (0, 1))
    line((2 + 1/2, 0), (2, 1))
    line((2 + 1/2, 0), (3, 1))
    set-style(mark: (end: ">"))
    line((0, 0), (1/4 + 0.07, 0), name: "l1")
    line((0, 0), (3/4 + 0.07, 0), name: "l2")
    line((0, 1), (1/2 + 0.07, 1))
    line((2, 0), (2 + 1/4 + 0.07, 0), name: "l3")
    line((2, 0), (2 + 3/4 + 0.07, 0), name: "l4")
    line((2, 1), (2 + 1/2 + 0.07, 1))

    content("l1.end", padding: 0.4em, box(fill: white)[$lambda$], anchor: "north-east")
    content("l2.end", padding: 0.4em, box(fill: white)[$overline(lambda)$], anchor: "north-east")
    content("l3.end", padding: 0.4em, box(fill: white)[$overline(lambda)$], anchor: "north-east")
    content("l4.end", padding: 0.4em, box(fill: white)[$lambda$], anchor: "north-east")

    content("el.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("el.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("el.north", padding: -1.2em, box(fill: white)[$e$], anchor: "north")

    content("le.west", padding: -1.2em, box(fill: white)[$x_0$], anchor: "west")
    content("le.east", padding: -1.2em, box(fill: white)[$x_0$], anchor: "east")
    content("le.north", padding: -1.2em, box(fill: white)[$e$], anchor: "north")
}))
where, for the first diagram, a horizontal path at fixed $t$ is given by $ s |-> cases(lambda(2s) & "if" 0 <= s <= (1 - t)/2, lambda(1 - t) & "if" (1 - t)/2 <= s <= (1 + t)/2, overline(lambda)(2s - 1) & "if" (1 + t)/2 <= s <= 1) $
#definition[
    Let $f: (X, x_0) -> (Y, y_0)$ based map. Define a function $ f_*: pi_1 (X, x_0) -> pi_1 (Y, y_0), quad f_* ([lambda]) := [f compose lambda] $
]
#lemma[
    $f_*: pi_1 (X, x_0) -> pi_1 (Y, y_0)$ is well-defined and group homomorphism.
]
#proof[
    - Well-defined: show that $lambda_1 tilde.eq lambda_2 ==> f compose lambda_1 tilde.eq f compose lambda_2$ (use definition of $lambda_1 tilde.eq lambda_2$).
    - Homomorphism: use that $f compose (lambda * mu) = (f compose lambda) * (f compose mu)$.
]
#lemma[
    Let $f, g: (X, x_0) -> (Y, y_0)$ based maps, $f tilde.eq g$ ($f$ and $g$ are based homotopic), then $f_* = g_*$.
]
#proof[
    For loop $lambda$ in $(X, x_0)$, find based homotopy between $f compose lambda$ and $g compose lambda$ in terms of based homotopy $H$ between $f$ and $g$.
]
#lemma[
    The operation of passing from based map $f$ to induced homomorphism $f_*$ preserves/respects composition and the identity, i.e. if we have $ (X, x_0) limits(-->)^f (Y, y_0) limits(-->)^g (Z, z_0) $ then $(g compose f)_* = g_* compose f_*$ and $(id_X)_* = id_(pi_1 (X, x_0))$.
]<induced-homo-preserves-composition-identity>
#proof[
    Straightforward, just use the definition of $f_*$.
]
#corollary[
    Fundamental group is homotopy-invariant: if $(X, x_0)$, $(Y, y_0)$ are homotopy equivalent, then $ pi_1 (X, x_0) tilde.equiv pi_1 (Y, y_0) $
]
#proof[
    Use definition of homotopy equivalent based spaces and above lemma, to show the induced homomorphisms of the homotopy equivalences are inverse to each other.
]
#theorem[
    Let $X$ path-connected space, $x_0, x_1 in X$. Then $ pi_1 (X, x_0) tilde.equiv pi_1 (X, x_1) $
]
#proof[
    - There is path $p$ from $x_0$ to $x_1$.
    - Let $lambda$ loop in $X$ based at $x_0$.
    - Define $overline(p)(s) = p(1 - s)$, define loop $lambda_p$ in $X$ based at $x_1$ by $ lambda_p (s) = cases(overline(p(3s)) & "if" s in [0, 1\/3], lambda(3s - 1) & "if" s in [1\/3, 2\/3], p(3s - 2) & "if" s in [2\/3, 1]) $
    - Claim: $ Phi_p: pi_1 (X, x_0) -> pi_1 (X, x_1), quad Phi_p ([lambda]) = [lambda_p] $ is isomorphism.
        - Well-defined: show if $lambda, mu$ loops based at $x_0$, $lambda tilde.eq mu ==> lambda_p tilde.eq mu_p$ by homotopy diagram (merge $overline(p), lambda, p$ on bottom and $overline(p), mu, p$ on top).
        - Homomorphism: show $(lambda times mu)_p tilde.eq lambda_p * mu_p$ using homotopy diagram (for each $t in [0, 1]$, we want to partially traverse $p$ (until $s = 1/2$) then back along $overline(p)$, before traversing $mu$).
        - Isomorphism: show that $Phi_(overline(p))$ defined analogously satisfies $Phi_(overline(p)) = \(Phi_p\)^(-1)$, i.e. $\(lambda_p\)_(overline(p)) tilde.eq lambda$ and $\(mu_(overline(p))\)_p tilde.eq mu$ for all loops $lambda$ based at $x_0$, $mu$ based at $x_1$. (As $t -> 1$, want to retract the spurs $p * overline(p)$ of the loop back to $x_0$).
]
#notation[
    Write $pi_1 (X)$ for fundamental group of path-connected space $X$ (although isomorphism between $pi_1 (X, x_0)$ and $pi_1 (X, x_1)$ is not canonical).
]
#proposition[
    Let $X$ contractible space, then $pi_1 (X) tilde.equiv bb(1)$, the trivial group with one element.
]
#proof[
    - Show we can omit based point in notation.
    - Reason that there is only loop in one point space.
    - Use definition of contractibility and above corollary.
]
#definition[
    Topological space $X$ is *simply connected* if path-connected and $pi_1 (X) = bb(1)$ (i.e. its fundamental group is trivial).
]
#example[
    - $pi_1 (S^1) tilde.equiv ZZ$ where $n in ZZ$ corresponds to homotopy class of *$n$ times* map $phi_n: S^1 -> S^1$, $phi_n (z) = z^n$.
    - $pi_1 (S^n) tilde.equiv bb(1)$ for all $n >= 2$.
    - $pi_1 (T) tilde.equiv ZZ^2$.
    - $pi_1 (PP) tilde.equiv ZZ\/2$.
]<fundamental-group-examples>

== Brouwer's fixed point theorem

#theorem[
    Every map $f: D^2 -> D^2$ has a fixed point: $ exists x in D^2: f(x) = x $
]
#proof[
    - Assume no fixed point, so every $x, f(x) in D^2$ defines straight line $L_x$ passing through $D^2$.
    - Define $g(x)$ as point of intersection of boundary and $L_x$ (the one closer to $x$ than $f(x)$). Note $g(x) = x$ if $x in diff D^2$.
    - Let $i: S^1 -> D^2$ be inclusion map of boundary circle to disc, then $g compose i = id_(S^1)$, and $g_* compose i_* = (g compose i)_* = id_(pi_1 (S^1))$.
    - Obtain contradiction using @induced-homo-preserves-composition-identity and @fundamental-group-examples.
]

= Computing the fundamental group

== Finitely presented groups

#definition[
    *Free group on $n$ letters* $x_1, ..., x_n$, $F^n = ideal(x_1, ..., x_n)$, is the group whose elements are finite words in the generators $x_1, ..., x_n$ and their formal inverses $x_1^(-1), ..., x_n^(-1)$, where the group operation $*$ is given by concatenation of words: $x_i * x_j = x_i x_j$. Identity element is the empty word $e$. We assume $forall i in [n], thick thick x_i x_i^(-1) = x_i^(-1) x_i = e$.
]
#notation[
    If $k in ZZ$, then define $ x_j^k = cases(e & "if" k = 0, x_j ... x_j & "if" k > 0, x_j^(-1) ... x_j^(-1) & "if" k < 0) $
]
#note[
    $F^n$ is not abelian for all $n >= 2$ since e.g. $x_1 x_2 != x_2 x_1$. $forall n in NN$, $F^n$ is infinite group.
]
#example[
    - $F^1 = ideal(x) tilde.equiv ZZ$ since every element is of the form $x^k$, $k in ZZ$. There is isomorphism $phi: F^1 -> ZZ$ given by $phi(x) = 1$.
    - $F^2 = ideal(x, y) tilde.equiv.not ZZ^2 = ZZ xor ZZ$ since $x y != y x$.
]
#definition[
    *Finitely presented group* is group which isomorphic to a group denoted by the *group presentation* $ ideal(x_1, ..., x_n | r_1, ..., r_m) $ consisting of finite words in *generators* $x_1, ..., x_n$ and their formal inverses $x_1^(-1), ..., x_n^(-1)$, subject to *relations* $r_1, ..., r_m in F^n = ideal(x_1, ..., x_n)$ (i.e. $forall j in [m], thick thick r_j = r_j^(-1) = e$), and group operation is concatenation of words.
]
#note[
    - A finitely presented group is a quotient of a free group.
    - Free groups on $n$ letters are finitely presented (with no relations).
    - Group presentations are *not unique*.
]
#example[
    - $ideal(x, y | x y^(-1)) tilde.equiv ideal(a) = F^1 tilde.equiv ZZ$ via isomorphism $phi: ideal(x, y | x y^(-1)) -> ideal(a)$ defined by $phi(x) = phi(y) = a$ since $x y^(-1) = e <==> x = y$ so can replace every $y$ in words of $ideal(x, y | x y^(-1))$ with $x$, yielding an element of $ideal(x)$.
    - $ZZ\/2 tilde.equiv ideal(x | x^2)$ since $x = x^(-1)$ and $forall n in NN$, $x^(-n) = x^n = e$ if $n$ even, $x$ if $n$ odd.
    - $ideal(x, y | x y x^(-1) y^(-1)) tilde.equiv ZZ^2$ since $x y = y x$ so the group is abelian. Isomorphism given by $phi(x) = (1, 0)$, $phi(y) = (0, 1)$.
    - $ideal(x, y | x y x^(-1) y^(-1), y^2) tilde.equiv ZZ times ZZ\/2$.
]
#definition[
    Let $G_1, G_2$ finitely presented groups, $G_1 sect G_2 = emptyset$, given by $ G_1 = ideal(x_1, ..., x_n | r_1, ..., r_m), quad G_2 = ideal(y_1, ..., y_k | s_1, ..., s_ell) $ *Free product* of $G_1$ and $G_2$ is the finitely presented group $ G_1 * G_2 := ideal(x_1, ..., x_n, y_1, ..., y_m | r_1, ..., r_k, s_1, ..., s_ell) $ If $H$ is another group and there exist homomorphisms $i_1: H -> G_1$, $i_2: H -> G_2$, then *amalgamated product* of $G_1$ and $G_2$ with respect to $H$ is $ G_1 *_H G_2 := ideal(x_1, ..., x_n, y_1, ..., y_k | r_1, ..., r_m, s_1, ..., s_ell, i_1 (h) i_2 (h)^(-1) thick forall h in H) $ i.e. we impose the additional relations $i_1 (h) = i_2 (h)$ for all $h in H$, on $G_1 * G_2$. $G_1 *_H G_2$ is finitely presented iff $H$ is finitely generated.
]
#example[
    - If $H tilde.equiv bb(1)$, then $G_1 *_H G_2 = G_1 * G_2$.
    - If $F^n$, $F^k$ are free groups, then $F^n * F^k = F^(n + k)$.
    - $F^n = F^1 * dots.h.c * F^1 tilde.equiv ZZ * dots.h.c * ZZ$ (not this is $tilde.equiv.not ZZ^n$ for $n >= 2$).
    - If $G_1 tilde.equiv bb(1)$, then $ G_1 *_H G_2 = ideal(y_1, ..., y_k | s_1, ..., s_ell, i_2 (h) thick forall h in H) $
]

== The fundamental group of a triangulated surface

#definition[
    *Tree* is finite, connected graph with no cycles.
]
#definition[
    Let $K$ be connected, finite simplicial complex of dimension $<= 2$.
    - A *maximal tree* in $K$ is tree formed out of the $0$ and $1$-simplices in $K$ which cannot be extended to any larger tree (and necessarily contains all $0$-simplices).
    - If $L$ is maximal tree in $K$, *maximal simply connected subcomplex* $M$ of $K$ (associated to $L$) is constructed as follows: let $M_0 = L$ and for each $j in NN$, let $M_j$ be subcomplex of $K$ given by $ M_j = M_(j - 1) union {"2-simplices in" K "with two edges contained in" M_(j - 1)} $ Since $K$ is finite simplicial complex, this process must stabilise after finite number of steps. Let $M$ be final subcomplex obtained.
]
#algorithm[
    Let $K$ be connected, finite simplicial complex of dimension $<= 2$, let $x_0 in K$ be $0$-simplex. To compute $pi_1 (K, x_0)$:
    + Find a maximal tree $L$ in $K$.
    + Extend $L$ to maximal simply connected subcomplex $M$ of $K$.
    + Assign a direction and a label to each $1$-simplex in $K$ which is not contained in $M$. The labels give the generators of a group presentation for $pi_1 (K, x_0)$.
    + Impose relations on the labels as follows:
        + For $2$-simplices with exactly one edge in $M$: if the directions of the other two edges, $a$ and $b$, either both point towards or both point away from the edge in $M$, impose the relation $a = b$. If one points towards and the other away, then impose the relation $a = b^(-1)$.
        + For $2$-simplices with no edges in $M$ and with labels $a, b, c$: (up to permutation of $a, b, c$) if the directions of $b$ and $c$ point towards a common vertex and the directions of $a$ and $c$ point away from a common vertex, then impose the relation $c = a b$, otherwise (in this case, the directions form a cycle), if $a$ has direction pointing away from $c$ and $b$ has direction pointing towards $c$, impose $c = (a b)^(-1)$.
    + We have $pi_1 (K, x_0) tilde.equiv ideal("labels" | "relations")$.
]
#note[
    We can use step 4 to more efficiently choose labels and directions in step 3.
]
#definition[
    Each directed $1$-simplex in $M^c$ gives a *basic loop* (opposite choice of direction yields the inverse loop).
]
#proof("Proof of algorithm")[
    Let $K$ be connected finite simplicial complex, $v_0$ be $0$-simplex in $K$, $L$ be maximal tree in $K$, $M$ be maximal simply connected subcomplex in $K$ associated to $L$.
    - Simplices are convex, so every path in $K$ is homotopic to one which passes through only $0$- and $1$-simplices (with no doubling back). In particular, every element of $pi_1 (K, v_0)$ can be represented by a loop based at $v_0$ which passes through only $0$- and $1$-simplices.
    - If $v$ is $0$-simplex then $v in L subset.eq M$, and $L$ has no cycles, so there exists unique path from $v$ to $v_0$ in $L$ with no doubling back.
    - For all $0$-simplices $v in K$, there exists unique homotopy class of paths in $M$ from $v$ to $v_0$ and this class can be represented by a unique path in $L$ that doesn't double back on itself.
    - Trees are contractible and so $L$ is simply connected, hence $M$ is simply connected.
    - Thus, if there is another path in $M$ from $v$ to $v_0$, there is a loop in $M$, which must be null-homotopic. Hence, the paths must be homotopic in $M$.
    - If $M^c = K - M != emptyset$, it consists of $1$- and $2$-simplices (minus points on boundaries) and every $1$-simplex in $M^c$ with a choice of direction yields a homotopically non-trivial loop in $(K, v_0)$. Each vertex of a $1$-simplex in $M^c$ can be connected back to $v_0$ by a unique (up to homotopy) path in $L$. So each directed $1$-simplex in $M^c$ gives a *basic loop* (opposite choice of direction yields the inverse loop).
    - Every non-trivial loop in $K$ is homotopic to a product of basic loops:
        - If $lambda$ is loop in $(K, v_0)$, we have $lambda tilde.eq mu$, where $mu$ is loop through only $0$- and $1$-simplices (so $mu$ consists of a sequence of directed $1$-simplices, with some in $M$ and others not).
        - Every time $mu$ enters/exists $M$ (necessarily at a vertex), draw a path through $L$ back to $v_0$. This shows that $mu$ is homotopic to product of basic loops.
    - Therefore, by assigning labels to directed $1$-simplices in $M^c$, we obtain a list of generators of $pi_1 (K, v_0)$.
    - Also, $2$-simplices in $M^c$ give relations between the generators of $pi_1 (K, v_0)$.
    - So we have surjective homomorphism $ ideal("labels of directed 1-simplices in " M^c | "2-simplex relations") --> pi_1 (K, v_0) $ and this can be shown to be injective.
]
#example[
    Consider $S^1$ triangulated with three $1$-simplices and no $2$-simplices. A maximal tree consists of two edges, the maximal connected subcomplex $M$ is already the maximal tree. There is one $1$-simplex not in $M$  and there are no relations (since no $2$-simplices). Hence $pi_1 (S^1, x_0) tilde.equiv ideal(a) = F^1 tilde.equiv ZZ$.
]

== Van Kampen's theorem

#theorem("van Kampen's theorem")[
    Let $(K, v_0)$ be based, connected finite simplicial complex. Suppose there exists connected simplicial subcomplexes $A, B subset.eq K$ such that:
    - $K = A union B$
    - $A sect B$ is path-connected simplicial subcomplex.
    - $v_0 in A sect B$.
    Then $ pi_1 (K, v_0) tilde.equiv pi_1 (A, v_0) *_(pi_1 (A sect B, x_0)) pi_1 (B, x_0) $ where the homomorphisms $(i_A)_*: pi_1 (A sect B, v_0) -> pi_1 (A, v_0)$, $(i_B)_*: pi_1 (A sect B, v_0) -> pi_1 (B, v_0)$ are those induced from the respective inclusion maps $i_A: A sect B -> A$, $i_B: A sect B -> B$.
]
#proof[
    - Find maximal tree $L_(A sect B)$ in $A sect B$. Extend to maximal trees $L_A$ in $A$, $L_B$ in $B$. Then $L = L_A union L_B$ is maximal tree in $K$.
    - Extend $L_(A sect B)$, $L_A$, $L_B$ to maximal simply connected subcomplexes to $M_(A sect B)$, $M_A$, $M_B$. Then $M = M_A union M_B$ is maximal simply connected subcomplex in $K$.
    - By the algorithm, $pi_1 (K, v_0) tilde.equiv ideal("directed 1-simplices in" M^c | "relations from 2-simplices in" M^c)$ where $ {"directed 1-simplices in" M^c} = & D_A union D_B \ := & {"directed 1-simplices in" A - M_A} \ union & {"directed 1-simplices in" B - M_B} $ and $ {"2-simplices in" M^c} = & {"2-simplices in" A - M_A} \ union & {"2-simplices in" B - M_B} $
    - However, $D_A sect D_B = {"directed 1-simplices in" (A sect B) - M_(A sect B)}$. So to avoid counting homotopy classes of twice, we identify corresponding generators in thre free product $pi_1 (A, v) * pi_1 (B, v_0)$, which gives the amalgamated product.
]
#example[
    Let $W_2$ be *figure 8 space* - the one-point union of two copies of $S^1$, i.e. two copies of $S^1$ joined at single point (the base point) $w_0$. So $W_2 = A union B$ where $A = B = S^1$, $A sect B = {p}$, the one-point space, is path-connected. $pi_1 ({p}, w_0) tilde.equiv bb(1)$. So $ pi_1 (W_2, w_0) & tilde.equiv pi_1 (S^1, w_0) *_(bb(1)) pi_1 (S^1, w_0) \ & = pi_1 (S^1, w_0) * pi_1 (S^1, w_0) \ & tilde.equiv ideal(x) * ideal(y) \ & = ideal(x, y) = F^2 $
]
#example[
    - Decompose torus as $TT = A union B$ where $A$ is small closed disc in $TT$, $B$ is closure of the remainder (i.e. remainder together with circle boundary of the disc) so $A sect B = S^1$.
    - $B$ is homotopy equivalent to the figure-eight space so $pi_1 (B) tilde.equiv ideal(x, y)$. $A$ is contractible so $pi_1 (A) tilde.equiv bb(1)$, and $pi_1 (A sect B) tilde.equiv ideal(z)$. But the loop going once around $A sect B$ is homotopy equivalent to the loop going along the boundary of unit square whose quotient gives $TT$, which corresponds to $x y x^(-1) y^(-1)$.
    - So by van Kampen's theorem, $ pi_1 (TT) & tilde.equiv pi_1 (A) *_(pi_1 (A sect B)) pi_1 (B) \ & tilde.equiv bb(1) *_(ideal(z)) ideal(x, y) \ & = ideal(x, y | z) \ & = ideal(x, y | x y x^(-1) y^(-1)) tilde.equiv ZZ^2 $ since the image of $z$ under the homomorphism $h_1: pi_1 (A sect B) -> A$ must be $e$.
]

= Euler characteristics and the classification of closed surfaces

== The Euler characteristic of a graph

#definition[
    Let $G$ be finite graph with $v$ vertices and $e$ edges. *Euler characteristic* of $G$ is $ chi(G) := v - e $
]
#definition[
    *Degree* of vertex in graph of number of edge ends with that vertex as endpoint (so degree of vertex with loop is $2$).
]
#lemma[
    A non-trivial finite tree contains a vertex of degree $1$.
]
#lemma[
    Let $G$ be finite tree, then $chi(G) = 1$.
]
#proof[
    Induction of number of vertices.
]
#lemma[
    If $G$ is finite connected graph, then $chi(G) <= 1$ with equality iff $G$ is tree.
]
#proof[
    Remove edges from cycles until $G$ is a tree, note what happens to Euler characteristic each time.
]
#remark[
    $chi(G)$ is a homotopy invariant, i.e. $G_1 tilde.eq G_2$, then $chi(G_1) = chi(G_2)$.
]
#theorem("Euler's Theorem")[
    Let $G$ be finite, connected graph drawn on $S^2$. Then $S^2 - G$ consists of $f = 2 - chi(G)$ *faces* (connected regions homeomorphic to open discs).
]
#proof[
    - Assume first that $S^2 - G$ consists of $f$ connected regions homeomorphic to open discs.
    - If $G$ has cycle, remove edge to obtain new connected graph $G'$. This means two of the $f$ regions are joined into one region, and $chi(G') = chi(G) + 1$. Hence $chi(G') + f' = chi(G) + f$.
    - Remove edges until resulting graph is tree $T$. Then $S^2 - T tilde.equiv E^2$, a single connected region. Deduce that $chi(G) + f = 2$.
    - Assumption was correct, since if $T$ is tree then $S^2 - T$ is always homeomorphic to open disc. With reverse of above argument, every edge added to $T$ creates cycle and divides disc into two sub-discs.
]
#corollary[
    Let $K$ be finite simplicial complex which triangulates $S^2$, with $v$ $0$-simplices, $e$ $1$-simplices and $f$ $2$-simplices. Then $ v - e + f = 2 $
]
#proof[
    Let $G = {"0-simplices"} union {"1-simplices"}$, then $G$ is finite connected graph and $S^2 - G = {"interiors of 2-simplices"}$.
]

== The Euler characteristic of a surface

#definition[
    Let $S$ be surface.
    - Finite connected graph $G subset S$ is *good* if every connected component of $S - G$ is homeomorphic to an open disc.
    - Let $G subset S$ be a good graph. The *$G$-Euler characteristic* of $S$ is $ chi_G (S) := chi(G) + ("number of components of" S - G) $
]
#note[
    - If $diff S != nothing$ and $G subset S$ is a good graph, then $diff S subset G$ as a subgraph.
    - Not every graph in a surface is good, e.g. if $G$ is single vertex in the torus, then $TT - G$ is homotopy equivalent to the figure $8$ space.
]
#lemma[
    Let $G$, $G'$ be good graphs on surface $S$, with $G$ subgraph of $G'$ ($G'$ is an *enlargement* of $G$). Then $ chi_G (S) = chi_(G')(S) $
]
#proof[
    - $G'$ can be constructed from $G$ by sequence of one or more of the following operations, none of which change $chi_G (S)$:
        - Add new vertex to interior of existing edge. This adds one vertex, one edge, number of components in complement does not change.
        - Add new edge between existing vertices. Number of components in complement increases by $1$.
        - Add new edge and new vertex by attaching new edge at one to existing vertex and at other end to new vertex. Number of components in complement does not change.
]
#theorem[
    The $G$-Euler characteristic of surface $S$ does not depend on choice of good graph $G$.
]
#proof[
    - Let $G_1, G_2$ be good graphs on $S$. If $diff S != nothing$, consider $diff S$ as (possibly) disconnected graph with ${"vertices"} = {"all vertices in" (G_1 union G_2) sect diff S}$.
    - Position $G_1$ such that it crosses $G_2$ in only isolated points in $int(S) = S - diff S$. Add new vertices at these interior intersection points.
    - Now $G_1 union G_2$ is common enlargment of $G_1$ and $G_2$ and a good graph, so result follows by above lemma.
]
#definition[
    *Euler characteristic* of surface $S$, is $chi(S) := chi_G (S)$ where $G$ is any good graph on $S$.
]
#theorem[
    Euler characteristic is homeomorphism-invariant: i.e. if $S_1$, $S_2$ homeomorphic surfaces, then $chi(S_1) = chi(S_2)$.
]
#example[
    If surface $S$ is triangulated by finite simplicial complex $K$ with $v$ $0$-simplices, $e$ $1$-simplices and $f$ $2$-simplices, then $ chi(S) = v - e + f $
]
#proposition[
    Euler characteristic is also homotopy-invariant: $X tilde.eq Y ==> chi(X) = chi(Y)$.
]
#proof[
    Non-examinable.
]
#definition[
    For $n$-dimensional finite simplicial complex $K$, Euler characteristic is defined as $ sum_(k = 0)^n (-1)^k ("number of " k #h(0em) "-simplices in" K) $
]
#lemma("Union Lemma")[
    Let $K = A union B$ be $2$-dimensional finite simplicial complex with $A$, $B$, $A sect B$ simplicial sub-complexes. Then $ chi(K) = chi(A union B) = chi(A) + chi(B) - chi(A sect B) $
]
#proof[
    Express number of vertices, edges and faces of $A union B$ in terms of those of $A$, $B$ and $A sect B$.
]
#lemma[
    Let $X$, $Y$ surfaces. Then $ chi(X \# Y) = chi(X) + chi(Y) - 2 $
]
#proof[
    - For closed surface $X$, $chi(X - "open disc") = chi(X) - 1$ (justify using triangulations).
    - Use Union lemma with $A = X - "open disc"$, $B = Y - "open disc"$, $A sect B = S^1$.
]
#lemma[
    Let $S$ be surface, let $S_M$ be $S$ with cross-cap attached. Then $ chi(S_M) = chi(S) - 1 $
]
#proof[
    - $S_M = A union B$ where $A = (S - "open disc")$, $B$ is Mobius band.
    - Use Union lemma.
]
#lemma[
    Let $S$ surface, let $S_H$ be $S$ with handle added. Then $ chi(S_H) = chi(S) - 2 $
]
#proof[
    - $S_H = A union B$, where $A = (S - 2 "open discs")$, $B$ is cylinder.
    - $A sect B$ is disjoint union of $S^1$ and $S^1$, $S^1 product.co S_1$.
    - Use Union lemma to show $chi(A sect B) = 0$.
    - Use Union lemma again to deduce the result.
]

== The classification of closed surfaces

#theorem("Classification Theorem for Closed Surfaces")[
    The complete list of closed surfaces, up to homeomorphism, is
    - *Orientable*: for $g in NN_0$, $ M_g tilde.equiv S^2 \# underbrace(T \# dots.h.c \# T, g "times") tilde.equiv S^2 "with" g "handles attached" $
    - *Non-orientable*: for $g in NN$, $ N_g tilde.equiv underbrace(PP \# dots.h.c \# PP, g "times") tilde.equiv S^2 "with" g "cross caps attached" $
    Since $chi(M_g) = 2 - 2g$ and $chi(N_g) = 2 - g$, a closed surface is classified up to homeomorphism (its *homeomorphism type*) by its Euler characteristic and whether it is orientable or not.
]
#definition[
    Let $K$ be finite simplicial complex that triangulates a closed surface $S$, let $L$ be sub-complex of $K$ of dimension $<= 1$. The *thickening* of $L$, $Theta(L)$, is sub-complex of $K^((2))$ given by the union of all $2$-simplices in $K^((2))$ (including all their faces) which meet $L$.
]
#proposition[
    Let $L$ be $1$-dimensional sub-complex of $2$-dimensional finite simplicial complex $K$. Then
    - $Theta(L) tilde.eq L$.
    - If $L$ is tree, then $Theta(L)$ is homeomorphic to closed disc $D^2$.
    - If $L$ is simple closed curve (i.e. homeomorphic to $S^1$) then $Theta(L)$ is homeomorphic to either cylinder or Mobius band.
]
#lemma[
    Let $K$ be finite simplicial complex that triangulates closed surface, let $L$ be $1$-dimensional sub-complex of $K$. Then $ chi(L) = chi(Theta(L)) $
]
#proof[
    - Let $diff Theta(L)$ be boundary of $Theta(L)$ in $K$, let $C = Theta(L) - L - diff Theta(L)$ (note $C$ is not simplicial complex).
    - By definition, $L$, $diff Theta(L)$ and $C$ are pairwise disjoint and $Theta(L) = L union diff Theta(L) union C$.
    - By Union lemma, $chi(Theta(L)) = chi(L) + chi(diff Theta(L)) + chi(C)$.
]
#definition[
    Let $K$ finite simplicial complex that triangulates closed surface.
    - A *maximal tree* in $K$ is tree formed out of the $0$- and $1$-simplices in $K$ which cannot be extended to any larger tree (and necessarily contains all $0$-simplices).
    - For maximal tree $L$ in $K$, *dual graph* of $L$, $L^* subset K$, is defined as follows:
        - The vertices of $L^*$ are the barycentres of the $2$-simplices of $K$.
        - Two vertices of $L^*$ are joined by an edge iff the corresponding two $2$-simplices meet in a $1$-simplex not in $L$.
]
#proposition[
    Let $L$ be maximal tree in $K$.
    - $L^*$ is connected.
    - $Theta(L) union Theta(L^*) = K^((2)) tilde.equiv K$.
    - $Theta(L) sect Theta(L^*) = "boundary of disc" Theta(L) tilde.equiv S^1$.
]
#theorem[
    Let $K$ finite simplicial complex that triangulates closed surface. Then $chi(K) = 1 + chi(L^*) <= 2$ (where $L$ is maximal tree in $K$) with equality iff $K tilde.equiv S^2$.
]
#proof[
    - Let $L$ be maximal tree in $K$ with dual graph $L^*$. Use Union lemma and above two propositions to show $chi(K) <= 2$.
    - Show if $chi(K) = 2$ then $L^*$ is tree, conclude that $K$ is homeomorphic to union of two closed discs glued along their boundary circles, so is copy of $S^2$.
]
#lemma[
    Let $S$ be closed surface. Then $(S + "handle") tilde.equiv S \# TT$.
]
#proof[
    - Up to homeomorphism, we can always arrange that a handle is attached to the interior of a region homeomorphic to a closed disc in $S$.
    - So $S + "handle" tilde.equiv (S - "open disc") union (TT - "open disc") tilde.equiv S \# TT$.
]
#lemma[
    Let $S$ be non-orientable closed surface. Then $(S + "handle") tilde.equiv S \# KK tilde.equiv S \# PP \# PP tilde.equiv (S + 2 "cross caps")$.
]
#definition[
    Let $L$ be maximal tree in finite simplicial complex $K$ with dual graph $L^*$, let $C subset.eq L^*$ be a cycle. Then $C$ is a *non-separating* simple closed curve.
]
#definition[
    Performing *surgery* along a non-separating simple closed curve $C$ is the following process:
    - Remove interior of $Theta(C)$ from $K^((2)) tilde.equiv K tilde.equiv S$, giving a simplicial complex $K^((2)) - int(Theta(C))$ which has either two holes (if $Theta(C) tilde.equiv$ cylinder) or one hole (if $Theta(C) tilde.equiv$ Mobius band), with the boundary of each of these holes being a triangulated circle.
    - Glue triangulated closed discs onto each boundary circle to "cap off" the holes.
    - This gives a new finite simplicial complex $K'$ which triangulates a closed surface $S'$. So $ S tilde.equiv cases(S' + "handle" & "if" Theta(C) tilde.equiv "cylinder", S' + "cross cap" & "if" Theta(C) tilde.equiv "Mobius band") $
    - So $ chi(S') = cases(chi(S) + 2 & "if" Theta(C) tilde.equiv "cylinder", chi(S) + 1 & "if" Theta(C) tilde.equiv "Mobius band") $
]
#theorem[
    Up to homeomorphism, any closed surface can be obtained from a sphere by adding a finite number of handles and/or a finite number of cross caps.
]
#proof[
    - Let $S$ be closed surface, triangulated by a finite simpicial complex $K$. Let $L$ be maximal tree in $K$ with dual graph $L^*$.
    - Then $chi(S) = chi(K) = 1 + chi(L^*)$. If $L^*$ is tree, then $chi(S) = 2$ so $S tilde.equiv S^2$.
    - So suppose $L^*$ contains cycle $C$, i.e. a simple closed curve.
    - We show we can always reduce to the case that the dual graph is a tree by performing "surgeries", and hence, that $S$ can be constructed from $S^2$.
    - Claim: the cycle $C subset L^*$ is *non-separating*, i.e. $K - C$ is path-connected.
        - Suppose not. Then each connected component of $K - C$ must contain a $0$-simplex in $K$ (since $C subset L^*$ avoids them all).
        - Clearly, $0$-simplices in different components cannot be joined by a path in $K - C$. However, $L subset K - C$ contains all $0$-simplices by definition of the dual graph: contradiction.
    - Since $C tilde.equiv S^1$, $Theta(C) tilde.equiv$ cylinder or Mobius band.
    - Perform surgery along the non-separating closed curve:
        - Remove interior of $Theta(C)$ from $K^((2)) tilde.equiv K tilde.equiv S$, giving a simplicial complex $K^((2)) - int(Theta(C))$ which has either two holes (if $Theta(C) tilde.equiv$ cylinder) or one hole (if $Theta(C) tilde.equiv$ Mobius band), with the boundary of each of these holes being a triangulated circle.
        - Glue triangulated closed discs onto each boundary circle to "cap off" the holes.
        - This gives a new finite simplicial complex $K'$ which triangulates a closed surface $S'$. So $ S tilde.equiv cases(S' + "handle" & "if" Theta(C) tilde.equiv "cylinder", S' + "cross cap" & "if" Theta(C) tilde.equiv "Mobius band") $
        - So $ chi(S') = cases(chi(S) + 2 & "if" Theta(C) tilde.equiv "cylinder", chi(S) + 1 & "if" Theta(C) tilde.equiv "Mobius band") $
    - We can repeat this surgery procedure along cycles in "the" dual graph in each such new surface obtained.
    - This process must terminate after a finite number of surgeries in a closed surface $Z$ for which "the" dual graph (in every triangulation) has no cycles (i.e. the dual graph is a tree, i.e. $Z tilde.equiv S^2$), since each surgery increases the Euler characteristic and $chi(S) <= 2$ for all closed surfaces $S$.
]
#corollary[
    If $S$ is non-orientable surface, then $S \# T tilde.equiv S \# KK$.
]
#corollary[
    Up to homeomorphism, every closed surface $S$ is given by precisely one of the closed surfaces
    - If $S$ is orientable: $M_g = S^2 + g "handles" tilde.equiv S^2 \# T \# dots.c \# T$, $g in NN_0$.
    - If $S$ is non-orientable: $N_g = S^2 + g "cross caps" tilde.equiv PP \# dots.c \# PP$ where $g in NN$.
]
#proof[
    - If $S$ orientable, then $S$ can only be obtained by attaching handles to $S^2$ by above theorem. So $S^2 tilde.equiv S^2 + g "handles" = M_g$. But $chi(M_g) = 2 - 2g$ so homeomorphism type is determined by number of handles.
    - If $S$ non-orientable, then $S tilde.equiv S^2 + k "handles" + ell "cross caps"$, $k >= 0$, $ell >= 1$. But attaching handle to non-orientable surface is same as attaching two cross caps, so $S^2 tilde.equiv S^2 + (2k + ell) "cross caps" = N_(2k + ell)$. But $chi(N_g) = 2 - g$ so homeomorphism type is determined by number of cross caps.
]