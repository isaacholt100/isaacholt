#import "../../template.typ": template
#show: template

#let powset(X) = $cal(P)(X)$
#let inv(x) = $#x^(-1)$

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

== Limits, bases and products

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