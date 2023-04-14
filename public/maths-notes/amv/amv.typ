#import "../template.typ": template
#show: template

= Maps between real vector spaces

- *Scalar field*: maps $RR^n -> RR$.
- *Vector field*: maps $RR^n -> RR^n$.
- *Curve*: maps $RR -> RR^n$.
- A *tangent* to a curve $underline(x)(t)$ is given by $(d underline(x)) / (d t)$.
- The *arc-length* parameterisation of a curve $underline(x)$ is such that $ abs((d underline(x)(s)) / (d s)) = 1 quad forall s $
- *Partial derivatives*: $ (diff f(underline(x))) / (diff x_a) = lim_(h -> 0) (f(underline(x) + h underline(e)_a) - f(underline(x))) / h $
- *Chain rule*: for a scalar field $f(underline(x))$ and curve $underline(x)(t) = x_1(t) underline(e)_1 + ... + x_n(t) underline(e)_n$, $ (d f(underline(x)(t))) / (d t) = sum_(i = 1)^n (diff f(underline(x))) / (diff x_i) (d x_i) / (d t) $ Here $F(t) := f(underline(x)(t))$ is the restriction of $f(underline(x))$ to the curve $underline(x)(t)$.

= The gradient of a scalar field

- *Differential operator*: maps functions to functions, e.g. $ d/(d t) = sum_(i = 1)^n (diff ) / (diff x_i) (d x_i) / (d t) $
- Let $f, g: RR -> RR$, then
	- $f(x) d / (d x)$ is a differential operator. It acts on $g(x)$ to give $f(x) (d g(x)) / (d x)$.
	- $d / (d x) f(x)$ is a differential operator. It acts on $g(x)$ to give $d / (d x) (f(x) g(x))$.
	- $(d / (d x) f(x))$ is an differential operator. It acts on $g(x)$ to give $(d f(x)) / (d x) g(x)$.
- *del (or nabla)*: $underline(nabla) = sum_(i = 1)^n (diff ) / (diff x_i) underline(e)_i $ so $d / (d t) = underline(nabla) . (d underline(x)(t)) / (d t)$.
- *gradient* of a scalar field $f: RR^n -> RR$: $ underline(nabla) f ident "grad"(f) = sum_(i = 1)^n (diff f) / (diff x_i) underline(e)_i $
- *Directional derivative* of $f: RR^n -> RR$ in direction of a unit tangent $underline(hat(n)) = (d underline(x)(s)) / (d s)$ to a curve $x: RR -> RR^n$: $ (d f(underline(x)(s))) / (d s) = underline(hat(n)) . underline(nabla) f ident (d f) / (d underline(hat(n))) $ where $underline(x)$ is parameterised in terms of arc-length $s$.
- $underline(nabla) f$ at a point $underline(p)$ is orthogonal to curves contained in level set of $f$ at $underline(p)$.
- $underline(nabla) f$ points in the direction where $f$ increases fastest.
- *Properties of the gradient*: let $f, g: RR^n -> RR$, $a, b in RR$, $phi: RR -> RR$, then
	- $underline(nabla) (a f + b g) = a underline(nabla) f + b underline(nabla) g$
	- $underline(nabla) (f g) = f underline(nabla) g + g underline(nabla) f$
	- $underline(nabla) phi(f) = (underline(nabla) f) (d phi) / (d f)$

= $underline(nabla)$ acting on vector fields

- *Divergence* of a vector field $underline(v)(underline(x)) = sum_(i = 1)^n v_i(underline(x)) underline(e)_i$: $ underline(nabla) . underline(v) ident "div"(underline(v)) = sum_(i = 1)^n (diff v_i) / (diff x_i) $ Note that the formula will be different in other coordinates systems. Also $underline(nabla) . underline(v) != underline(nabla) dot.op underline(v)$.
- Considering a vector field as a fluid, if the divergence at a point is positive the vector field acts as a *source* at that point (more fluid leaving than entering), if the divergence is negative the vector field acts as a *sink* at that point (more fluid entering than leaving). The magnitude of the divergence is the rate of flow and the direction of the divergence is the direction of flow.
- *Properties of div*: for $f: RR^n -> RR$, $underline(v), underline(w): RR^n -> RR^n$, $a, b in RR$,
	- $underline(nabla) . (a underline(v) + b underline(w)) = a underline(nabla) . underline(v) + b underline(nabla) . underline(w)$
	- $underline(nabla) . (f underline(v)) = (underline(nabla) f) . underline(v) + f underline(nabla) . underline(v)$
#set math.mat(delim: "|")
- *Curl* of $underline(v): RR^n -> RR^n$: $ underline(nabla) times underline(v) ident "curl"(underline(v)) = mat(
	underline(e)_1, underline(e)_2, underline(e)_3;
	(diff ) / (diff x), (diff ) / (diff y), (diff ) / (diff z);
	v_1, v_2, v_3
) = underline(e)_1 ( (diff v_3) / (diff y) - (diff v_2) / (diff z) ) - underline(e)_2 ( (diff v_3) / (diff x) - (diff v_1) / (diff z) ) + underline(e)_3 ( (diff v_2) / (diff x) - (diff v_1) / (diff y) ) $
- Considering a vector field as a fluid, the magnitude of the curl at a point corresponds to the rotational speed of the fluid, and the direction of the curl corresponds to which axis the fluid is rotating around, determined using the right-hand rule (fingers represent rotation of the fluid, thumb points in direction of curl).
- *Properties of curl*: for $f: RR^3 -> RR$, $underline(v), underline(w): RR^3 -> RR^3$, $a, b in RR$,
	- $underline(nabla) times (a underline(v) + b underline(w)) = a underline(nabla) times underline(v) + b underline(nabla) times underline(w)$
	- $underline(nabla) times (f underline(v)) = (underline(nabla) f) times underline(v) + f underline(nabla) times underline(v)$
- *Laplacian* of $f: RR^n -> RR$: $ Delta f ident underline(nabla)^2 f := underline(nabla) . (underline(nabla) f) = "div"("grad"(f)) = sum_(i = 1)^n (diff^2 f)/(diff x_i^2) $ Note this formula is only valid for *cartesian* coordinates.

= Index notation

- *Einstein summation convention*: in an expression involving a summation, then index of summation always appears twice. The convention is that the summation sign is removed, and whenever an index appears twice, it is summed over.
- *Dummy indices*: repeated indices. They can be renamed without changing the expression.
- *Free indices*: non-repeated indices. They must match on both sides of an equation.
- An index can't be repeated more than twice in the same term, so $(underline(u) . underline(v))^2 = u_i v_i u_j v_j != u_i v_i u_i v_i$.
- *Kronecker delta*: $ delta_(i j) := cases(
	1 & "if" i = j \
	0 & "if" i != j
) quad = (diff x_i) / (diff x_j) $
- If $delta_(i j)$ has a dummy index $i$, then remove the $delta_(i j)$ and replace the dummy index $i$ by $j$ in the rest of the expression.
- *Levi-Cevita symbol*: $ epsilon_(i j k) & = -epsilon_(j i k) = -epsilon(i k j) quad "(antisymmetry)" med epsilon_(123) & = 1 $
- *Properties of $epsilon_(i j k)$*:
	- $epsilon_(i j k) = -epsilon_(k j i)$
	- $epsilon_(i j k) = 0$ if $i = j$ or $j = k$ or $k = i$
	- If $epsilon_(i j k)$ is zero then $(i med j med k)$ is a permutation of $(1 med 2 med 3)$.
	- $epsilon_(i j k) = 1$ if $(i med j med k)$ is an even permutation of $(1 med 2 med 3)$ (even number of swaps).
	- $epsilon_(i j k) = -1$ if $(i med j med k)$ is an odd permutation of $(1 med 2 med 3)$ (odd number of swaps).
	- $epsilon_(i j k) = epsilon_(j k i) = epsilon_(k i j)$ (cyclic permutation).
- The cross product $underline(C) = underline(A) times underline(B)$ can be written as $C_i = epsilon_(i j k) A_j B_k$.
- *Very useful $epsilon_(i j k)$ formula*: $ sum_(k = 1)^3 epsilon_(i j k) epsilon_(k l m) = delta_(i l) delta_(j m) - delta_(i m) delta_(j l) $
- Notation: $diff_i := (diff ) / (diff x_i)$.
- $underline(nabla) . underline(v) = (diff v_i) / (diff x_i) = diff_i v_i$.
- $(underline(nabla) times underline(v))_i = epsilon_(i j k) (diff ) / (diff x_j) v_k = epsilon_(i j k) diff_j v_k$.

= Differentiability of scalar fields

- *$f(underline(x))$ tends to $L$ as $x$ tends to $a$*:3 $ lim_(underline(x) -> underline(a)) f(underline(x)) = L <==> forall epsilon > 0, exists delta > 0, forall underline(x), 0 < |underline(x) - underline(a)| < delta ==> |f(underline(x)) - L| < epsilon $
- Scalar field $f$ *continuous* at $underline(a)$ if $lim_(underline(x) -> underline(a)) f(underline(x))$ exists and is equal to $f(underline(a))$
- If $f$ and $g$ are continuous scalar fields at $underline(a)$ then so are:
	- $f + g$
	- $f g$
	- $f \/ g$ (if $g(underline(a)) != 0$)
- $f(underline(x)) = c$ for a constant $c$ is continuous at every $underline(x) in RR^n$
- $f(underline(x)) = x_a$, $a in {1, ..., n}$ is continuous at every $underline(x) in RR^n$
- *Open ball, centre $underline(a)$, radius $delta > 0$*: $ B_delta(underline(a)) := {underline(x) in RR^n: |underline(x) - underline(a)| < delta} $
- $S subset.eq RR^n$ *open* if $forall underline(a) in S$, $exists delta > 0$ such that $B_delta(underline(a)) subset.eq S$
- *Neighbourhood* $N subset.eq RR^n$ of $underline(a) in RR^n$: contains an open set containing $underline(a)$
- $S subset.eq RR^n$ *closed* if its complement $RR^n - S$ is open
- Every open ball is open
- Let $U subset.eq RR^n$ be open and $f: U -> RR$. $f$ is *continuous on $U$* if it is continuous at every $underline(a) in U$
- Let $U subset.eq RR^n$ be open and $f: U -> RR$. $f$ is *differentiable* at $underline(a) in U$ if for some vector $underline(v)(underline(a))$, $ f(underline(a) + underline(h)) - f(underline(a)) = underline(h) . underline(v)(underline(a)) + R(underline(h)), quad lim_(underline(h) -> underline(0)) R(underline(h)) / abs(underline(h)) = 0 $ If $underline(v)(underline(a))$ exists, $underline(v)(underline(a)) = underline(nabla) f$
- *Warning*: $underline(nabla) f$ being defined at a point does not imply that $f$ is differentiable at that point.
- Let $U subset.eq RR^n$ be open and $f: U -> RR$. Then $f$ is differentiable at $underline(a)$ if all partial derivatives of $f$ exist and are continuous in a neighbourhood of $underline(a)$
- Function is *continuously differentiable* at $underline(a)$ if it and all its partial derivatives exist and are continuous at $underline(a)$. It is *continuously differentiable* on an open $U$ if it and all its partial derivatives exist and are continuous on $U$.
- Continuous differentiability implies differentiability.
- *Smooth function*: partial derivatives of all orders exist.
- Let $U subset.eq RR^n$ be open. If $f, g: U -> RR$ continuous at $underline(a) in RR^n$ then so are:
	- $f + g$
	- $f g$
	- $f \/ g$ (if $g(underline(a)) != 0$)
- Let $U subset.eq RR^n$ be open, $f: U -> RR$ be differentiable, $underline(x)$ be a function of $u_1, ... u_m$ where all partial derivatives $(diff x_i) / (diff u_j)$ exist. Let $F(u_1, ... u_m) = f(underline(x)(u_1, ... u_m))$, then $ (diff F) / (diff u_b) = (diff underline(x)) / (diff u_b) . underline(nabla) f $
- *Level set* of $f: U -> RR$, $U subset.eq RR^n$ open, is the set ${underline(x) in U: f(underline(x)) = c}$ for some $c in RR$. For $n = 2$ it is called a *level curve*.
- *Implicit function theorem for level curves*: if $f: U -> RR$ is differentiable, and $(x_0, y_0) in U$ is on the level curve $f(x, y) = c$ where $(diff f) / (diff y) (x_0, y_0) != 0$, then there exists a differentiable function $g(x)$ in a neighbourhood of $x_0$ satisfying $ g(x_0) = y_0 \ f(x, g(x)) = c \ (d g) / (d x) = - ((diff f(x, g(x))) / (diff x)) / ((diff f(x, g(x))) / (diff y)) $
- *Critical point*: point of level curve $f(x, y) = c$ where $underline(nabla) f = underline(0)$. $c$ is a *critical value*, otherwise it is a *regular value*.
- At a critical point, the level curve can't be written as either $y = g(x)$ or as $x = h(y)$ in a neighbourhood of $Q$, with $g, h$ differentiable.
- *Implicit function theorem for level surfaces*: Let $f: U -> RR$ be differentiable, $U subset.eq RR^3$ open, $(x_0, y_0, z_0) in U$ be on the level set $f(x, y, z) = c$. If $(diff f) / (diff z) (x_0, y_0, z_0) != 0$ then $f(x, y, z) = c$ defines a surface $z = g(x, y)$ in a neighbourhood of $(x_0, y_0, z_0)$, where $ f(x, y, g(x, y)) = c \ g(x_0, y_0) = z_0 \ (diff g) / (diff x) (x_0, y_0) = -((diff f) / (diff x) (x_0, y_0, z_0)) / ((diff f) / (diff z) (x_0, y_0, z_0)) \ (diff g) / (diff y) (x_0, y_0) = -((diff f) / (diff y) (x_0, y_0, z_0)) / ((diff f) / (diff z) (x_0, y_0, z_0)) $
- $underline(nabla) f (x_0, y_0, z_0)$ is normal to the tangent plane of the level set $z = g(x, y)$ at $(x_0, y_0)$. So the normal line is given by $ underline(x)(t) = underline(x_0) + t underline(nabla) f $ and the tangent plane is given by $ (underline(x) - underline(x_0)) . underline(nabla) f = 0 $

= Differentiability of vector fields

- *Jacobian matrix (differential)* of $underline(F)(underline(x))$ at $underline(x) = underline(a)$ (written $D underline(F)(underline(a))$ or $D underline(F)_(underline(a))$): matrix with components $a_(i, j) = (diff F_i) / (diff x_j)$.
- For open $U subset.eq RR^n$, $underline(F): U -> RR^n$ *differentiable* at $underline(a) in U$ if for some *linear* function $underline(L): RR^n -> RR^n$, $ underline(F)(underline(a) + underline(h)) - underline(F)(underline(a)) = underline(L)(underline(h)) + R(underline(h)) $ where $ lim_(underline(h) -> underline(0)) R(underline(h)) / abs(underline(h)) = underline(0) $ Here, $underline(L)(underline(h)) = (D underline(F)(underline(a))) underline(h)$.
- *Jacobian, $J(underline(v))$*: determinant of differential: $J(underline(v)) = det(D underline(v))$
- Can think of vector fields as *coordinate transformations* on $RR^n$.
- *Inverse function theorem*: let $U$ open, $v: U -> RR^n$ differentiable with continuous partial derivatives. If $J(underline(v)(underline(a))) != 0$ then exists open $tilde(U) subset.eq U$ containing $underline(a)$ such that:
	- $underline(v)(tilde(U))$ is open and
	- Mapping $underline(v)$ from $tilde(U)$ to $underline(v)(tilde(U))$ has differentiable inverse $underline(w): underline(v)(tilde(U)) -> RR^n$ with $underline(v)(underline(w)(underline(x))) = underline(x)$ and $underline(w)(underline(v)(underline(y))) = underline(y)$.
- Map $underline(v): tilde(U) -> V subset.eq RR^n$ which satisfies above two properties is called *diffeomorphism* of $tilde(U)$ onto $tilde(V) = underline(v)(tilde(U))$. $tilde(U)$ and $tilde(V)$ are *diffeomorphic*.
- *Local diffeomorphism*: map $underline(v): U -> V$ where $forall underline(a) in U$, exists open $tilde(U) subset.eq U$ containing $underline(a)$ such that $underline(v): tilde(U) -> underline(v)(tilde(U))$ is diffeomorphism.
- *Chain rule for vector fields*: $ D underline(w)(underline(v)(underline(x))) = D underline(w)(underline(v)) D underline(v)(underline(x)) $
- When $underline(v)$ is local diffeomorphism and $underline(w)$ is its inverse, then $ (D underline(v))^(-1) = D underline(w), quad J(underline(w)) = 1 / J(underline(v)), quad J(underline(v)) != 0 $
- $underline(v)$ is *orientation preserving* if $J(underline(v)) > 0$.
- $underline(v)$ is *orientation reversing* if $J(underline(v)) < 0$.

= Volume, line and surface integrals

- *One dimensional integral*: calculates area under curve. $ integral_a^b f(x) dif x = lim_(n -> infinity) sum_(i = 0)^(n - 1) f(x_i^*) Delta x_i $ where $[a, b]$ partitioned as $a = x_0 < x_1 < dots.h.c < x_n = b$, $Delta x_i = x_(i + 1) - x_i$, $x_i^* in [x_i, x_(i + 1)]$ is arbitrary.
- *Double integral*: calculates volume under surface $z = f(x, y)$ over region $R$. $ integral_R f(x, y) dif A = lim_(N -> infinity) sum_(k = 1)^N f(x_k^*, y_k^*) Delta A_k $ $R$ is split into $N$ rectangle $Delta A_k$. $(x_k^*, y_k^*)$ lies in base of $k$th prism.
- If rectangles chosen on rectangular grid, then $Delta A_k = Delta x_i Delta y_j$ where $Delta x_i = x_(i + 1) - x_i$, $Delta y_j = y_(j + 1) - y_j$, $x$ and $y$ partitioned as $x_0 < x_1 < dots.h.c < x_n$ and $y_0 < y_1 < dots.h.c < y_m$. As before $x_i^* in [x_i, x_(i + 1)]$ and $y_j^* in [y_j, y_(j + 1)]$. Integral is $ integral_R f(x, y) dif A = lim_(n, m -> infinity) sum_(i = 0)^(n - 1) sum_(j = 0)^(m - 1) f(x_k^*, y_k^*) Delta x_i Delta y_j = integral_x (integral_y f(x, y) dif y) dif x $
- *Fubini's theorem*: if $f(x, y)$ continuous over compact (bounded and closed) region $A$, then double integral over $A$ can be written as *iterated integral*, with integrals in either order: $ integral_A f(x, y) dif A = integral_y integral_x f(x, y) dif x dif x = integral_x integral_y f(x, y) dif y dif x $
- *Important*: Fubini's theorem holds if region and/or function is unbounded, provided *double integral absolutely convergent* (integral of $|f(x, y)|$ over $A$ is finite).
- To *calculate area in plane* (e.g. between two curves), set $f(x, y) = 1$: $ "Area of" R = integral_R 1 dif A $
- *Volume integral*: partition volume $V$ into $N$ volumes $Delta V_i$. $ I = integral_V f(underline(x)) dif V = lim_(N -> infinity) sum_(i = 1)^N f(x_i) Delta V_i $
- If $f(underline(x))$ is density of a quantity, then $I = integral_V f(underline(x)) dif V$ is amount of that quantity.
- To *calculate volume inside surface*, ($S$ is surface which encloses $V$) set $f(x, y, z) = 1$: $ "Volume inside" S = "Volume of" V = integral_V 1 dif V $
- As for double integrals, if $V$ partition parallel to coordinate planes than $ I = integral_x integral_y integral_z f(x, y, z) dif z dif y dif x $
- Fubini's theorem holds for triple integrals.
- *Regular arc*: curve $underline(x)(t)$ where $x_a(t)$ continuous with continuous first derivatives.
- *Regular curve*: finite number of regular arcs joined end to end.
- *Line integral* of $underline(v)(underline(x))$ along arc $C: t -> underline(x)(t)$, $t in [alpha, beta]$: $ integral_C underline(v) dot.op d underline(x) = integral_alpha^beta underline(v)(underline(x)(t)) dot.op (d underline(x)(t)) / (d t) dif t $
- Line integral doesn't depend on parameterisation of $C$.
- Line integral along regular curve $C$ is sum of line integrals of arcs of $C$. If $C$ is closed, written $integral.cont_C underline(v) dot.op dif underline(x)$.
- *Length of curve*: $ integral_C dif s = integral_a^b norm((d underline(x)(t)) / (d t)) dif t $
- If $f$ is density function, mass is $ integral_C f dif s = integral_a^b f(underline(x)(t)) norm((d underline(x)(t)) / (d t)) dif t $
- If $underline(F)$ is force, work done is $ integral_C underline(F) dot.op dif underline(x) $
- If curve is ellipse $x^2 / a^2 + y^2 / b^2 = 1$, can parameterise as $x(t) = a cos(t)$, $y(t) = b sin(t)$.
- If curve is $y = f(x)$, can parameterise as $x(t) = t$, $y(t) = f(t)$.
- If curve is $x = g(y)$, can parameterise as $x = g(t)$, $y(t) = t$.
- If curve is straight line segment from $(x_0, y_0)$ to $(x_1, y_1)$, can parameterise as $x(t) = (1 - t) x_0 + t x_1$, $y(t) = (1 - t) y_0 + t y_1$.
- Surface can be given in *parametric form* as $underline(x)(u, v)$ where $u, v in U$ ($U$ is *parameter domain*).
- If curve is $z = f(x, y)$, can parameterise as $x = u, y = v, z = f(u, v)$. Similarly for $y = g(x, z)$ and $x = h(y, z)$.
- For surface $S$ as $underline(x)(u, v)$, *unit normal* vector is $ hat(underline(n)) =  underline(a) / |underline(a)|, quad a = ((diff underline(x)(u, v)) / (diff u) times (diff underline(x)(u, v)) / (diff v)) $ (negative of this is also).
- For surface given as *level surface* of scalar field $f$, $f(x, y, z) = c$, *unit normal* vector is $ hat(underline(n)) = (underline(nabla) f) / |underline(nabla) f| $ (negative of this is also).
- Surface $underline(x)(u, v)$ *orientable* if partial derivatives of $underline(x)$ exist and are continuous, and $hat(underline(n))$ is continuous.
- *Surface integral* defined as $ integral_S underline(F) dot.op dif underline(A) = lim_(Delta A_k -> 0) sum_k underline(F)(underline(x)_k^*) dot.op hat(underline(n))_k Delta A_k $
- For surface $underline(x)(u, v)$, $ integral_S underline(F) dot.op dif underline(A) = integral_U underline(F)(underline(x)(u, v)) dot.op ((diff underline(x)) / (diff u) times (diff underline(x)) / (diff v)) dif u dif v $ since $((diff underline(x)) / (diff u) times (diff underline(x)) / (diff v))$ is normal to surface.
- For surface $f(x, y, z) = c$, $ integral_S underline(F) dot.op dif underline(A) = integral_A (underline(F) dot.op underline(nabla) f) / (underline(e_3) dot.op underline(nabla) f) dif x dif y $ where $(x, y)$ range over $A$, $A$ is *projection* of $S$ onto $x, y$ plane.

= Green's, Stoke's and divergence theorems

- *Green's theorem*: let $P(x, y)$ and $Q(x, y)$ be continuously differentiable scalar fields in $2$ dimensions. Then $ integral.cont_C (P(x, y) dif x + Q(x, y) dif y) = integral_A ((diff Q) / (diff x) - (diff P) / (diff y)) dif x dif y $ where $C$ is boundary of $A$ traversed in positive (anticlockwise) direction (imagine walking around $C$ with $A$ to your left).
- *Green's theorem in vector form*: let $underline(F)(x, y, z) = (P(x, y), Q(x, y), R)$, then $ integral.cont_C underline(F) dot.op dif underline(x) = integral_A (underline(nabla) times underline(F)) dot.op underline(e)_3 dif A $
- *Stokes' theorem*: let $underline(F)(x, y, z)$ be continuously differentiable vector field, $S$ in $RR^3$ be surface with area elements $dif underline(A) = hat(underline(n)) dif A$ and boundary curve $C = diff S$, then $ integral.cont_C underline(F) dot.op dif underline(x) = integral_S (underline(nabla) times underline(F)) dot.op dif underline(A) $ Orientation of $C$ and choice of $hat(underline(n))$ or $-hat(underline(n))$ given by *right hand rule*: curl fingers of right hand and extend thumb. When thumb points in direction of surface normal, fingers point in direction of orientation of boundary, and vice versa. (Equivalently, if you stood on boundary with head pointing in direction of normal, and walked around boundary with surface on your left, direction of walking is direction of orientation of boundary.)
- *Divergence theorem*: let $underline(F)$ be continuously differentiable vector field defined over volume $V$ with bounding surface $S$, then $ integral_S underline(F) dot.op dif underline(A) = integral_V underline(nabla) dot.op underline(F) dif V $ where $dif underline(A) = hat(underline(n)) dif A$, $hat(underline(n))$ is outward unit normal.
- Vector field *conservative* if line integral is path independent.
- $underline(F)$ *closed* if $underline(nabla) times underline(F) = underline(0)$.
- Region $D$ *simply connected* if any closed curve in $D$ can be continuously shrunk to point in $D$.
- Every closed curve in $D$ is boundary of surface in $D$.
- Let $underline(F)$ vector field and $underline(nabla) times underline(F) = underline(0)$ in simply connected region $D$. If $C_1$ and $C_2$ are paths in $D$ joining $underline(a)$ to $underline(b)$ then $ integral_(C_1) underline(F) dot.op dif underline(x) = integral_(C_2) underline(F) dot.op dif underline(x) $ so line integral is path-independent and $underline(F)$ is conservative.
- If $underline(F) = underline(nabla) phi$ for scalar field $phi$ ($underline(F)$ is *exact*) then $integral_C underline(F) dot.op dif underline(x)$ is path-independent so $underline(F)$ is conservative. If $C$ goes from $underline(a)$ to $underline(b)$ then $ integral_C underline(F) dot.op dif underline(x) = phi(underline(a)) - phi(underline(b)) $
- $underline(nabla) times underline(F) = 0 <==> "path indepence of integral" <==> exists phi, underline(F) = underline(nabla) phi$