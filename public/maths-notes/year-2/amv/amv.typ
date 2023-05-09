#import "../../template.typ": template
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
- Considering a vector field as a fluid, if the divergence at a point is positive the vector field acts as a *source* at that point (more fluid leaving than entering), if the divergence is negative the vector field acts as a *sink* at that point (more fluid entering than leaving). The magnitude of vector at point is the rate of flow at that point and direction of vector is direction of flow.
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
- *Levi-Cevita symbol*: $ epsilon_(i j k) & = -epsilon_(j i k) = -epsilon_(i k j) quad "(antisymmetry)" med epsilon_(123) & = 1 $
- *Properties of $epsilon_(i j k)$*:
	- $epsilon_(i j k) = -epsilon_(k j i)$
	- $epsilon_(i j k) = 0$ if $i = j$ or $j = k$ or $k = i$
	- If $epsilon_(i j k) != 0$ then $(i med j med k)$ is a permutation of $(1 med 2 med 3)$.
	- $epsilon_(i j k) = 1$ if $(i med j med k)$ is an even permutation of $(1 med 2 med 3)$ (even number of swaps).
	- $epsilon_(i j k) = -1$ if $(i med j med k)$ is an odd permutation of $(1 med 2 med 3)$ (odd number of swaps).
	- $epsilon_(i j k) = epsilon_(j k i) = epsilon_(k i j)$ (cyclic permutation).
- The cross product $underline(C) = underline(A) times underline(B)$ can be written as $C_i = epsilon_(i j k) A_j B_k$.
- *Very useful $epsilon_(i j k)$ formula*: $ sum_(k = 1)^3 epsilon_(i j k) epsilon_(k l m) = delta_(i l) delta_(j m) - delta_(i m) delta_(j l) $
- Notation: $diff_i := (diff ) / (diff x_i)$.
- $underline(nabla) . underline(v) = (diff v_i) / (diff x_i) = diff_i v_i$.
- $(underline(nabla) times underline(v))_i = epsilon_(i j k) (diff ) / (diff x_j) v_k = epsilon_(i j k) diff_j v_k$.

= Differentiability of scalar fields

- *$f(underline(x))$ tends to $L$ as $x$ tends to $a$*: $ lim_(underline(x) -> underline(a)) f(underline(x)) = L <==> forall epsilon > 0, exists delta > 0, forall underline(x), 0 < |underline(x) - underline(a)| < delta ==> |f(underline(x)) - L| < epsilon $
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
- Let $U subset.eq RR^n$ be open. If $f, g: U -> RR$ differentiable (or smooth) at $underline(a) in RR^n$ then so are:
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
- If unit normal to surface $S$, $underline(hat(n))$, is known and $underline(F) dot.op underline(hat(n))$ is constant, then $ integral_S underline(F) dot.op dif underline(A) = integral_S underline(F) dot.op underline(hat(n)) dif A = underline(F) dot.op underline(hat(n)) integral_S dif A = underline(F) dot.op underline(hat(n)) times "area of" S $

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
- If $underline(F) = underline(nabla) phi$ for scalar field $phi$ ($underline(F)$ is *exact*) then $integral_C underline(F) dot.op dif underline(x)$ is path-independent so $underline(F)$ is conservative. If $C$ goes from $underline(a)$ to $underline(b)$ then $ integral_C underline(F) dot.op dif underline(x) = phi(underline(b)) - phi(underline(a)) $
- $underline(nabla) times underline(F) = 0 <==> "path indepence of integral" <==> exists phi, underline(F) = underline(nabla) phi$

= Non-Cartesian systems

- Polar, spherical polar and cylindrical polar coordinates are all *curvilinear coordinates*.
- Cartesian coordinates $(x, y, z)$ can be expressed as smooth functions of curvlinear coordinates $(u, v, w)$: $ x = g(u, v, w), y = h(u, v, w), z = k(u, v, w), quad g, h, k in C^oo(RR^3) $ $g, h, k$ can be inverted to give $ u = tilde(g)(x, y, z), v = tilde(h)(x, y, z), w = tilde(k)(x, y, z), quad tilde(g), tilde(h), tilde(k) in C^oo(RR^3) $
- *Coordinate surfaces*: planes with equations $u = "constant"$, $v = "constant"$ or $w = "constant"$.
- *Coordiante curve*: intersection of two coordinate surfaces.
- *Orthogonal curvilinear system*: where tangent vectors $underline(e)_u, underline(e)_v, underline(e)_w$ are mutually orthogonal at any point $P$. Orientation of these vectors may depend on $P$.
- Let $g$ invertible map from $u$-space to $x$-space, $g(u) = x$. Distortion factor $g'(u)$ is *Jacobian* of $g$. $dif x = g'(u) dif u$ so *method of substitution* is $ integral_a^b f(x) dif x = integral_(g^(-1)(a))^(g^(-1)(b)) f(g(u)) g'(u) dif u $
#set math.mat(delim: "|")
- In two dimensions, *Jacobian* for maps $(tilde(g), tilde(h))$ is $ J(tilde(g), tilde(h)) = mat(diff_x tilde(g), diff_y tilde(g); diff_x tilde(h), diff_y tilde(h)) =: (diff(tilde(g), tilde(g))) / (diff(x, y)) = (diff(u, v)) / (diff(x, y)) $ Distortion factor is $|J(tilde(g), tilde(h))|$. So $ dif A_(u v) = |J(tilde(g), tilde(h))| dif A_(x y) $ where $dif A_(x y) = dif x dif y$ and $ dif A_(x y) = |J(g, h)| dif A_(u v) = |J(tilde(g), tilde(h))|^(-1) dif A_(u v) $ So $ integral.double_R f(x, y) dif x dif y = integral.double_(R') f(g(u, v), h(u, v)) |J(g, h)| dif u dif v $ where $R$ mapped to $R'$ by $(tilde(g), tilde(h))$.
- $dif A_(u v)$ is parallelogram-shaped.
- In three dimensions, $ integral.triple_R f(x, y, z) dif x dif y dif z = integral.triple_(R') f(g(u, v, w), h(u, v, w), k(u, v, w)) |(diff(x, y, z)) / (diff(u, v, w))| dif u dif v dif w $ where $|(diff(x, y, z)) / (diff(u, v, w))| := J(g, h, k)$.
- $dif V_(u v w)$ is parallelopiped-shaped.
- *Gradient in Cartesian coordinates*: $underline(nabla) = underline(e)_1 diff_x + underline(e)_2 diff_y + underline(e)_3 diff_z$.
- *Laplacian in Cartesian coordinates*: $underline(nabla)^2 = diff_x^2 + diff_y^2 + diff_z^2$.
- For 2D polar coordinates, let $underline(r) = r cos(theta) underline(e)_1 + r sin(theta) underline(e)_2$, then $ tilde(underline(e))_r & := diff_r underline(r) = cos(theta) underline(e)_1 + sin(theta) underline(e)_2, \ tilde(underline(e))_theta & := diff_theta underline(r) = -r sin(theta) underline(e)_1 + r cos(theta) underline(e)_2 $
- Let $x = g(u, v)$, $y = h(u, v)$, then *scale factors for mapping given by $g$ and $h$* are $h_u := norm(diff_u underline(r))$, $h_v := norm(diff_v underline(r))$.
- Unit vectors corresponding to $tilde(underline(e))_r$ and $tilde(underline(e))_theta$ are $underline(e)_r = tilde(underline(e))_r$ and $underline(e)_theta = 1/r tilde(underline(e))_theta$ which form orthonormal basis.
- $dif underline(r) = diff_r underline(r) dif r + diff_theta underline(r) dif theta = dif r underline(e)_r + r dif theta underline(e)_theta$ by chain rule.
- *Gradient in polar coordinates*: $underline(nabla) = underline(e)_r diff_r + underline(e)_theta 1/r diff_theta$, obtained by comparing $dif f := underline(nabla) f dot.op dif underline(r) = diff_r f dif r + diff_theta f dif theta$ for function $f(r, theta)$.
- *Divergence in polar coordinates*: for $underline(A)(r, theta) = A_r underline(e)_r + A_theta underline(e)_theta$, $ underline(nabla) dot.op underline(A) = 1/r (diff_r(r A_r) + diff_theta A_theta) $
- *Laplacian in polar coordinates*: $underline(nabla)^2 = diff_r^2 + 1/r diff_r + 1/r^2 diff_theta^2$
- *Spherical polar coordinates*: $x = r sin(theta) cos(phi)$, $y = r sin(theta) sin(phi)$, $z = r cos(theta)$, $r >= 0$, $theta in [0, pi]$, $phi in [0, 2 pi)$.
- *Cylindrical polar coordinates*: $x = r cos(theta)$, $y = r sin(theta)$, $z = z$, $r >= 0$, $theta in [0, 2 pi)$, $z in RR$.
- *General formula for curl of vector in Cartesian coordinates*: for $underline(A)(r, theta, phi) = A_r underline(e)_r + A_theta underline(e)_theta + A_phi underline(e)_phi$, $ underline(nabla) times underline(A) = h_r^(-1) h_theta^(-1) h_phi^(-1) mat(h_r underline(e)_r, h_theta underline(e)_theta, h_phi underline(e)_phi; diff_r, diff_theta, diff_phi; A_r h_r, A_theta h_theta, A_phi h_phi) $

= Generalised functions (distributions)

- *Unit step function (Heaviside)*: $ Theta(t - t_0) := cases(
	0 & "if" t <= t_0,
	1 & "if" t > t_0
) $
- Let $Omega subset.eq RR^n$ open. $psi: Omega -> CC$ is *test function* if:
	- $psi$ is *smooth*: $psi in C^oo(Omega)$.
	- *Support* of $psi$, $ "supp"(psi) := overline({underline(x) in Omega: psi(underline(x)) != 0}) $ is compact (in this case, bounded).
- Space of test functions on $Omega$, $cal(D)(Omega)$, is vector space.
- Let $psi in cal(D)(RR^n), underline(xi) in RR^n, a in RR - {0}, g in C^oo(RR^n)$. Then
	- $psi(underline(x) + underline(xi)), psi(-underline(x)), psi(a underline(x)) in cal(D)(RR^n)$.
	- $g(underline(x)) psi(underline(x)) in cal(D)(RR^n)$.
- Let $Omega subset.eq RR^n$ open, then ${psi_m}_(m in NN) subset.eq cal(D)(Omega)$ *converges* to $psi in cal(D)(Omega)$ if:
	- Exists compact $K subset.eq Omega$ such that $"supp"(psi), "supp"(psi_m) subset.eq K$ for every $m in NN$ and
	- ${psi_m}$ converges *uniformly* to $psi$ in $cal(D)(Omega)$ and
	- sequence $ D^k psi_m := psi_m^((k)) := (diff^(k_1)) / (diff x_1^(k_1)) dots.h.c (diff^(k_n)) / (diff x_1^(k_n)) $ converges uniformly to $D^k psi$ for every multi-index $k = (k_1, dots, k_n)$, $k_i in NN_0$, $|k| = k_1 + dots.h.c + k_n$. (Write $psi_m ->_(cal(D)) psi$.)
- ${psi_m}$ converges to $psi$ if:
	- Exists compact $K subset.eq Omega$ such that $"supp"(psi_i) subset.eq K$ for every $i$ and
	- For every multi-index $k = (k_1, ..., k_n)$ and $|k| = k_1 + dots.h.c + k_n$ (including $|k| = 0$), $norm(D^k psi_m - D^k psi)_oo -> 0$ as $m -> oo$ where $||f||_oo := sup{|f(underline(x))|: underline(x) in RR^n}$.
- Let $Omega subset.eq RR^n$ open. *Distribution* is continuous linear map $T: cal(D)(Omega) -> RR$.
	- $T$ *linear*: $T[a psi + b phi] = a T[psi] + b T[phi]$.
	- $T$ *continuous*: $forall psi in cal(D)(Omega), forall {psi_m} subset.eq D(Omega), psi_m ->_(cal(D)) psi ==> T[psi_m] -> T[psi] "as" m -> oo$
- Space of distibutions with test functions in $cal(D)(Omega)$, written $cal(D)'(Omega)$, is vector space.
- *Dirac delta function* $delta: cal(D)(RR^n) -> RR$, is distribution $ delta[psi] := psi(underline(0)) $
- Let $f in C^0(RR^n)$. Then $ T_f[psi] := integral_(RR^n) f(underline(x)) psi(underline(x)) dif underline(x) $ is a distribution.
- $f: RR^n -> RR$ *locally integrable* if for every compact $K subset.eq RR^n$, $ integral_K f(underline(x)) dif underline(x) < oo $
- $L_"loc"^1(RR^n)$ is set of locally integrable functions on $RR^n$.
- $T in cal(D)'(RR^n)$ is *regular distribution* if for some $f in L_"loc"^1(RR^n)$, $T[psi] = T_f[psi]$ for $psi in cal(D)(RR^n)$.
- *Any two locally integrable functions that differ by finite amounts at isolated points define the same regular distribution*.
- Distribution $T$ is *singular* if no $f in L_"loc"^1(RR^n)$ such that $T = T_f$.
- *Symbolically, in the sense of distributions*, can write singular distribution as $ T[psi] := integral_(RR^n) T[underline(x)] psi(underline(x)) dif underline(x) =: angle.l T, psi angle.r $ *Note* $T[underline(x)]$ not a function.
- $delta$ is singular distribution.
- *Sifting property* of $delta$: $ integral_(RR^n) delta(underline(x)) psi(underline(x)) dif underline(x) = cases(
	psi(underline(0)) & "if" underline(x) = underline(0),
	0 & "otherwise"
) $
- *General sifting property* of $delta$: $ integral_Omega delta(underline(x)) psi(underline(x)) = cases(
	psi(underline(0)) & "if" underline(0) in Omega,
	0 & "otherwise"
) $
- *Notation*: if $n = 1$, write $delta(underline(x)) = delta(x)$, if $n = 2$, write $delta(x) delta(y)$, etc.
- *Distribution operation rules*:
	- *Addition*: $(T_1 + T_2)[psi] = T_1[psi] + T_2[psi]$.
	- *Multiplication by constant*: $(c T)[psi] = c T[psi]$.
	- *Shifting of distribution* by $underline(xi) in RR^n$: $T_(underline(xi))[psi(underline(x))] := integral_(RR^n) T(underline(x) - underline(xi)) psi(underline(x)) dif underline(x) = integral_(RR^n) T(underline(y)) psi(underline(y) + underline(xi)) dif underline(y) =: T[psi(underline(x) + underline(xi))]$
	- *Transposition*: $T^t(psi(underline(x))) := integral_(RR^n) T(-underline(x)) psi(underline(x)) dif underline(x) = integral_(RR^n) T(underline(y)) psi(-underline(y)) dif underline(y) =: T[psi(-underline(x))]$
	- *Dilation* by $alpha in RR$: $T_((alpha))[psi(underline(x))] := integral_(RR^n) T(alpha underline(x)) psi(underline(x)) dif underline(x) = 1/(|a|^n) integral_(RR^n) T(underline(y)) psi(underline(y) / alpha) dif underline(y) =: 1/(|a|^n) T[psi(underline(x) / alpha)]$
	- *Multiplication by smooth function $phi$*: $ (phi T)[psi] := T[phi psi] $
- Delta distribution *sifting property*: $ delta_alpha [psi] := integral_Omega delta(x - a) psi(x) dif x = cases(
	psi(a) & "if" a in Omega,
	0 & "otherwise"
) $
- In sense of distributions, $phi(x) delta(x - xi) = phi(xi) delta(x - xi)$.
- Symbolically, $delta(alpha x) = 1/|a| delta(x)$.
- If $f in C^1(Omega)$ has simple (multiplicity one) zeros at ${x_1, ..., x_n}$ then $ integral_Omega delta(f(x)) psi(x) dif x = sum_(i = 1)^n psi(x_i) / |f'(x_i)| $
- Distributions $T_1$ and $T_2$ *equal* if $ forall psi in cal(D)(Omega), integral_Omega T_1(x) psi(x) dif x = integral_Omega T_2(x) psi(x) dif x $
- $n$th *derivative* of distribution $T$: $ T^((n))[psi] = (-1)^n T[psi^((n))] $
- *In the sense of distributions*, $Theta'(t) = delta(t)$.
- *Leibniz rule*: $ (phi T)' = phi' T + phi T', quad (phi T)^((n)) = sum_(k = 0)^n binom(n, k) phi^((k)) T^((n - k)) $
- $f$ *piecewise continuous* on $(a, b)$ if $(a, b)$ can be divided into finite number of sub-intervals such that:
	- $f$ continuous on interior of each sub-interval and
	- $f$ tends to finite limit on boundary of each sub-interval as approached from interior of that sub-interval.
- $f$ *piecewise smooth* if piecewise continuous and has piecewise continuous first derivatives.
- To calculate *derivative in sense of distributions* of *piecewise-smooth* $f$, with branches $f_1, ..., f_n$ and discontinuities at $x_1, ..., x_(k - 1)$:
	- Let $caron(f)(x) = f_1(x) + (f_2(x) - f_1(x)) Theta(x - x_1) + dots.h.c + (f_k - f_(k - 1)) Theta(x - x_(k - 1))$
	- Then differentiate $caron(f)$.
- If Jacobian $J$ of changes of variables from $underline(x)$ to $underline(xi)$, then $ delta(underline(x) - underline(x_0)) = 1/|J| delta(underline(xi) - underline(xi_0)) $

= Sturm-Liouville Theory

- Let $f: [a, b] -> RR$, $a = x_0 < x_1 < dots.h.c < x_n = b$, $x_i^* in [x_(i - 1), x_i]$ Let $Delta = sup_(1 <= i <= n) (x_i - x_(i - 1))$, $cal(R)(f) = sum_(i = 1)^n f(x_i^*) (x_i - x_(i - 1))$. $f$ *Riemann integrable* if exists real number, written $integral_a^b f(x) dif x$ such that $ integral_a^b f(x) dif x = lim_(Delta -> 0) cal(R)(f) $
- *Lebesgue integration*: choose $y_0 <= min(f)$, $y_n >= max(f)$, $y_0 < y_1 < dots.h.c < y_n$. Let $ s_n := sum_(i = 1)^n y_(i - 1) dot.op mu{x: y_(i - 1) <= f(x) < y_i} $ where $mu{x: y_(i - 1) <= f(x) < y_i}$ is measure of set ${x: y_(i - 1) <= f(x) < y_i}$, i.e. sum of lengths of subintervals $[a, b]$ where $y_(i - 1) <= f(x) <= y_i$. *Lebesgue integral* is limit of $s_n$ as $n -> oo$.
- *Riemann-Lebesgue theorem*: let $f: [a, b] -> RR$ bounded. Then $f$ Riemann integrable iff $f$ continuous everywhere except on set of measure zero (continuous almost everywhere).
- Measure of set with countable number of elements is zero.
- Measure of $[a, b]$: $mu([a, b]) = b - a$. Also, $mu([a, b] times [c, d]) = (b - a) (d - c)$.
- If function Riemann integrable, then it is Lebesgue integrable.
- $L^1$: space of Lebesgue measurable and absolutely integrable functions.
- $L^2$: space of Lebesgue measurable functions with absolutely integrable squares.
- *Hilbert space* $HH$: real/complex vector space which:
	- has Hermitian inner product $angle.l dot.op, dot.op angle.r: HH times HH -> CC$, with:
		- *Hermiticity*: $angle.l underline(u), underline(v) angle.r = overline(angle.l underline(v)\, underline(u) angle.r)$.
		- *Anti-linearity in first entry*: $angle.l a (underline(u) + underline(v)), underline(w) angle.r = overline(a) angle.l underline(u), underline(w) angle.r + overline(a) angle.l underline(v), underline(w) angle.r $, $a in CC$.
		- *Positivity*: $angle.l underline(u), underline(u) angle.r >= 0$ and $angle.l underline(u), underline(u) angle.r = 0 <==> underline(u) = 0$.
	- is complete for inner product-induced norm: $ norm(dot.op): HH -> RR_(>= 0), quad norm(underline(u)) = (angle.l underline(u), underline(u) angle.r)^(1 \/ 2) $, with:
		- *Separation of points*: $norm(underline(u)) = 0 <==> u = 0$.
		- *Absolute homogeneity*: $norm(a underline(u)) = |a| norm(underline(u))$, $a in CC$.
		- *Triangle inequality*: $norm(underline(u) + underline(v)) <= norm(underline(u)) + norm(underline(v))$.
- Complex inner product *sesquilinear* as anti-linear in first entry, but linear in second.
- *Inner product space*: vector space with inner product and induced norm.
- *Metric* on vector space $V$: function $d: V times V -> RR$, with:
	- $d(underline(u), underline(v)) >= 0$.
	- $d(underline(u), underline(v)) = 0 <==> underline(u) = underline(v)$.
	- $d(underline(u), underline(v)) = d(underline(v), underline(u))$.
	- $d(underline(u), underline(v)) + d(underline(v), underline(w)) >= d(underline(u), underline(w))$.
- *Metric space*: pair $(V, d)$.
- One metric given by $d(underline(u), underline(v)) = norm(underline(u) - underline(v))$. Sequence ${underline(v)_n} subset.eq V$ *converges to $underline(v) in V$ in the mean (in norm)* if $ lim_(n -> oo) norm(underline(v)_n - underline(v)) = 0 <==> forall epsilon > 0, exists N in NN, forall n >= N, quad norm(underline(v)_n - underline(v)) < epsilon $
- ${underline(v)_n}$ *Cauchy sequence* if $ forall epsilon > 0, exists N in NN, forall m, n >= N, quad d(underline(v)_n, underline(v)_m) < epsilon $
- Metric space *complete* if every Cauchy sequence in $(V, d)$ converges in $V$.
- Let space $V$ be function $[a, b] -> CC$. Let *weight* function $w: [a, b] -> RR_(>= 0)$ with finitely many zeros. *Inner product with weight $w$*: $ angle.l underline(u), underline(v) angle.r_w := integral_a^b overline(u)(x) v(x) w(x) dif x $ Write $angle.l underline(u), underline(v) angle.r_(w = 1)$ as $angle.l underline(u), underline(v) angle.r$.
- $W subset.eq V$ *dense in $V$* if $ forall v in V, forall epsilon > 0, exists w in W, quad d(v, w) < epsilon $
- *Linear Operator*: $(L, D(L))$, $D(L)$ is dense linear subspace of $HH$, $L: D(L) -> HH$ linear: $ L(a u + v b) = a L(u) + b L(v) $ $L$ is the *operator*, $D(L)$ is *domain* of $L$.
- Linear operator $L: HH_1 -> HH_2$ *bounded* if for some $M >= 0$, $ forall v in HH_1, quad norm(L v)_(HH_2) <= M norm(v)_(HH_1) $ If $M$ doesn't exist, $L$ *unbounded*.
- *Norm* of $L$ is $ norm(L) := inf{M: forall h in HH_1, norm(L v)_(HH_2) <= M norm(v)_(HH_1)} $
- To show $L$ unbounded, find sequence ${x_n} subset D(L)$ with $norm(x_n)_(HH_1) <= M$ for some $M$, but $norm(L x_n)_(HH_2) -> oo$ as $n -> oo$.
- *Adjoint* of $(L, D(L))$ is $(L^*, D(L^*))$ where $L*: D(L*) -> HH_1$, $ angle.l L v_1, v_2 angle.r^(HH_2) = angle.l v_1, L^* v_2 angle.r^(HH_1), quad v_1 in D(L), v_2 in D(L^*) $ and $ D(L^*) := {v_2 in HH_2: exists v_2^* in HH_1, forall v_1 in D(L), angle.l L v_1, v_2 angle.r^(HH_2) = angle.l v_1, v_2^* angle.r^(HH_1) } $ For each $v_2 in D(L*)$, $v_2^* = L^* v_2$ is unique.
- *Boundary value problem (BVP) on $[a, b]$*: $ L u(x) = f(x), a < x < b, quad B_1(u) = B_2(u) = 0 $
- *Dirichlet boundary conditions*: $B_1(u) = u(a) = 0, B_2(u) = u(b) = 0$.
- *Neumann boundary conditions*: $B_1(u) = u'(a) = 0, B_2(u) = u'(b) = 0$.
- *Periodic boundary conditions*: $B_1(u) = u(a) - u(b) = 0, B_2(u) = u'(a) - u'(b) = 0$.
- *Mixed boundary conditions*: $B_1(u) = alpha_1 u(a) + beta_1 u'(a) = 0, B_2(u) = eta_2 u(b) + kappa_2 u'(b) = 0$
- *Initial value problem (IVP) on $[a, b]$*: $ L u(x) = f(x), a < x < b, quad u(a) = 0, u'(a) = 0 $
- *Formal adjoint* of $L = p_0(x) d_x^2 + p_1(x) d_x + p_2(x)$ is $ L^* := overline(p_0) d_x^2 + (2 overline(p_0)' - overline(p_1)) d_x + overline(p_0)'' - overline(p_1)' + overline(p_2) $
- Domain of $L = p_0(x) d_x^2 + p_1(x) d_x + p_2(x)$ is $ D(L) := {u in C^2([a, b]): B_1(u) = B_2(u) = 0} $
- *Green's formula*: let $L = p_0(x) d_x^2 + p_1(x) d_x + p_2(x)$, $L^*$ be formal adjoint. Then $ angle.l L u, v angle.r - angle.l u, L^* v angle.r = [overline(p_0)(v overline(u)' - v' overline(u)) + (overline(p_1) - overline(p_0)') v overline(u)]_a^b $
- For $L = p_0(x) d_x^2 + p_1(x) d_x + p_2(x)$, $D(L^*)$ consists of all functions $v$ satisfying *adjoint boundary conditions*: $ [overline(p_0)(v overline(u)' - v' overline(u)) + (overline(p_1) - overline(p_0)') v overline(u)]_a^b = 0 quad forall u in C^2([a, b]) "with" B_1(u) = B_2(u) = 0 $
- $(L, D(L))$ self-adjoint if $angle.l L u, v angle.r = angle.l u, L^* v angle.r$ (boundary terms vanish).
- BVP $L u(x) = f(x)$, $B_1(u) = B_2(u) = 0$ *self-adjoint* if $L = L^*$ and $D(L) = D(L^*)$ (so adjoint boundary conditions equal original boundary conditions) ($(L, D(L))$ is self-adjoint).
- If $L = p_0(x) d_x^2 + p_1(x) d_x + p_2(x)$ with real-valued coefficients and $p_1 = p_0'$, then $ L^* = d_x(p_0 d_x) + p_2 = L $ $L$ is *formally self-adjoint* with respect to inner product. $L$ is *Sturm-Liouville operator*. $L$ Sturm-Liouville iff $p_0' = p_1$.
- Let $L = p_0(x) d_x^2 + p_1(x) d_x + p_2(x)$, then $ frak(L) := rho L = d_x (rho p_0 d_x) + rho p_2, quad rho = 1 / p_0 exp(integral p_1 / p_0 dif x) $ is Sturm-Liouville.
- *Eigenfunction* $u_n$ with *eigenvalue* $lambda_n$ with respect to weight function $w(x)$ satisfies $L u_n(x) = lambda_n w(x) u_n(x)$.
- *Method of separation of variables*: write $U(x, t) = T(t) u(x)$ when solving PDE.
- $[a, b]$ *natural interval* if $p_0(a) = p_0(b) = 0$ and $p_0(x) > 0$ for $x in (a, b)$.
- *Sturm-Liouville eigenvalue problem*: $frak(L) u_n(x) + lambda_n w(x) u_n(x) = 0$.
- For Sturm-Liouville eigenvalue problem:
	- Eigenvalues real.
	- Eigenfunctions corresponding to distinct eigenvalues are orthogonal with respect to inner product $angle.l u, v angle.r_w$.
	- Eigenfunctions can be chosen to be real.
	- Eigenvalues of regular Sturm-Liouville eigenfunction problem ($|alpha_1| + |beta_1| > 0, |eta_2| + |kappa_2| > 0$) are simple (multiplicity one).
	- Set of eigenvalues is countably infinite and monotonically increasing sequence: $lambda_1 < lambda_2 < dots.h.c$ and $lim_(n -> oo) lambda_n = oo$.
	- For regular SL problem, can write *generalised Fourier expansion (eigenfunction expansion)* of $u$ as $ u = sum_(n = 0)^oo angle.l hat(u)_n, u angle.r_w hat(u)_n $ for normalised eigenfunctions $hat(u)_n$.
	- If $frak(L) u_n(x) + lambda_n w(x) u_n(x) = f(x)$, then $f(x) = sum_(n = 0)^oo angle.l hat(u)_n, f angle.r_w hat(u)_n$. Equate eigenfunction of $f$ with eigenfunction expansion of $u$ in $frak(L) u_n(x) + lambda_n w(x) u_n(x)$ and take inner product with $hat(u)_m$ to determine $c_m = angle.l hat(u)_m, u angle.r$
- If $f$ piecewise smooth on $[a, b]$, for all $x in (a, b)$, $ 1/2 (f(x_+) + f(x_-)) := 1/2 (lim_(epsilon -> 0) f(x + epsilon) + lim_(epsilon -> 0) f(x - epsilon)) = sum_(n = 0)^oo angle.l hat(u)_n, u angle.r_w hat(u)_n(x) $
- *Completeness of eigenfunctions*: $ sum_(n = 0)^oo hat(u)_n(y) hat(u)_n(x) w(y) = delta(x - y) = delta(y - x) = sum_(n = 0)^oo hat(u)_n(x) hat(u)_n(y) w(x) $

= Green's functions

- *IN/IN IVP*: $L u(t) = f(t)$, $u(a) = gamma_1 != 0$, $u'(a) = gamma_2 != 0$.
- *IN/HOM IVP*: $L u(t) = f(t)$, $u(a) = u'(a) = 0$.
- *HOM/IN IVP*: $L u(t) = 0$, $u(a) = gamma_1 != 0$, $u'(a) = gamma_2 != 0$.
- Similarly for BVP.
- *BVP* boundary conditions: $B_1(u) = alpha_1 u(a) + beta_1 u'(a) + eta_1 u(b) + kappa_1 u'(b) = gamma_1$, $B_2(u) = alpha_2 u(a) + beta_2 u'(a) + eta_2 u(b) + kappa_2 u'(b) = gamma_2$. If $gamma_1 = gamma_2 = 0$, conditions are *homogeneous*. If $eta_1 = kappa_1 = alpha_2 = beta_2 = 0$, conditions are *separate*.
- $u_1, u_2$ *linearly independent* if $c_1 u_1(x) + c_2 u_2(x) = 0$ only satisfied by $c_1 = c_2 = 0$.
#set math.mat(delim: "|")
- *Wronskian* of $u_1, u_2$: $ W(u_1, u_2) := mat(u_1, u_2; u_1', u_2') = u_1 u_2' - u_1' u_2 $
- If $u_1, u_2 in C^1([a, b])$ and $W(u_1, u_2)(x_0) != 0$ for some $x_0 in [a, b]$ then $u_1, u_2$ linearly independent on $[a, b]$.
- If $u_1, u_2$ solutions of $L u = 0$, Wronskian either identically zero or never zero on $[a, b]$. $u_1, u_2$ linearly dependent iff Wronskian identically zero.
- *To solve IN/IN IVP* $L u(t) = f(t), u(0) = u_0, u'(0) = v_0$:
	- Solve HOM/IN IVP: $ L u_"hom"(t) = 0, u_"hom"(0) = u_0, u_"hom"'(0) = v_0 $ $u_"hom"(t) = c_1 tilde(u)_1(t) + c_2 tilde(u)_2(t)$ where $tilde(u)_1, tilde(u)_2$ linearly independent solutions.
	- Solve IN/HOM IVP: $ L u_p(t) = f(t), u_p(0) = 0, u_p'(0) = 0 $.
	- General solution: $u(t) = u_"hom"(t) + u_p(t)$.
- *To solve IN/HOM IVP*:
	- Let $f(t) = integral_0^oo delta(t - tau) f(tau) dif tau$.
	- $L_t G(t, tau) = delta(t - tau)$, $G(0, tau) = 0 = diff_t G(0, tau)$.
	- $G(0, tau) = 0 = diff_t G(0, tau)$.
	- $G$ continuous at $t = tau$: $ lim_(epsilon -> 0^+) G(tau + epsilon, tau) = lim_(epsilon -> 0^+) G(tau - epsilon, tau) $
	- Jump discontinuity of $diff_t G$ at $t = tau$: $ lim_(epsilon -> 0^+) ((diff G) / (diff t) (tau + epsilon, tau) - (diff G) / (diff t) (tau - epsilon, tau)) = 1/(p_0(tau)) $
	- Define ansatz: $ G(t, tau) & = A_1(tau) u_1(t) + B_1(tau) u_2(t) quad "for" t < tau \ G(t, tau) & = A_2(tau) u_1(t) + B_2(tau) u_2(t) quad "for" tau < t $ where $u_1, u_2$ linearly independent solutions of $L u = 0$.
	- For $t < tau$, $G(0, tau) = 0 = diff_t G(0, tau)$ which should give $A_1(tau) = B_1(tau) = 0$ so $G(t, tau) = 0$ for $t < tau$.
	- For $t > tau$, use jump discontinuity of $diff_t G$ and continuity of $G$ to find $A_2(tau)$ and $B_2(tau)$.
	- $ G(t, tau) = cases(
		0 & "if" t < tau,
		(u_1(tau) u_2(t) - u_2(tau) u_1(t)) / (p_0(tau) W(u_1, u_2)(tau)) & "if" t > tau
	) $
	- *Final solution*: $ u_p(t) = integral_0^oo G(t, tau) f(tau) dif tau $ $G(t, tau)$ is *Green's function* encoding response of system at time $t$ to unit impulse at time $tau$.
- *To solve IN/IN BVP* $L u(x) = f(x)$, $u(a) = u_a, u(b) = u_b$:
	- Solve HOM/IN BVP: $ L u_"hom"(x) = 0, u_"hom"(a) = u_a, u_"hom"(b) = u_b $ $u_"hom"(x) = c_1 tilde(u)_1(x) + c_2 tilde(u)_2(x)$ where $tilde(u)_1, tilde(u)_2$ linearly independent solutions.
	- Solve IN/HOM BVP: $ L u_p(x) = f(x), u_p(a) = 0, u_p(b) = 0 $
	- General solution: $u(x) = u_"hom"(x) + u_p(x)$.
- *To solve IN/HOM BVP*:
	- $L_x G(x, xi) = delta(x - xi)$, $G(a, xi) = 0$ for $x < xi$, $G(b, xi) = 0$ for $xi < x$.
	- Define ansatz: $ G(x, xi) & = A_1(xi) u_1(x) + B_1(xi) u_2(x) quad "for" x < xi \ G(x, xi) & = A_2(xi) u_1(x) + B_2(xi) u_2(x) quad "for" xi < x $ where $u_1, u_2$ linearly independent solutions of $L u = 0$.
	- $G$ continuous at $x = xi$: $ lim_(epsilon -> 0^+) G(xi + epsilon, xi) = lim_(epsilon -> 0^+) G(xi - epsilon, xi) $
	- Jump discontinuity of $diff_x G$ at $x = xi$: $ lim_(epsilon -> 0^+) ((diff G) / (diff x) (xi + epsilon, xi) - (diff G) / (diff x) (xi - epsilon, xi)) = 1/(p_0(xi)) $
	- Use continuity, jump discontinuity and boundary conditions to find $A_1, B_1, A_2, B_2$.
	- *Final solution*: $ u_p(x) = integral_a^b G(x, xi) f(xi) dif xi $
	- *Note*: if boundary conditions are $B_1(u) = gamma_1, B_2(u) = gamma_2$, $G$ must satisfy $B_1(G) = 0, B_2(G) = 0$.
- *Laplace equation*: $underline(nabla)^2 u = u_(x x) + u_(y y) = 0$
- *Poisson's equation*: $underline(nabla)^2 u(x, y) = f(x, y)$.
- *Fundamental solution of Laplace's equation*: $ G_2(underline(x)) := 1/(2 pi) ln(r), quad r = |underline(x)| $
- *Fundamental solution of Laplace's equation in plane with pole at $x = xi$*: $ G_2(underline(x), underline(xi)) := G_2(underline(x) - underline(xi)) = 1/(2 pi) ln|underline(x) - underline(xi)| $
- *Green's first identity*: let $underline(F) = underline(nabla) u$ in Divergence theorem: $ integral_Omega underline(nabla)^2 u dif x dif y = integral_(diff Omega) underline(nabla) u dot.op underline(n) dif s = integral_(diff Omega) underline(n) dot.op underline(nabla) u dif s = integral_(diff Omega) diff_n u dif s $
- *Green's second identity*: let $F = u underline(nabla) v$ in Divergence theorem: $ integral_Omega underline(nabla) dot.op (u underline(nabla) v) = integral_Omega (u underline(nabla)^2 v + underline(nabla) u dot.op underline(nabla) v) dif x dif y = integral_(diff Omega) u underline(nabla) v dot.op underline(n) dif s = integral_(diff Omega) u diff_n v dif s $
- *Green's third identity*: interchange $u$ and $v$ in second identity, subtract one from other: $ integral_Omega (u underline(nabla)^2 v - v underline(nabla)^2 u) dif x dif y = integral_(diff Omega) (u diff_n v - v diff_n u) dif s $
- *Dirichlet problem*: IN/IN BVP $ underline(nabla)^2 u(underline(x)) = f(underline(x)), u(underline(x))_(diff Omega) = g(underline(x)) $ To solve:
	- Subtract function $G_"reg"$ from $G_2$ so that $G := G_2 - G_"reg"$ satisfies $underline(nabla)^2 G(underline(x), underline(xi)) = delta(underline(x) - underline(xi))$, $G(underline(x), underline(xi)) = 0 <==> G_2 = G_"reg"$ for $x in diff Omega$. $G$ is *Green's function for Dirichlet problem on domain $Omega$*. $G_"reg"$ must satisfy Laplace equation on $Omega$.
	- *Full solution*: $ u(underline(xi)) = integral_Omega G(underline(x), underline(xi)) f(underline(x)) dif x + integral_(diff Omega) g(underline(x)) diff_n G(underline(x), underline(xi)) dif s $ $underline(n)$ is unit normal to $Omega$ at $underline(x)$ pointing outwards.
- To find $G_"reg"$, use *method of images*:
	- Fix point $P in Omega$ with position vector $underline(xi)_0$, let $Q in Omega$ have position vector $underline(x)$. Then $G_2(underline(x), underline(xi)_0) = 1/(2 pi) ln|P Q|$.
	- Let $P_1, ..., P_n$ be reflection of $P$ in boundary lines of $diff Omega$ (repeat reflection until back to $P$). Label $P_1, ..., P_n$ with alternating $-$ and $+$. Then $ -G_"reg" = -1/(2pi) ln|Q P_1| + 1/(2pi) ln|Q P_2| - dots.h.c - ln|Q P_n| $
	- *Note*: if $diff Omega$ is circle radius $R$, $O P_1$ must satisfy $|O P| dot.op |O P_1| = R^2$ so $ tilde(underline(xi))_0 := O P_1 = R^2 / |underline(xi)_0|^2 underline(xi)_0 $
	- Check if $G_"reg"$ satisfies $underline(nabla_x)^2 G_"reg"(underline(x), underline(xi)_0) = 0$ and $G_"reg" = G_2$ on $diff Omega$. If $G_"reg" != G_2$, add constant $c$ to $G_"reg"$ so that $G_"reg" = G_2$.