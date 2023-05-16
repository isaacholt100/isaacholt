#import "../../template.typ": template
#show: template

= The complex plane and Riemann sphere

- $CC^* = CC - {0}$
- $z_1 z_2 = 0 <==> z_1 = 0$ or $z_2 = 0$.
- $|z| = sqrt(z overline(z))$.
- $"Re"(z) = (z + overline(z)) \/ 2$, $"Im"(z) = (z - overline(z)) \/ 2i$.
- $z^(-1) = overline(z) \/ |z|^2$.
- *Principal value of $arg(z)$*: in interval $lr((-pi, pi])$, written $"Arg"(z)$.
- $arg(z_1 z_2) ident arg(z_1) + arg(z_2) quad (mod 2pi)$.
- $arg(1 \/ z) = -arg(z) quad (mod 2pi)$.
- $arg(overline(z)) = -arg(z) quad (mod 2pi)$.
- Multiplication by $z_1 = r_1 e^(i theta_1)$ represents rotation by $theta_1$ followed by dilation by factor $r_1$.
- Addition represents translation.
- Conjugation represents reflection in the real axis.
- Taking the real (imaginary) part represents projection onto the real (imaginary) axis.
- $|z_1 z_2| = |z_1| |z_2|$.
- *De Moivre's formula*: $(cos(theta) + i sin(theta))^n = cos(n theta) + i sin(n theta)$.
- *Triangle inequality*: $|z_1 + z_2| <= |z_1| + |z_2|$.
- $|z| >= 0$ and $|z| = 0 <==> z = 0$.
- $max{|"Re"(z)|, |"Im"(z)|} <= |z| <= |"Re"(z)| + |"Im"(z)|$.
- *Complex exponential function*: $ exp(z) := e^x (cos(y) + i sin(y)) $.
- $forall z in CC, e^z != 0$.
- $e^(z_1 + z_2) = e^(z_1) e^(z_2)$.
- $e^z = 1 <==> z = 2 pi i k$ for some $k in ZZ$.
- $e^(-z) = 1 \/ e^z$.
- $|e^z| = e^("Re"(z))$.
- $forall k in ZZ$, $exp(z) = exp(z + 2k pi i)$.
- $ sin(z) := 1 / (2 i) (e^(i z) - e^(-i z)), quad cos(z) := 1/2 (e^(i z) + e^(-i z)) \ sinh(z) := 1/2 (e^z - e^(-z)), quad cosh(z) := 1/2 (e^z + e^(-z)) $
- For every $w in CC^*$, $ e^z = w = |w| e^(i phi) $ has solutions $ z = log(|w|) + i(phi + 2k pi), quad k in ZZ $
- Let $theta_2 - theta_1 = 2 pi$, let $arg$ be the argument function in $lr((theta_1, theta_2])$. Then $ log(z) := log(|z|) + i arg(z) $ is a *branch of logarithm*. Jump discontinuity on *branch cut*, the ray $R_(theta_1) = R_(theta_2)$.
- *Principal branch of log*: where $arg(z) = "Arg"(z) in lr((-pi, pi])$.
- $e^(log(z)) = z$.
- Generally, $log(z w) != log(z) + log(w)$.
- Generally, $log(e^z) != z$.
- Given a branch of log, *power function* is $ z^w := exp(w log(z)) $
- $hat(CC) = C union {infinity}$.
- Unit sphere: $S^2 = {(x, y, s) in RR^3: x^2 + y^2 + s^2 = 1}$, north pole: $N = (0, 0, 1) in S^2$. *Stereographic projection*: map that takes $v in S^2 - {N}$ to $x + i y in CC$, where $(x, y)$ is where the line from $N$ through $v$ intersects the $(x, y)$-plane.
- *Stereographic projection formula*: $ P(x, y, s) = x / (1 - s) + (i y) / (1 - s) $ North pole is mapped to $infinity$.
- Inverse of stereographic projection found by intersection of line (from $z in CC$ to $N$) and $S^2$.
- *Riemann sphere*: unit sphere $S^2$ with stereographic projections from north and south pole.

= Metric spaces

- *Metric space*: set $X$ and *metric* function $d: X times X -> RR_(>= 0)$, for every $x, y, z in X$
	- *positivity*: $d(x, y) >= 0$ and $d(x, y) = 0 <==> x = y$
	- *symmetry*: $d(x, y) = d(y, x)$
	- *triangle inequality*: $d(x, y) <= d(x, z) + d(z, y)$
- *norm* on vector space $V$:
	- $||v|| >= 0$ and $||v|| = 0 <==> v = 0$
	- $||lambda v|| = |lambda| dot.op ||v||$
	- $||v + w|| <= ||v|| + ||w||$
- $d(v, w) = ||v - w||$ always defines a metric
- $d(v, w) = sqrt(angle.l v - w \, v - w angle.r)$
- *$l_p$ norm*: $ ||x||_p = root(p, sum_(i = 1)^n |x_i|^p) $
- *Taxicab norm*: $l_1$ norm
- *$l_oo$ norm (sup-norm)*: $||x||_oo := max_(i = 1, dots, n) |x_i|$
- *Riemannian (chordal) metric on $hat(CC)$*: $d(z, w) = ||f(z) - f(w)||_2$ where $f: hat(CC) -> S^2$ is the inverse stereographic projection.
- *Discrete metric*: $ d(x, y) := cases(
	0 "if" x = y,
	1 "if" x != y
) $
- *Open ball of radius $r$ centred at $x$*: $B_r(x) := {y in X: d(x, y) < r}$
- *Closed ball of radius $r$ centred at $x$*: $overline(B)_r(x) := {y in X: d(x, y) <= r}$
- *$U subset.eq X$ open* if $forall x in U, exists epsilon > 0, B_epsilon(x) subset U$
- *$U subset.eq X$ closed* if $X - U$ open
- *clopen*: open and closed, e.g. empty set and $X$
- Open balls are open
- Closed balls are closed
- Arbitrary unions of open sets are open
- Finite intersections of open sets are open
- Finite unions of closed sets are closed
- Arbitrary intersections of closed sets are closed
- *Interior of $A$*: $A^0 := {x in A: "for some open" U subset.eq A, x in U}$. It is the largest open set in $A$.
- *Closure of $A$*: complement of interior of complement: $overline(A) := {x in X: U union A != nothing "for every open set" U "with" x in U} = X - (X - A)^0$. It is the smallest closed set containing $A$.
- *Boundary of $A$*: closure without interior: $diff A := overline(A) - A^0$
- *Exterior of $A$*: complement of closure: $A^e := X - overline(A) = (X - A)^0$
- $A "is open" <==> diff A sect A = nothing <==> A = A^0$
- $A "is closed" <==> diff A subset.eq A <==> A = overline(A)$
- For simple sets in $RR^n$ or $CC^n$, closure (or interior) is obtained by replacing by replacing strict inequality with equality (or vice versa).
- Sequence ${x_n}$ *converges to* $x in X$ if $lim_(n -> oo) d(x_n, x) = 0$ or equivalently, $ forall epsilon > 0, exists N in NN, forall n > N, d(x_n, x) < epsilon $
- Limits in the complex plane follow COLT rules
- ${z_n}$ converges iff ${"Re"(z_n)}$ and ${"Im"(z_n)}$ converge.
- $lim_(n -> oo) x_n = x <==> forall "open" U "with" x in U, exists N in NN, forall n > N, x_n in U$
- $f: (X_1, d_1) -> (X_2, d_2)$ is *continuous at $x_0 in X_1$* if $ forall epsilon > 0, exists delta > 0, forall x in X_1, d_1(x, x_0) < delta ==> d_2(f(x), f(x_0)) < epsilon $
- $f$ is *continuous on $X_1$* if continuous at every $x_0 in X_1$
- Products, sums and quotients of real/complex continuous functions are continuous
- Compositions of continuous functions are continuous
- *Preimage*: $f^(-1)(U) := {x in X_1: f(x) in U}$
- *Properties of preimage*:
	- $f^(-1)(A union B) = f^(-1)(A) union f^(-1)(B)$
	- $f^(-1)(A sect B) = f^(-1)(A) sect f^(-1)(B)$
	- $f^(-1)(A - B) = f^(-1)(A) - f^(-1)(B)$
- $f: X_1 -> X_2 "continuous" & <==> f^(-1)(U) "open in" X_1 forall "open" U subset.eq X_2 \ & <==> f^(-1)(F) "closed in" X_1 forall "closed" F subset.eq X_2$
- $f: X_1 -> X_2 "continuous at" x in X_1 <==> f^(-1)(U) "open in" X_1 forall "open" U subset.eq X_2 "containing" f(x)$
- Non-empty $K subset.eq X$ *compact* if for every sequence ${x_k}$ in $K$, there exists a convergent subsequence ${x_(n_k)}$ with limit in $K$.
- If ${x_k}$ is a convergent sequence in $X$ then every subsequence ${x_(n_k)}$ converges to the same limit.
- $F subset.eq X$ is closed iff every sequence in $F$ converging in $X$ also converges in $F$.
- Compact sets are closed
- Every closed subset of a compact set is compact
- $A subset.eq X$ *bounded* if for some $R > 0$, $x in X$, $A subset.eq B_R(x)$
- Compact sets are bounded
- *Heine-Borel for $CC$*: $K subset.eq CC$ is compact iff $K$ is closed and bounded.
- $f: X -> Y$ is continuous at $x in X$ iff $ lim_(n -> oo) f(x_n) = f(x) $ for every convergent sequence ${x_n}$ in $X$ with $x_n -> x$.
- If $K subset.eq X$ is compact and $f: X -> Y$ is continuous, then $f(K)$ is compact in $Y$. So for $Y = RR$, any continuous real-valued function attains maxima and minima on compact sets.

= Complex differentiation

- $f: U -> CC$ for open $U$ is *complex differentiable at $z_0 in U$* if $ lim_(z -> z_0) (f(z) - f(z_0)) / (z - z_0) $ exists. Limit is the *derivative of $f$ at $z_0$*: $ f'(z_0) = lim_(h -> 0) (f(z_0 + h) - f(z_0)) / h $. $h in CC$ so limit must exist from every direction.
- Complex differentiability at $z_0$ implies continuity at $z_0$.
- Sums, products and quotients of complex differentiable functions are complex differentiable.
- Compositions of complex differentiable functions are complex differentiable.
- The product, quotient and chain rules hold for complex differentiable functions.
- Most non-constant purely real/imaginary functions are not complex differentiable.
- If $f = u + i v$ is complex differentiable at $z_0$ then $u_x, u_y, v_x, v_y$ exist at $z_0$ and satisfy *Cauchy-Riemann equations*: $ u_x(z_0) = v_y(z_0), quad u_y(z_0) = -v_x(z_0) $. Also, $ f'(z_0) = u_x(z_0) + i v_x(z_0) $
- Let $f: U -> CC$, $U$ open, $f = u + i v$. If $u_x, u_y, v_x, v_y$ exist and are continuous at $z_0$ and satisfy the Cauchy-Riemann equations at $z_0$, then $f$ is complex differentiable at $z_0$.
- Let $U subset.eq C$ open, $f: U -> CC$. $f$ is *holomorphic on $U$* if $f$ is complex differentiable at every $z_0 in U$.
- $f$ is *holomorphic at $z_0 in U$* if $f$ is complex differentiable on some $B_epsilon(z_0)$.
- Affine linear maps $z -> a z + b$, $a != 0$ are holomorphic.
- *Path (curve) from $a$ to $b$*: continuous function $gamma: [0, 1] -> CC$ with $gamma(0) = a$ and $gamma(1) = b$. Path *closed* if $a = b$.
- *Smooth* path: continuously differentiable.
- $U subset.eq CC$ *path-connected* if for every $a, b in U$, there exists a path $gamma$ from $a$ to $b$ with $gamma(t) in U$ for every $t in [0, 1]$.
- *Domain (region)*: open and path-connected.
- *Chain rule*: Let $U subset.eq CC$ open, $f: U -> CC$ holomoprhic, $gamma: [0, 1] -> U$ smooth path. Then $ (f compose gamma)'(t_0) = f'(gamma(t_0)) gamma'(t_0) $
- Let $D$ domain, $f: D -> CC$ holomorphic on $D$. If $forall z in D, f'(z) = 0$, or $f$ is purely real/imaginary, or $f$ has constant real/imaginary part, or $f$ has constant modulus, then $f$ is constant on $D$.
- Let $D$ domain, $f: D -> CC$ *conformal at $z_0$* if $f$ preserves angle and orientation of any two tangent vectors at $z_0$. Equivalently, $f$ preserves angle and orientation of any two smooth paths through $z_0$. $f$ *conformal* if conformal at every $z_0 in D$.
- If $f$ holomorphic, $f'(z_0) != 0$ then $f$ conformal at $z_0$.
- $f$ transforms the tangent vector $gamma'(t_0)$ by multiplying it by $f'(gamma(t_0))$.
- If $f$ is conformal at $z_0$, then $f$ is complex differentiable at $z_0$ and $f'(z_0) != 0$.
- $f$ is conformal on domain $D$ iff $f$ is holomorphic on $D$ and $forall z in D, f'(z) != 0$.
- Conformal maps map orthogonal grids in the $(x, y)$-plane to orthogonal grids. (Grids can be made of arbitrary smooth curves, not necessarily straight lines).
- For $D$ and $D'$ domains, $f: D -> D'$ is *biholomorphic* if $f$ holomorphic, bijection and $f^(-1): D' -> D$ holomorphic. $f$ is a *biholomorphism*. $D$ and $D'$ are *biholomorphic* if such an $f$ exists and write $f: D op("~", limits: #true)_(->) D'$
- Affine linear maps $z -> a z + b$, $a != 0$, are biholomorphic from $CC$ to $CC$.
- For $D$ domain, set of all biholomorphic maps from $D$ to $D$ forms a group under composition, called *automorphism group of $D$*, $"Aut"(D)$.

= Mobius transformations

- $"GL"_2(CC) := {A in M_2(CC): det(A) != 0}$.
- Let $T = mat(a, b; c, d) in "GL"_2(CC)$, then *Mobius transformation* is $M_T(z) = infinity$ if $c z + d = 0$, else $ M_T(z) = (a z + b) / (c z + d) $ Also $ M_T(infinity) = cases(
	a/c & "if" c != 0,
	infinity & "if" c = 0
) $ So $M_T: hat(CC) -> hat(CC)$.
- Let $k^2 = det(T)$ then $ M_(1/k T)(z) = ((a z)/k + b/k) / ((c z)/k + d/k) = (a z + b) / (c z + d) = M_T(z) $ so any $T$ can be scaled to $T' = 1/k T$ so that $det(T') = det(1/k T) = 1/k^2 det(T) = 1$.
- *Cayley map*: $M_T(z) = (z - i) / (z + i)$ where $T = mat(1, -i; 1, i)$.
- Cayley map maps $HH -> DD$.
- Set of Mobius transformations forms group under composition:
	- $M_(T_1) compose M_(T_2) = M_(T_1 T_2)$.
	- $(M_T)^(-1) = M_(T^(-1))$.
	- $M_T = "Id" <==> T = t mat(1, 0; 0, 1)$, $t in CC^*$.
- Let $T = mat(a, b; c, d) in "GL"_2(CC)$. If $c = 0$, $M_T$ is biholomorphic from $hat(CC)$ to $hat(CC)$. If $c != 0$, $M_T$ is biholomorphic from $CC - { -d/c }$ to $CC - { a/c }$.
- $M_T$ conformal at every $z in CC$ where $M_T(z) != infinity$.
- $M_T$ is bijection from $hat(CC)$ to $hat(CC)$.
- $z$ is *fixed point* of $M_T$ if $M_T(z) = z$.
- If $M_T$ is not identity map, then it has at most $2$ fixed points in $hat(CC)$. So if $M_T$ has $3$ fixed points in $hat(CC)$, it is identity map.
- *Cross ratio* of distinct $z_0, z_1, z_2, z_3 in CC$: $ (z_0, z_1; z_2, z_3) := ((z_0 - z_2)(z_1 - z_3)) / ((z_0 - z_3)(z_1 - z_2)) $ If some $z_i = infinity$ then same definition but remove all differences involving $z_i$, so $ (infinity, z_1; z_2, z_3) := ((z_1 - z_3)) / ((z_1 - z_2)) $
- *Three points theorem*: Let ${z_1, z_2, z_3}$, ${w_1, w_2, w_3}$ be sets of distinct ordered points in $hat(CC)$. Then exists unique Mobius transformation $f$ such that $f(z_i) = w_i$, $i = 1, 2, 3$, given by $F^(-1) compose G$, where $ F(z) = (z, w_1; w_2, w_3), quad G(z) = (z, z_1; z_2, z_3) $
- *Mobius transformations preserve cross ratio*: For Mobius transformation $f$, $ (f(z_0), f(z_1); f(z_2), f(z_3)) = (z_0, z_1; z_2, z_3) $
- *Strategy to find Mobius transformation from how it acts on three points*: since cross-ratio preserved, rearrange the equation $ (f(z), w_1; w_2, w_3) = (z, z_1; z_2, z_3) $
- *Strategy to find image of domain $D$ under $M_T$*:
	- Find image of boundary: $M_T(diff D)$.
	- Find image of point $z_0 in D$ in interior: $M_T(z_0)$.
	- Image $D'$ is domain bounded by $M_T(diff D)$ and containing $M_T(z_0)$.
- *Circline*: circle or line.
- Mobius transformations map circlines in $hat(CC)$ to circlines in $hat(CC)$.
- *Equations of circles and lines in $CC$*: $ gamma z overline(z) - alpha overline(z) - overline(alpha) z + beta = 0 $ is equation of circle if $gamma = 1$ and $|alpha|^2 - beta > 0$, and equation of line if $gamma = 0$ and $alpha != 0$. Also, any circle or line can be described by this equation.
- Circle uniquely determined by three points, line determined by two points, so to determine how Mobius transformation maps circle, check where three points on circle are mapped.
- Circles through $N$ in $S^2$ correspond to lines in $hat(CC)$. Circles not through $N$ correspond to circles in $hat(CC)$ (via stereographic projection).
- For domain $D$, $"Mob"(D)$ is set of Mobius transformations that map $D$ to $D$.
- *H2H*: $ f in "Mob"(HH) <==> f = M_T, quad T in "SL"_2(RR) := {A in M_2(RR): det(A) = 1} $
- *D2D*: $ f in "Mob"(DD) <==> f = M_T, quad T in "SU"(1, 1) := {A = mat(alpha, beta; overline(beta), overline(alpha)): alpha, beta in CC, det(A) = 1} $
- *D2D\**:
	- Every $f in "Mob"(DD)$ is of form $ f(z) = e^(i theta) (z - z_0) / (overline(z_0) z - 1) $ where $z_0 in DD$ is unique point such that $f(z_0) = 0$.
	- Every $f in "Mob"(DD)$ where $f(0) = 0$ is a rotation about $0$.
- *Strategy to find biholomorphic map between two domains*: build up biholomorphic map from simpler known ones, e.g. Mobius transformations, Cayley map, translations.

= Notions of convergence in complex analysis and power series

- For $X$ and $Y$ metric spaces, ${f_n}_(n in NN): X -> Y$ *converges pointwise on $X$ to $f$* if $ forall x in X, forall epsilon > 0, exists N in NN, forall n > N, quad d_Y(f_n(x), f(x)) < epsilon $ $f(x) = lim_(n -> infinity) f_n(x)$ is *limit function*.
- ${f_n}_(n in NN)$ *converges uniformly on $X$ to $f$* if $ forall epsilon > 0, exists N in NN, forall n > N, forall x in X, quad d_Y(f_n(x), f(x)) < epsilon $
- Uniform convergence implies pointwise convergence.
- *Uniform limits of continuous functions are continuous*: let ${f_n}_(n in NN)$ be all continuous on $X$ and converge uniformly to $f$ on $X$. Then $f$ is continuous on $X$.
- *Test for uniform convergence*: let ${f_n}: X -> CC$ converge pointwise to $f$.
	- If $forall x in X, |f_n(x) - f(x)| <= s_n$, ${s_n}$ is sequence with $lim_(n -> oo) s_n = 0$, then ${f_n}$ converges uniformly to $f$ on $X$.
	- If for some sequence ${x_n} subset X$, $|f_n(x_n) - f(x_n)| >= c$ for some $c > 0$, then $f_n$ does not converge uniformly to $f$ on $X$.
- *Weierstrass M-test*: Let ${f_n}: X -> CC$ satisfy $ forall x in X, |f_n(x)| <= M_n, quad sum_(n = 1)^oo M_n < oo $ Then $sum_(n = 1)^oo f_n$ converges uniformly to some $f$ on $X$.
- Let ${f_n}: [a, b] -> RR$ be continuous and converge uniformly to $f$ on $[a, b]$. Then $ forall c in [a, b], quad lim_(n -> oo) integral_a^c f_n(x) dif x = integral_a^c f(x) dif x $
- ${f_n}$ *converges locally uniformly on $X$ to $f$* if $forall x in X$, exists open $U subset X$ containing $x$ such that ${f_n}$ converges uniformly to $f$ on $U$.
- Let ${f_n}$ be continuous on $X$ and converge locally uniformly to $f$ on $X$. Then $f$ is continuous on $X$.
- *Local M-test*: let ${f_n}: X -> CC$ be continuous, such that $forall y in X$, exists open $U subset X$ containing $y$ and $M_n > 0$ with $ forall x in U, |f_n(x)| <= M_n, quad sum_(n = 1)^oo M_n < oo $ Then $sum_(n = 1)^oo f_n$ converges locally uniformly to continuous function on $X$.
- *Complex power series*: $ sum_(n = 0)^oo a_n (z - c)^n, quad a_n, c in CC $
- Either:
	- Series converges only for $z = c$ ($R = 0$).
	- Series converges absolutely for $|z - c| < R <==> z in B_R(c)$. $R$ is *radius of convergence*, $B_R(c)$ is *disc of convergence* and diverges for $|z - c| > R$.
	- Series converges absolutely for all $z$ ($R = oo$).
- Power series with radius of convergence $R$ converges absolutely on $B_r(c)$ for every $0 < r < R$. So series is locally uniformly convergent (but not uniformly convergent) on disc of convergence.
- *Term-by-term differentiation and integration preserve radius of convergence*: let $sum_(n = 0)^oo a_n (z - c)^n$ have radius of convergence $R$. Then formal derivative and antiderivative $ sum_(n = 1)^oo n a_n (z - c)^(n - 1), quad sum_(n = 0)^oo a_n / (n + 1) (z - c)^(n + 1) $ have radius of convergence $R$.
- *Power series can be differentiated term-by-term in disc of convergence*: let $sum_(n = 0)^oo a_n (z - c)^n$ have radius of convergence $R$ and converge to $f: B_R(c) -> CC$. Then $f$ is holomorphic on $B_R(c)$ and $ f'(z) = sum_(n = 1)^oo n a_n (z - c)^(n - 1) $
- Power series with $R > 0$ can be differentiated infinitely many times and $ f^((k))(z) = sum_(n = k)^oo k! binom(n, k) a_n (z - c)^(n - k) $ So $f^((k))(c) = k! a_k$.
- *Power series can be integrated term-by-term in disc of convergence*: power series with $R > 0$ has holomorphic antiderivative $F: B_R(c) -> CC$ given by $ F(z) = sum_(n = 0)^oo a_n / (n + 1) (z - c)^(n + 1) $

= Complex integration over contours

- Let $f: [a, b] -> CC$, $f = u + i v$, then $ integral_a^b f(t) dif t = integral_a^b u(t) dif t + i integral_a^b v(t) dif t $
- Let $f_1, f_2: [a, b] -> CC$, $c in CC$, then $ integral_a^b (f_1(t) + f_2(t)) dif t = integral_a^b f_1(t) dif t + integral_a^b f_2(t) dif t, quad integral_a^b c f_1(t) dif t = c integral_a^b f_1(t) dif t $
- Curve $gamma: [a, b] -> CC$ is $C^1$ if *continuously differentiable* (derivative exists and is continuous).
- *Integral of continuous $f: U -> CC$ along curve $gamma: [a, b] -> U$, $gamma in C^1$*: $ integral_gamma f(z) dif z := integral_a^b f(gamma(t)) gamma'(t) dif t $
- Let $f_1, f_2: [a, b] -> CC$, $c in CC$, then $ integral_gamma (f_1(z) + f_2(z)) dif z = integral_gamma f_1(z) dif z + integral_gamma f_2(z) dif z, quad integral_gamma c f_1(z) dif z = c integral_gamma f_1(z) dif z $
- $(-gamma): [-b, -a] -> CC$, $(-gamma)(t) := gamma(-t)$, then $ integral_(-gamma) f(z) dif z = - integral_gamma f(z) dif z $
- Let $phi: [a', b'] -> [a, b]$ be continuously differentiable, $phi(a') = a$, $phi(b') = b$, $delta: [a', b'] -> CC$, $delta = gamma compose phi$. Then $ integral_gamma f(z) dif z = integral_delta f(z) dif z $
- Let $gamma: [a, b] -> CC$, $a = a_0 < a_1 < dots.h.c < a_n = b$, $gamma_i: [a_(i - 1), a_i] -> CC$ be $C^1$, $gamma_i(t) := gamma(t)$ for $t in [a_(i - 1), a_i]$. Then $gamma$ is *piecewise $C^1$ curve*, or *contour*. $ integral_gamma f(z) dif z = sum_(i = 1)^n integral_gamma_i f(z) dif z $ is a *contour integral*.
- *Contour union*: let $gamma: [a, b] -> CC$, $delta: [c, d] -> CC$, then $ (gamma union delta): [a, b + d - c] -> CC, quad (gamma union delta)(t) := cases(
	gamma(t) & "if" t in [a, b],
	delta(t + c - b) & "if" t in [b, b + d - c]
) $ Then $ integral_(gamma union delta) f(z) dif z = integral_gamma f(z) dif z + integral_delta f(z) dif z $
- *Complex Fundamental Theorem of Calculus (FTC)* Let $U subset.eq CC$ open, $F: U -> CC$ holomorphic with derivative $f$, $gamma: [a, b] -> U$ contour. Then $ integral_gamma f(z) dif z = F(gamma(b)) - F(gamma(a)) $ So if $gamma$ closed, then $integral_gamma f(z) dif z = 0$. Also, if $gamma_1$ and $gamma_2$ have same endpoints, then $ integral_(gamma_1) f(z) dif z = integral_(gamma_2) f(z) dif z $
- If $F' = f$, $F$ is *antiderivative* or *primitive* of $f$.
- *Length* of contour $gamma$: $ L(gamma) := integral_a^b |gamma'(t)| dif t $
- *Estimation lemma*: Let $f: U -> CC$ continuous, $gamma: [a, b] -> U$ contour. Then $ |integral_gamma f(z) dif z| <= L(gamma) dot.op sup_gamma |f| $ where $sup_gamma |f| := sup{|f(z)|: z in gamma}$
- *Converse to FTC*: Let $D$ domain, $f: D -> CC$ continuous, $integral_gamma f(z) dif z = 0$ for every closed contour $gamma in D$. Then exists holomorphic antiderivative $F: D -> CC$ (unique up to addition of constant) such that $ F'(z) = f(z) $
- Domain $D$ *starlike* if for some $a_0 in D$, for every $a_0 != b in D$, straight line from $a_0$ to $b$ contained in $D$.
- *Cauchy's theorem for starlike domains*: let $D$ starlike domain, $f: D -> CC$ holomorphic, $gamma in D$ closed contour. Then $ integral_gamma f(z) dif z = 0 $ Same holds if $f$ holomorphic on $D - S$, $S$ finite set of points, and $f$ continuous on $D$.
- Let $U$ open, $f: U -> C$ holomorphic, $Delta in U$ be triangle. Then $ integral_(diff Delta) f(z) dif z = 0 $ Same holds if $f$ holomorphic on $U - S$, $S$ finite set of points, and $f$ continuous on $U$.
- By default, always use *anti-clockwise* parameterisation of contour.
- Let $D$ starlike domain, $f: D -> CC$ continuous, $integral_(diff Delta) f(z) dif z = 0$ for every triangle $Delta in D$. Then exists holomorphic $F: D -> CC$ such that $F' = f$.
- *Cauchy's integral formula (CIF)*: let $B = B_r(a)$, $f: B -> CC$ holomorphic. Then for every $w in B, rho$ such that $|w - a| < rho < r$, $ f(w) = 1/(2 pi i) integral_(|z - a| = rho) f(z) / (z - w) dif z $

= Features of holomorphic functions

- *Cauchy-Taylor theorem*: let $U subset.eq CC$ open, $f: U -> CC$ holomorphic, $r > 0$, $B_r(a) subset U$. Then $f$ is given by power series (*Taylor series of $f$ around $a$*) that converges on $B_r(a)$: $ f(z) = sum_(n = 0)^oo c_n (z - a)^n, quad z in B_r(a) $ where $ c_n = 1 / (2 pi i) integral_(|z - a| = rho) f(z) / ((z - a)^(n + 1)) dif z $ for any $0 < rho < r$.
- Function with Taylor series expansion on $B_r(a)$, $r > 0$, is *analytic at $a$*.
- Function *analytic* if analytic at every point in domain.
- Holomorphic $<==>$ analytic.
- *Cauchy's integral formula (CIF) for derivatives*: let $B = B_r(a)$, $f: B -> CC$ holomorphic. For every $0 < rho < r$, $ integral_(|z - a| = rho) f(z) / ((z - a)^(n + 1)) dif z = (2 pi i) / (n!) f^((n))(a) $
- So $f$ has Taylor series expansion on $B_r(a)$: $ f(z) = sum_(n = 0)^oo (f^((n))(a)) / (n!) (z - a)^n $
- Equivalent of Cauchy-Taylor doesn't hold for real analysis, e.g. $ f(x) = cases(
	e^(-1/x) & "if" x > 0,
	0 & "if" x <= 0
) $ has derivatives of all orders and $f^((n))(0) = 0$. But Taylor series around $x = 0$ would be $ f(x) = sum_(n = 0)^oo c_n x^n, quad x in (0 - epsilon, 0 + epsilon) $ for some $epsilon > 0$. But then $c_n = f^((n)) / (n!) = 0$ but $f$ isn't identically zero in any neighbourhood of the origin. So $f$ doesn't have a Taylor series.
- *Holomorphic functions have infinitely many derivatives*: let $U subset.eq CC$ open, $f: U -> CC$ holomorphic. Then $f$ has derivatives of all orders on $U$ which are all holomorphic.
- *Morera's theorem*: let $D$ domain, $f: D -> CC$ continuous. If for every closed contour $gamma$ in $D$, $ integral_gamma f(z) dif z = 0 $ then $f$ holomorphic.
- $f: CC -> CC$ *entire* if holomorphic on $CC$.
- $f: CC -> CC$ *bounded* if for some $M > 0$, $|f(z)| <= M$ for every $z in CC$.
- *Liouville's theorem*: every bounded entire function is constant.
- *Fundamental theorem of algebra*: every non-constant polynomial with complex coefficients has complex root.
- *Local maximum modulus principle*: let $f: B_r(a) -> CC$ holomorphic. If $ forall z in B_r(a), |f(z)| <= |f(a)| $ then $f$ constant on $B_r(a)$.
- *Maximum modulus principle*: let $D$ domain, $f: D -> CC$ holomorphic. If for some $a in D$, $ forall z in D, |f(z)| <= |f(a)| $ then $f$ constant on $D$.
- If $U subset CC$ path-connected and open, then not possible to write $U = U_1 union U_2$, where $U_1, U_2$ disjoint, open, non-empty. So domains are connected.
- $f: B_r(a) -> CC$ has *zero of order $m$ at $a$* if for some $m > 0$, exists holomorphic $h: B_r(a) -> CC$ such that $f(z) = (z - a)^m h(z)$, $h(a) != 0$.
- $f$ has zero of order $m$ at $a$ iff $ f(a) = f^((1))(a) = dots.h.c = f^((m - 1))(a) = 0 $ and $f^((m))(a) != 0$.
- *Principle of isolated zeros*: let $f: B_r(a) -> CC$ holomorphic, $f != 0$. Then for some $0 < rho <= r$, $ forall z in B_rho(a) - {a}, quad f(z) != 0 $ Holds for $f(a) = 0$, i.e. zeros of holomorphic functions are isolated.
- *Uniqueness of analytic continuation theorem*: let $D' subset D$ non-empty domains, $f: D' -> CC$ holomorphic. Then exists at most one holomorphic $g: D -> CC$ such that $ forall z in D', quad f(z) = g(z) $ If $g$ exists, it is *analytic continuation of $f$ to $D$*.
- Let $D$ domain, $f, g: D -> CC$ holomorphic, $B_r(a) subset D$. If $f(z) = g(z)$ on $B_r(a)$ then $f(z) = g(z)$ on $D$.
- Let $S subset C$, $w in S$.
	- $w$ *isolated point of $S$* if for some $epsilon > 0$, $B_epsilon(w) sect S = {w}$.
	- $w$ *non-isolated point of $S$* if $forall epsilon > 0$, exists $w != z in S$ such that $z in B_epsilon(w)$.
- *Identity theorem*: Let $f, g: D -> CC$ holomorphic on domain $D$. If $S := {z in D: f(z) = g(z)}$ contains non-isolated point, then $f(z) = g(z)$ on $D$.
- Let $D subset.eq CC$ domain, $u: D -> RR$ *harmonic* if has continuous second order partial derivatives and satisfies *Laplace's equation*: $ u_(x x) + u_(y y) = 0 $
- Let $f = u + i v: D -> CC$ holomorphic on domain $D$. Then $u$ and $v$ harmonic.
- *Existence of harmonic conjugates theorem*: let $D$ starlike domain, $u: D -> RR$ harmonic. Then exists harmonic $v: D -> RR$ such that $f = u + i v$ holomorphic on $D$. $v$ is *harmonic conjugate of $u$*, unique up to addition of real constant. *Note*: condition of $D$ being starlike is removed when Cauchy's theorem is proved in generality.
- Let $f: D -> CC$ holomorphic on domain $D$. Then $f$ has holomorphic antiderivative on $D$.
- *Dirichlet problem*: let $D subset.eq CC$ domain with closure $overline(D)$, boundary $diff D$, $g: diff D -> RR$ continuous. Find continuous $mu: overline(D) -> RR$ such that $mu$ harmonic on $D$ and $mu = g$ on $diff D$.
- Let $f = u + i v: D -> CC$ holomorphic on domain $D$, $mu$ harmonic on $f(D)$. Then $tilde(mu) := mu compose f$ harmonic on $D$.
- So if $mu$ harmonic on $D'$ and want to find a harmonic $tilde(mu)$ on $D$, find holomorphic $f$ mapping $D$ to $D'$ so $f(D) = D'$. Then $tilde(mu) = mu compose f$ is solution.

= General form of Cauchy's theorem and C.I.F.

- Let curve $gamma: [a, b] -> CC$, $gamma(t) = w + r(t) e^(i theta(t))$, $w in CC$, $r, theta: [a, b] -> RR$, piecewise $C^1$, $r(t) > 0$. *Winding number (index)* of $gamma$ around $w$ is $ I(gamma; w) := (theta(b) - theta(a)) / (2 pi) $
- Let contour $gamma: [a, b] -> CC$, $w in CC$, $w in.not gamma$. Then exists $r, theta: [a, b] -> RR$ piecewise $C^1$, $r(t) > 0$ such that $ gamma(t) = w + r(t) e^(i theta(t)) $. Here, $r(t) = |gamma(t) - w|$.
- Let $gamma: [a, b] -> CC$ closed contour, $w in.not gamma$. Then $ I(gamma; w) = 1/(2 pi i) integral_gamma 1/(z - w) dif z $
- Let $D$ starlike domain, $gamma$ closed contour in $D$. If $w in.not D$, then $I(gamma; w) = 0$.
- Let $U subset.eq CC$ open.
	- Closed contour $gamma$ in $U$ *homologous to zero in $U$* if $I(gamma; w) = 0$ for every $w in.not U$.
	- $U$ is *simply connected* if every closed contour in $U$ homologous to zero in $U$.
- *Cycle*: finite collection of closed contours in $U$, denoted as formal sum $ Gamma := gamma_1 + dots.h.c + gamma_n $ $w$ *does not lie in $Gamma$* if $w in.not gamma_i$ for all $i$. Define $ I(Gamma; w) := sum_(i = 1)^n I(gamma_i; w) $ and $ integral_Gamma f(z) dif z := sum_(i = 1)^n integral_(gamma_i) f(z) dif z $ $Gamma$ *homologous to zero in $U$* if $I(Gamma; w) = 0$ for every $w in.not U$.
- Closed curve $gamma: [a, b] -> CC$ *simple* if for any $t_1 < t_2$, $gamma(t_1) = gamma(t_2) ==> t_1 = a "and" t_2 = b$ (no self-crossing or backtracking).
- *Jordan curve theorem*: Let $gamma$ closed curve. Then $CC - gamma$ is disjoint union of two domains, exactly one of which is bounded. Bounded domain is *interior* of $gamma$, $D_gamma^"int"$. Unbounded domain is *exterior*, $D_gamma^"ext"$. $w$ lies inside $gamma$ if $w in D_gamma^"int"$ and outside $gamma$ if $w in D_gamma^"ext"$.
- Let $gamma$ simple closed contour. Then possible to put orientation on $gamma$ such that $forall w in CC - gamma$, $ I(gamma; w) = cases(
	1 & "if" w in D_gamma^"int",
	0 & "if" w in D_gamma^"ext",
) $ Then $gamma$ is *positively oriented* (interior always on left of curve - anticlockwise).
- Let $D$ domain, $f: D -> CC$ holomorphic, $Gamma$ cycle in $D$, homologous to zero in $D$.
	- *General form of Cauchy's theorem*: $ integral_Gamma f(z) dif z = 0 $
	- *General form of CIF*: $ forall w in D - Gamma, quad integral_Gamma f(z) / (z - w) dif z = 2 pi i I(Gamma; w) f(w) $
- For simple closed curve $gamma$, $f$ holomorphic on $D_gamma^"int" union gamma$ if exists domain $D$ such that $D_gamma^"int" union gamma subset D$ and $f$ holomorphic on $D$.
- Let $gamma$ simple closed, positively oriented contour and $f$ holomorphic on $D_gamma^"int" union gamma$.
	- *Cauchy's theorem for simple closed contours*: $ integral_gamma f(z) dif z = 0 $
	- *CIF for simple closed contours*: $ forall w in D_gamma^"int", quad integral_gamma f(z) / (z - w) dif z = 2 pi i f(w) $

= Holomorphic functions on punctured domains

- *Laurent series*: $ sum_(n = -oo)^oo c_n (z - a)^n $ *Principal part*: $sum_(n = -oo)^(-1) c_n (z - a)^n$. *Analytic part*: $sum_(n = 0)^oo c_n (z - a)^n$.
- Laurent series converges at $z$ iff principal and analytic parts converge at $z$.
- *Annulus centre $a$, internal/external radii $r$ and $R$*: $ A_(r, R)(a) := {z in CC: r < |z - a| < R} $
- If Laurent series isn't power series ($c_n != 0$ for some $n < 0$) then either:
	- It never converges or
	- Exists $0 <= r < R <= oo$ such that it converges on $A_(r, R)(a)$ and diverges for $|z - a| < r$ or $|z - a| > R$. $A_(r, R)(a)$ is *annulus of convergence*.
- If Laurent series has annulus of convergence $A_(r, R)(a)$ then it converges uniformly on any $A_(rho_1, rho_2)$ with $r < rho_1 < rho_2 < R$. So it converges locally uniformly on $A_(r, R)(a)$ so represents holomorphic function on $A_(r, R)(a)$.
- If Laurent series has annulus of convergence containing $A_(r, R)(a)$, then $c_n$ are unique and given by, for any $rho in (r, R)$ $ c_n = 1/(2 pi i) integral_(|z - a| = rho) f(z) / (z - a)^(n + 1) dif z $ So Laurent series in $A_(r, R)(a)$ unique.
- *Holomorphic functions on annuli have Laurent series*: let $f: A_(r, R)(a) -> CC$ holomorphic, then exist unique $c_n in CC$ such that $ forall z in A_(r, R)(a), quad f(z) = sum_(n = -oo)^oo c_n (z - a)^n $ and annulus of convergence of Laurent series contains $A_(r, R)(a)$. Series is *Laurent series of $f$ on $A$*.
- *Punctured ball*: $B_R^*(a) := B_R(a) - {a} = A_(0, R)(a)$.
- If $f$ holomorphic on $B_R^*(a)$, $f$ has *isolated singularity* at $a$.
- Types of isolated singularity:
	- $f$ has *removable singularity* at $z = a$ if $c_n = 0$ for all $n <= -1$ (principal part is zero).
	- $f$ has *pole of order $k$* at $z = a$ if $c_(-k) != 0$ and $c_n = 0$ for all $n < -k$.
	- $f$ has *essential singularity* at $z = a$ if exist infinitely many $n < 0$ such that $c_n != 0$.
- $f: B_R^*(a) -> CC$ has removable singularity at $z = a$ iff $f$ extends to holomorphic function on $B_R(a)$ ($f$ has analytic continuation to $B_R(a)$).
- Let $f: B_R^*(a) -> CC$ holomorphic, $R > 0$. Then $f$ has removable singularity at $z = a$ iff $ lim_(z -> a) (z - a) f(z) = 0 $
- *Riemann extension theorem*: Let $f: B_R^*(a) -> CC$ holomorphic and bounded, then $f$ has removable singularity at $z = a$.
- Let $f: B_R^*(a) -> CC$ holomorphic. The following are equivalent:
	- $f$ has pole of order $k$ at $z = a$.
	- $f(z) = (z - a)^(-k) g(z)$, $g: B_R(a) -> CC$ holomorphic, $g(a) != 0$.
	- Exists $0 < r <= R$ and $h: B_r(a) -> CC$ holomorphic with zero of order $k$ at $z = a$ such that $f(z) = 1 \/ h(z)$ for $z in B_r^*(a)$.
- Let $f: B_R^*(a) -> CC$ holomorphic. Then $f$ has pole at $z = a$ iff $ lim_(z -> a) |f(z)| = oo $
- *Casorati-Weierstrass theorem*: let $f: B_R^*(a) -> CC$ holomorphic with essential singularity at $z = a$. Then $ forall w in CC, forall 0 < r < R, forall epsilon > 0, exists z in B_r^*(a), quad f(z) in B_epsilon(w) $
- *Big Picard theorem*: let $f: B_R^*(a) -> CC$ holomorphic with essential singularity at $z = a$. Then for some $b in CC$, $ forall 0 < r < R, quad CC - {b} subset.eq f(B_r^*(a)) $

= Cauchy's residue theorem

- $f$ *meromorphic* on domain $D$ if $f$ holomorphic on $D - S$, $S subset D$ has no non-isolated points and $f$ has pole at every $s in S$.
- $f$ meromorphic on $D_gamma^"int" union gamma$ if exists domain $D$ containing $D_gamma^"in" union gamma$ and $f$ meromorphic on $D$.
- Let $f$ meromorphic on domain $D$ with pole at $a$, with Laurent series $ f(z) = sum_(n = -k)^oo c_n (z - a)^n $ *Residue of $f$ at $a$* is $ "Res"_(z = a)(f) := c_(-1) $
- *Cauchy's residue theorem*: Let $f$ meromorphic on $D_gamma^"int" union gamma$, $gamma$ positively oriented simple closed contour, $f$ has no poles on $gamma$ and finite number of poles inside $gamma$, ${a_1, ..., a_m}$. Then $ integral_gamma f(z) dif z = 2 pi i sum_(j = 1)^m "Res"_(z = a_j)(f) $
- *Simple pole*: pole of order $1$.
- *Rules for calculating residues*:
	- *Linear combinations*: $"Res"_(z = a) (A f + B g) = A "Res"_(z = a)(f) + B "Res"_(z = a)(g)$.
	- *Cover up rule for poles of order $1$*: if $z = a$ is pole of order $1$, $ "Res"_(z = a)(f) = lim_(z -> a) (z - a) f(z) $
	- *Simple zero on denominator*: if $f(z) = g(z) \/ h(z)$, $g, h$ holomorphic at $a$, $g(a) != 0$, $z = a$ is zero of order $1$ of $h$, then $ "Res"_(z = a)(f) = g(a) / (h'(a)) $
	- *Poles of higher orders*: if $f(z) = g(z) \/ (z - a)^k$, $k > 0$, $g$ holomorphic at $a$, then $ "Res"_(z = a)(f) = (g^((k - 1))(a)) / ((k - 1)!) $
- To calculate $ integral_0^(2 pi) F(sin(theta), cos(theta)) dif theta $ where $F$ is rational function, use change of variable $z = e^(i theta)$, and use $ integral_0^(2 pi) F(sin(theta), cos(theta)) dif theta = integral_(|z| = 1) F((z - z^(-1)) / (2 i), (z + z^(-1)) / 2) (dif z) / (i z) $
- To calculate $ lim_(R -> oo) integral_(-R)^R p(x) / q(x) dif x $ where $deg(q) >= deg(p) + 2$ and $q$ has no real roots, integrate $f(z) = p(z) \/ q(z)$ over $gamma_R = L_R union C_R$ where $R$ greater than maximum modulus of roots of $q$. Use e.g. Estimation Lemma or Jordan's lemma to show $lim_(R -> oo) integral_(C_R) f(z) dif z = 0$.
- $ integral_(-oo)^oo f(x) dif x = lim_(r -> oo) integral_(0)^r f(x) dif x + lim_(s -> oo) integral_(-s)^0 f(x) dif x $
- *Cauchy principal value* of $integral_(-oo)^oo f(x) dif x$: $ P.V. integral_(-oo)^oo f(x) dif x = lim_(r -> oo) integral_(-r)^r f(x) dif x $
- If $f$ even, $P.V. integral_(-oo)^oo f(x) dif x = integral_(-oo)^oo f(x) dif x$
- *Jordan's lemma*: let $f$ holomorphic on $D = {z in CC: |z| > r}$ for some $r > 0$, $z f(z)$ bounded on $D$. Then for every $alpha > 0$, $ lim_(R -> oo) integral_(C_R) f(z) e^(i alpha z) dif z = 0 $ where $C_R = R e^(i theta), theta in [0, pi]$.
- To calculate $ P.V. integral_(-oo)^oo f(x) sin(alpha x) dif x quad "or" quad P.V. integral_(-oo)^oo f(x) cos(alpha x) dif x $ where $f$ meromorphic in $CC$ with no real poles and $f$ satisfies Jordan's lemma, calculate integral $ integral_(gamma_R) f(z) e^(i alpha z) dif z $ with CRT, where $gamma_R = L_R union C_R$. Then use $ integral_(L_R) f(z) e^(i alpha z) dif z = integral_(-R)^R f(x) cos(alpha x) dif x + i integral_(-R)^R f(x) sin(alpha x) dif x $ and equate real/imaginary parts. Use Jordan's lemma to show $lim_(R -> oo) integral_(C_R) f(z) e^(i alpha z) dif z = 0$.
- *Indentation lemma*: Let $g$ meromorphic on $CC$ with simple pole at $0$, $C_epsilon(theta) = epsilon e^(i theta), theta in [0, pi]$. Then $ lim_(epsilon -> 0) integral_(C_epsilon) g(z) dif z = pi i "Res"_(z = 0)(g) $
- To calculate $ integral_(-oo)^oo f(x) dif x $ where $f$ has simple pole at $z = 0$, let $gamma_(rho, R) = L_2 union (-C_rho) union L_1 union C_R$ where $L_2$ is line from $-R$ to $-rho$, $L_1$ is line from $rho$ to $R$. Take $rho -> 0$ and $R -> oo$, use indentation lemma and Jordan's lemma. *Note*: may have to choose appropriate branch cut so that $f$ holomorphic on $D$.
- Let $f$ meromorphic with zero or pole order $k > 0$ at $a$. Then $f' \/ f$ has simple pole at $a$ and $ "Res"_(z = a)(f' \/ f) = cases(
	k & "if f has zero at" z = a,
	-k & "if f has pole at" z = a
) $
- *Argument principle*: let $gamma$ positively oriented simple closed contour, $f$ meromorphic on $D_gamma^"int" union gamma$, $f$ has no zeros or poles on $gamma$, $Z_f$ be number of zeros of $f$ in $D_gamma^"int"$ (counted with multiplicity), $P_f$ be number of poles of $f$ in $D_gamma^"int"$ (counted with multiplicity). Then $ 1/(2 pi i) integral_gamma (f'(z)) / f(z) dif z = Z_f - P_f = I(Gamma_f; 0), quad Gamma_f = f compose gamma $ (Counted with multiplicity means zero/pole of order $k$ counts $k$ times).
- *Rouche's theorem*: let $gamma$ simple closed contour, $f, g$ holomorphic on $D_gamma^"int" union gamma$, with $ forall z in gamma, |f(z) - g(z)| < |g(z)| $ Then $f$ and $g$ have same number of zeros (counted with multiplcity) inside $gamma$.
- *Open mapping theorem*: let $f$ holomorphic, non-constant on domain $D$. Then if $U subset D$ open, $f(U)$ is open.