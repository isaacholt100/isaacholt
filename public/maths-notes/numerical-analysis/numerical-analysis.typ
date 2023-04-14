#import "../template.typ": template
#show: template

= Floating-point arithmetic

- *Fixed point representation*: $ x = plus.minus (d_1 d_2 ... d_(k-1) . d_k ... d_n)_beta $
- *Floating-point representation*: $ x = (0.d_1...d_(k-1)) beta^(d_k...d_n - B) $ where $B$ is an *exponent bias*.
- If $d_1 != 0$ then the floating point system is *normalised* and each float has a unique representation.
- *binary64*: stored as $ s e_10...e_0 d_1...d_52 $ where $s$ is the *sign* ($0$ for positive, $1$ for negative), $e_10...e_0$ is the *exponent*, and $d_1...d_52$ is the *mantissa*. The bias is $1023$. The number represented is $ cases(
	(-1)^s (1.d_1...d_52)_2 2^e "if" e != 0 "or" 2047,
	(-1)^s (0.d_1...d_52)_2 2^(-1022) "if" e = 0
) $ where $e = (e_10...e_0)_2$ $e = 2047$ is used to store $"NaN", plus.minus infinity$. The first case $e != 0$ is a *normal* representation, the $e = 0$ case is a *subnormal representation*.
- Floating-point numbers have finite range and precision.
- *Underflow*: where floating point calculation result is smaller than smallest representable float. Result is set to zero.
- *Overflow*: where floating point calculation result is larger than largest representable float. *Floating-point exception* is raised.
- *Machine epsilon $epsilon_M$*: difference between smallest representable number greater than $1$ and $1$. $epsilon_M = beta^(-k+1)$.
- $"fl"(x)$ maps real numbers to floats.
- *Chopping*: rounds towards zero. Given $x = (0.d_1...d_k d_(k + 1)...)_beta dot.op beta^e$, if the float has $k$ mantissa digits, then $ "fl"_"chop"(x) = (0.d_1...d_k) dot.op beta^e $
- *Rounding*: rounds to nearest. Given $x = (0.d_1...d_k d_(k + 1)...)_beta dot.op beta^e$, if the float has $k$ mantissa digits, then $ tilde("fl")_"round"(x) = cases(
	(0.d_1...d_k)_beta dot.op beta^e & "if" rho < 1/2,
	((0.d_1...d_k)_beta + beta^(-k)) dot.op beta^e & "if" rho >= 1/2
) $ where $rho = (0.d_(k + 1)...)$.
- *Relative rounding error*: $ epsilon_x = ("fl"(x) - x) / x <==> "fl"(x) = x(1 + epsilon_x) $
- $ |("fl"_"chop" - x) / x| <= beta^(-k + 1), quad |(tilde("fl")_"round"(x) - x) / x| <= 1/2 beta^(-k + 1) $
- *Round-to-nearest half-to-even*: fairer rounding than regular rounding for discrete values. In the case of a tie, round to nearest even integer: $ "fl"_"round"(x) = cases(
	(0.d_1...d_k)_beta dot.op beta^e & "if" rho < 1/2 "or" (rho = 1/2 "and" d_k "is even"),
	((0.d_1...d_k)_beta + beta^(-k)) dot.op beta^e & "if" rho > 1/2 "or" (rho = 1/2 "and" d_k "is odd")
) $
- $x plus.circle y = "fl"("fl"(x) + "fl"(y))$ and similarly for $times.circle$, $minus.circle$, $div.circle$.
- Relative error in $x plus.minus y$ can be large: $ "fl"(x) plus.minus "fl"(y) - (x plus.minus y) = x(1 + epsilon_x) plus.minus y(1 + epsilon_y) - (x plus.minus y) = x epsilon_x plus.minus y epsilon_y $ so relative error is $ (x epsilon_x plus.minus y epsilon_y) / (x plus.minus y) $
- In general, $x plus.circle (y plus.circle z) != (x plus.circle y) plus.circle z$
- For some computations, can avoid round-off errors (usually caused by subtraction of numbers close in value) e.g. instead of $ x = (-b + sqrt(b^2 - 4a c)) / (2 a) $ compute $ x = (-b + sqrt(b^2 - 4a c)) / (2 a) dot.op (-b - sqrt(b^2 - 4a c)) / (-b - sqrt(b^2 - 4a c)) = (-2c) / (b + sqrt(b^2 - 4a c)) $

= Polynomial Interpolation

- $cal(P)_n$ is set of polynomials of degree $<= n$.
- $"conv"{x_0, ..., x_n}$ is smallest closed interval containing ${x_0, ..., x_n}$.
- *Taylor's theorem*: for function $f$, if for $t in cal(P)_n$, $t^((j))(x_0) = f^((j))(x_0)$ for $j in {0, ..., n}$ then $ f(x) - t(x) = (f^((n + 1))(xi)) / ((n + 1)!) (x - x_0)^(n + 1) $ for some $xi in "conv"{x_0, x}$ (*Lagrange form of remainder*).
- *Polynomial interpolation*: given nodes ${x_j}_(j = 0)^n$ and function $f$, there exists unique $p in cal(P)_n$ such that $p$ interpolates $f$: $p(x_j) = f(x_j)$ for $j in {0, ..., n}$.
- *Cauchy's theorem*: let $p in P_n$ interpolate $f$ at ${x_j}^(j = 0)^n$, then $ forall x in "conv"{x_j}, f(x) - p(x) = (f^((n + 1))(xi)) / ((n + 1)!) (x - x_0) dots.h.c (x - x_n) quad "for some" xi in "conv"{x_j} $
- *Chebyshev polynomials*: $ T_n(x) = cos(n cos^(-1)(x)), quad x in [-1, 1] $
- $T_(n + 1)(x) = 2x T_n(x) - T_(n - 1)(x)$.
- Roots of $T_n(x)$ are $x_j = cos(pi(j + 1/2) \/ n)$ for $j in {0, ..., n - 1}$. Local extrema at $y_j = cos(j pi \/ n)$ for $j in {0, ..., n - 1}$.
- Let $omega_n(x) = (x - x_0) dots.h.c (x - x_n)$, ${x_j}_(j = 0)^n subset [-1, 1]$ (if ${x_j} subset.not [-1, 1]$ so interval is $[a, b]$, then we can map $x_j -> a + 1/2 (x_j + 1) (b - a)$). Then $sup_(x in [-1, 1]) |omega_n(x)|$ attains its min value iff ${x_j}$ are zeros of $T_(n + 1)(x)$. Also, $ 2^(-n) <= sup_(x in [-1, 1]) |omega_n(x)| < 2^(n + 1) $
- *Convergence theorem*: let $f in C^2([-1, 1])$, ${x_j}_(j = 0)^n$ be zeros of Chebyshev polynomial $T_(n + 1)(x)$ and $p_n in cal(P)_n$ interpolate $f$ at ${x_j}$. Then $ sup_(x in (-1, 1)) |f(x) - p_n(x)| -> 0 quad "as" n -> infinity $
- *Weierstrass' theorem*: let $f in C^0([a, b])$. $forall epsilon > 0$, exists polynomial $p$ such that $ sup_(x in (a, b)) |f(x) - p(x)| < epsilon $
- *Lagrange construction*: basis polynomials given by $ L_k(x) = product_(j != k) (x - x_j) / (x_k - x_j) $ satisfy $L_k(x_j) = delta_(j k)$. Then $ p(x) = sum_(k = 0)^n L_k(x) f(x_k) $ interpolates $f$ at ${x_j}$.
- *Note*: Lagrange construction not often used due to computational cost and as we have to recompute from scratch if ${x_j}$ is extended.
- *Divided difference operator*: $ [x_j] f & := f(x_j) \ [x_j, x_k] f & := ([x_j] f - [x_k] f) / (x_j - x_k), quad [x_k, x_k] f := lim_(y -> x_k) [x_k, y] = f'(x_k) \ [x_j, ..., x_k, y, z] f & := ([x_j, ..., x_k, y] f - [x_j, ..., x_k, z] f) / (y - z) $ These can be computed incrementally as new nodes are added.
- *Newton construction*: Interpolating polynomial $p$ is $ p(x) = [x_0] f & + (x - x_0) [x_0, x_1] f + (x - x_0)(x - x_1) [x_0, x_1, x_2] f \ & + dots.h.c + (x - x_0) dots.h.c (x - x_(n - 1)) [x_0, ..., x_n] f $
- *Hermite construction*: for nodes ${x_j}_(j = 0)^n$, exists unique $p_(2n + 1) in cal(P)_(2n + 1)$ that interpolates $f$ and $f'$ at ${x_j}$. Can be found using Newton construction, using nodes $(x_0, x_0, x_1, x_1, ..., x_n, x_n)$. Generally, if $p'(x_k) = f'(x_k)$ is needed, include $x_k$ twice. If $p^((n))(x_k) = f^((n))(x_k)$ is needed, include $x_k$ $n + 1$ times.
- If $y_0, ..., y_k$ is permutation of $x_0, ..., x_k$ then $[y_0, ..., y_k] f = [x_0, ..., x_k] f$.
- Interpolating error is $ f(x) - p(x) = (x - x_0) dots.h.c (x - x_n) [x_0, ..., x_n, x] f $ which gives $ [x_0, ..., x_(n - 1), x] f = (f^((n + 1))(xi)) / ((n + 1)!) $
- *Range reduction*: when computing a function e.g. $f(x) = arctan(x)$, $f(-x) = -f(x)$ and $f(1 \/ x) = pi / 2 - f(x)$ so only need to compute for $x in [0, 1]$.

= Root finding

- *Intermediate value theorem*: if $f$ continuous on $[a, b]$ and $f(a) < c < f(b)$ then exists $x in (a, b)$ such that $f(x) = c$.
- *Bisection*: let $f in C^0([a_n, b_n])$, $f(a_n) f(b_n) < 0$. Then set $m_n = (a_n + b_n) \/ 2$ and $ (a_(n + 1), b_(n + 1)) = cases(
	(m_n, b_n) "if" f(a_n) f(m_n) > 0,
	(a_n, m_n) "if" f(b_n) f(m_n) > 0
) $ Then:
	- $b_(n + 1) - a_(n + 1) = 1/2 (b_n - a_n)$.
	- By intermediate value theorem, exists $p_n in (a_n, b_n)$ with $f(p_n) = 0$.
	- $|p_n - m_n| <= 2^(-(n + 1)) (b_0 - a_0)$.
- *False position*: same as bisection except set $m_n$ as $x$ intercept of line from $(a_n, f(a_n))$ to $(b_n, f(b_n))$: $ m_n = b_n - f(b_n) / (f(b_n) - f(a_n)) (b_n - a_n) $
- Bisection and false position are *bracketing methods*. Always work but slow.
- *Fixed-point iteration*: rearrange $f(x_*) = 0$ to $x_* = g(x_*)$ then iterate $x_(n + 1) = g(x_n)$.
- $f$ is *Lipschitz continuous* if for some $L$, $ |f(x) - f(y)| <= L|x - y| $
- Space of Lipschitz functions on $X$ is $C^(0, 1)(X)$.
- Smallest such $L$ is *Lipschitz constant*.
- Every Lipschitz function is continuous.
- Lipschitz constant is bounded by derivative: $ sup_(x != y) |f(x) - f(y)| / |x - y| <= sup_x |f'(x)| $
- $f$ is *contraction* if Lipschitz constant $L < 1$.
- *Contraction mapping or Banach fixed point theorem*: if $g$ is a contraction and $g(X) subset X$ ($g$ maps $X$ to itself) then:
	- Exists unique solution $x_* in X$ to $g(x) = x$ and
	- The fixed point iteration method converges $x_n -> x_*$.
- *Local convergence theorem*: Let $g in C^1([a, b])$ have fixed point $x_* in (a, b)$ with $|g'(x_*)| < 1$. Then with $x_0$ sufficiently close to $x_*$, fixed point iteration method converges to $x_*$.
	- If $g'(x_*) > 0$, $x_n -> x_*$ monotonically.
	- If $g'(x_*) < 0$, $x_n - x_*$ alternates in sign.
	- If $|g'(x_*)| > 1$, iteration method almost always diverges.
- $x_n -> x_*$ with *order at least $alpha > 1$* if $ lim_(n -> oo) |x_(n + 1) - x_*| / |x_n - x_*|^alpha = lambda < oo $ If $alpha = 1$, then $lambda < 1$ is required.
- *Exact order of convergence* of $x_n -> x_*$: $ alpha := sup{beta: lim_(n -> oo) |x_(n + 1) - x_*| / |x_n - x_*|^beta < oo} $ Limit must be $< 1$ for $alpha = 1$.
- Convergence is *superlinear* if $alpha > 1$, *linear* if $alpha = 1$ and $lambda < 1$, *sublinear* otherwise.
- If $g in C^2$, then with fixed point iteration, $ |x_(n + 1) - x_*| / |x_n - x_*| -> |f'(x_*)| "as" n -> oo $ so $x_n -> x_*$ superlinearly if $g'(x_*) = 0$ and linearly otherwise.
- If $g in C^N$, fixed point iteration converges with order $N > 1$ iff $ g'(x_*) = dots.h.c = g^((N - 1))(x_*) = 0, quad g^((N))(x_*) != 0 $
- *Newton-Raphson*: fixed point iteration with $g(x) = x - f(x) \/ f'(x)$ $ x_(n + 1) = x_n - f(x_n) / (f'(x_n)) $
- For Newton-Raphson, $g'(x_*) = 0$ so quadratic convergence.
- Can use Newton-Raphson to solve $1 \/ x - b = 0$: $ x_(n + 1) = x_n - (1 \/ x_n - b) / (-1 \/ x_n^2) = x_n (2 - b x_n) $
- *Newton-Raphson in $d$ dimensions*: $ underline(x)_(n + 1) = underline(x)_n - (D f)^(-1) (underline(x)_n) underline(f)(underline(x)_n) $ where $D f$ is *Jacobian*.
- *Secant method*: approximate $f'(x_n) approx (f(x_n) - f(x_(n - 1))) / (x_n - x_(n - 1))$ with Newton-Raphson: $ x_(n + 1) = x_n - (x_n - x_(n - 1)) / (f(x_n) - f(x_(n - 1))) f(x_n) $

= Numerical differentiation

- *Taylor expansion*: $ f(x plus.minus h) = f(x) plus.minus h f'(x) + h^2 / (2!) f''(x) plus.minus h^3 / (3!) f'''(x) + dots.h.c $
- *Forward difference approximation*: $ f'(x) = (f(x + h) - f(x)) / h - h/2 f''(xi), quad xi in "conv"{x, x + h} $ with $h > 0$.
- *Backward difference approximation*: forward difference but with $h < 0$.
- *Centred difference approximation*: $ f'(x) = (f(x + h) - f(x - h)) / (2h) - h^2 / 12 (f'''(xi_-) + f'''(xi_+)), quad xi_(plus.minus) in [x - h, x + h] $
- *Richardson extrapolation*: for approximation of $R(x; 0)$ of the form $ R(x; h) = R^((1))(x; h) = R(x; 0) + a_1(x) h + a_2(x) h^2 + a_3(x) h^3 + dots.h.c $ we have $ R^((1))(x; h \/ 2) = R(x; 0) + a_1(x) h/2 + a_2(x) h^2/4 + a_3(x) h^3 / 8 + dots.h.c $ This gives *second order approximation*: $ R^((2))(x; h) = 2 R^((1))(x; h \/ 2) - R^((1))(x; h) = R(x; 0) - a_2(x) h^2/2 + dots.h.c $ Similarly, $ R^((3))(x; h) = (4 R^((2))(x; h \/ 2) - R^((2))(x; h)) / 3 = R(x; 0) + tilde(a)_3 (x) h^3 + dots.h.c $ is *third order approximation*. Generally, $ R^((n + 1))(x; h) = (2^n R^((n))(x; h \/ 2) - R^((n))(x; h)) / (2^n - 1) = R(x; 0) + O(h^(n + 1)) $