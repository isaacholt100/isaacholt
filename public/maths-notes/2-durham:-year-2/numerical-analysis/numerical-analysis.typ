#import "../../template.typ": template
#show: template

= Floating-point arithmetic

- *Fixed point representation*: $ x = plus.minus (d_1 d_2 ... d_(k-1) . d_k ... d_n)_beta $
- *Floating-point representation*: $ x = (0.d_1...d_(k-1)) beta^(d_k...d_n - B) $ where $B$ is an *exponent bias*.
- If $d_1 != 0$ then the floating point system is *normalised* and each float has a unique representation.
- *binary64*: stored as $ s e_10...e_0 d_1...d_52 $ where $s$ is the *sign* ($0$ for positive, $1$ for negative), $e_10...e_0$ is the *exponent*, and $d_1...d_52$ is the *mantissa*. The bias is $1023$. The number represented is $ cases(
	(-1)^s (1.d_1...d_52)_2 2^(e - 1023) "if" e != 0 "or" 2047,
	(-1)^s (0.d_1...d_52)_2 2^(-1022) "if" e = 0
) $ where $e = (e_10...e_0)_2$ $e = 2047$ is used to store $"NaN", plus.minus infinity$. The first case $e != 0$ is a *normal* representation, the $e = 0$ case is a *subnormal representation*.
- Floating-point numbers have *finite precision*: exists $epsilon_M > 0$ such that $"fl"(x) = "fl"((1 + epsilon) x)$ for all $epsilon < epsilon_M$.
- Floating-point numbers have *finite range*: exists $m_"max"$ and $m_"min"$ such that $"fl"$ defined only when $m_"min" <= |x| <= m_"max"$.
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
- $ |("fl"_"chop"(x) - x) / x| <= beta^(-k + 1), quad |(tilde("fl")_"round"(x) - x) / x| <= 1/2 beta^(-k + 1) $
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
- If $g in C^2$, then with fixed point iteration, $ |x_(n + 1) - x_*| / |x_n - x_*| -> |g'(x_*)| "as" n -> oo $ so $x_n -> x_*$ superlinearly if $g'(x_*) = 0$ and linearly otherwise.
- If $g in C^N$, fixed point iteration converges with order $N > 1$ iff $ g'(x_*) = dots.h.c = g^((N - 1))(x_*) = 0, quad g^((N))(x_*) != 0 $
- *Newton-Raphson*: fixed point iteration with $g(x) = x - f(x) \/ f'(x)$ $ x_(n + 1) = x_n - f(x_n) / (f'(x_n)) $
- For Newton-Raphson, $g'(x_*) = 0$ so quadratic convergence.
- Can use Newton-Raphson to solve $1 \/ x - b = 0$: $ x_(n + 1) = x_n - (1 \/ x_n - b) / (-1 \/ x_n^2) = x_n (2 - b x_n) $
- *Newton-Raphson in $d$ dimensions*: $ underline(x)_(n + 1) = underline(x)_n - (D f)^(-1) (underline(x)_n) underline(f)(underline(x)_n) $ where $D f$ is *Jacobian*.
- *Secant method*: approximate $f'(x_n) approx (f(x_n) - f(x_(n - 1))) / (x_n - x_(n - 1))$ with Newton-Raphson: $ x_(n + 1) = x_n - (x_n - x_(n - 1)) / (f(x_n) - f(x_(n - 1))) f(x_n) $ If $f'(x_*) != 0$, order is $(1 + sqrt(5)) \/ 2$.

= Numerical differentiation

- *Taylor expansion*: $ f(x plus.minus h) = f(x) plus.minus h f'(x) + h^2 / (2!) f''(x) plus.minus h^3 / (3!) f'''(x) + dots.h.c $
- *Forward difference approximation*: $ f'(x) = (f(x + h) - f(x)) / h - h/2 f''(xi), quad xi in "conv"{x, x + h} $ with $h > 0$.
- *Backward difference approximation*: forward difference but with $h < 0$.
- *Centred difference approximation*: $ f'(x) = (f(x + h) - f(x - h)) / (2h) - h^2 / 12 (f'''(xi_-) + f'''(xi_+)), quad xi_(plus.minus) in [x - h, x + h] $
- *Richardson extrapolation*: for approximation of $R(x; 0)$ of the form $ R(x; h) = R^((1))(x; h) = R(x; 0) + a_1(x) h + a_2(x) h^2 + a_3(x) h^3 + dots.h.c $ we have $ R^((1))(x; h \/ 2) = R(x; 0) + a_1(x) h/2 + a_2(x) h^2/4 + a_3(x) h^3 / 8 + dots.h.c $ This gives *second order approximation*: $ R^((2))(x; h) = 2 R^((1))(x; h \/ 2) - R^((1))(x; h) = R(x; 0) - a_2(x) h^2/2 + dots.h.c $ Similarly, $ R^((3))(x; h) = (4 R^((2))(x; h \/ 2) - R^((2))(x; h)) / 3 = R(x; 0) + tilde(a)_3 (x) h^3 + dots.h.c $ is *third order approximation*. Generally, $ R^((n + 1))(x; h) = (2^n R^((n))(x; h \/ 2) - R^((n))(x; h)) / (2^n - 1) = R(x; 0) + O(h^(n + 1)) $

= Linear systems

- $A$ *symmetric* if $A^T = A$.
- *Hermitian conjugate*: $(A^*)_(i j) = overline(A_(j i))$. $A$ *Hermitian* if $A^* = A$.
- $A$ *non-singular* iff $forall b in K^n$, exists solution $x in K^n$ to $A x = b$ ($K = RR$ or $CC$).
- If $A$ non-singular, exists exactly one solution $x$ to $A x = b$ and unique $A^(-1)$ such that $forall b in K^n$, $x = A^(-1) b$.
- $A$ non-singular iff $det(A) != 0$.
- $A$ *positive-definite* iff $x dot.op A x > 0$ $forall x != 0$.
- $A$ *positive-semidefinite* iff $x dot.op A x >= 0$ $forall x in K^n$.
- $L$ *lower-triangular* iff $L_(i j) = 0$ for $i < j$.
- $U$ *upper-triangular* iff $U_(i j) = 0$ for $i > j$.
- Can solve $L x = b$ by *forward substitution*: for $j = 1, ..., n$: $ x_j = (b_j - sum_(k = 1)^(j - 1) L_(j k) x_k) / (L_(j j)) $
- Can solve $U x = b$ by *backward substitution*: for $j = n, ..., 1$: $ x_j = (b_j - sum_(k = j + 1)^n U_(j k) x_k) / (U_(j j)) $
- If $A$ not upper/lower triangular, use *Gaussian elimination* to reduce $A$ to upper triangular $U$ using addition of multiple of row to another row. If leading element in current row is zero, swap with row below.
- *Gaussian elimination with row pivoting*: at $s$th stage of Gaussian elimination, if largest element in $s$th column is in row $j$, swap row $j$ and row $s$, then proceeed as usual. This gives more accurate results.
- For operation count, assume each arithmetic operation takes one *flop*.
- When asked about *order* of operation count, include *constant multiple* as well as highest power of $n$.
- *$L U$ decomposition*: write $A = L U$, then solve $L y = b$, then $U x = y$ with backward/forward substitution. Better when solving with multiple $b$.
- *Frobenius matrix of index $s$*: diagonal elements are $1$, other elements zero except for $s$th colum below main diagonal.
- Any Frobenius matrix can be written $ F_(i j)^((s)) = delta_(i j) - f_i^((s)) e_j^((s)) $ where $e^((s))$ is $s$th unit vector, $f^((s)) = (0, ..., 0, f_(s + 1)^((s)), ..., f_n^((s)))$ or $ F^((s)) = I - f^((s)) times.circle e^((s)) $ where $(v times.circle w)_(i j) = v_i w_j$ is tensor product.
- Inverse of Frobenius matrix is Frobenius matrix of same index: $ G^((s)) = I + f^((s)) times.circle e^((s)) $
- $G^((1)) dots.h.c G^((s)) = I + sum_(r = 1)^s f^((r)) times.circle e^((r))$
- If $A$ can be transform to upper triangular $U$ by Gaussian eliminiation without pivoting, then exists lower triangular $L$ such that $A = L U$. $L$ given by $ L_(i i) = 1, quad L_(i s) = A_(i s)^((s - 1)) \/ A_(s s)^((s - 1)) $ where $A^((s - 1))$ is matrix at $(s - 1)$th stage of Gaussian elimination ($A^0 = A$ is initial matrix).
- Any non-singular $A$ can be written as $P A = L U$ where $L$ is *permutation (pivot) matrix* (each row and column has exactly one $1$ and all other elements are $0$).
- *Norm* of vector space $V$: map $norm(dot.op): V -> RR$ with:
	- *Triangle inequality*: $norm(x + y) <= norm(x) + norm(y)$.
	- *Linearity*: $norm(alpha x) = |a| norm(x)$.
	- *Positivity*: $norm(x) >= 0$ and $norm(x) = 0 ==> x = 0$.
- *Seminorm* $|[x]|$: norm except non-zero vectors with $|[x]| = 0$.
- *$l_p$ norm*: for $p >= 1$, $ norm(x)_p := (sum_(i = 1)^n |x_i|^p)^(1 \/ p) $
- *$l_oo$ norm*: $ norm(x)_oo := max_i |x_i| $
- Matrix *row-sum norm*: $ norm(A)_"row" := max_(i = 1, ..., n) sum_(j = 1)^n |A_(i j)| $
- Matrix *column-sum norm*: $ norm(A)_"col" := max_(j = 1, ..., n) sum_(i = 1)^n |A_(i j)| $
- *Frobenius norm*: $ norm(A)_"Fro" := (sum_(i, j = 1)^n |A_(i j)|^2)^(1 \/ 2) $
- For $n$ dimensional vector space $V$, $"Hom"(V)$ is vector space of $n times n$ matrices.
- Given norm $norm(dot.op)$ on $V$, *induced norm* on $"Hom"(V)$ is $ norm(A) := sup_(x != 0) norm(A x) / norm(x) = max_(norm(x) = 1) norm(A x) $
- Properties of induced norm:
	- $norm(A x) <= norm(A) norm(x)$, $x in V$, $A in "Hom"(V)$.
	- $norm(A B) <= norm(A) norm(B)$, $A, B in "Hom"(V)$.
- *Spectral radius* of matrix: $ rho(A) := max{|lambda|: lambda "eigenvalue of" A} $
- We have these equalities:
	- $norm(A)_1 = norm(A)_"col"$.
	- $norm(A)_2 = max{sqrt(|lambda|): lambda "eigenvalue of" A^T A} = rho(A^T A)^(1 \/ 2) = rho(A A^T)^(1 \/ 2) $
	- $norm(A)_oo = norm(A)_"row"$.
- *Condition number* of $A$ with respect to norm $norm(dot.op)_*$: $ kappa_*(A) := norm(A^(-1))_* norm(A)_* $
- For $A (x + delta x) = b + delta b$, $ norm(delta x)_* / norm(x)_* <= kappa_*(A) norm(delta b)_* / norm(b)_* $
- If $norm(B) < 1$ for any submultiplicative matrix norm $norm(dot.op)$, $ B^k -> 0 quad "as" k -> oo $ Also, $ B^k -> 0 quad "as" k -> oo <==> rho(B) < 1 $
- *Richardson's method for lineary systems*: $A x = b$ so $x = x + w(b - A x)$ for some $w$. So iterate $ x^((k + 1)) = x^((k)) + w(b - A x^((k))) $ *Residual*: $ r^((k)) := x^((k)) - x$ satisfies $ r^((k + 1)) = (I - w A) r^((k)) ==> r^((k)) = (I - w A)^k r^((0)) $ So iteration converges iff $(I - w A)^k -> 0 <==> rho(I - w A) < 1$
- *Jacobi's method*: split $A$ into $A = D - E - F$, $D$ diagonal, $E$ strictly lower triangular, $F$ strictly upper triangular. Rewrite $A x = b$ as $D x = (E + F) x + b$, and iterate $ x^((k + 1)) = D^(-1) ((E + F) x^((k)) + b) $ Residual satisfies $r^((k + 1)) = D^(-1) (E + F) r^((k))$ so iteration converges iff $(D^(-1) (E + F))^k -> 0$. Converges if $A$ *strictly diagonally dominant* ($|a_(i i)| > sum_(j != i) |a_(i j)|$ for all $i$).
- *Gauss-Seidel method*: iterate $ (D - E) x^((k + 1)) = F x^((k)) + b $ Residual satisfies $r^((k + 1)) = (D - E)^(-1) F r^((k))$. Converges if $A$ strictly diagonally dominant.

= $L^2$ approximations and orthogonal polynomials

- *Inner product over vector space $V$*: map $(dot.op, dot.op): V times V -> CC$ satisfying:
	- $(alpha u + beta u', v) = alpha (u, v) + beta (u', v)$.
	- $(u, v) = overline((v\, u))$.
	- $(u, u) >= 0$ and $(u, u) = 0 <==> u = 0$.
- For $V = C^0([a, b])$, define inner product $ (u, v)_(L^2_w (a, b)) := integral_a^b u(x) v(x) w(x) dif x $ where *weight function* $w(x) > 0$ except at finite set of points. $w(x) = 1$ if not specified.
- Inner product induces norm $norm(u) = sqrt((u, u))$.
- Let $V$ inner product space, $X$ linear subspace of $V$. Then the $tilde(p) in X$ that minimises $ E(p) = norm(f - p)^2 $ satisfies $ forall p in X, (f - tilde(p), p) = 0 <==> (f, p) = (p, tilde(p)) <==> (f, phi_k) = (tilde(p), phi_k) quad forall k $ where $X$ spanned by ${phi_k}$. So if $tilde(p) = tilde(p)_0 phi_0 + dots.h.c + tilde(p)_K phi_K$ then $ (f, phi_k) = sum_j (phi_j, phi_k) tilde(p)_j $
- *Gram-Schmidt*: to construct orthogonal basis ${hat(phi)_k}$ from non-orthogonal basis ${phi_k}$:
	- $hat(phi)_0 = phi_0$.
	- $hat(phi)_k = phi_k - sum_(j = 0)^(k - 1) ((phi_k, hat(phi)_j)) / (norm(hat(phi)_j)^2) hat(phi)_j$ where norm is respect to given inner product.
- Properties of orthogonal basis:
	- Unique up to normalisation: if ${phi_j^*}$ is another orthogonal basis, then $phi_j^* = c_j hat(phi)_j$ for some constant $c_j$.
	- Has exactly $k$ simple roots in $(a, b)$.
- *Recurrence formula* to recursively calculate orthogonal basis: $ hat(phi)_(k + 1) = 1/norm(hat(phi)_k) x hat(phi)_k(x) - ((x hat(phi)_k, hat(phi)_k)) / (norm(hat(phi)_k)^3) hat(phi)_k(x) - norm(hat(phi)_k) / norm(hat(phi)_(k - 1)) hat(phi)_(k - 1)(x) $

= Numerical integration

- Want to approximate $ I(f) := integral_a^b f(x) w(x) dif x $ with *quadrature formula*: $ Q_n(x) = sum_(k = 0)^n hat(sigma)_k f(x_k) $ for *nodes* ${x_k}$ and *coefficients* ${hat(sigma)_k}$.
- $Q_n$ has *degree of exactness* $r$ if $Q_n(x^j) = I(x^j)$ for all $j <= r$, and $Q_n(x^(r + 1)) != I(x^(r + 1))$.
- By linearity, if $Q_n$ has degree of exactness $r$, then $Q_n(p) = I(p)$ for all $p in P_r$.
- *Interpolatory quadrature*: given nodes ${x_k}$, find $p$ that interpolates $f$ at nodes, $f(x_k) = p(x_k)$ and find integral of $p$. E.g. with Lagrange interpolation, $ I_n(f) := integral_a^b p(x) dif x = sum_(k = 0)^n f(x_k) integral_a^b L_k(x) $ Let $t = (x - a) \/ (b - a)$ then $ integral_a^b L_k(x) dif x = (b - a) integral_0^1 product_(l != k) (t - t_l) / (t_k - t_l) dif t =: (b - a) sigma_k $ so $ I_n(f) = (b - a) sum_(k = 0)^n sigma_k f(x_k) $
- Degree of exactness of $I_n$ is $n$.
- *Newton-Cotes* formula: interpolatory quadrature with equidistant nodes.
- *Closed Newton-Cotes* formula: Newton-Cotes with $x_0 = a$ and $x_n = b$, so $t_k = k/n$.
- If nodes symmetric, $t_(n - k) = 1 - t_k$ then $sigma_(n - k) = sigma_k$.
- *Rectangle method*: $ I_0(f) = (b - a) f((a + b) / 2) $
- If $p$ interpolates $f$ at ${x_k} subset [a, b]$ then for all $x in [a, b]$, $ f(x) - p(x) = (omega_(n + 1)(x)) / ((n + 1)!) f^((n + 1))(xi) $ where $omega_(n + 1)(x) = (x - x_0) dots.h.c (x - x_n)$ and $xi in (a, b)$.
- Error bounded by $ |I(f) - I_n(f)| <= 1/((n + 1)!) max_(xi in [a, b]) |f^((n + 1))(xi)| integral_a^b |omega_(n + 1)(x)| dif x $
- *Composite quadrature*: divide $[a, b]$ into $m$ subintervals ${[x_(i - 1), x_i]}_(i = 1)^m$ of each length $h = (b - a)/m$ and apply interpolatory quadrature to each subinterval, then add each of these together.
- *Trapezium rule*: use composite with closed Newton-Cotes formula with $n = 1$: $I_1(f) = (b - a) (f(a) + f(b)) / 2$ to give $ C_(1, m)(f) = (b - a) / m (1/2 f(x_0) + f(x_1) + dots.h.c + f(x_(m - 1)) + 1/2 f(x_m)) $
- *Simpson's $1/3$ rule*: use composite with closed Newton-Cotes formula with $n = 2$: $I_2(f) = (b - a) (1/6 f(a) + 2/3 f((a + b) / 2) + 1/6 f(b))$ to give $ C_(2, m)(f) = (b - a) / m (1/6 f(x_0) + 2/3 f(x_(1/2)) + 1/3 f(x_1) + dots.h.c + 1/3 f(x_(m - 1)) + 2/3 f(x_(m - 1/2)) + 1/6 f(x_m)) $
- To compute error bounds for composite, add individual error bounds for each of the individual quadratures.
- *Gaussian* interpolatory formula $ G_n = sum_(k = 0)^n rho_k f(x_k) $ obtains highest degree of exactness $2n + 1$ iff nodes ${x_k}$ chosen so that $hat(p)(x) = (x - x_0) dots.h.c (x - x_n)$ satisfies $ forall p in P_n, quad (hat(p), p) = 0 $ ${x_k}$ must be roots of $phi_(n + 1) in P_(n + 1)$ where ${phi_j}$ are orthogonal polynomials with respect to inner product $(dot.op, dot.op)_(a, b, w)$ Then coefficients given by $ rho_k = integral_a^b product_(l != k) (x - x_l) / (x_k - x_l) w(x) dif x $ where $w$ is weight function.