#import "../../template.typ": *
#let name-abbrvs = (:)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)
#set document(
    title: "Concentration Inequalities Notes",
    author: "Isaac Holt",
    keywords: ("concentration inequalities")
)
#let sim = sym.tilde
#let Bern = math.op("Bern")
#let Var = math.op("Var")
#let Geom = math.op("Geom")
#let Pois = math.op("Pois")

Question: toss a fair coin $n = 10000$ times. How many heads?

$X = sum_(i = 1)^n$, $X_i sim Bern(1 \/ 2)$. $EE[X] = 5000$. But $PP(X = 5000) = binom(10^4, 5000) dot 2^(-10^4) approx 0.008$.


By WLLN, $PP(X in [5000 - n epsilon, 5000 + n epsilon]) approx 1$.

#theorem("Central Limit Theorem")[
    Let $X_1, ..., X_n$ be IID RVs with mean $EE[X_1] = mu$. Let $Var(X_1) = sigma^2 < oo$. Then $1/(sigma sqrt(n)) sum_(i = 1)^n (X_i - mu) ->_D N(0, 1)$, i.e. $
        PP(1/(sigma sqrt(n)) sum_(i = 1)^n (X_i - mu) in A) -> integral_A 1/sqrt(2n) e^(-x^2 \/ 2) dif x
    $ for all $A$.
]
So $PP(X in [n/2 - sqrt(n)/2 Q^(-1) (delta), n/2 + sqrt(n)/2 Q^(-1) (delta)]) >= 1 - delta$, for $n$ large enough, where $Q(delta) = integral_delta^oo 1/sqrt(2n) e^(-x^2 \/ 2d) dif x$. We have $Q^(-1) (x) prop sqrt(log 1/x)$. So interval has length $prop sqrt(n) sqrt(log 1/delta)$.

#theorem("Chebyshev's Inequality")[
    $PP(abs(X - mu) >= epsilon) <= Var(X) / epsilon^2$ for all $epsilon > 0$.
]
#corollary[
    $PP(abs(sum_(i = 1)^n (X_i) - n/2) >= t) <= Var(sum_(i = 1)^n X_i)/t^2 = n sigma^2 / t^2 <= delta$ where $t = sqrt(n) sigma \/ sqrt(delta)$.
]
So $PP(X in [n/2 - , n/2]) >= 1 - delta$.

Question 2: we have $N$ coupons. Each day receive one uniformly at random independent of the past. How many days until all coupons received?

We have $X = sum_(i = 1)^n X_i$, $X_i sim Geom(i/n)$. $EE[X] = sum_i EE[X_i] approx n log n$ (verify this).

Question 3: Let $(X_1, ..., X_n), (Y_1, ..., Y_n)$ be IID. What is the longest common subsequence, i.e. $f(X_1, ..., X_n, Y_1, ..., Y_n) = max{k: exists i_1, ..., i_k, j_1, ..., j_k "s.t." X_(i_j) = Y_(i_j) med forall j in [k]}$. Computing $f$ is NP-hard. $f$ is smooth.

Principle: a smooth function of many independent random variables concentrates around its mean.

#theorem("Law of Total Expectation")[
    We have $EE_Y [EE_X [X | Y]] = EE_X [X]$.
]<thm:law-of-total-expectation>
#theorem("Tower Property of Conditional Expectation")[
    We have $EE[EE[Z | X, Y] | Y] = EE[Z | Y]$.
]<thm:tower-property-of-conditional-expectation>
#theorem[
    We have $EE[f(Y) X | Y] = f(Y) EE[X | Y]$.
]<thm:conditional-expectation-commutes-with-function-of-rv>
#theorem("Holder's Inequality")[
    Let $p >= 1$ and $1 \/ p + 1 \/ q = 1$. Then $
        EE[X Y] <= EE[abs(X)^p]^(1 \/ p) dot EE[abs(X)^q]^(1 \/ q).
    $
]<thm:holders-inequality>
#definition[
    The *conditional variance* of $Y$ given $X$ is the random variable $
        Var(Y | X) := EE[(Y - EE[Y | X])^2 | X].
    $
]

= The Chernoff-Cramer method

== The Chernoff bound and Cramer transform

#theorem("Weak Law of Large Numbers")[
    Let $X_1, ..., X_n$ be IID RVs with mean $EE[X_1] = mu$. Then, for all $epsilon > 0$, $
        PP(abs(1/n sum_(i = 1)^n X_i - mu) > epsilon) -> 0 quad "as" n -> oo.
    $
]<thm:wlln>
#theorem("Markov's Inequality")[
    Let $Y$ be a non-negative RV. For any $t >= 0$, $
        PP(Y >= t) <= EE[Y] / t.
    $
]<thm:markovs-inequality>
#proofhints[
    Split $Y$ using indicator variables.
]
#proof[
    We have $Y = Y dot II_({Y >= t}) + Y dot II_({Y < t}) >= t dot II_({Y >= t})$. Taking expectations gives the result.
]
#corollary[
    Let $phi: RR -> RR_+$ be non-decreasing, then $
        PP(Y >= t) <= PP(phi(Y) >= phi(t)) <= EE[phi(Y)]/phi(t).
    $ For $phi(t) = t^2$, we can use $Var(sum_(i = 1)^n X_i) = sum_(i = 1)^n Var(X_i)$.
]<crl:generalised-markovs-inequality>
#corollary("Chebyshev's Inequality")[
    For any RV $Y$ and $t > 0$, $
        PP(abs(Y - EE[Y]) >= t) <= Var(Y)/t^2.
    $
]<crl:chebyshevs-inequality>
#proofhints[
    Straightforward.
]
#proof[
    Take $Z = abs(Y - EE[Y])$ and use @crl:generalised-markovs-inequality with $phi(t) = t^2$.
]
#exercise[
    Prove WLLN, assuming that $Var(X_1) < oo$, using Chebyshev's inequality.
]
#remark[
    If higher moments exist, we can use them in a similar way: let $phi(t) = t^q$ for $q > 0$, then for all $t > 0$, $
        PP(abs(Z - EE[Z]) >= t) <= (EE[abs(Z - EE[Z])^q])/t^q.
    $ We can then optimise over $q$ to pick the lowest bound on $PP(abs(Z - EE[Z]) >= t)$. Note that @crl:chebyshevs-inequality is the most popular form of this bound due to the additivity of variance.
]
#definition[
    The *moment generating function (MGF)* of $F$ is $
        F(lambda) := EE[e^(lambda Z)] = sum_(k = 0)^oo (lambda^k EE[Z^k])/(k!).
    $
]<def:moment-generating-function>
#definition[
    The *log-MGF* of $Z$ is $psi_Z (lambda) = log F(lambda)$.
    
    Note that $psi_Z (lambda)$ is additive: if $Z = sum_(i = 1)^n Z_i$, with $Z_1, ..., Z_n$ independent, then $
        psi_(Z) (lambda) = log(EE[e^(lambda Z)]) = sum_(i = 1)^n log EE[e^(lambda Z_i)] = sum_(i = 1)^n psi_(Z_i) (lambda).
    $
]<def:log-mgf>
#definition[
    The *Cramer transform* of $Z$ is $
        psi_Z^* (t) = sup{lambda t - psi_Z (lambda): lambda > 0}.
    $
]<def:cramer-transform>
#proposition("Chernoff Bound")[
    Let $Z$ be an RV. For all $t > 0$, $
        PP(Z >= t) <= e^(-psi_Z^* (t)).
    $
]<prop:chernoff-bound>
#proof[
    By @crl:generalised-markovs-inequality, we have $
        PP(Z >= t) <= EE[e^(lambda Z)]/(e^(lambda t)) = e^(-(lambda t - psi_Z (lambda))).
    $ Taking the infimum over all $lambda > 0$ gives $PP(Z >= t) <= inf{e^(-(lambda t - psi_Z (lambda))): lambda > 0}$, which gives the result.
]
#remark[
    Our goal is to obtain an upper bound on $psi_Z (lambda)$, as this will give exponential concentration. The function $psi_(Z - EE[Z])(lambda)$ gives upper bounds on $PP(Z - EE[Z] >= t)$, the function $psi_(-Z + EE[Z])(lambda)$ gives upper bounds on $PP(Z - EE[Z] <= -t)$.
]
#proposition[
    + $psi_Z (lambda)$ is convex and infinitely differentiable on $(0, b)$, where $b = sup_(lambda > 0) {EE[e^(lambda Z)] < oo}$.
    + $psi_Z^* (t)$ is non-negative and convex.
    + If $t > EE[Z]$, then $psi_Z^* (t) = sup_(lambda in RR) {lambda t - psi_Z (lambda)}$, the *Fenchel-Legendre* dual.
]<prop:properties-of-log-mgf-and-cramer-transform>
#proofhints[
    + Differentiability proof omitted. For convexity, use @thm:holders-inequality.
    + Straightforward (note that each $t |-> lambda t - psi_Z (lambda)$ is linear).
    + Straightforward.
]
#proof[
    + $psi_Z (alpha lambda_1 + (1 - alpha) lambda_2) = log EE[e^(alpha lambda_1 Z) dot e^((1 - alpha) lambda_2 Z)] <= alpha log EE[e^(lambda_1 Z)] + (1 - alpha) log EE[e^(lambda_2 Z)]$ by Holder's inequality. The differentiability proof is omitted.
    + $lambda t - psi_Z (lambda)|_(lambda = 0) = 0$, so $psi_Z^* (t) >= 0$ by definition. Convexity follows since it is a supremum of linear functions.
    + By convexity and Jensen's inequality, $EE[e^(lambda Z)] >= e^(lambda EE[Z])$. So for $lambda < 0$, $lambda t - psi_Z (lambda) <= lambda (t - EE[Z]) < 0 = lambda t - psi_Z (lambda)|_(lambda = 0)$.
]
#example[
    Let $Z sim N(0, sigma^2)$. Then the MGF of $Z$ is $
        EE[e^(lambda Z)] & = integral_(-oo)^oo 1/sqrt(2 pi sigma^2) e^(-x^2 \/ 2 sigma^2) e^(lambda x) dif x \
        & = integral_(-oo)^oo 1/sqrt(2 pi sigma^2) e^(-(x^2 - 2 lambda sigma^2 x + lambda^2 sigma^4) \/ 2 sigma^2) e^(lambda^2 sigma^2 / 2) dif x \
        & = integral_(-oo)^oo 1/sqrt(2 pi sigma^2) e^(-(x - lambda sigma^2)^2 \/ 2 sigma^2) e^(lambda^2 sigma^2 / 2) dif x \
        & = e^(lambda^2 sigma^2 \/ 2).
    $ By @prop:properties-of-log-mgf-and-cramer-transform, for $t > 0 = EE[Z]$, the Cramer transform is $
        psi_Z^* (t) = sup_(lambda in RR) {lambda t - lambda^2 sigma^2 \/ 2} =: sup_(lambda in RR) g(lambda).
    $ We have $g' (lambda) = t - lambda sigma^2 = 0$ iff $lambda = t \/ sigma^2$. So $psi_Z^* (t) = t^2 \/ sigma^2 - sigma^2 t^2 \/ 2 sigma^4 = t^2 \/ 2 sigma^2$. So @prop:chernoff-bound gives $
        PP(Z >= t) <= e^(-t^2 \/ 2 sigma^2).
    $
]
#definition[
    Let $X$ be an RV with $EE[X] = 0$. $X$ is *sub-Gaussian* with variance parameter $nu$ if $
        psi_X (lambda) <= (lambda^2 nu)/2 quad forall lambda in RR.
    $ The set of all such variables is denoted $cal(G)(nu)$.
]<def:sub-gaussian>
#proposition[
    For any sub-Gaussian RV $X$,
    + If $X in cal(G)(nu)$, then $PP(X >= t), PP(X <= -t) <= e^(-t^2 \/ 2 nu)$ for all $t > 0$.
    + If $X_1, ..., X_n$ are independent with each $X_i in cal(G)(nu_i)$ then $sum_(i = 1)^n X_i in cal(G)(sum_(i = 1)^n nu_i)$.
    + If $X in cal(G)(nu)$, then $Var(X) <= nu$.
]<prop:properties-of-sub-gaussian-rv>
#proof[
    Exercise.
]
#definition[
    The *Gamma function* is defined as $
        Gamma(z) := integral_0^oo t^(z - 1) e^(-t) dif t.
    $
]
#theorem[
    Let $EE[X] = 0$. TFAE for suitable choices of $nu, b, c, d$:
    + $X in cal(G)(nu)$.
    + $PP(X >= t), PP(X <= -t) <= e^(-t^2 \/ 2b)$ for all $t > 0$.
    + $EE[X^(2q)] <= q! c^q$ for all $q >= NN$.
    + $EE[e^(d X^2)] <= 2$.
]<thm:equivalent-conditions-for-sub-gaussian-rv>
#proofhints[
    - $(1 => 2)$: straightforward.
    - $(2 => 3)$: Explain why we can assume $b = 1$. Use that $EE[Y] = integral_0^oo PP(Y > t) dif t$ for $Y >= 0$, and the $Gamma$ function.
    - $(3 => 1)$: show that $EE[e^(lambda X)] <= EE[e^(lambda(X - X'))]$ where $X'$ is an IID copy of $X$. Show that $EE\[(X - X')^(2q)\] <= EE[X^(2q)]$. Expand $EE[e^(lambda(X - X'))]$ as a series. Conclude that $X in cal(G)(4c)$.
    - $(3 <=> 4)$: exercise.
]
#proof[
    ($1 => 2$) instantly follows (with $b = nu$) by @prop:properties-of-sub-gaussian-rv.

    ($2 => 3$): WLOG, $b = 1$. Otherwise consider $tilde(X) = X \/ sqrt(b)$. Recall that for $Y >= 0$, $EE[Y] = integral_0^oo PP(Y > t) dif t$. Now $
        EE[X^(2q)] & = integral_0^oo PP(X^(2q) > t) dif t = integral_0^oo PP(abs(X) > t^(1 \/ 2q)) dif t \
        & <= 2 integral_0^oo e^(-t^(1 \/ q) \/ 2) dif t \
        & = 2 dot 2^q dot q integral_0^oo u^(q - 1) e^(-u) dif u \
        & = 2 dot 2^q dot q  dot Gamma(q) \
        & = 2^(q + 1) dot q! <= c^q q!
    $ for some constant $c$, where we use the substitution $t^(1 \/ q) \/ 2 = u$, so $t = (2u)^q$, so $dif t = 2^q q u^(q - 1) dif u$.

    ($3 => 1$): $EE[e^(-lambda X)] dot EE[e^(lambda X)] = EE[e^(lambda(X - X'))]$, where $X'$ is an IID copy of $X$. By Jensen's inequality, $EE[e^(-lambda X)] >= e^(-lambda EE[X]) = 1$. So $
        EE[e^(lambda X)] <= EE[e^(lambda(X - X'))] = sum_(q = 0)^oo (lambda^(2q) EE[(X - X')^(2q)])/(2q)!
    $ (we can ignore odd powers since $X - X'$ is a symmetric RV: $X - X'$ has the same distribution as $X' - X$). Now $
        EE\[(X - X')^(2q)\] = sum_(k = 0)^(2q) binom(2q, k) EE[X^k] EE[(X')^(2q - k)] <= sum_(k = 0)^(2q) binom(2q, k) EE[X^(2q)] = 2^(2q) dot EE[X^(2q)],
    $ by Holder's inequality with $p = 2q \/ k$ and $q = 2q \/ (2q - k)$ for each $k$. /*by pointwise Jensen and convexity of $x |-> x^(2q)$.*/ Thus, $
        EE[e^(lambda X)] & <= sum_(q = 0)^oo (lambda^(2q) EE[X^(2q)] dot 2^(2q))/(2q)! \
        & <= sum_(q = 0)^oo (lambda^(2q) c^q q! 2^(2q))/(2q)! \
        & <= sum_(q = 0)^oo (lambda^(2q) dot c^q 2^q)/(q!) = sum_(q = 0)^oo (lambda^2 dot 2c)^q / q! = e^(2 lambda^2 c),
    $ where we used that $(2q)! \/ q! = product_(j = 1)^q (q + 1)! >= 2^q dot q!$. Hence $psi_X (lambda) = 2 lambda^2 c = (lambda^2 dot 4c) / 2$, hence $X in cal(G)(4c)$.

    ($3 <=> 4$): exercise.
]

== Hoeffding's and related inequalities

#lemma("Hoeffding's Lemma")[
    Let $Y$ be a RV with $EE[Y] = 0$ and $Y in [a, b]$ almost surely. Then $psi''_Y (lambda) <= (b - a)^2 \/ 4$ and $Y in cal(G)((b - a)^2 \/ 4)$.
]<lem:hoeffding>
#proofhints[
    - Define a new distribution based on $lambda$, which should be obvious after expanding $psi'_Y (lambda)$.
    - To conclude the result, use a Taylor expansion at $0$ of $psi_Y (lambda)$.
]
#proof[
    Let $Y$ have distribution $P$. We have $
        psi'_Y (lambda) = (EE_(Y sim P)[Y e^(lambda Y)])/(EE_(Y sim P)[e^(lambda Y)]) = EE_(Y sim P)[Y dot e^(lambda Y)/EE[e^(lambda Y)]] = EE_(Y sim P_lambda) [Y],
    $ where if $P$ is discrete, then $P_lambda$ is the discrete distribution with PMF $
        P_lambda (y) = (e^(lambda y) P(y))/(sum_z P(z) e^(lambda z)),
    $ and if $P$ is continuous with PDF $f$, then $P_lambda$ is the continuous distribution with PDF $
        f_lambda (y) = (e^(lambda y) f(y))/(integral_(-oo)^oo f(z) e^(lambda z) dif z).
    $ Now $
        psi''_Y (lambda) & = (EE_(Y sim P)[Y^2 e^(lambda Y)] dot EE_(Y sim P)[e^(lambda Y)] - EE_(Y sim P)[Y e^(lambda Y)]^2)/(EE_(Y sim P)[e^(lambda Y)]^2) \
        & = EE_(Y sim P)[Y^2 e^(lambda Y)/(EE_(Y sim P)[e^(lambda Y)])] - EE[Y e^(lambda Y)/(EE_(Y sim P)[e^(lambda Y)])]^2 \
        & = EE_(Y sim P_lambda)[Y^2] - EE_(Y sim P_lambda)[Y]^2 = Var_(Y sim P_lambda)(Y).
    $ Note that if $Y in [a, b]$, then $abs(Y - (b - a)/2)^2 <= (b - a)^2 \/ 4$. So we have $
        Var_(Y sim P_lambda)(Y) = Var_(Y sim P_lambda)(Y - (b - a) \/ 2) <= EE_(Y sim P_lambda)[(Y - (b - a)/2)^2] <= (b - a)^2 / 4.
    $ Finally, using a Taylor expansion at $0$, we obtain $
        psi_Y (lambda) = psi_Y (0) + lambda'_Y (0) lambda + psi''_Y (xi) lambda^2 / 2 = psi''_Y (xi) lambda^2 / 2 <= lambda^2 (b - a)^2 / 8,
    $ for some $xi in [0, lambda]$, since $EE_(Y sim P)[Y] = EE_(Y sim P_0)[Y] = 0$.
]
#remark[
    The distribution $P_lambda$ in the above proof is called the *exponentially tilted* distribution.
]
#theorem("Hoeffding's Inequality")[
    Let $X_1, ..., X_n$ be independent RVs where each $X_i$ takes values in $[a_i, b_i]$. Then for all $t >= 0$, $
        PP(sum_(i = 1)^n (X_i - EE[X_i]) >= t) <= exp(-(2t^2) / (sum_(i = 1)^n (b_i - a_i)^2)).
    $
]<thm:hoeffdings-inequality>
#proofhints[
    Straightforward.
]
#proof[
    By @lem:hoeffding, $X_i - EE[X_i] in cal(G)((b_i - a_i^2) \/ 4)$ for all $i$. By @prop:properties-of-sub-gaussian-rv (part 2), we have $
        sum_(i = 1)^n (X_i - EE[X_i]) in cal(G)(1/4 sum_(i = 1)^n (b_i - a_i)^2).
    $ Hence, by @prop:properties-of-sub-gaussian-rv (part 1), we are done.
]
#remark[
    A drawback of @thm:hoeffdings-inequality is that the bound does not involve $Var(X_i)$ the variance could be much smaller than the upper bound of $(b_i - a_i)^2 \/ 4$. This is addressed by Bennett's inequality:
]
#theorem("Bennett's Inequality")[
    Let $X_1, ..., X_n$ be independent RVs with $EE[X_i] = 0$ and $abs(X_i) <= c$ for all $i$. Let $nu = Var(X_1) + dots.c + Var(X_n)$. Then for all $t >= 0$, $
        PP(sum_(i = 1)^n X_i >= t) <= exp(-nu / c^2 dot h_1 ((c t)/nu)),
    $ where $h_1 (x) = (1 + x) log(1 + x) - x$ for $x > 0$.
]<thm:bennetts-inequality>
#proofhints[
    - Show that $EE[e^(lambda X_i)] = 1 + Var(X_i)/c^2 (e^(lambda c) - lambda c - 1)$.
    - Deduce that $psi_(sum_i X_i) <= nu_c^2 (e^(lambda c) - lambda c - 1)$.
    - Find an upper lower for $psi_(sum_i X_i)^* (t)$.
]
#proof[
    Denote $sigma_i^2 = Var(X_i) = EE[X_i^2] - EE[X_i]^2 = EE[X_i]^2$. The MGF of $X_i$ is $
        EE[e^(lambda X_i)] & = sum_(k = 0)^oo lambda^k/k! EE[X_i^k] = 1 + sum_(k = 2)^oo lambda^k/k! EE[X_i^(k - 2) X_i^2] \
        & <= 1 + c^(k - 2) sum_(k = 2)^oo lambda^k/k! EE[X_i^2] = 1 + sigma_i^2 / c^2 sum_(k = 2)^oo (lambda^k c^k)/k! \
        & = 1 + sigma_i^2 / c^2 (sum_(k = 0)^oo (lambda^k c^k)/k! - lambda c - 1) \
        & = 1 + sigma_i^2 / c^2 (e^(lambda c) - lambda c - 1).
    $ So $psi_(X_i)(lambda) = log(1 + sigma_i^2 / c^2 (e^(lambda c) - lambda c - 1)) <= sigma_i^2 / c^2 (e^(lambda c) - lambda c - 1)$. So by additivity of $psi$, we have $
        psi_(sum_(i = 1)^n X_i)(lambda) <= nu / c^2 e^(lambda c) - nu/c^2 lambda c - nu / c^2.
    $ So for $t >= 0 = EE[sum_i X_i]$, by @prop:properties-of-log-mgf-and-cramer-transform, $
        psi_(sum_i X_i)^* (t) >= sup_(lambda in RR) {lambda t - nu / c^2 e^(lambda c) + nu / c lambda + nu / c^2} =: sup_(lambda in RR) {g(lambda)}
    $ We have $g'(lambda) = t - nu / c e^(lambda c) + nu / c$ which is $0$ iff $t + nu / c = nu / c e^(lambda c)$, i.e. iff $lambda = 1/c log(1 + t c / v) =: lambda^*$. So $
        psi_(sum X_i)^* (t) & >= 1/c t log (1 + (t c)/nu) - nu / c^2 (1 + (t c)/nu) + nu/c^2 log(1 + (t c)/nu) + nu / c^2 \
        & = nu/c^2 ((1 + (t c)/(nu)) log(1 + (t c)/nu) - (t c)/nu) \
        & = nu/c^2 h_1 ((t c)/nu).
    $ So we are done by the @prop:chernoff-bound.
]
#remark[
    We can show that $h_1 (x) >= x^2 / (2(x \/ 3 + 1))$ for $x >= 0$. So by @thm:bennetts-inequality, we obtain $
        PP(sum_(i = 1)^n X_i >= t) <= exp(-t^2 / (2(c t \/ 3 + nu))),
    $ which is *Bernstein's inequality*. If $nu >> c t$, then this yields a sub-Gaussian tail bound, and if $nu << c t$, then this yields an exponential bound. So Bernstein misses a log factor.
]
#remark[
    If $Z sim Pois(lambda)$, then $psi_(Z - nu)(lambda) = nu(e^lambda - lambda - 1)$.
]


= The variance method

== The Efron-Stein inequality

#notation[
    Denote $X^((i)) = (X_(1:(i - 1)), X_((i + 1):n))$ and for $i < j$, denote $X_(i:j) = (X_i, ..., X_j)$.
]
#notation[
    Denote $E_i Z = EE[Z | X_(1:i)]$, $E_0 Z = EE[Z]$, $E^((i)) = EE[Z | X^((i))]$, and $Var^((i))(Z) = Var(Z | X^((i)))$.
]
We want to study the concentration of $Z = f(X_1, ..., X_n)$ for independent $X_i$. If $Z = sum_i X_i$, then $Var(sum_i X_i) = sum_i Var(X_i)$ if $EE[X_i X_j] = 0$ for all $i != j$, which holds if the $X_i$ are independent.
#theorem("Efron-Stein Inequality")[
    Let $X_1, ..., X_n$ be independent and let $Z = f(X_1, ..., X_n)$. Then $
        Var(Z) <= sum_(i = 1)^n EE[(Z - E^((i)) Z)^2] = EE[sum_(i = 1)^n Var^((i))(Z)].
    $
]<thm:efron-stein-inequality>
#proofhints[
    - The @thm:law-of-total-expectation and @thm:tower-property-of-conditional-expectation will come in handy a lot...
    - Let $Delta_i = E_i Z - E_(i - 1) Z$. Show that $EE[Delta_i] = 0$.
    - Show that the $Delta_i$ are uncorrelated, i.e. $EE[Delta_i Delta_j] = EE[Delta_i] EE[Delta_j]$.
    - Show that $Delta_i = E_i (Z - E^((i)) Z)$.
]
#proof[
    Let $Delta_i = E_i Z - E_(i - 1) Z$. By the @thm:law-of-total-expectation, we have $
        EE[Delta_i] = EE[EE[Z | X_(1:i)]] - EE[EE[Z | X_(1:(i - 1))]] = EE[Z] - EE[Z] = 0.
    $ Also, note that $Z - EE[Z] = EE[Z | X_(1:n)] - EE[Z] = sum_(i = 1)^n Delta_i$. We claim that the $Delta_i$ are uncorrelated, i.e. $EE[Delta_i Delta_j] = EE[Delta_i] EE[Delta_j] = 0$ for $i != j$. Indeed, for $i < j$, by the @thm:law-of-total-expectation, we can write $
        EE[Delta_i Delta_j] = EE[EE[Delta_i Delta_j | X_(1:i)]] = EE[Delta_i EE[Delta_j | X_(1:i)]],
    $ since $Delta_i$ is a function of $X_(1:i)$. But $
        EE[Delta_j | X_(1: i)] & = EE(E_j Z - E_(j - 1) Z | X_(1:i)) \
        & = EE[EE[Z | X_(1:j)] | X_(1:i)] - EE[EE[Z | X_(1:(j - 1))] | X_(1:i)] \
        & = EE[Z | X_(1:i)] - EE[Z | X_(1:i)] = E_i Z - E_i Z = 0,
    $ where on the third line we used the @thm:tower-property-of-conditional-expectation. Hence, the $Delta_i$ are uncorrelated, which implies $
        Var(Z) = Var(Z - EE[Z]) = sum_(i = 1)^n Var(Delta_i) = sum_(i = 1)^n EE[Delta_i^2] - EE[Delta_i]^2 = sum_(i = 1)^n EE[Delta_i^2].
    $ Now $
        E_i (E^((i)) Z) & = EE[E^((i)) Z | X_(1:i)] \
        & = EE[E^((i)) Z | X_(1:(i - 1)), X_i] \
        & = EE[EE[Z | X^((i))] | X_(1:(i - 1))] \
        & = EE[Z | X_(1:(i - 1))] \
        & = E_(i - 1) Z,
    $ where on the third line we used that $X_i$ and $X^((i))$ are independent, and on the fourth line we used the @thm:tower-property-of-conditional-expectation. So we can rewrite $Delta_i = E_i Z - E_(i - 1) Z = E_i (Z - E^((i)) Z)$, and so by Jensen's inequality $
        Delta_i^2 & = (E_i (Z - E^((i)) Z))^2 = EE[Z - E^((i)) Z | X_(1:i)]^2 \
        & <= EE[(Z - E^((i)) Z)^2 | X_(1:i)] = E_i ((Z - E^((i)) Z)^2).
    $ Hence, by the @thm:law-of-total-expectation, $
        Var(Z) & = sum_(i = 1)^n EE[Delta_i^2] <= sum_(i = 1)^n EE[E_i ((Z - E^((i)) Z)^2)] \
        & = sum_(i = 1)^n EE[EE[(Z - E^((i)) Z)^2 | X_(1:i)]] = sum_(i = 1)^n EE[(Z - E^((i)) Z)^2].
    $ Finally, we have $EE[E^((i)) (Z - E^((i)) Z)^2] = EE[Var(Z | X^((i)))] = EE[Var^((i)) (Z)]$, which gives the equality in the theorem statement.
]
#theorem[
    Let $X_1, ..., X_n$ be independent and $f$ be square integrable. Let $Z = f(X_1, ..., X_n)$. Then $
        Var(Z) <= EE[sum_(i = 1)^n (Z - E^((i)) Z)^2] =: nu.
    $ Moreover, if $X'_1, ..., X'_n$ are IID copies of $X_1, ..., X_n$, and $Z'_i = f(X_(1:(i - 1)), X'_i, X_((i + 1):n))$, then $
        nu = 1/2 EE[sum_(i = 1)^n (Z - Z'_i)^2] = EE[sum_(i = 1)^n (Z - Z'_i)_+^2] = EE[sum_(i = 1)^n (Z - Z'_i)_-^2],
    $ where $X_+ = max{0, X}$ and $X_- = max{-X, 0}$. Moreover, $
        nu = sum_(i = 1)^n inf_(Z_i) EE[(Z - Z_i)^2],
    $ where the infimum is over all $X^((i))$-measurable and square-integrable RVs $Z_i$.
]
#proofhints[
    - First part is straightforward.
    - For second part, show that $Var^((i)) (Z) = 1/2 Var^((i))(Z - Z'_i)$.
    - For last part, use that $Var(X) = inf_a EE[(X - a)^2]$.
]
#proof[
    The first part follows instantly from the @thm:efron-stein-inequality by linearity of expectation. Now $Var(X) = 1/2 Var(X - Y)$, if $X$ and $Y$ are IID. Conditional on $X^((i))$, $Z$ and $Z'_i$ are independent. Hence, since $EE[Z] = EE[Z'_i]$, $
        Var^((i)) (Z) = 1/2 Var^((i))(Z - Z'_i) = 1/2 EE[(Z - Z'_i)^2].
    $ Thus we have $
        nu = 1/2 sum_(i = 1)^n EE[(Z - Z'_i)^2].
    $ Finally, recall that $Var(X) = inf_a EE[(X - a)^2]$, with equality if $a = EE[X]$. So $Var^((i))(Z) = inf_(Z_i) E^((i)) ((Z - Z_i)^2)$, with equality if $Z_i = E^((i)) Z$. Taking expectations and summing completes the proof.
]