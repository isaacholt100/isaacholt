#import "../../template.typ": *
#let name-abbrvs = (:)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs, slides-ref-hints: true)
#set document(
    title: "Concentration Inequalities Notes",
    author: "Isaac Holt",
    keywords: ("concentration inequalities")
)
#let sim = sym.tilde
#let Bern = math.op("Bern")
#let Ent = math.op("Ent")
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
]<thm:clt>
So $PP(X in [n/2 - sqrt(n)/2 Q^(-1) (delta), n/2 + sqrt(n)/2 Q^(-1) (delta)]) >= 1 - delta$, for $n$ large enough, where $Q(delta) = integral_delta^oo 1/sqrt(2n) e^(-x^2 \/ 2d) dif x$. We have $Q^(-1) (x) prop sqrt(log 1/x)$. So interval has length $prop sqrt(n) sqrt(log 1/delta)$.

#theorem("Chebyshev's Inequality")[
    $PP(abs(X - mu) >= epsilon) <= Var(X) / epsilon^2$ for all $epsilon > 0$.
]<thm:chebyshevs-inequality>
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
        EE[abs(X Y)] <= EE[abs(X)^p]^(1 \/ p) dot EE[abs(X)^q]^(1 \/ q).
    $
]<thm:holders-inequality>
#theorem("Cauchy-Schwarz")[
    A special case of Holder's inequality: $
        EE[abs(X Y)] <= EE[X^2]^(1 \/ 2) dot EE[Y^2]^(1 \/ 2).
    $
]<thm:cauchy-schwarz>
#definition[
    The *conditional variance* of $Y$ given $X$ is the random variable $
        Var(Y | X) := EE[(Y - EE[Y | X])^2 | X].
    $
]<def:conditional-variance>

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
#proofhints[
    Use @crl:generalised-markovs-inequality.
]
#proof[
    By @crl:generalised-markovs-inequality, we have $
        PP(Z >= t) <= EE[e^(lambda Z)]/(e^(lambda t)) = e^(-(lambda t - psi_Z (lambda))).
    $ Taking the infimum over all $lambda > 0$ gives $PP(Z >= t) <= inf{e^(-(lambda t - psi_Z (lambda))): lambda > 0}$, which gives the result.
]
#remark[
    Our goal is to obtain an upper bound on $psi_Z (lambda)$, as this will give exponential concentration. The function $psi_(Z - EE[Z])(lambda)$ gives upper bounds on $PP(Z - EE[Z] >= t)$, the function $psi_(-Z + EE[Z])(lambda)$ gives upper bounds on $PP(Z - EE[Z] <= -t)$.
]
#proposition[
    + $psi_Z (lambda)$ is convex and infinitely differentiable on $(0, b)$, where $b = sup{lambda > 0: psi_Z (lambda) < oo}$.
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
    $ So $psi_Z (lambda) = (lambda^2 sigma^2) / 2$. By @prop:properties-of-log-mgf-and-cramer-transform, for $t > 0 = EE[Z]$, the Cramer transform is $
        psi_Z^* (t) = sup_(lambda in RR) {lambda t - lambda^2 sigma^2 \/ 2} =: sup_(lambda in RR) g(lambda).
    $ We have $g' (lambda) = t - lambda sigma^2 = 0$ iff $lambda = t \/ sigma^2$. So $psi_Z^* (t) = t^2 \/ sigma^2 - sigma^2 t^2 \/ 2 sigma^4 = t^2 \/ 2 sigma^2$. So @prop:chernoff-bound gives $
        PP(Z >= t) <= e^(-t^2 \/ 2 sigma^2).
    $
]
#definition[
    Let $X$ be an RV with $EE[X] = 0$. $X$ is *sub-Gaussian* with variance parameter $nu$ if $
        psi_X (lambda) <= (lambda^2 nu)/2 quad forall lambda in RR,
    $ i.e. if its log MGF is less than that of a normally distributed random variable with mean $0$ and variance $nu$. The set of all such sub-Gaussian variables is denoted $cal(G)(nu)$.
]<def:sub-gaussian>
#proposition[
    For any sub-Gaussian RV $X$,
    + If $X in cal(G)(nu)$, then $PP(X >= t), PP(X <= -t) <= e^(-t^2 \/ 2 nu)$ for all $t > 0$.
    + If $X_1, ..., X_n$ are independent with each $X_i in cal(G)(nu_i)$ then $sum_(i = 1)^n X_i in cal(G)(sum_(i = 1)^n nu_i)$.
    + If $X in cal(G)(nu)$, then $Var(X) <= nu$. // *haven't proven this yet*
]<prop:properties-of-sub-gaussian-rv>
#proof[
    Exercise.
]
#definition[
    The *Gamma function* is defined as $
        Gamma(z) := integral_0^oo t^(z - 1) e^(-t) dif t.
    $
]<def:gamma-function>
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
    - $(3 => 1)$: show that $EE[e^(lambda X)] <= EE[e^(lambda(X - X'))]$ where $X'$ is an IID copy of $X$. Show that $EE\[(X - X')^(2q)\] <= 2^(2q) dot EE[X^(2q)]$. Expand $EE[e^(lambda(X - X'))]$ as a series. Conclude that $X in cal(G)(4c)$.
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
    - Show that $psi''_Y (lambda)$ is equal to the variance of this distribution, and obtain the upper bound on $psi''_Y (lambda)$ by using the shift-invariance of the variance.
    - To conclude the result, use a Taylor expansion at $0$ of $psi_Y (lambda)$.
]
#proof[
    Let $Y$ have distribution $P$. We have $
        psi'_Y (lambda) = (EE_(Y sim P)[Y e^(lambda Y)])/(EE_(Y sim P)[e^(lambda Y)]) = EE_(Y sim P)[Y dot e^(lambda Y)/EE[e^(lambda Y)]] = EE_(Y sim P_lambda) [Y],
    $ where if $P$ is discrete, then $P_lambda$ is the discrete distribution with PMF $
        P_lambda (y) = (e^(lambda y) P(y))/(sum_z P(z) e^(lambda z)) = (e^(lambda y) P(y))/EE[e^(lambda Y)],
    $ and if $P$ is continuous with PDF $f$, then $P_lambda$ is the continuous distribution with PDF $
        f_lambda (y) = (e^(lambda y) f(y))/(integral_(-oo)^oo f(z) e^(lambda z) dif z) = (e^(lambda y) f(y))/EE[e^(lambda Y)].
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
    A drawback of @thm:hoeffdings-inequality is that the bound does not involve $Var(X_i)$, and the variances could be much smaller than the upper bound of $(b_i - a_i)^2 \/ 4$. This is addressed by Bennett's inequality:
]
#theorem("Bennett's Inequality")[
    Let $X_1, ..., X_n$ be independent RVs with $EE[X_i] = 0$ and $abs(X_i) <= c$ for all $i$. Let $nu = Var(X_1) + dots.c + Var(X_n)$. Then for all $t >= 0$, $
        PP(sum_(i = 1)^n X_i >= t) <= exp(-nu / c^2 dot h_1 ((c t)/nu)),
    $ where $h_1 (x) = (1 + x) log(1 + x) - x$ for $x > 0$.
]<thm:bennetts-inequality>
#proofhints[
    - Show that $EE[e^(lambda X_i)] <= 1 + Var(X_i)/c^2 (e^(lambda c) - lambda c - 1)$.
    - Deduce that $psi_(sum_i X_i) <= nu/c^2 (e^(lambda c) - lambda c - 1)$.
    - Find a lower bound for $psi_(sum_i X_i)^* (t)$.
]
#proof[
    Denote $sigma_i^2 = Var(X_i) = EE[X_i^2] - EE[X_i]^2 = EE[X_i]^2$. The MGF of $X_i$ is $
        EE[e^(lambda X_i)] & = sum_(k = 0)^oo lambda^k/k! EE[X_i^k] = 1 + sum_(k = 2)^oo lambda^k/k! EE[X_i^(k - 2) X_i^2] \
        & <= 1 + c^(k - 2) sum_(k = 2)^oo lambda^k/k! EE[X_i^2] = 1 + sigma_i^2 / c^2 sum_(k = 2)^oo (lambda^k c^k)/k! \
        & = 1 + sigma_i^2 / c^2 (sum_(k = 0)^oo (lambda^k c^k)/k! - lambda c - 1) \
        & = 1 + sigma_i^2 / c^2 (e^(lambda c) - lambda c - 1).
    $ (We can apply the inequality since $EE[X_i^k] >= EE[X_i]^k = 0$ by Jensen's inequality.) So $psi_(X_i)(lambda) = log(1 + sigma_i^2 / c^2 (e^(lambda c) - lambda c - 1)) <= sigma_i^2 / c^2 (e^(lambda c) - lambda c - 1)$. So by additivity of $psi$, we have $
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
We want to study the concentration of $Z = f(X_1, ..., X_n)$ for independent $X_i$. If $Z = sum_i X_i$, then $Var(sum_i X_i) = sum_i Var(X_i)$ if $EE[X_i X_j] = EE[X_i] EE[X_j]$ for all $i != j$, which holds if the $X_i$ are independent.
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
#theorem("Efron-Stein Inequality")[
    Let $X_1, ..., X_n$ be independent and $f$ be square integrable. Let $Z = f(X_1, ..., X_n)$. Then $
        Var(Z) <= EE[sum_(i = 1)^n (Z - E^((i)) Z)^2] =: nu.
    $ Moreover, if $X'_1, ..., X'_n$ are IID copies of $X_1, ..., X_n$, and $Z'_i = f(X_(1:(i - 1)), X'_i, X_((i + 1):n))$, then $
        nu = 1/2 EE[sum_(i = 1)^n (Z - Z'_i)^2] = EE[sum_(i = 1)^n (Z - Z'_i)_+^2] = EE[sum_(i = 1)^n (Z - Z'_i)_-^2],
    $ where $X_+ = max{0, X}$ and $X_- = max{-X, 0}$. Moreover, $
        nu = sum_(i = 1)^n inf_(Z_i) EE[(Z - Z_i)^2],
    $ where the infimum is over all $X^((i))$-measurable and square-integrable RVs $Z_i$.
]<thm:efron-stein>
#proofhints[
    - First part is straightforward.
    - For second part, show that $Var^((i)) (Z) = 1/2 Var^((i))(Z - Z'_i)$.
    - For last part, use that $Var(X) = inf_a EE[(X - a)^2]$.
]
#proof[
    The first part follows instantly from the @thm:efron-stein-inequality by linearity of expectation. Now $Var(X) = 1/2 Var(X - Y)$, if $X$ and $Y$ are IID. Conditional on $X^((i))$, $Z$ and $Z'_i$ are independent. Hence, since $EE[Z] = EE[Z'_i]$, $
        Var^((i)) (Z) = 1/2 Var^((i))(Z - Z'_i) = 1/2 EE^((i))[(Z - Z'_i)^2].
    $ Thus we have $
        nu = 1/2 sum_(i = 1)^n EE[(Z - Z'_i)^2].
    $ The equality with $dot_+$ and $dot_-$ follows since $Z - Z'_i$ is a symmetric RV. Finally, recall that $Var(X) = inf_a EE[(X - a)^2]$, with equality if $a = EE[X]$. So $Var^((i))(Z) = inf_(Z_i) E^((i)) ((Z - Z_i)^2)$, with equality if $Z_i = E^((i)) Z$. Taking expectations and summing completes the proof.
]

== Functions with bounded differences

#definition[
    $f: A^n -> RR$ has the *bounded differences (b.d.)* property if $
        sup_((vd(x), x'_i) in A^(n + 1)) abs(f(x_(1:(i - 1)), x_i, x_((i + 1):n)) - f(x_(1:(i - 1)), x'_i, x_((i + 1):n))) <= c_i quad forall i in [n].
    $ So changing one of the coordinates changes the value of the function at most by a constant.
]<def:bounded-differences-property>
#corollary[
    Let $X_1, ..., X_n$ be independent and $Z = f(X_(1:n))$ have bounded differences with constants $c_i$. Then $Var(Z) <= 1/4 sum_(i = 1)^n c_i^2$.
]<crl:bound-on-variance-of-function-with-bounded-differences>
#proofhints[
    Consider the random variable $
        Z_i = 1/2 (sup_(x_i in A) f(X_(1:(i - 1)), x_i, X_((i + 1):n)) + inf_(x_i in A) f(X_(1:(i - 1)), x_i, X_((i + 1):n))).
    $
]
#proof[
    Define $
        Z_i = 1/2 (sup_(x_i in A) f(X_(1:(i - 1)), x_i, X_((i + 1):n)) + inf_(x_i in A) f(X_(1:(i - 1)), x_i, X_((i + 1):n)))
    $ $Z_i$ is a function of $X^((i))$. We have $abs(Z - Z_i) <= c_i \/ 2$. By the final part of the @thm:efron-stein, we have $Var(Z) <= sum_(i = 1)^n EE[(Z - Z_i)^2] <= 1/4 sum_(i = 1)^n c_i^2$.
]
#example("Bin packing")[
    Given $x_1, ..., x_n in [0, 1]$, what is the minimum number $k$ of bins $B_j$ into which $sum_(x in B_j) x <= 1$ for each $j = 1, ..., k$?

    Suppose $X_1, ..., X_n$ be independent and let $Z = f(X_(1:n))$ be the minimum number of bins. Note that changing any one $x_i$ changes $f$ by at most $1$, so $f$ has bounded differences with constants $c_i = 1$. So by the @thm:efron-stein, $Var(Z) <= 1/4 n$.

    Note that this bound is tight, e.g. when $X_i sim Bern(1 \/ 2)$, $Z sim B(n, 1 \/ 2)$, which has variance $n dot 1/2 dot 1/2$.
]
#example("Longest common sub-sequence")[
    Let $X_(1:n)$ and $Y_(1:n)$ be independent sequences of coin flips. Let $
        Z = f(X_(1:n), Y_(1:n)) = max{k: exists i_1 < dots.c < i_k, j_1 < dots.c < j_k "s.t." X_(i_ell) = Y_(i_ell) med forall ell in [k]}
    $ Note that changing any one coin flip changes $Z$ by at most $1$, so $f$ has bounded differences with constants $c_i = 1$, so by the @thm:efron-stein, $Var(Z) <= n \/ 2 = Theta(n)$. Since it is known that $EE[Z] = Theta(n)$, the deviations from the mean are small compared to the mean.
]
#example("Chromatic numbers of graphs")[
    Let $G$ be an *Erdos-Renyi random graph* with $n$ vertices, i.e. each ${i, j} in E(G)$ with probability $p$ (independently). The *chromatic number* $chi(G)$ of $G$ is the smallest number of colors on the vertices such that there are no two adjacent vertices with the same colour. For $i < j$, let $X_(i j) = bb(1)_{{i, j} in E}$. We have $
        chi(G) = f({X_(i j)}_(1 <= i < j <= n)),
    $ for some (complicated) function $f$. Since adding or removing an edge changes $chi(G)$ by at most $1$, $f$ has bounded differences with constants $c_(i j) = 1$. By @thm:efron-stein, $Var(Z) <= binom(n, 2) \/ 4 = Theta(n^2)$. It is known that $EE[chi(G)] approx n \/ log n$, so the bound on the variance is not useful when applying @crl:chebyshevs-inequality. However:

    Now for each $1 <= i <= n - 1$, let $Y^((i))$ be a random vector taking values in ${0, 1}^i$ where $Y_j^((i)) = bb(1)_{{i + 1, j} in E}$ for each $1 <= j <= i$. The $Y_i$ are independent. Also, note that ${Y^((i))}_(i = 1)^(n - 1)$ determines the graph. Hence, $chi(G) = g(Y^((1)), ..., Y^((n - 1)))$ for some (complicated) function $g$. $g$ has bounded differences with constants $1$ (e.g. by considering giving vertex $i + 1$ a new colour). Then by @thm:efron-stein, $Var(chi(G)) <= (n - 1) \/ 4$, which is a tighter bound. This yields a useful application of @crl:chebyshevs-inequality, which shows that $chi(G)$ is close to its mean value.
]


= Poincaré inequalities

Let $X_1, ..., X_n$ be real-valued random variables, and let $Z = f(X_1, ..., X_n)$. A Poincaré inequality is of the form $Var(Z) lt.tilde EE[norm(nabla f (X))^2]$. So we have a local property (smoothness) which gives a global property (bound on the variance).

#definition[
    Let $f: RR^d -> RR$ is *separately convex* if it is convex if all of its individual arguments.
]<def:separately-convex>
#theorem("Convex Poincaré Inequality")[
    Let $X_(1:n)$ be independent RVs supported on $[0, 1]$ and $f: RR^n -> RR$ be separately convex with partial derivatives that exist. Let $Z = f(X_(1:n))$. Then $
        Var(Z) <= EE[norm(nabla f (X_(1:n)))^2],
    $ where $norm(dot) = norm(dot)_2$ is the Euclidean norm.
]<thm:convex-Poincaré-inequality>
#proofhints[
    - Let $Z_i = inf_(x'_i) f(X_(1:(i - 1)), x'_i, X_((i + 1):n))$. Let $X'_i$ be the value for which the infimum is achieved (why is it achieved?).
    - Use that $abs(Z - Z_i)^2 <= abs(X_i - X'_i)^2 dot ((diff f) / (diff x_i) (X))^2$ (since $X'_i$ is a minimiser).
]
#proof[
    Let $Z_i = inf_(x'_i) f(X_(1:(i - 1)), x'_i, X_((i + 1):n))$. Let $X'_i$ be the value for which the infimum is achieved (since $f$ is continuous and the domain $[0, 1]^n$ we consider is compact). Denote $overline(X)^((i)) = (X_(1:(i - 1)), X'_i, X_((i + 1):n))$. Note that since $f$ is separately convex and $X'_i$ is a minimiser  (so $f(X'_((i))) <= f(X)$), $
        abs(Z - Z_i)^2 = abs(f(X_(1:n)) - f(overline(X)^((i))))^2 <= abs(X_i - X'_i)^2 dot ((diff f) / (diff x_i) (X_(1:n)))^2.
    $ By the @thm:efron-stein, $
        Var(Z) & <= sum_(i = 1)^n EE[(Z - Z_i)^2] \
        & <= sum_(i = 1)^n EE[(X_i - X'_i)^2 ((diff f) / (diff x_i) (X_(1:n)))^2] \
        & <= sum_(i = 1)^n EE[((diff f) / (diff x_i) (X_(1:n)))^2] = EE[norm(nabla f(X_(1:n)))^2].
    $
]
#example[
    Let $X in RR^(n times d)$ be a random matrix with $X_(i, j) in [-1, 1]$ independent. The spectral norm (or $ell_2$-operator norm) of $X$ is its largest singular value: $
        sigma_1 (X) = sup{norm(X u): u in RR^d, norm(u) = 1} = sup_(u in RR^n, norm(u) = 1) sup_(v in RR^d, norm(v) = 1) gen(u, X v).
    $ $sigma_1$ is convex (and so separately convex) since it is a supremum of linear functions. Since it is a norm, we have $sigma_1 (A + B) <= sigma_1 (A) + sigma_1 (B)$ and $sigma_1 (A - B) >= abs(sigma_1 (A) - sigma_1 (B))$. Fix $A$. Since $X$ ranges over a compact set, the supremum is achieved: let $u, v$ achieve the supremum. Then $
        sigma_1 (A) = gen(v, X u) & <= norm(v) dot norm(X u) quad "by Cauchy-Schwarz" \
        & <= norm(v) dot norm(u) (sum_(i, j) X_(i, j)^2)^(1 \/ 2) = (sum_(i, j) X_(i, j)^2)^(1 \/ 2) = norm(X)_F.
    $ Now if $X, X'$ are independent, $d(X, X') = norm(X - X')_F >= sigma_1 (X - X') >= abs(sigma_1 (X) - sigma_1 (X'))$ where $d$ is the Euclidean distance between vectorised $X$ and $X'$ (i.e. Frobenius norm). So $sigma_1$ is a $1$-Lipschitz function, and note that an $L$-lipchitz function satisfies $norm(nabla f) <= L$. So by the @thm:convex-Poincaré-inequality, $Var(sigma_1 (X)) <= 4$ (the RHS is $4$, not $1$, since $X_(i j)$ take values in $[-1, 1]$ instead of $[0, 1]$). Note that this is independent of the dimension of $X$!
]
#theorem("Gaussian Poincaré Inequality")[
    Let $X_(1:n)$ be IID and standard Gaussian (i.e. each $X_i sim N(0, 1)$). Then for any continuously differentiable $f in C^1 (RR^n)$, $
        Var(f(X_(1:n))) <= EE[norm(nabla f(X_(1:n)))^2].
    $
]<thm:gaussian-Poincaré-inequality>
#proofhints[
    - Show, using the @thm:efron-stein-inequality, that it is sufficient to prove the result for $n = 1$.
    - You may assume that $f in C^2 (RR)$ ($f$ is twice continuously differentiable) and has compact support.
    - Using the definition of conditional variance, show that $Var^((i))(f(S_n)) = 1/4 (f(S_n - epsilon_i / sqrt(n) + 1 / sqrt(n)) - f(S_n - epsilon_i / sqrt(n) - 1/sqrt(n)))^2$, where $S_n = 1/sqrt(n) sum_(i = 1)^n epsilon_i$ and $epsilon_i$ are IID Rademacher random variables (taking values in ${-1, 1}$ with equal probability).
    - Use Taylor's theorem to find an upper bound for $
        abs(f(S_n - epsilon_i / sqrt(n) + 1 / sqrt(n)) - f(S_n - epsilon_i / sqrt(n) - 1/sqrt(n)))
    $
    - Use @thm:efron-stein for $f(S_n)$ and the central limit theorem to conclude the result.
]
#proof[
    Assume the result holds for the $n = 1$ case, i.e. $Var(f(X)) <= EE[f'(X)^2]$ for $X sim N(0, 1)$. Then by the @thm:efron-stein and @thm:law-of-total-expectation, $
        Var(Z) & <= EE [sum_(i = 1)^n Var^((i)) (f(X_(1:n)))] \
        & <= EE[sum_(i = 1)^n EE[((diff f) / (diff x_i) (X_(1:n)))^2 | X^((i))]] \
        & = EE[sum_(i = 1)^n ((diff f) / (diff x_i) (X_(1:n)))^2] = EE[norm(nabla f (X_(1:n)))]^2.
    $ So it suffices to prove the result for $n = 1$: WLOG, assume $EE[norm(nabla f (X))^2] < oo$. Let $epsilon_i$ be IID Rademacher random variables (taking values in ${-1, 1}$ with equal probability). Consider $S_n = 1/sqrt(n) sum_(i = 1)^n epsilon_i$. It suffices to prove the case when $f in C^2 (RR)$ ($f$ is twice continuously differentiable) and has compact support. So $f'$ and $f''$ are bounded. By the @thm:efron-stein, $
        Var(f(S_n)) <= EE[sum_(i = 1)^n Var^((i))(S_n)].
    $ Note $Var^((i))$ here is conditional on $epsilon^((i))$. We have $S_n = S_n - epsilon_i \/ sqrt(n) plus.minus 1 \/ sqrt(n)$ with equal probabilities. Note that $S_n - epsilon_i \/ sqrt(n)$ is a function of $epsilon^((i))$. We have $
        EE^((i))[f(S_n)] = 1/2 f(S_n - epsilon_i \/ sqrt(n) + 1 \/ sqrt(n)) + 1/2 f(S_n - epsilon_i \/ sqrt(n) - 1 \/ sqrt(n))
    $ and so $
        Var^((i))(f(S_n)) & = 1/2 (f(S_n - epsilon_i \/ sqrt(n) + 1 \/ sqrt(n)) - (1/2 f(S_n - epsilon_i \/ sqrt(n) + 1 \/ sqrt(n)) + 1/2 f(S_n - epsilon_i \/ sqrt(n) - 1 \/ sqrt(n))))^2 \
        & + 1/2 (f(S_n - epsilon_i \/ sqrt(n) - 1 \/ sqrt(n)) - (1/2 f(S_n - epsilon_i \/ sqrt(n) + 1 \/ sqrt(n)) + 1/2 f(S_n - epsilon_i \/ sqrt(n) - 1 \/ sqrt(n))))^2 \
        & = 1/4 (f(S_n - epsilon_i \/ sqrt(n) + 1 \/ sqrt(n)) - f(S_n - epsilon_i \/ sqrt(n) - 1 \/ sqrt(n)))^2 \
    $ Let $K$ be an upper bound for $abs(f'')$. Then $
        & abs(f(S_n + (1 - epsilon_i) \/ sqrt(n)) - f(S_n - (1 + epsilon_i) \/ sqrt(n))) \
        & = abs(f(S_n) + (1 - epsilon_i) / sqrt(n) f'(S_n - epsilon_i \/ sqrt(n)) + (1 - epsilon_i)^2/(2n) f''(S_n - epsilon_i \/ sqrt(n) + xi_(i, m)) \
        & - f(S_n) + (1 + epsilon_i) / sqrt(n) f'(S_n - epsilon_i \/ sqrt(n)) - (1 + epsilon_i)^2/(2n) f''(S_n - epsilon_i \/ sqrt(n) + xi_(i, m)^((2)))) \
        & <= abs(2/sqrt(n) f'(S_n)) + 2 K \/ n.
    $ Thus, $Var^((i))(f(S_n)) <= (abs(f'(S_n) \/ sqrt(n)) + K \/ n)^2$. Hence, $
        Var(f(S_n)) <= EE[sum_(i = 1)^n (abs(f'(S_n) \/ sqrt(n)) + K \/ n)^2] = EE[f'(S_n)^2] + 2K / sqrt(n) EE[abs(f'(S_n))] + K^2 / n
    $ As $n -> oo$, $Var(f(S_n)) -> Var(X)$, $X sim N(0, 1)$ by the central limit theorem. Also, $EE[f'(S_n)^2] -> EE[f'(X)^2]$ by the central limit theorem. So in the limit, $Var(f(X)) <= EE[f'(X)^2]$.
]
#remark[
    The above proof uses a *tensorisation* argument. Tensorisation roughly means decomposing a high-dimensional function into a sum of lower-dimensional functions. E.g. the formula $Var(sum_i X_i) = sum_i Var(X_i)$ uses the tensorisation property of variance. Also, the @thm:efron-stein-inequality $
        Var(Z) <= sum_(i = 1)^n EE[Var^((i))(Z)].
    $ can be thought of as an example of the tensorisation of variance.
]
#remark[
    If $f$ is $L$-Lipschitz, i.e. $abs(f(x) - f(y)) <= L dot norm(x - y)$, then $norm(nabla f) <= L$. The @thm:gaussian-Poincaré-inequality holds for $L$-Lipschitz functions (with $L^2$ on the RHS).
]
#example[
    Recall from earlier that the operator norm $sigma_1$ is $1$-Lipschitz. If $X in RR^(n times d)$ with each $X_(i j) sim N(0, 1)$ IID, then by the @thm:gaussian-Poincaré-inequality, $Var(sigma_1 (X)) <= 1$, which is a good bound, given that it is known that $EE[sigma_1 (X)] = O(sqrt(n) + sqrt(d))$.
]
#example[
    Let $X_1, ..., X_n sim N(0, 1)$ be independent. Let $Z = f(X) = max_i X_i$. We have $nabla f = (0, ..., 1, ..., 0)$ where $1$ is at the index of the maximum. Hence, by the @thm:gaussian-Poincaré-inequality, $Var(Z) <= 1$, which is a good bound, given it is known that $EE[Z_n] approx log n$.
]

== Poincaré constant

#definition[
    Let $X$ be an RV taking values in $RR^d$. We say $X$ satisfies the Poincaré inequality with constant $C$ if $
        Var(f(X)) <= C dot EE[norm(nabla f(X))^2] quad forall f in C^1 (RR^d).
    $ The smallest such constant $C_P (X)$ is the *Poincaré constant* of $X$: $
        C_P (X) = sup_(f in C^1 (RR^d)) Var(f(X)) / EE[norm(nabla f(X))^2].
    $
]<def:Poincaré-constant>
#proposition[
    The Poincaré constant satisfies the following properties:
    + $C_P (a X + b) = a^2 C_P (X)$ for constants $a in RR, b in RR^d$.
    + For any unit vector $theta in RR^d$, $Var(gen(X, theta)) <= C_P (X)$. In particular, $Var(X_i) <= C_P (X)$ for all $i$.
    + If $X_1, ..., X_n$ are independent, then $
        C_P (X_(1:n)) = max_i C_P (X_i).
    $
    + If $C_P (X) < oo$, then $X$ has connected support.
]<prop:properties-of-Poincaré-constant>
#proof[
    Exercise.
]
#remark[
    The constant $1 \/ C_P (X)$ is called the *spectral gap*.
]
#definition[
    We say ${X_n}_(n in NN)$ is a *(time homogenous) Markov chain* on a finite state space $S$ (which WLOG we can take to be $[d]$) if $
        PP(X_(n + 1) = j | X_(1:n) = i_(1:n)) = PP(X_(n + 1) = j | X_n = i_n)
    $ for all $n$ and $i_1, ..., i_n, j in S$, i.e. if $X_(n + 1)$ is conditionally independent of $X_(1:(n - 1))$ given $X_n$ for all $n$.
]<def:markov-chain>
#definition[
    The *transition matrix* $P in RR^(d times d)$ of the Markov chain is defined by $
        P_(i j) = PP(X_(n + 1) = j | X_n = i),
    $ and its *discrete generator* is $Lambda := P - I$.
]<def:transition-matrix-and-discrete-generator>
#definition[
    Let $P$ be the transition matrix of a Markov chain. A row vector $pi in RR^d$ (which represents a distribution on $[d]$) on state space $S$ is called *stationary* if $pi_j = sum_i pi_i P_(i j)$ for all $j$ (i.e. $pi P = pi$).
]<def:stationary-distribution>
#definition[
    Given a Markov chain with stationary distribution $pi in RR^d$ and $f, g in RR^d$, the *Dirichlet form* is defined as $
        cal(E)(f, g) := -gen(f, Lambda g)_pi,
    $ where $gen(x, y)_pi = sum_(i = 1)^d x_i y_i pi_i$.
]<def:dirichlet-form>
#proposition[
    Let $P in RR^(d times d)$ be a reversible transition matrix with stationary distribution $pi in RR^d$. Assume the *reversibility* condition: $
        pi_i P_(i j) = pi_j P_(j i) quad forall i, j in [d].
    $ Let $f in RR^d$. Then $
        cal(E)(f, f) = 1/2 EE_(X_(n + 1), X_n sim pi) [(f(X_(n + 1)) - f(X_n))^2],
    $ which is the *discrete gradient* (we may view $f$ as a function $i |-> f_i$).
]<prop:dirichlet-form-of-f-and-f-is-discrete-gradient-for-reversible-transition-matrix>
#proofhints[
    Use that $sum_j P_(i j) = 1$ for all $i$ to split the sum $sum_i f_i^2 pi_i$ into two sums.
]
#proof[
    Since $sum_j P_(i j) = 1$ for all $i$, we have $
        cal(E)(f, f) & = gen(f, (I - P) f)_pi = sum_i f_i^2 pi_i - sum_i f_i pi_i sum_j P_(i j) f_j \
        & = 1/2 (sum_(i, j) f_i^2 pi_i P_(i j) + sum_(i, j) f_j^2 pi_j P_(j i) - 2 sum_(i, j) pi_i P_(i j) f_i f_j) \
        & = 1/2 sum_(i, j) pi_i P_(i j) (f_i - f_j)^2 \
        & = 1/2 sum_(i, j) PP(X_(n + 1) = j | X_n = i) PP(X_n = i) (f_i - f_j)^2 \
        & = 1/2 sum_(i, j) PP(X_(n + 1) = j, X_n = i) (f(i) - f(j))^2 \
        & = 1/2 EE[(f(X_(n + 1)) - f(X_n))^2].
    $
]
#remark[
    If the transition matrix $P$ is reversible, then $Lambda = P - I$ is self-adjoint with respect to $gen(dot, dot)_pi$ (i.e. $gen(Lambda f, g)_pi = gen(f, Lambda g)_pi$), so has real eigenvalues $lambda_1 >= dots.c >= lambda_n$. By @prop:dirichlet-form-of-f-and-f-is-discrete-gradient-for-reversible-transition-matrix, we have $gen(f, -Lambda f)_pi >= 0$, so $-Lambda$ is positive semi-definite, and so all $lambda_i <= 0$. Since $sum_j Lambda_(i j) = 0$ for all $i$, we have $lambda_1 = 0$, corresponding to eigenvector $f_1 = (1, ..., 1)$.

    Now $lambda_2 = sup_(f: gen(f, f_1)_pi = 0) (gen(f, Lambda f)_pi)/(gen(f, f)_pi)$, so $
        cal(E)(f, f) = - gen(f, Lambda f)_pi >= -lambda_2 gen(f, f)_pi = -lambda_2 EE_pi [f(X_1)^2] = -lambda_2 Var_pi (f) = (lambda_1 - lambda_2) Var_pi (f)
    $ for all $f in RR^d$ such that $EE_pi [f(X_1)] = gen(f, f_1)_pi = 0$. There is equality if $f = f_2$, the eigenvector corresponding to $lambda_2$.

    The best constant, $c$, in the inequality $Var_pi (f) <= c dot cal(E)(f, f)$ is $c = 1/(lambda_1 - lambda_2)$, the spectral gap.
]


= The entropy method

== Entropy, chain rules and Han's inequality

In the following section, let $A$ be a discrete (countable) alphabet and let $X$ be an RV on $A$.

#definition[
    The *Shannon entropy* of $X$ with PMF $P$ is $
        H(X) = EE[-log P(X)] = -sum_(x in A) PP(X = x) log PP(X = x),
    $ where we use the convention $0 log 0 = 0$.
]<def:shannon-entropy>
#example[
    The entropy of $X sim Bern(p)$ is $H(X) = -p log p - (1 - p) log(1 - p)$.
]
#remark[
    Note that for $x_1^n in A^n$, $P^n (x_1^n) = e^(-n 1/n sum_(i = 1)^n -log P(x_i))$ ($P^n$ is the product distribution). So $P^n (X_1^n) = e^(-n 1/n sum_(i = 1)^n -log P(X_i)) approx e^(-n H(X_i))$ for IID $X_i$, by the @thm:wlln.
]
#proposition[
    Properties of Shannon entropy:
    - $H$ is non-negative.
    - $H(dot)$ is concave as a functional of $P$.
    - If $abs(A) < oo$, then $H(X) <= log abs(A)$ with equality if $X sim "Unif"(A)$.
]<prop:properties-of-shannon-entropy>
#proof[
    Exercise.
]
#definition[
    For PMFs $Q, P$ on $A$, $Q$ is *absolutely continuous* with respect to $P$, written $Q << P$, if $P(x) = 0 => Q(x) = 0$ for all $x in A$.
]<def:absolutely-continuous-pmf>
#definition[
    Let $Q, P$ be PMFs on $A$ such that $Q << P$ (which means if $P(x) = 0$, then $Q(x) = 0$). The *relative entropy* between $Q$ and $P$ is $
        D(Q || P) = EE_Q [log Q(X)/P(X)] = sum_(x in A) Q(x) log Q(x)/P(x)
    $ if $Q << P$, and $D(Q || P) = oo$ otherwise. We use the convention that $0 log 0/0 = 0$.
]<def:relative-entropy>
#proposition[
    Properties of relative entropy:
    - $D(Q || P) >= 0$.
    - $D(Q || P)$ is convex in both arguments.
    - If $X sim P$ where $P$ is the uniform distribution on $A$, and $Y sim Q$, then $D(Q || P) = H(X) - H(Y)$.
]<prop:properties-of-relative-entropy>
#proof[
    Exercise.
]
#definition[
    The *conditional entropy* of $X$ given $Y$ is $
        H(X | Y) & = EE[-log P_(X | Y)(X | Y)] = -sum_(x, y) P(x, y) log P(x | y) \
        & = sum_y PP(Y = y) H(X | Y = y)
    $
]<def:conditional-entropy>
#theorem("Chain Rule for Entropy")[
    We have $
        H(X_(1:n)) = EE[-log P(X_(1:n))] = sum_(i = 1)^n H(X_i | X_(1:(i - 1))).
    $
]<thm:entropy-chain-rule>
#proofhints[
    Straightforward.
]
#proof[
    Since $
        PP(X_(1:n) = x_(1:n)) = PP(X_1 = x_1) PP(X_2 = x_2 | X_1 = x_1) dots.c PP(X_n = x_n | X_(1:(n - 1)) = X_(1:(n - 1))),
    $ we have $
        H(X_(1:n)) & = EE[-log P(X_(1:n))] = EE[sum_(i = 1)^n -log P(X_i | X_(1:(i - 1)))] \
        & = sum_(i = 1)^n EE[-log P(X_i | X_(1:(i - 1)))] \
        & = sum_(i = 1)^n H(X_1 | X_(1:(i - 1))).
    $
]
#proposition("Conditioning Reduces Entropy")[
    $H(X | Y) <= H(X)$.
]<prop:conditioning-reduces-entropy>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        H(X) - H(X | Y) & = EE[log 1/P(X) + log P(X | Y)] \
        & = EE[log (P(X | Y) P(Y))/(P(X) P(Y))] = D(P_(X, Y) || P_X P_Y) >= 0.
    $
]
#definition[
    Similarly to the definition of relative entropy, the *conditional relative entropy* of $X$ and $Y$ given $Z$ is $
        D(X || Y | Z) = sum_z PP(Z = z) D(X | Z = z || Y | Z = z).
    $ We also write e.g. $
        D(Q_(Y | X) || P_Y | Q_(X)) = sum_x PP(X = x) D(Q_(Y | X = x) || P_Y).
    $
]<def:conditional-relative-entropy>
#proposition("Chain Rule for Relative Entropy")[
    Let $P, Q$ be PMFs on $A^n$. Let $X_(1:n) sim Q$. Then $
        D(Q_(X_(1:n)) || P_(X_(1:n))) & = sum_(i = 1)^n EE_(Q_(X_1:(i - 1))) [D(Q_(X_i | X_(1:(i - 1))) || P_(X_i | X_(1:(i - 1))))] \
        & =: sum_(i = 1)^n D(Q_(X_i | X_(1:(i - 1))) || P_(X_i | X_(1:(i - 1))) | Q_(X_(1:(i - 1))))
    $
]<prop:relative-entropy-chain-rule>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        D(Q_(X_(1:n)) || P_(X_(1:n))) & = EE_Q [log Q(X_(1:n))/P(X_(1:n))] \
        & = EE_Q [sum_(i = 1)^n log (Q_(X_i | X_(1:(i - 1)))(X_i | X_(1:(i - 1))))/(P_(X_i | X_(1:(i - 1))) (X_i | X_(1:(i - 1))))] \
        // & = sum_(i = 1)^n EE_(Q_(X_1:(i - 1))) EE_(Q_(X_i | X_(1:(i - 1)))) log Q(X_i | X_(1:(i - 1)))/P(X_i | X_(1:(i - 1))) \
        & = sum_(i = 1)^n EE_(Q_(X_1:(i - 1))) [D(Q_(X_i | X_(1:(i - 1))) || P_(X_i | X_(1:(i - 1))))]
    $
]
#remark[
    The @prop:relative-entropy-chain-rule is similar to the chain rule for variance: $
        Var(Z) = sum_(i = 1)^n EE[Delta_i^2],
    $ $Delta_i = EE[Z | X_(1:i)] - EE[Z | X_(1:(i - 1))]$, which led to the @thm:efron-stein.
]
#lemma("Conditioning Reduces Conditional Entropy")[
    $H(X | Y, Z) <= H(Y)$.
]<lem:conditioning-reduces-conditional-entropy>
#proofhints[
    Straightforward.
]
#proof[
    $H(X | Y, Z) = sum_z PP(Z = z) H(X | Y, Z = z) <= sum_z PP(Z = z) H(X | Z = z) = H(X | Z)$ by @prop:conditioning-reduces-entropy.
]
#theorem("Han's Inequality")[
    Let $X_(1:n)$ be discrete RVs. Then $
        H(X_(1:n)) <= 1/(n - 1) sum_(i = 1)^n H(X^((i))).
    $
]<thm:hans-inequality>
#proofhints[
    Show that $H(X_(1:n)) <= H(X^((i))) + H(X_i | X_(1:(i - 1)))$.
]
#proof[
    By the @thm:entropy-chain-rule and @prop:conditioning-reduces-entropy, $
        H(X_(1:n)) & = H(X^((i))) + H(X_i | X^((i))) \
        & <= H(X^((i))) + H(X_i | X_(1:(i - 1)))
    $ Summing over $i$, we obtain $n H(X_(1:n)) <= sum_(i = 1)^n H(X^((i))) + H(X_(1:n))$ by the chain rule.
]
#corollary("Loomis-Whitney Inequality")[
    The Loomis-Whitney inequality states that for finite $A subset.eq ZZ^n$, $
        abs(A) <= product_(i = 1)^n abs(A^((i)))^(1 \/ (n - 1))
    $
]<crl:loomis-whitney-inequality>
#proofhints[
    Straightforward.
]
#proof[
    Let $X_(1:n)$ be uniform on $A$. Then $log abs(A) = H(X_(1:n))$. By @thm:hans-inequality, $
        H(X_(1:n)) <= 1/(n - 1) sum_(i = 1)^n H(X^((i))) <= 1/(n - 1) sum_(i = 1)^n log abs(A^((i)))
    $
]
#lemma[
    Let $Q, P$ be PMFs on a discrete set $A times B times C$. Then $
        D(Q_(Y | X, Z) || P_Y | Q_(X, Z)) >= D(Q_(Y | X) || P_Y | Q_X)
    $
    // TODO: I'm struggling to understand this a bit, what the D(. || . | .) means
]<lem:conditioning-on-first-argument-increases-relative-entropy>
#proofhints[
    Use convexity of relative entropy.
]
#proof[
    By convexity of relative entropy, $
        D(Q_(Y | X, Z) || P_Y | Q_(X, Z)) & =: sum_(x, z) Q_(X, Z)(x, z) D(Q_(Y | X = x, Z = z) || P_Y) \
        & = sum_x Q(x) sum_z Q(z | x) D(Q_(Y | X = x, Z = z) || P_Y) \
        & >= sum_x Q(x) D(sum_z Q(z | x) Q_(Y | X = x, Z = z) || P_Y) \
        & = sum_x Q(x) D(Q_(Y | X = x) || P_Y) \
        & = D(Q_(Y | X) || P_Y | Q_X).
    $
]
#theorem("Han's Inequality for Relative Entropy")[
    Suppose $Q, P$ are PMFs on $A^n$, and assume that $P = P_1 times.circle dots.c times.circle P_n$. Then $
        D(Q || P) = D(Q_(X_(1:n)) || P_(X_(1:n))) >= 1/(n - 1) sum_(i = 1)^n D(Q_(X^((i))) || P_(X^((i))))
    $ Equivalently, $
        D(Q || P) <= sum_(i = 1)^n D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))
    $ (this is tensorisation of $D(dot || dot)$).
]<thm:hans-inequality-for-relative-entropy>
#remark[
    Taking $P$ to be uniform in @thm:hans-inequality-for-relative-entropy gives @thm:hans-inequality for Shannon entropy.
]
#proofhints[
    Explain why $D(Q || P) & = D(Q_(X^((i))) || P_(X^((i)))) + D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))$, then use @lem:conditioning-on-first-argument-increases-relative-entropy.
]
#proof[
    By the @prop:relative-entropy-chain-rule and @lem:conditioning-on-first-argument-increases-relative-entropy, $
        D(Q || P) & = D(Q_(X^((i))) || P_(X^((i)))) + D(Q_(X_i | X^((i))) || P_(X_i | X^((i))) | Q_(X^((i)))) \
        & = D(Q_(X^((i))) || P_(X^((i)))) + D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i)))) quad "since" P "is a product distribution" \
        & >= D(Q_(X^((i))) || P_(X^((i)))) + D(Q_(X_i | X_(1:(i - 1))) || P_(X_i) | Q_(X_(1:(i - 1))))
    $ Summing over $i$, we obtain $n D(Q || P) >= sum_(i = 1)^n D(Q_(X^((i))) || P_(X^((i)))) + D(Q || P)$ by the @prop:relative-entropy-chain-rule, hence $
        D(Q || P) & >= 1/(n - 1) sum_(i = 1)^n D(Q_(X^((i))) || P_(X^((i)))) \
        & = 1/(n - 1) sum_(i = 1)^n (D(Q || P) - D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i)))) \
        <==> n / (n - 1) D(Q || P) - D(Q || P) & <= 1/(n - 1) sum_(i = 1)^n D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))
    $
]
#definition[
    There is another notion of entropy. Let $Z >= 0$ almost surely. Let $phi(x) = x log x$ for $x > 0$ and $phi(0) = 0$. The *entropy* of $Z$ is defined as $
        Ent(Z) = EE[phi(Z)] - phi(EE[Z]),   
    $ Note the similarity to the definition $Var(Z) = EE[Z^2] - EE[Z]^2$. Also, since $phi$ is convex, $Ent(Z)$ is non-negative by Jensen's inequality.
]<def:entropy>
#proposition[
    Let $X sim P$, where $Q << P$ are PMFs on a countable alphabet $A$. Let $Z = Q(X)/P(X)$. Then $
        Ent(Z) = D(Q || P).
    $
]<prop:expression-for-relative-entropy-in-terms-of-entropy>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        Ent(Z) & = EE_P [Q(X)/P(X) log Q(X)/P(X)] - (EE_P Q(X)/P(X)) log EE_P [Q(X)/P(X)] \
        & = D(Q || P) - 1 log 1 = D(Q || P).
    $
]
#remark[
    In general, when $Z$ is the Radon-Nikodym derivative $(dif Q)/(dif P)(X)$ and $X sim P$, then $Ent(Z) = D(Q || P)$.
]
#theorem("Tensorisation of Entropy")[
    Let $X_1, ..., X_n$ be independent RVs taking values in a countable set $A$, and let $f: A^n -> RR_(>= 0)$. Let $Z = f(X_(1:n)) = f(X)$. Then $
        Ent(Z) <= EE[sum_(i = 1)^n Ent^((i))(Z)],
    $ where $
        Ent^((i))(Z) & = E^((i))[Z log Z] - E^((i)) [Z] log E^((i)) [Z] \
        & = EE[Z log Z | X^((i))] - EE[Z | X^((i))] log EE[Z | X^((i))].
    $
]<thm:tensorisation-of-entropy>
#remark[
    @thm:tensorisation-of-entropy is analogous to the @thm:efron-stein-inequality.
]
#proofhints[
    - Let $X sim P = P_1 times.circle cdots times.circle P_n$. Let $Q(x) = f(x) P(x)$.
    - Show that $Ent(a Z) = a Ent(Z)$, and so can assume WLOG that $EE[Z] = 1$, so $Q$ is PMF.
    - Use @thm:hans-inequality-for-relative-entropy on $Q$ and $P$.
    - Show that $
        Q_(X_i | X^((i)))(x_i | x^((i))) = (P(x_i) f(x))/(EE[f(X) | X^((i)) = x^((i))]).
    $
    - Show that $Q^((i))(x^((i))) = P^((i))(x^((i))) EE[f(X) | X^((i)) = x^((i))]$, and so that $EE[D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))] = EE_P [Ent^((i))(f(X))]$.
]
#proof[
    Let $X sim P = P_1 times.circle cdots times.circle P_n$. Let $Q(x) = f(x) P(x)$. Since $
        Ent(a Z) = a EE[Z log Z] + a EE[Z log a] - a EE[Z] log EE[Z] - a EE[Z] log a = a Ent(Z),
    $ we may assume WLOG that $EE[Z] = 1$, and so $Q$ is a valid PMF. By @thm:hans-inequality-for-relative-entropy, $
        D(Q || P) <= sum_(i = 1)^n EE[D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))]
    $ Now $
        Q_(X_i | X^((i)))(x_i | x^((i))) & = (Q_X (x))/(Q_(X^((i)))(x^((i)))) = (P(x) f(x))/(sum_(x'_i in A) Q(x_(1:(i - 1)), x'_i, x_((i + 1):n))) \
        & = (P_i (x_i) P^((i))(x^((i))) f(x))/(sum_(x'_i in A) P_i (x'_i) P^((i))(x^((i))) f(x^((i)), x'_i)) \
        & = (P_i (x_i) f(x))/(EE[f(X) | X^((i)) = x^((i))])
    $ (write $f(x^((i)), x'_i) = f(x_(1:(i - 1)), x'_i, x_((i + 1):n))$). By definition, $
        & EE[D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))] \
        = & sum_(x^((i)) in A^(n - 1)) Q^((i))(x^((i))) sum_(x_i in A) (P_i (x_i) f(x))/(EE[f(X) | X^((i)) = x^((i))]) log f(x)/(EE[f(X) | X^((i)) = x^((i))]) 
    $ But $Q^((i))(x^((i))) = P^((i))(x^((i))) EE[f(X) | X^((i)) = x^((i))]$. So, $
        & EE[D(Q_(X_i | X^((i))) || P_(X_i) | Q_(X^((i))))] \
        = & sum_(x^((i)) in A^(n - 1)) P^((i))(x^((i))) (sum_(x_i in A) P_i (x_i) f(x) log f(x) - EE[f(X) | X^((i)) = x^((i))] log EE[f(X) | X^((i)) = x^((i))]) \
        = & sum_(x^((i)) in A^(n - 1)) P^((i))(x^((i))) (EE[f(X) log f(X) | X^((i)) = x^((i))] - EE[f(X) | X^((i)) = x^((i))] log EE[f(X) | X^((i)) = x^((i))]) \
        = & EE_P [Ent^((i)) (f(X))]
    $ So $Ent(f(X)) = D(Q || P) <= sum_(i = 1)^n EE[Ent^((i))(f(X))]$.
]

== Herbst's argument

#theorem("Herbst's Argument")[
    Let $Z$ be a real-valued RV such that $EE[e^(lambda Z)] < oo$ for all $lambda > 0$. Suppose there exists $nu > 0$ such that for all $lambda > 0$, $
        Ent(e^(lambda Z))/EE[e^(lambda Z)] <= lambda^2 nu / 2.
    $ Then $
        psi_(ZZ - EE[Z])(lambda) = log EE[e^(lambda(Z - EE[Z]))] <= lambda^2 nu / 2 quad forall lambda > 0.
    $
]<thm:herbsts-argument>
#proofhints[
    - Show that $Ent(e^(lambda Z))/EE[e^(lambda Z)] = lambda^2 G'(lambda)$, where $G(lambda) = 1/lambda psi_(Z - EE[Z])(lambda)$.
    - Given an upper bound for $integral_0^lambda G'(t) dif t$ (explain using a Taylor expansion of $psi_(Z - EE[Z])$ why this integral is valid).
]
#proof[
    Write $psi = psi_(Z - EE[Z])$. We have $
        Ent(e^(lambda Z)) & = lambda EE[e^(lambda Z) dot Z] - EE[e^(lambda Z)] log EE[e^(lambda Z)] \
        & = EE[e^(lambda Z)] (lambda EE[(Z e^(lambda Z))/(EE[e^(lambda Z)])] - log EE[e^(lambda Z)])
    $ But $
        psi'(lambda) = (psi_Z (lambda) - lambda EE[Z])' = EE[(Z e^(lambda Z))/(EE[e^(lambda Z)])] - EE[Z].
    $ So by the above expression for $Ent$, $
        Ent(e^(lambda Z))/EE[e^(lambda Z)] & = [lambda psi'(lambda) + lambda EE[Z] - lambda EE[Z] - psi(lambda)] \
        & = lambda^2 (1/lambda psi'(lambda) - 1/lambda^2 psi(lambda)) = lambda^2 G'(lambda)
    $ where $G(lambda) = 1/lambda psi(lambda)$. Also, by assumption, $
        Ent(e^(lambda Z))/EE[e^(lambda Z)] <= lambda^2 nu / 2
    $ By Taylor's theorem, $G(lambda) = 1/lambda (psi(0) + lambda psi'(0) + O(lambda^2)) = 1/lambda O(lambda^2) = O(lambda) -> 0$ as $lambda -> 0$. Hence, we may integrate $G'(theta)$ from $0$ to $lambda$: $
        G(lambda) & = integral_0^lambda G'(theta) dif theta <= integral_0^lambda nu / 2 dif theta quad "since" theta^2 G'(theta) <= theta^2 nu / 2 \
        & = lambda nu / 2
    $ So $psi(lambda) <= lambda^2 nu / 2$.
]
#theorem("Bounded Differences Inequality")[
    Let $X = (X_1, ..., X_n)$, where the $X_i$ are independent. Let $f$ have bounded differences with constants $c_i$. Let $Z = f(X)$. Then for all $t > 0$, $
        PP(Z - EE[Z] >= t), PP(Z - EE[Z] <= -t) <= e^(-2t^2 \/ sum_(i = 1)^n c_i^2) = e^(-t^2 \/ 2 nu),
    $ where $nu = 1/4 sum_(i = 1)^n c_i^2$.
]<thm:bounded-differences-inequality>
#proofhints[
    - Use @lem:hoeffding and an equality from the proof of @thm:herbsts-argument to show that $(Ent^((i)) (e^(lambda Z)))/EE[e^(lambda Z) | X^((i))] = lambda psi'_i (lambda) - psi_i (lambda) <= 1/8 lambda^2 c_i^2$ (you should use an integral somewhere), where $psi_i (lambda) = log EE[e^(lambda(Z - EE[Z])) | X^((i))]$.
    - Use @thm:tensorisation-of-entropy and @thm:herbsts-argument to show that $Z - EE[Z]$ has sub-Gaussian right tail with parameter $nu$.
    - Why does the result also hold for $-f$?
]
#proof[
    The first step is tensorisation of entropy: by @thm:tensorisation-of-entropy, we have $
        Ent(e^(lambda Z)) <= EE[sum_(i = 1)^n Ent^((i))(e^(lambda Z))]
    $ Write $f_(X^((i)))(x_i) = f(X_(1:(i - 1)), x_i, X_((i + 1):n))$. Conditional on $X^((i))$, $f_(X^((i)))$ takes values on an interval of length $<= c_i$ by the bounded differences property.

    The second step is to apply @lem:hoeffding. Let $psi_i (lambda) = log EE[e^(lambda(Z - EE[Z])) | X^((i))]$. As in the proof of @thm:herbsts-argument, we have $
        Ent(e^(lambda Z))/EE[e^(lambda Z)] & = lambda psi'_(Z - EE[Z])(lambda) - psi_(Z - EE[Z])(lambda).
    $ Note that this holds for the random variable $Z | X^((i)) = x^((i))$, for any value of $x^((i))$. By @lem:hoeffding, we have $psi''_i (lambda) <= c_i^2 \/ 4$, and so $
        (Ent^((i)) (e^(lambda Z)))/EE[e^(lambda Z) | X^((i))] & = lambda psi'_i (lambda) - psi_i (lambda)= integral_0^lambda theta psi''_i (theta) dif theta \
        & <= integral_0^lambda theta c_i^2 / 4 dif theta \
        & = 1/8 lambda^2 c_i^2
    $

    The third step is using @thm:herbsts-argument: we have $
        Ent(e^(lambda Z)) & <= EE[sum_(i = 1)^n Ent^((i))(e^(lambda Z))] <= EE[sum_(i = 1)^n 1/8 lambda^2 c_i^2 EE[e^(lambda Z) | X^((i))]] \
        & = 1/2 lambda^2 dot 1/4 sum_(i = 1)^n c_i^2 EE[e^(lambda Z)]
    $ by @thm:law-of-total-expectation. By @thm:herbsts-argument, we have $
        psi_(Z - EE[Z])(lambda) <= (lambda^2 nu)/2 quad forall lambda > 0,
    $ and so the @prop:chernoff-bound gives $PP(Z - EE[Z]) <= e^(-t^2 \/ 2nu)$. Now noting that $-f$ also has bounded differences with the same constants, we obtain the left-tail bound.
]

== Log-Sobolev inequalities on the hypercube

#notation[
    Let $X_1, ..., X_n$ be IID and uniform on ${-1, 1}$, so $X = X_(1:n)$ is uniform on the hypercube ${-1, 1}^n$. Let $Z = f(X)$. By @thm:efron-stein, $Var(Z) <= 1/2 EE[sum_(i = 1)^n (Z - Z'_i)^2] =: nu$, where $Z'_i = f(X_(1:(i - 1)), X'_i, X_((i + 1):n))$ and $X'_i$ is an independent copy of $X_i$. Define $cal(E)(f)$ as $
        nu & = 1/4 EE[sum_(i = 1)^n (f(X) - f(overline(X)^((i))))^2] \
        & = 1/2 EE[sum_(i = 1)^n (f(X) - f(overline(X)^((i))))_+^2] =: cal(E)(f),
    $ where $overline(X)^((i)) = (X_(1:(i - 1)), -X_i, X_((i + 1):n))$. $1/2 (f(X) - f(overline(X)^((i))))$ looks like a discrete partial derivative in the $i$-th direction. So $cal(E)(f)$ is a discrete analogue of $EE[norm(nabla f (X))^2]$.
]
#theorem("Log-Sobolev Inequality for Bernoullis")[
    Let $X$ be uniformly distributed on ${-1, 1}^n$ and $f: {-1, 1}^n -> RR$. Then $
        Ent(f^2 (X)) <= 2 dot cal(E)(f).
    $
]<thm:log-sobolev-inequality-for-bernoullis>
#proofhints[
    - Use @thm:tensorisation-of-entropy to show that it is enough to prove the result for $n = 1$.
    - Based on the one-dimensional inequality that needs to be shown, construct a suitable function $h(a, b)$. Let $g(a) = h(a, b)$ for fixed $b$. Show that $g(b) = 0$, $g'(b) = 0$, and $g''(a) <= 0$ for all $a >= b$.
]
#proof[
    Let $Z = f(X)$. By @thm:tensorisation-of-entropy, $
        Ent(Z^2) <= EE[sum_(i = 1)^n Ent^((i))(Z^2)]
    $ If the result was true for $n = 1$, then we would have $Ent^((i))(Z^2) <= 1/2 (f(X) - f(overline(X)^((i))))^2$ (since when $X^((i))$ is fixed, we may think of $Z^2$ as being a function of $X_i$, and this function is $f(X)^2$ or $f(overline(X)^((i)))^2$ with equal probability) and so $Ent(Z^2) <= 2 cal(E)(f)$. So it suffices to prove the $n = 1$ case. Let $f(1) = a$, $f(-1) = b$. In the $n = 1$ case, the inequality we want to show is $
        1/2 a^2 log (a^2) + 1/2 b^2 log(b^2) - 1/2 (a^2 + b^2) log((a^2 + b^2)/2) <= 1/2 (b - a)^2.
    $ We may assume $a, b >= 0$, since $(b - a)^2 / 2 >= (abs(b) - abs(a))^2 / 2$. Also, by symmetry, WLOG we assume $a >= b$. For fixed $b >= 0$, define $
        h(a) = 1/2 a^2 log (a^2) + 1/2 b^2 log(b^2) - 1/2 (a^2 + b^2) log((a^2 + b^2)/2) - 1/2 (b - a)^2.
    $ Since $h(b) = 0$, it is enough to show that $h'(b) = 0$ and $h''(a) <= 0$ (so $h$ is concave). We have $
        h'(a) = a log (2a^2)/(a^2 + b^2) - (a - b)
    $ Hence, $h'(b) = 0$. Also, $
        h''(a) = 1 + log (2a^2) / (a^2 + b^2) - (2a^2)/(a^2 + b^2) <= 0,
    $ since $log x <= x - 1$.
]
#remark[
    @thm:log-sobolev-inequality-for-bernoullis is stronger than @thm:efron-stein. Also, the constant $2$ on the RHS is tight.
]
#theorem("Gaussian Log-Sobolev Inequality")[
    Let $X = (X_1, ..., X_n)$ be a vector of $n$ independent RVs with each $X_i sim N(0, 1)$, let $f: RR^n -> RR$ be continuously differentiable. Then $
        Ent(f^2 (X)) <= 2 dot EE[norm(nabla f(X))^2].
    $
]<thm:gaussian-log-sobolev-inequality>
#proof[
    Exercise (use tensorisation and the central limit theorem).
]
#definition[
    $f: RR^n -> RR$ is *$L$-Lipschitz* if $
        abs(f(x) - f(y)) <= L dot norm(x - y) quad forall x, y in RR^n.
    $ An $L$-Lipschitz function $f$ satisfies $norm(nabla f(x)) <= L$ for all $x in RR^n$.
]<def:lipschitz-function>
#theorem("Gaussian Concentration Inequality")[
    Let $X = (X_1, ..., X_n)$ be a vector of $n$ independent RVs with each $X_i sim N(0, 1)$. Let $f: RR^n -> RR$ be $L$-Lipschitz and $Z = f(X)$. Then $Z - EE[Z] in cal(G)(L^2)$, i.e. for all $lambda in RR$, $
        psi_(Z - EE[Z])(lambda) <= (lambda^2 L^2)/2,
    $ and so for all $t > 0$, $
        PP(Z - EE[Z] >= t) <= e^(-t^2 \/ 2L^2), quad "and" quad P(Z - EE[Z] <= -t) <= e^(-t^2 \/ 2L^2).
    $ Note that these bounds are independent of the dimension $n$.
]<thm:gaussian-concentration-inequality>
#proofhints[
    - Explain why we can assume $f$ is continuously differentiable (think sequences).
    - Use that $norm(nabla f(X)) <= L$ and the @thm:gaussian-log-sobolev-inequality on $e^(lambda f \/ 2)$ to obtain an upper bound that is a suitable assumption for @thm:herbsts-argument.
]
#proof[
    WLOG, we can assume $f$ is continuously differentiable (otherwise, we can approximate $f$ with a sequence of contiuously differentiable functions which converge to $f$). Note that $norm(nabla f(X)) <= L$. By the @thm:gaussian-log-sobolev-inequality for $e^(lambda f \/ 2)$, we have $
        Ent(e^(lambda f(X))) & <= 2 dot EE[norm(nabla e^(lambda f(X) \/ 2))^2] \
        & = 2 dot EE[norm(lambda / 2 nabla (f(X)) dot e^(lambda f(X) \/ 2))^2] \
        & = lambda^2 / 2 EE[e^(lambda f(X)) norm(nabla f(X))^2] \
        & <= (lambda^2 L^2)/2 EE[e^(lambda f(X))]
    $ So by @thm:herbsts-argument, $
        psi_(Z - EE[Z])(lambda) <= (lambda^2 L^2)/2,
    $ and the @prop:chernoff-bound gives the right tail bound. The left tail bound follows from the fact that $-f$ is also $L$-Lipschitz.
]
#theorem("Concentration on the Hypercube")[
    Let $f: {-1, 1}^n -> RR$ and let $X = (X_1, ..., X_n)$ be uniform on ${-1, 1}^n$. Let $Z = f(X)$ and assume $
        max_(x in {-1, 1}^n) sum_(i = 1)^n (f(x) - f(overline(x)^((i))))_+^2 <= nu
    $ for some $nu > 0$. Then for all $t > 0$, $
        PP(Z - EE[Z] >= t) <= e^(-t^2 \/ nu),
    $ i.e. $Z$ has a sub-Gaussian right tail with variance parameter $nu \/ 2$.
]<thm:concentration-on-the-hypercube>
#proofhints[
    - Explain why $(e^(z \/ 2) - e^(y \/ 2))/((z - y) \/ 2) <= e^(z \/ 2)$ for $z > y$.
    - Use the @thm:log-sobolev-inequality-for-bernoullis on an appropriate function to obtain an upper bound that is a suitable assumption for @thm:herbsts-argument.
]
#proof[
    We use the @thm:log-sobolev-inequality-for-bernoullis for the function $e^(lambda f \/ 2)$: for $lambda > 0$, we have $
        Ent(e^(lambda f(X))) & <= 1/2 EE[sum_(i = 1)^n (e^(lambda f(X) \/ 2) - e^(lambda f(overline(X)^((i)) \/ 2)))^2] \
        & = EE[sum_(i = 1)^n (e^(lambda f(X) \/ 2) - e^(lambda f(overline(X)^((i))) \/ 2))_+^2]
    $ Since for $z > y$, $(e^(z \/ 2) - e^(y \/ 2))/((z - y) \/ 2) <= e^(z \/ 2)$ (by convexity of $exp$), $
        Ent(e^(lambda f(X))) & <= EE[sum_(i = 1)^n lambda^2 / 2^2 (f(X) - f(overline(X)^((i))))_+^2 dot e^(lambda f(X))] \
        & <= (nu lambda^2) / 4 EE[e^(lambda f(X))].
    $ By @thm:herbsts-argument, we thus have $psi_(Z - EE[Z])(lambda) <= (lambda^2 nu \/ 2)/2$ for all $lambda > 0$, and the @prop:chernoff-bound gives $PP(Z - EE[Z] >= t) <= e^(-t^2 \/ nu)$.
]
#remark[
    - If the same condition for the negative part $(dot)_-$ holds, then we get the analogous left tail bound.
    - If $max_(x in {-1, 1}^n) sum_(i = 1)^n (f(x) - f(overline(x)^((i))))^2 <= nu$, then $Z - EE[Z] in cal(G)(nu \/ 2)$. In fact, more careful analysis shows that $Z - EE[Z] in cal(G)(nu \/ 4)$.
    - If $f$ has bounded differences with constants $c_i$ where $sum_(i = 1)^n c_i^2 <= nu$, then $f$ also satisfies $
        max_(x in {-1, 1}^n) sum_(i = 1)^n (f(x) - f(overline(x)^((i))))^2 <= nu
    $ so $Z - EE[Z] in cal(G)(nu \/ 4)$. @thm:bounded-differences-inequality also gives $Z - EE[Z] in cal(G)(nu \/ 4)$ under stronger assumptions. So we are able to prove a result that is as strong as @thm:bounded-differences-inequality but under a weaker assumption.
    - The @thm:efron-stein gives $
        Var(Z) <= EE[sum_(i = 1)^n (Z - Z'_i)_+^2] = 1/2 EE[sum_(i = 1)^n (Z - overline(Z)^((i)))^2] <= nu \/ 2
    $ if $EE[sum_(i = 1)^n (Z - overline(Z)^((i)))^2] <= nu$. Note that this a weaker result, but makes a weaker assumption than @thm:concentration-on-the-hypercube.
]

== The modified log-Sobolev inequality (MLSI)

#lemma("Variational Principle for Entropy")[
    For any non-negative random variable $Y$, $
        Ent(Y) = inf_(u > 0) EE[Y (log Y - log u) - (Y - u)]
    $ and the infimum is achieved at $u = EE[Y]$.
]<lem:variational-principle-for-entropy>
#proofhints[
    Use the inequality $log x <= x - 1$ and show that the difference is non-positive for all $u > 0$.
]
#proof[
    We have $
        Ent(Y) - EE[Y log Y + Y log u - (Y - u)] & = EE[Y log u/EE[Y] + Y - u] \
        & <= EE[Y]/EE[Y] u - EE[Y] + EE[Y] - u = 0
    $ since $log x <= x - 1$. For $u = EE[Y]$, $
        EE[Y log Y] - EE[Y log u + Y - u] = Ent(Y).
    $
]
#remark[
    This is an entropy analogue of $Var(Y) = inf_(a in RR) EE[(Y - a)^2]$. In fact, for any convex function $phi$, we can prove that the infimum $
        inf_(u > 0) EE[phi(Y) - phi(u) - phi'(u)(Y - u)]
    $ is achieved when $u = EE[Y]$. The @lem:variational-principle-for-entropy is a special case for $phi(x) = x log x$.
]
#theorem("Modified Log-Sobolev Inequality")[
    Let $X_1, ..., X_n$ be independent RVs taking values on $A$. Let $f: A^n -> RR$ and $Z = f(X)$. Let $f_i: A^(n - 1) -> RR$ be an arbitrary function and $Z_i = f_i (X^((i)))$ for each $i in [n]$. Then $
        Ent(e^(lambda Z)) <= sum_(i = 1)^n EE[e^(lambda Z) phi(-lambda(Z - Z_i))] quad forall lambda > 0,
    $ where $phi(x) = e^x - x - 1$.
    
    For $lambda > 0$ and $Z >= Z_i$, we may use the inequality $phi(-x) <= x^2 \/ 2$ for $x >= 0$ to give a simpler upper bound: $
        Ent(e^(lambda Z)) <= lambda^2 / 2 sum_(i = 1)^n EE[e^(lambda Z) (Z - Z_i)^2].
    $
]<thm:mlsi>
#proofhints[
    Use @thm:tensorisation-of-entropy and the @lem:variational-principle-for-entropy, with $u = Y_i = e^(lambda Z_i)$ (conditional on $X^((i))$).
]
#proof[
    Let $Y = e^(lambda Z)$ and $Y_i = e^(lambda Z_i)$. By @thm:tensorisation-of-entropy, $
        Ent(Y) <= EE[sum_(i = 1)^n Ent^((i))(Y)]
    $ We will bound each of the $n$ terms on the RHS. Conditional on $X^((i))$, take $u = Y_i$ (note that $u > 0$). By the @lem:variational-principle-for-entropy, $
        Ent^((i))(Y) & <= EE[Y log Y/Y_i - (Y - Y_i) | X^((i))] \
        & = EE[e^(lambda Z) lambda (Z - Z_i) - (e^(lambda Z) - e^(lambda Z_i)) | X^((i))] \
        & = EE[e^(lambda Z) (lambda(Z - Z_i) + e^(-lambda (Z - Z_i)) - 1) | X^((i))] \
        & = EE[e^(lambda Z) phi(-lambda (Z - Z_i)) | X^((i))].
    $ The result follows by summing and taking expectations.
]
#theorem("Relaxed Bounded Differences")[
    Let $Z = f(X_1, ..., X_n)$ for independent RVs $X_1, ..., X_n$ which take values on $A$ and $f: A^n -> RR$. Let $
        Z_i = inf_(x'_i) f(X_(1:(i - 1)), x'_i, X_((i + 1):n)).
    $ Suppose that $
        sum_(i = 1)^n (Z - Z_i)^2 <= nu
    $ almost surely for some $nu > 0$. Then for all $t > 0$, $
        PP(Z - EE[Z] >= t) <= e^(-t^2 \/ 2 nu).
    $
]<thm:relaxed-bounded-differences>
#proofhints[
    By the @thm:mlsi.
]
#proof[
    By the @thm:mlsi, $
        Ent(e^(lambda Z)) & <= lambda^2 / 2 EE[e^(lambda Z) sum_(i = 1)^n (Z - Z_i)^2] <= (lambda^2 nu)/2 EE[e^(lambda Z)]
    $ The result follows by @thm:herbsts-argument and the @prop:chernoff-bound.
]
#remark[
    If $Z_i = sup_(x'_i) f(X_(1:(i - 1)), x'_i, X_((i + 1):n))$ and $sum_(i = 1)^n (Z - Z_i)^2 <= nu$, then we also obtain a left tail bound. If this condition holds for the supremum and the infimum, then $Z - EE[Z] in cal(G)(nu)$.
]

== Concentration of convex Lipschitz functions

Let $f: [0, 1]^n -> RR$ be separately convex and $1$-Lipschitz. The @thm:convex-Poincaré-inequality says that $Var(f(X)) <= EE[norm(nabla f(X))^2] <= 1$.
#theorem[
    Let $f: [0, 1]^n -> RR$ be separately convex and $1$-Lipschitz. Let $Z = f(X_1, ..., X_n)$ where $X_1, ..., X_n$ are independent and are supported on $[0, 1]$. Then for all $t > 0$, $
        PP(Z - EE[Z] >= t) <= e^(-t^2 \/ 2),
    $ so $Z - EE[Z]$ has a sub-Gaussian right tail.
]<thm:convex-concentration-inequality>
#proofhints[
    - You may assume the partial derivatives of $f$ exist.
    - Find an appropriate upper bound for $sum_(i = 1)^n (f(X) - f(X'_((i))))^2$, where $X'_((i)) = (X_(1:(i - 1)), X'_i, X_((i + 1):n))$ and $X'_i$ is the value for which the infimum is achieved (why is the infimum achieved?).
    - Conclude using @thm:relaxed-bounded-differences.
]
#proof[
    We may assume the partial derivatives of $f$ exist (by approximating $f$ as a sequence of differentiable functions if necessary). By @thm:relaxed-bounded-differences, it is enough to show that $sum_(i = 1)^n (Z - Z_i)^2 <= 1$, where $Z_i = inf_(x'_i) f(X_(1:(i - 1)), x'_i, X_((i + 1):n))$. We have $
        sum_(i = 1)^n (Z - Z_i)^2 = sum_(i = 1)^n (f(X) - f(X'_((i))))^2,
    $ where $X'_((i)) = (X_(1:(i - 1)), X'_i, X_((i + 1):n))$ and $X'_i$ is the value for which the infimum is achieved. (The infimum is achieved since $f$ is continuous and $[0, 1]$ is compact) By convexity and the fact that $X'_i$ is a minimiser (so $f(X'_((i))) <= f(X)$), $
        sum_(i = 1)^n (f(X) - f(X'_((i))))^2 <= & sum_(i = 1)^n (X_i - X'_i)^2 (diff / (diff x_i) f(X))^2 \
        <= & sum_(i = 1)^n (diff / (diff x_i) f(X))^2 \
        = & norm(nabla f(X))^2 <= 1
    $ since $f$ is $1$-Lipschitz.
]
#remark[
    The proof wouldn't work for a left-tail bound, since $-f$ is concave not convex. The entropy method does not seem to give a left tail.
]
#remark[
    The naive bound using just the Lipschitz-ness of $f$ would give $sum_(i = 1)^n (Z - Z_i)^2 <= n$, so convexity gives a big improvement.
]


= The transport method

#definition[
    Let $Omega$ be a countable set and $cal(A)$ be a collection of subsets of $Omega$ which is a $sigma$-algebra. A *probability space* is $(Omega, cal(A), P)$, where $P$ is a probability measure.
]<def:probability-space>
#definition[
    A *real-valued RV* $Z$ is a map $Omega -> RR$.
    We define $
        PP(Z in A) = sum_(omega in Omega: Z(omega) in A) P(omega)
    $ for $A subset.eq RR$. We define $EE[Z] = sum_(omega in Omega) P(omega) Z(omega)$. If $Q << P$, write $EE_Q [Z] = sum_(omega in Omega) Q(omega) Z(omega)$.
]<def:real-valued-rv>
#theorem("Variational Representation for log-MGF and Relative Entropy")[
    Let $(Omega, A, P)$ be a countable probability space and $Z$ be a random variable with $EE[abs(Z)] < oo$. Then $
        log EE[e^Z] = log EE_P [e^Z] = sup_(Q << P) (EE_Q [Z] - D(Q || P))
    $ where the supremum is taken over all probability measures $Q$ that are absolutely continuous with respect to $P$ such that $EE_Q [abs(Z)] < oo$.

    Conversely, fix $Q << P$. Then $
        D(Q || P) = sup_Z (EE_Q Z - log EE_P [e^Z]),
    $ where the supremum is over all RVs $Z$ such that $EE_P [abs(Z)], EE_Q [abs(Z)] < oo$.
]<thm:variational-formulae-for-log-mgf-and-relative-entropy>
#proofhints[
    - For first statement, define $
        Q^* (omega) = (e^(Z(omega)) P(omega))/(EE_P [e^Z])
    $ and show that $D(Q || P) + log EE_P [e^Z] - EE_Q [Z] = D(Q || Q^*)$.
    - For second statement, show that $D(Q || P) >= EE_Q [Z] - log EE[e^Z]$ for any $Q << P$ and $Z$, with equality if $Z(omega) = log Q(omega)/P(omega)$.
]
#proof[
    // Assume first that $EE[abs(Z) e^Z] < oo$. // TODO: why assume EE[abs(Z) e^Z] < oo and not EE[e^Z] < oo?
    Define $ 
        Q^* (omega) = (e^(Z(omega)) P(omega))/(EE_P [e^Z]).
    $ Note that $Q^*$ is a valid PMF. For any $Q << P$ such that $EE_Q [abs(Z)] < oo$, we have $
        0 & <= D(Q || Q^*) \
        & = EE_(Y sim Q) [log Q(Y)/(Q^* (Y))] \
        & = EE_(Y sim Q) [log (Q(Y)/P(Y) P(Y)/(Q^* (Y)))] \
        & = EE_(Y sim Q) [log Q(Y)/P(Y)] + EE_Q [log (P(Y) EE_(Z sim P) [e^Z])/(P(Y) e^Z)] \
        & = D(Q || P) + log EE_P [e^Z] - EE_Q [Z]
    $ Hence $log EE[e^Z] >= EE_Q Z - D(Q || P)$, with equality iff $Q = Q^*$. The result follows since $Q^* << P$.
    // If $EE[abs(Z) e^Z] = oo$, we can take $
    //     Q_n (omega) = (e^(Z(omega)) P(omega) II_{abs(Z(omega)) <= n})/EE[e^Z; abs(Z) <= n]
    // $
    For the second statement, note that $D(Q || P) >= EE_Q [Z] - log EE[e^Z]$, for any $Q << P$ and $Z$. There is equality if $Z(omega) = log Q(omega)/P(omega)$.
    (Note that $EE_Q [abs(Z)] = EE_Q [abs(log Q/P)] < oo$ since $D(Q || P) < oo$ and the negative part of $x log x$ is finitely bounded.)
    // If $D(Q || P) = oo$, set $
    //     Z_n (omega) = min{(log Q(omega)/P(omega))_+, n},
    // $ and take $n -> oo$.
    // 
    Note it can be shown that the result holds when $D(Q || P) = oo$ and when $EE_P [e^Z] = oo$.
]
#corollary[
    For all $lambda in RR$, we have $
        log EE_P [e^(lambda (Z - EE_P [Z]))] = sup_(Q << P) (lambda(EE_Q Z - EE_P Z) - D(Q || P))
    $
]<crl:variational-formulae-for-log-mgf>
#theorem("Marton's Argument")[
    Let $P$ be a PMF and $Z sim P$. If there exists $nu > 0$ such that $
        EE_Q [Z] - EE_P [Z] <= sqrt(2 nu D(Q || P))
    $ for all PMFs $Q$ such that $Q << P$, then $
        psi_(Z - EE[Z])(lambda) = log EE_P [e^(lambda(Z - EE_P [Z]))] <= (lambda^2 nu)/2 quad forall lambda > 0,
    $ (and so also $PP(Z - EE[Z] >= t) <= e^(-t^2 \/ 2nu)$ by the @prop:chernoff-bound). Conversely, if there exists $nu > 0$ such that $psi_(Z - EE[Z])(lambda) =  log EE_P [e^(lambda(Z - EE_P [Z]))] <= (lambda^2 nu)/2$ for all $lambda > 0$, then $
        EE_Q [Z] - EE_P [Z] <= sqrt(2 nu D(Q || P))
    $ for all $Q << P$.
]<thm:martons-argument>
#proofhints[
    - Show that $log EE_P [e^(lambda(Z - EE[Z]))] <= sup_(t >= 0) (lambda sqrt(2 nu t) - t)$.
    - For converse, may assume that $EE_Q [Z] - EE_P [Z] >= 0$ (why?). The proof is similar to the first proof.
]
#proof[
    By the @thm:variational-formulae-for-log-mgf-and-relative-entropy, $
        log EE_P [e^(lambda(Z - EE[Z]))] & = sup_(Q << P) (lambda (EE_Q [Z] - EE_P [Z]) - D(Q || P)) \
        & <= sup_(Q << P) (lambda sqrt(2 nu D(Q || P)) - D(Q || P)) \
        & <= sup_(t >= 0) (lambda sqrt(2 nu t) - t).
    $ Let $f(t) = lambda sqrt(2 nu t) - t$. Then $f'(t) = 0$ iff $t = (lambda^2 nu)/2$, and so the $sup_(t >= 0) f(t) = (lambda^2 nu)/2$.

    For the converse, we may assume that $EE_Q [Z] - EE_P [Z] >= 0$, since otherwise we are trivially done. By @thm:variational-formulae-for-log-mgf-and-relative-entropy, for all $lambda > 0$, $
        D(Q || P) >= lambda (EE_Q [Z] - EE_P [Z]) - log EE_P e^(lambda (Z - EE_P [Z])) >= lambda (EE_Q [Z] - EE_P [Z]) - (lambda^2 nu)/2
    $ Taking the supremum over $lambda > 0$, we obtain $
        D(Q || P) >= sup_(lambda > 0) (lambda (EE_Q [Z] - EE_P [Z]) - (lambda^2 nu)/2)
    $ Differentiating the RHS, we see that it is maximised when $lambda = 1/nu (EE_Q [Z] - EE_P [Z])$, and so $
        D(Q || P) >= (EE_Q [Z] - EE_P [Z])^2 / (2nu).
    $
]

== Concentration via Marton's argument

#definition[
    Let $P, Q$ be distributions on $A$. Let $X sim P$ and $Y sim Q$. A *coupling* $pi$ is a joint distribution on $(X, Y)$ such that $X$ has marginal $P$ (w.r.t $pi$) and $Y$ has marginal $Q$ (w.r.t. $pi$). Write $Pi(P, Q)$ for the set of all couplings.
]<def:coupling>
#example[
    $P times.circle Q$ is the independent coupling.
]
#lemma[
    $f: A^n -> RR$ such that $f(y) - f(x) <= sum_(i = 1)^n c_i d(x_i, y_i)$ for some constants $c_i$ and distance $d(dot, dot)$. Let $X sim P_1 times.circle cdots times.circle P_n =: P$, $Z = f(X)$. Let $C > 0$ be such that $
        inf_(pi in Pi(P, Q)) sum_(i = 1)^n EE_pi [d(X_i, Y_i)]^2 <= 2 C D(Q || P).
    $ for all $Q << P$. Then $
        PP(Z - EE[Z] >= t) <= e^(-t^2 \/ 2 nu),
    $ where $nu = C sum_(i = 1)^n c_i^2$.
]<lem:concentration-via-marton>
#proofhints[
    Let $Q << P$ and $Y sim Q$. Show that $
        EE_Q [Z] - EE_P [Z] <= (sum_(i = 1)^n c_i^2)^(1 \/ 2) (sum_(i = 1)^n EE_pi [d(X_i, Y_i)]^2)^(1 \/ 2),
    $ and conclude the result using @thm:martons-argument.
]
#proof[
    Let $Q << P$ and $Y sim Q$. Then $
        EE_Q [Z] - EE_P [Z] & = EE[f(Y)] - EE[f(X)] \
        & = EE_pi [f(Y) - f(X)] quad "for all" pi in Pi(P, Q) \
        & <= EE_pi [sum_(i = 1)^n c_i d(X_i, Y_i)] \
        & = sum_(i = 1)^n c_i EE_pi [d(X_i, Y_i)] \
        & <= (sum_(i = 1)^n c_i^2)^(1 \/ 2) (sum_(i = 1)^n EE_pi [d(X_i, Y_i)]^2)^(1 \/ 2) quad "by Cauchy-Schwarz"
    $ So $
        EE_Q [Z] - EE_P [Z] <= (sum_(i = 1)^n c_i^2)^(1 \/ 2) (inf_(pi in Pi(P, Q)) sum_(i = 1)^n EE_pi [d(X_i, Y_i)]^2)^(1 \/ 2)
    $ Since $
        inf_(pi in Pi(P, Q)) sum_(i = 1)^n EE_pi [d(X_i, Y_i)]^2 <= 2 C D(Q || P)
    $ we have $EE_Q [Z] - EE_P [Z] <= sqrt(2 nu D(Q || P))$, where $nu = C sum_(i = 1)^n c_i^2$. The result follows by @thm:martons-argument.
]
#definition[
    Let $X sim P$ and $Y sim Q$. The *transportation cost* from $Q$ to $P$ w.r.t a distance $d(dot, dot)$ is $
        inf_(pi in Pi(P, Q)) EE_pi [d(X, Y)].
    $
]<def:transportation-cost>
#definition[
    Let $P$ and $Q$ be distributions on the same space $(Omega, cal(A))$. The *total variation distance* between $P$ and $Q$ is $
        d_"TV" (P, Q) := sup_(A in cal(A)) abs(P(A) - Q(A)).
    $
]<def:total-variation-distance>
#proposition[
    Let $A^* = {omega in Omega: P(omega) >= Q(omega)}.$ We have the alternative expressions $
        d_"TV" (P, Q) & = 1/2 sum_(omega in Omega) abs(P(omega) - Q(omega)) = sum_(omega in Omega) (P(omega) - Q(omega))_+ \
        & = P(A^*) - Q(A^*) = 1 - sum_(omega in Omega) min{P(omega), Q(omega)}.
    $
]<prop:expressions-for-total-variation-distance>
#proofhints[
    - For second equality, consider the $+$ and $-$ parts.
    - For the first equality, show $<=$ by splitting sum over $A$ and $A^c$ for $A in cal(A)$, show $>=$ by considering $A^* = {omega: P(omega) >= Q(omega)}$.
    - For the third equality, show the fourth expression is equal to the third.
]
#proof[
    For the first inequality: for any $A in cal(A)$, by the triangle inequality, $
        sum_(omega in Omega) abs(P(omega) - Q(omega)) & = sum_(omega in A) abs(P(omega) - Q(omega)) + sum_(omega in A^c) abs(P(omega) - Q(omega)) \
        & >= P(A) - Q(A) + Q(A^c) - P(A^c) = 2(P(A) - Q(A))
    $ and similarly $sum_(omega in Omega) abs(P(omega) - Q(omega)) >= 2(Q(A) - P(A))$. Conversely, $
        d_"TV" (P, Q) & >= P(A^*) - Q(A^*) \
        & = sum_(omega in Omega) (P(omega) - Q(omega))_+
        & = 1/2 sum_(omega in Omega) abs(P(omega) - Q(omega)),
    $ since $sum_(omega in Omega) (P(omega) - Q(omega))^+ = sum_(omega in Omega) (P(omega) - Q(omega))_-$. For the third inequality, $
        1 - sum_(omega in Omega) min{P(omega), Q(omega)} & = sum_(omega in Omega) P(omega) - min{P(omega), Q(omega)} \
        & = sum_(omega in Omega) (P(omega) - Q(omega))_+
    $
]
#lemma[
    Let $P$ and $Q$ be distributions on the same space. Then if $X sim P$ and $Y sim Q$, $
        inf_(pi in Pi(P, Q)) PP_pi (X != Y) = d_"TV" (P, Q) in [0, 1].
    $
]<lem:expression-for-total-variation-distance-in-terms-of-couplings>
#proofhints[
    Show that LHS $>=$ RHS by taking a supremum and infimum and using that $abs(indicator({x in A}) - indicator({Y in A})) <= indicator({X != Y})$, then consider $
        pi(omega_1, omega_2) = cases(
            min{P(omega), Q(omega)} quad & "if" omega_1 = omega_2 = omega,
            1/(d_"TV" (P, Q)) (P(omega_1) - Q(omega_1)) (Q(omega_2) - P(omega_2)) quad & "if" (omega_1, omega_2) in A^* times (A^*)^c,
            0 quad & "otherwise".
        )
    $
]
#proof[
    Let $pi in Pi(P, Q)$ and $A in cal(A)$. Since $abs(II_{X in A} - II_({Y in A})) <= II_({X != Y})$ We have $
        abs(P(A) - Q(A)) & = abs(EE_pi [II_({X in A}) - II_({Y in A})]) \
        & <= EE_pi [abs(II_{X in A} - II_({Y in A}))] \
        & <= EE[II_({X != Y})] quad "pointwise" \
        & = PP(X != Y).
    $ Taking the supremum over all $A in cal(A)$ and the infimum over all couplings gives $d_"TV" (P, Q) <= inf_(pi in Pi(P, Q)) PP(X != Y)$. We will construct $pi$ such that $PP(X != Y) = d_"TV" (P, Q)$. Intuitively, we want to place as much mass as possible on the "diagonal", i.e. make $pi(omega, omega)$ as large as possible.

    For $(omega_1, omega_2) in Omega times Omega$, let $
        pi(omega_1, omega_2) = cases(
            min{P(omega), Q(omega)} quad & "if" omega_1 = omega_2 = omega,
            1/(d_"TV" (P, Q)) (P(omega_1) - Q(omega_1)) (Q(omega_2) - P(omega_2)) quad & "if" (omega_1, omega_2) in A^* times (A^*)^c,
            0 quad & "otherwise".
        )
    $ Clearly, $PP_pi (X = Y) = sum_(omega in Omega) pi(omega, omega) = sum_(omega in Omega) min{P(omega), Q(omega)}$, and so by @prop:expressions-for-total-variation-distance, $PP_pi (X != Y) = 1 - sum_(omega in Omega) min{P(omega), Q(omega)} = d_"TV" (P, Q)$. Also, $pi$ is indeed a valid coupling: $
        sum_(omega_1 in Omega) pi(omega_1, omega_2) & = sum_(omega_1 in A^*) (P(omega_1) - Q(omega_1)) (Q(omega_2) - P(omega_2))/(d_"TV" (P, Q)) II_({omega_2 in (A^*)^c}) + min{P(omega_2), Q(omega_2)} \
        & = Q(omega_2),
    $ and similarly $sum_(omega_2 in Omega) pi(omega_1, omega_2) = P(omega_1)$.
]
#definition[
    The minimising coupling $
        pi(omega_1, omega_2) = cases(
            min{P(omega), Q(omega)} quad & "if" omega_1 = omega_2 = omega,
            1/(d_"TV" (P, Q)) (P(omega_1) - Q(omega_1)) (Q(omega_2) - P(omega_2)) quad & "if" (omega_1, omega_2) in A^* times (A^*)^c,
            0 quad & "otherwise".
        )
    $ in the proof of @lem:expression-for-total-variation-distance-in-terms-of-couplings is called the *optimal total variation coupling*.
]<def:optimal-total-variation-coupling>
#lemma("Pinsker's Inequality")[
    Let $P$ and $Q$ be PMFs such that $Q << P$. Then $
        d_"TV" (P, Q)^2 <= 1/2 D(Q || P).
    $
]<lem:pinskers-inequality>
#proofhints[
    Let $Y(omega) = Q(omega)/P(omega)$ and $Z = II_({Y >= 1})$. Use @lem:hoeffding and @thm:martons-argument.
]
#proof[
    Let $Y(omega) = Q(omega)/P(omega)$. Let $Z = II_({Y >= 1})$. By @lem:hoeffding, $
        psi_(Z - EE[Z])(lambda) <= lambda^2 / 8.
    $ But then by @thm:martons-argument, $
        EE_Q [Z] - EE_P [Z] <= sqrt(2 dot 1/4 dot D(Q || P)),
    $ i.e. $d_"TV" (P, Q) = Q(A) - P(A) <= sqrt(1/2 dot D(Q || P))$, where $A = {omega in Omega: Q(omega) >= P(omega)}$, by @prop:expressions-for-total-variation-distance.
]
#theorem("Marton's Transport Cost Inequality")[
    Let $P = P_1 times.circle cdots times.circle P_n$ and $Q << P$. Let $X sim P$ and $Y sim Q$. Then $
        inf_(pi in Pi(P, Q)) sum_(i = 1)^n EE_pi [II_{X_i != Y_i}]^2 = inf_(pi in Pi(P, Q)) sum_(i = 1)^n PP_pi (X_i != Y_i)^2 <= 1/2 D(Q || P).
    $
]<thm:martons-transport-cost-inequality>
// #proofhints[
//     - Use induction on $n$, $n = 1$ case is straightforward.
//     - Assume that for every $n <= k$, there exists a coupling $pi_n$ on $(X_(1:n), Y_(1:n))$ such that $sum_(i = 1)^n PP(X_i != Y_i)^2 <= 1/2 D(Q || P)$.
//     - Let $pi_(k + 1)(x_(1:(k + 1)), y_(1:(k + 1))) = pi_k (x_(1:k), y_(1:k)) dot pi_(y_(1:k))(x_(k + 1), y_(k + 1))$.
// ]
#proof[ // TODO: I'm not comfortable with most of this proof
    We use induction on $n$. The $n = 1$ case follows from @lem:expression-for-total-variation-distance-in-terms-of-couplings and @lem:pinskers-inequality. Assume that for every $n <= k$, there exists a coupling $pi_n$ on $(X_(1:n), Y_(1:n))$ such that $sum_(i = 1)^n PP(X_i != Y_i)^2 <= 1/2 D(Q || P)$. We will extend it to a coupling $pi_(k + 1)$ on $(X_(1:(k + 1)), Y_(1:(k + 1)))$. Write $
        sum_(i = 1)^(k + 1) PP(X_i != Y_i)^2 = sum_(i = 1)^k PP(X_i != Y_i)^2 + PP(X_(k + 1) != Y_(k + 1))^2
    $ For fixed $y_(1:k)$, let $pi_(y_(1:k)) in Pi(P_(X_(k + 1)), Q_(Y_(k + 1) | Y_(1:k) = y_(1:k)))$ be the optimal total variation coupling of $X_(k + 1)$ and $Y_(k + 1) | Y_(1:k) = y_(1:k)$.
    Define $
        pi_(k + 1)(x_(1:(k + 1)), y_(1:(k + 1))) & := pi_k (x_(1:k), y_(1:k)) dot pi_(y_(1:k))(x_(k + 1), y_(k + 1)) \
        & = PP(X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k)) PP(X_(k + 1) = x_(k + 1)) PP(Y_(k + 1) = y_(k + 1) | X_(k + 1) = x_(k + 1))
    $ This new coupling has two properties: // TODO: not quite sure why these both hold
    + Given $(X_(1:k), Y_(1:k))$, the distribution of $(X_(k + 1), Y_(k + 1))$ depends only on $Y_(1:k)$, i.e. $X_(1:k) - Y_(1:k) - (X_(k + 1), Y_(k + 1))$ form a Markov chain.
    + Also, $X_(k + 1)$ is independent of $(X_(1:k), Y_(1:k))$.
    These properties imply that $(X_(k + 1), Y_(k + 1))| X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k) sim pi_(y_(1:k))$. // TODO: also not sure why this follows
    Hence, $
        PP(X_(k + 1) != Y_(k + 1) | X_(1:k) & = x_(1:k), Y_(1:k) = y_(1:k)) = d_"TV" (P_(X_(k + 1)), Q_(Y_(k + 1) | Y_(1:k) = y_(1:k))) \
        & <= sqrt(1/2 D(Q_(Y_(k + 1) | Y_(1:k) = y_(1:k)) || P_(X_(k + 1))))
    $ by the $n = 1$ result. Taking expectation over $pi_k$ on the LHS gives $
        PP(X_(k + 1) != Y_(k + 1)) & = EE_(pi_k) [PP(X_(k + 1) != Y_(k + 1) | X_(1:k), Y_(1:k))] \
        & <= EE_(Q_(Y_(1:k)))[sqrt(1/2 D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1))))]
    $ Squaring and using Jensen's inequality gives $
        PP(X_(k + 1) != Y_(k + 1))^2 & <= 1/2 EE_(Q_(Y_(1:k))) [D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)))] \
        & = 1/2 D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)) | Q_(Y_(1:k)))
    $ By the induction hypothesis, $
        sum_(i = 1)^(k + 1) PP(X_1 != Y_i)^2 & <= 1/2 (D(Q_(Y_(1:k)) || P_(X_(1:k))) + D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)) | Q_(Y_(1:k)))) \
        & = 1/2 D(Q_(Y_(1:(k + 1))) || P_(X_(1:(k + 1))))
    $ by the @prop:relative-entropy-chain-rule.
    // We have $
    //     & sum_(i = 1)^k PP(X_i != Y_i)^2 + PP(X_(k + 1) != Y_(k + 1))^2 \
    //     <= & 1/2 D(Q_(Y_(1:k)) || P_(X_(1:k))) + (EE[PP(X_(k + 1) != Y_(k + 1) | X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k))])^2 quad "by induction hypothesis"
    // $ For fixed $x_(1:k), y_(1:k)$, $
    //     PP(X_(k + 1) != Y_(k + 1) | X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k))^2 <= 1/2 D(Q_(Y_(k + 1) | Y_(1:k) = y_(1:k)) || P_(X_(k + 1)))
    // $ So by Jensen, $
    //     PP(X_(k + 1) != Y_(k + 1))^2 & <= EE[PP(X_(k + 1) != Y_(k + 1) | X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k))^2] \
    //     & = 1/2 EE[D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)))] \
    //     & = 1/2 D(Q_(Y_(k + 1) | Y_(1:k)) | P_(X_(k + 1)) | Q_(Y_(1:k)))
    // $
]
#remark[
    We can recover the @thm:bounded-differences-inequality from @thm:martons-transport-cost-inequality: the conditions of @lem:concentration-via-marton are satisfied with $C = 1/4$, since $f$ having bounded differences with constant $c_i$ implies $
        f(y) - f(x) <= sum_(i = 1)^n c_i d(x_i, y_i),
    $ where $d(x_i, y_i) = II_{x_i != y_i}$. This gives the concentration bound.
]

== Talagrand's inequality

#definition[
    *Marton's divergence* is $
        d_2^2 (Q, P) = EE_(X sim P) [(1 - Q(X)/P(X))_+^2] = sum_(omega: P(omega) > 0) (P(omega) - Q(omega))_+^2 / P(omega).
    $
]<def:martons-divergence>
#lemma[
    Let $P$ and $Q$ be distributions on the same space $(Omega, cal(A))$. Then $
        inf_(pi in Pi(P, Q)) EE_((X, Y) sim pi) [PP(X != Y | X)^2] = d_2^2 (Q, P).
    $
]<lem:infimum-expression-for-marton-divergence>
#proofhints[
    - For $>=$, explain why $PP(X = Y | X = x) <= min{1, Q(x) \/ P(x)}$, then take expectation.
    - Showing equality, by showing that the optimal total variation coupling minimises the LHS, is left as an exercise.
]
#proof[
    We have $
        PP(X = Y | X = x) = PP(X = x, Y = x) / PP(X = x) <= min{1, Q(x)/P(x)}.
    $ So for any coupling $pi$, $
        EE_pi [PP(X != Y | X)^2] >= EE_P [(1 - min{1, Q(X)/P(X)})^2] = EE_P [(1 - Q(X)/P(X))_+^2] = d_2^2 (Q, P).
    $ Showing equality is left as an exercise.
]
#lemma("Pinsker's Inequality for Marton Divergence")[
    Let $P, Q$ be distributions on the same space $(Omega, A)$ with $Q << P$. Then $
        d_2^2 (Q, P) <= 2 D(Q || P).
    $
]<lem:pinskers-inequality-for-marton-divergence>
#proofhints[
    - Let $h(t) = (1 - t) log(1 - t) + t$ for $t <= 1$, expression $D(Q || P)$ using $h$ (as an expectation w.r.t $P$).
    - Show that $h(t) >= 0$ and by considering derivatives, show that $h(t) >= t^2 \/ 2$ for all $t in [0, 1]$.
]
#proof[
    Let $h(t) = (1 - t) log(1 - t) + t$ for $t <= 1$ and $q(X) = Q(X)/P(X)$. Then $
        D(Q || P) = EE_(X sim P) [h(1 - q(X))].
    $ We have $h(t) = -(1 - t) log(1 + t/(1 - t)) + t >= -t + t >= 0$ since $log x <= x - 1$. Also, $h(t) >= t^2 \/ 2$ for $t in [0, 1]$: indeed, $h(0) = 0^2 \/ 2$, and $h'(t) = -1 - log(1 - t) + 1 = -log(1 - t)$, thus $
        dif / (dif t) (h(t) - t^2 / 2) = -log(1 - t) - t >= (1 - t) + 1 - t = 0.
    $ So we have $
        D(Q || P) & = EE[h(1 - q(X))] >= EE[h((1 - q(X))_+)] \
        & >= EE[(1 - q(X))_+^2 / 2] = 1/2 d_2^2 (Q, P).
    $ where first inequality is since $h >= 0$ and $h(0) = 0$.
]
#theorem("Marton's Conditional Transport Cost Inequality")[
    Let $X = (X_1, ..., X_n)$, $X sim P = P_1 times.circle cdots times.circle P_n$, and let $Q << P$. Then $
        inf_(pi in Pi(P, Q)) sum_(i = 1)^n EE_pi [PP(X_i != Y_i | X)^2] <= 2 D(Q || P).
    $
]<thm:martons-conditional-transport-cost-inequality>
#proof[
    We use induction on $n$. The $n = 1$ case follows by @lem:infimum-expression-for-marton-divergence and @lem:pinskers-inequality-for-marton-divergence. Now assume that for every $n <= k$, there exists a $pi_n in Pi(P, Q)$ such that $sum_(i = 1)^n EE_(pi_n)[PP(X_i != Y_i | X)^2] <= 2 D(Q_(X_(1:n)) || P_(X_(1:n)))$. We will find a coupling $pi_(k + 1)$ (extended from $pi_k$) such that $
        sum_(i = 1)^k EE_(pi_(k + 1))[PP(X_i != Y_i | X_(1:(k + 1)))^2] + EE_(pi_(k + 1))[PP(X_(k + 1) != Y_(k + 1) | X_(1:(k + 1)))^2] & = sum_(i = 1)^(k + 1) EE_(pi_(k + 1))[PP(X_i != Y_i | X_(1:(k + 1)))^2] \
        & <= D(Q_(Y_(1:(k + 1))) || P_(X_(1:(k + 1))))
    $ For fixed $y_(1:k)$, let $pi_(y_(1:k))$ be the optimal total variation coupling of $X_(k + 1)$ and $Y_(k + 1) | Y_(1:k) = y_(1:k)$. Let $
        pi_(k + 1)(x_(1:(k + 1)), y_(1:(k + 1))) & = pi_k (x_(1:k), y_(1:k)) dot pi_(y_(1:k)) (x_(k + 1), y_(k + 1)) \
        & = PP(X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k)) dot PP(X_(k + 1) = x_(k + 1)) dot PP(Y_(k + 1) = y_(k + 1) | X_(k + 1) = x_(k + 1)),
    $ where the probabilities in the last line are w.r.t. the new coupling $pi_(k + 1)$. This coupling has two properties:
    - $X_(1:k) - Y_(1:k) - (X_(k + 1), Y_(k + 1))$ form a Markov chain, i.e. given $(X_(1:k), Y_(1:k))$, the distribution of $(X_(k + 1), Y_(k + 1))$ only depends on $Y_(1:k)$.
    - $X_(k + 1)$ is independent of $(X_(1:k), Y_(1:k))$.
    These properties imply that given $X_(1:k) = x_(1:k), Y_(1:k) = y_(1:k)$, we have $(X_(k + 1), Y_(k + 1)) sim pi_(y_(1:k))$.
    By the induction hypothesis, $
        sum_(i = 1)^k EE_(pi_(k + 1)) [PP(X_i != Y_i | X_(1:(k + 1)))^2] & = sum_(i = 1)^k EE_(pi_(k + 1)) [PP(X_i != Y_i | X_(1:k))^2] "by second property" \
        & = sum_(i = 1)^k EE_(pi_k) [PP(X_i != Y_i | X_(1:k))^2] \
        & <= 2 D(Q_(Y_(1:k)) || P_(X_(1:k))).
    $ We want to show $
        EE[PP(X_(k + 1) != Y_(k + 1) | X_(1:(k + 1)))^2] <= 2 D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)) | Q_(Y_(1:k)))
    $ From the $n = 1$ case (and since the optimal total variation coupling $pi_(y_(1:k))$ is a minimiser in @lem:infimum-expression-for-marton-divergence), we know that $
        EE_(pi_(y_(1:k))) [PP(X_(k + 1) != Y_(k + 1) | X_(k + 1), Y_(1:k) = y_(1:k))^2] <= 2 D(Q_(Y_(k + 1) | Y_(1:k) = y_(1:k)) || P_(X_(k + 1))).
    $ By the two properties of $pi_(k + 1)$, $
        PP(X_(k + 1) != Y_(k + 1) | X_(k + 1), Y_(1:k) = y_(1:k)) = PP(X_(k + 1) != Y_(k + 1) | X_(1:(k + 1)), Y_(1:k) = y_(1:k))
    $ Taking $EE_(Y_(1:k))(dot)$ in the above, we obtain $
        EE [PP(X_(k + 1) != Y_(k + 1) | X_(1:(k + 1)), Y_(1:k))^2] & = EE [PP(X_(k + 1) != Y_(k + 1) | X_(k + 1), Y_(k + 1))^2] \
        & <= 2 D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)) | Q_(Y_(1:k)))
    $ The LHS is equal to $
        & EE EE[EE[II_({X_(k + 1) != Y_(k + 1)}) | X_(1:(k + 1)), Y_(1:k)]^2 | X_(1:(k + 1))] \
        & >= EE EE[EE[II_({X_(k + 1) != Y_(k + 1)}) | X_(1:(k + 1)), Y_(1:k)] | X_(1:(k + 1))]^2 quad "by Jensen" \
        & = EE EE[II_({X_(k + 1) != Y_(k + 1)}) | X_(1:(k + 1))]^2 quad "by tower property" \
        & = EE PP(X_(k + 1) != Y_(k + 1) | X_(1:(k + 1)))^2
    $ So $
        & sum_(i = 1)^k EE PP(X_i != Y_i | X_(1:(k + 1)))^2 + EE PP(X_(k + 1) != Y_(k + 1) | X_(1:k))^2 \
        <= & 2 D(Q_(Y_(1:k)) || P_(X_(1:k))) + 2 D(Q_(Y_(k + 1) | Y_(1:k)) || P_(X_(k + 1)) | Q_(Y_(1:k))) \
        = & 2 D(Q || P)
    $ by the @prop:relative-entropy-chain-rule.
]
#definition[
    $f: A^n -> RR$ satisfies the *one-sided bounded differences* property if $
        f(y) - f(x) <= sum_(i = 1)^n II_({x_i != y_i}) c_i (x) quad forall x, y in A^n,
    $ where $c_i: A^n -> RR_(>= 0)$.
]<def:one-sided-bounded-differences>
#remark[
    We can't apply results for bounded differences on functions with this property, since it is a weaker property.
]
#remark[
    By @thm:relaxed-bounded-differences, if $sum_(i = 1)^n (Z_i - Z)^2 <= nu$, where $Z_i = sup_(x_i) f(X_(1:(i - 1)), x_i, X_((i + 1):n))$, then $PP(Z - EE[Z] <= -t) <= e^(-t^2 \/ 2 nu)$. Under one-sided bounded differences, $
        0 <= sum_(i = 1)^n (Z_i - Z)^2 <= sum_(i = 1)^n c_i (X)^2 <= sup_(x in A^n) sum_(i = 1)^n c_i (x)^2 =: nu_oo,
    $ so we obtain the left-tail bound $PP(Z - EE[Z] <= -t) <= e^(-t^2 \/ 2 nu_oo)$. But now if $Z_i = inf_(x_i) f(X_(1:(i - 1)), x_i, X_((i + 1):n))$, with infimum achieved at $(X')^((i)) = (X_(1:(i - 1)), x'_i, X_((i + 1):n))$, then $
        0 <= sum_(i = 1)^n (Z - Z_i)^2 <= sum_(i = 1)^n c_i ((X')^((i)))^2.
    $ We generally can't say that this is $<= sup_(x in A^n) sum_(i = 1)^n c_i (x)^2$, so can't immediately deduce a right tail bound.

    However, the transport method gives us a right-tail bound with a better parameter $nu = EE[sum_(i = 1)^n c_i (X)^2] <= nu_oo$.
]
#theorem("Talagrand's One-sided Bounded Differences Inequality")[
    Let $X = (X_1, ..., X_n) sim P_1 times.circle cdots times.circle P_n$, $X_i$ independent. Let $f: A^n -> RR$ be a function with one-sided bounded differences with associated functions $c_i$. Let $Z = f(X)$ and let $nu = EE[sum_(i = 1)^n c_i (X)^2]$. Then $
        psi_(Z - EE[Z])(lambda) <= (lambda^2 nu)/2 quad forall lambda > 0
    $ which implies that $
        PP(Z - EE[Z] >= t) <= e^(-t^2 \/ 2nu) quad forall t > 0.
    $
]<thm:talagrands-inequality>
#proofhints[
    - For $Q << P$ and $pi in Pi(P, Q)$, show that, using @thm:law-of-total-expectation, $
        EE_Q [Z] - EE_P [Z] <= sum_(i = 1)^n EE_pi [c_i (X) PP(X_i != Y_i | X)],
    $ where $PP(X_i != Y_i | X) = EE_pi [II_({X_i != Y_i}) | X]$.
    - Apply Cauchy-Schwarz twice.
    - Conclude using @thm:martons-conditional-transport-cost-inequality and @thm:martons-argument.
]
#proof[
    Let $Q << P$. Then for all $pi in Pi(P, Q)$, $
        EE_Q [Z] - EE_P [Z] & = EE_pi [f(Y) - f(X)] \
        & <= EE_pi [sum_(i = 1)^n c_i (X) II_({X_i != Y_i})] quad "by assumption" \
        & = sum_(i = 1)^n EE_pi EE_pi [II_({X_i != Y_i}) c_i (X) | X] quad #[by @thm:law-of-total-expectation] \
        & = sum_(i = 1)^n EE_pi [c_i (X) PP(X_i != Y_i | X)] \
        & <= sum_(i = 1)^n (EE_pi [c_i (X)^2])^(1 \/ 2) (EE_pi [PP(X_i != Y_i | X)^2])^(1 \/ 2) quad "by Cauchy-Schwarz" \
        & <= (sum_(i = 1)^n EE_pi [c_i (X)^2])^(1 \/ 2) (sum_(i = 1)^n EE[PP(X_i != Y_i | X)^2])^(1 \/ 2) quad "by Cauchy-Schwarz"
    $ where we write $PP(X_i != Y_i | X) = EE_pi [II_({X_i != Y_i}) | X]$. By @thm:martons-conditional-transport-cost-inequality, $
        inf_(pi in Pi(P, Q)) sum_(i = 1)^n EE[PP(X_i != Y_i | X)^2] <= 2 D(Q || P).
    $ which implies that $
        EE_Q [Z] - EE_P [Z] <= sqrt(nu dot 2 dot D(Q || P)) 
    $ amd so by @thm:martons-argument, $psi_(Z - EE[Z])(lambda) <= (lambda^2 nu)/2$ for all $lambda > 0$, which gives the right tail bound by the @prop:chernoff-bound.
]

= Log-concave random variables

#definition[
    A continuous random variable $X in RR^n$ with density function $rho$ is *log-concave* if $log rho$ is concave, i.e. if $
        rho(lambda x + (1 - lambda) y) >= rho(x)^lambda rho(y)^(1 - lambda)
    $ for all $x, y in RR^n$ and $lambda in [0, 1]$.
]<def:log-concave-rv>
#definition[
    A *convex body* is a non-empty, convex, compact set. The *diameter* of a convex body $K$ is $"Diam"(K) = sup_(x, y in K) norm(x - y)_2$.
]<def:convex-body>
#example[
    The Gaussian $
        1/((2pi)^n det(Sigma)^(1 \/ 2)) e^(-(x Sigma^(-1) x) \/ 2),
    $ the exponential $alpha e^(-norm(x))$ and the uniform distribution on convex bodies are log-concave distributions.
]
#theorem("Log-concave Poincare inequality")[
    Let $X$ be log-concave, supported on a convex body $K subset.eq RR^n$. Then $X$ satisfies the Poincaré inequality with Poincaré constant $
        C_P (X) <= "Diam"(K)^2 dot C_n,
    $ for some absolute $C_n$ depending only on $n$; that is, $
        Var(f(X)) <= "Diam"(K)^2 dot C_n dot EE [norm(nabla f(X))^2],
    $ for all $f in C^1 (RR^n)$.
]<thm:poincare-inequality-for-log-concave-rvs>
#proof[
    WLOG $EE[f(X)] = 0$. We have $
        Var(f(X)) = 1/2 Var(f(X) - f(Y)) = 1/2 EE[(f(X) - f(Y))^2],
    $ where $Y$ is an independent copy of $X$. Hence, $
        Var(f(X)) & = 1/2 integral_(RR^n) integral_(RR^n) abs(f(y) - f(x))^2 rho(x) rho(y) dif x dif y \
        & = 1/2 integral_(RR^n) integral_(RR^n) abs(integral_([0, 1]) nabla f(t y + (1 - t) x) dot (y - x) dif t)^2 rho(x) rho(y) dif x dif y \
        & <= "Diam"(K)^2 / 2 integral_(RR^n) integral_(RR^n) integral_([0, 1]) norm(nabla f(t y + (1 - t) x))^2 dif t rho(x) rho(y) dif x dif y quad "by Cauchy-Schwarz" \
        & = "Diam"(K)^2 / 2 integral_([0, 1]) integral_(RR^n) integral_(RR^n) norm(nabla f(t y + (1 - t) x))^2 rho(x) rho(y) dif x dif y dif t
    $ First consider the case when $t approx 1/2$. We use the bound $min{rho(x), rho(y)} <= rho(t y + (1 - t) x)$ (due to concavity), which implies $
        rho(x) rho(y) & <= rho(t y + (1 - t) x) max{rho(x), rho(y)} \
        & <= rho(t y + (1 - t) x) (rho(x) + rho(y)).
    $ So $
        & integral_(RR^n) integral_(RR^n) norm(nabla f(t y + (1 - t) x))^2 rho(x) rho(y) dif x dif y \
        <= & integral_(RR^n) integral_(RR^n) norm(nabla f(t y + (1 - t) x))^2 rho(t y + (1 - t) x) (rho(x) + rho(y)) dif x dif y \
        <= & integral_(RR^n) integral_(RR^n) norm(nabla f(u))^2 rho(u) rho(x) (dif u dif x)/t^n + integral_(RR^n) integral_(RR^n) norm(nabla f(u))^2 rho(u) rho(y) (dif u)/(1 - t)^n dif y \
        = & (1/t^n + 1/(1 - t)^n) EE [norm(nabla f(X))^2].
    $ using the substitutions $t y + (1 - t) x = u$ (so $t^n dif y = dif u$), $t y + (1 - t) x = v$ (so $(1 - t)^n dif x = dif v$).

    In the case $t >> 1 \/ 2$ or $t << 1 \/ 2$, then $
        rho(x) rho(y) <= rho(t y + (1 - t) x) dot rho((1 - t) y + t x)
    $ hence $
        & integral_(RR^n) integral_(RR^n) norm(nabla f(t y + (1 - t) x))^2 rho(x) rho(y) dif x dif y \
        <= & integral_(RR^n) integral_(RR^n) norm(nabla f(t y + (1 - t) x))^2 rho(t y + (1 - t) x) rho((1 - t) y + t x) dif y dif x \
        = & integral_(RR^n) integral_(RR^n) norm(nabla f(u))^2 rho(u) rho(v) (dif u dif v) / abs(t^2 - (1 - t)^2)^n \
        = & 1/abs(t^2 - (1 - t)^2)^n EE[norm(nabla f(X))^2]
    $ since the map $(x, y) |-> (t x + (1 - t) y, (1 - t) x + t y)$ is represented by the matrix $mat(t, 1 - t; 1 - t, t)$ which has determinant $abs(t^2 - (1 - t)^2)$. So $dif x dif y = (dif u dif y)/abs(t^2 - (1 - t)^2)^n$.

    Combining these, we obtain $
        Var(f(X)) & <= "Diam"(K)^2 / 2 EE[norm(nabla f(X))^2] integral_([0, 1]) min{1/(t^n) + 1/((1 - t)^n), 1/abs(t^2 - (1 - t)^2)^n} dif t \
        & <= "Diam"(K)^2 / 2 C_n EE[norm(nabla f(X))^2].
    $
]
#remark[
    Let $X sim "Unif"(A)$, $A subset.eq RR^n$. The Poincaré constant $C_p (X)$ measures the *conductance* of $A$, which is large if $A$ has a bottleneck.
]

== One-dimensional log-concave random variables

#definition[
    Let $X$ be an RV on $RR$ with density function $f$. The *differential entropy* of $X$ is $
        h(X) = -integral_(-oo)^oo f(x) log f(x) dif x = EE[-log f(X)].
    $
]<def:differential-entropy>
#definition[
    Let $X, Y$ be an RVs on $RR$ with density functions $f, g$. The *differential relative entropy* of $X$ and $Y$ is $
        D(f || g) = D(X || Y) = integral_(-oo)^oo f(x) log f(x)/g(x) dif x = EE[log f(X)/g(X)] >= 0.
    $
]<def:differential-relative-entropy>
#lemma[
    Let $Y$ be an RV with density $f$ on $RR$ with variance $Var(Y) = sigma^2$. Let $Z sim N(EE[Y], sigma^2)$. Then $
        h(Y) <= h(Z) = 1/2 log (2pi e sigma^2).
    $ In other words, normally distributed random variables maximise differential entropy.
]<lem:normal-rvs-maximised-differential-entropy>
#proofhints[
    - Explain why we can assume $EE[Y] = 0$ WLOG.
    - Use non-negativity of differential relative entropy.
]
#proof[
    WLOG, $EE[Y] = 0$ (since entropy is invariant under constant shifts). Let $phi_(sigma^2)(x) := 1/sqrt(2pi sigma^2) e^(-x^2 \/ 2 sigma^2)$. We have $
        0 & <= D(f || phi_(sigma^2)) = integral_(-oo)^oo f(x) log f(x) dif x + 1/2 log(2pi sigma^2) + integral_(-oo)^oo x^2 / (2 sigma^2) f(x) dif x \
        & = -h(Y) + 1/2 log(2pi sigma^2) + 1/(2 sigma^2) EE[Y^2] \
        & = -h(Y) + 1/2 log(2pi sigma^2) + 1/2 = 1/2 log(2pi e sigma^2).
    $ It is straightforward to show that $h(Z) = 1/2 log(2pi e sigma^2)$.
]
#definition[
    A random variable $X$ is *isotropic* if $EE[X] = 0$ and $Var(X) = 1$.
]<def:isotropic>
#lemma[
    Let $X$ be log-concave and isotropic, with density function $rho$ on $RR$. Then $
        rho(0) >= 1/sqrt(2 pi e).
    $
]<lem:lower-bound-for-middle-density-of-log-concave-isotropic-rv>
#proofhints[
    Write $rho(0) = e^(log(rho(integral_(-oo)^oo rho(x) x dif x))$ and use log-concavity.
]
#proof[
    We have $
        rho(0) & = rho(integral_(-oo)^oo rho(x) x dif x) = e^(log rho(integral_(-oo)^oo rho(x) x dif x)) >= e^(integral_(-oo)^oo rho(x) log rho(x) dif x) \
        & = e^(-h(rho)) >= 1/sqrt(2 pi e),
    $ where the first inequality is by log-concavity (we use that $integral_(-oo)^oo rho(x) dif x = 1$), and the second is by @lem:normal-rvs-maximised-differential-entropy.
]
#remark[
    It can be shown that for log-concave $rho$, $max_x rho(x) <= c$ for some absolute constant $c$. So the above lemma says that $rho(0)$ and $max_x rho(x)$ are comparable.
]
#proposition[
    Let $X$ be log-concave, isotropic, with density function $rho$ on $RR$. Then for all $x >= 3 \/ rho(0)$, $
        rho(x) <= rho(0) e^(-rho(0)/3 log(2) x) <= e^(-x log(2) \/ (3 sqrt(2pi e)))
    $
]<prop:right-tail-upper-bound-for-densities-of-log-concave-isotropic-rv>
#proofhints[
    - Let $x_m$ denote the mode of $X$ (why is this unique?). Can assume WLOG that $x_m > 0$. WLOG, $x_m > 0$. Let $x_0 = 2/rho(0) + x_m$. Why is $x_0 >= x_m$?
    - By writing $1$ as an integral, show that $x_m <= 1 \/ rho(0)$ (justify using log-concavity).
    - Use the same idea to show that $rho(x_0) <= rho(0) \/ 2$.
    - For $x >= 3 \/ rho(0)$, write $x_0 = x_0 / x dot x + (1 - x_0 / x) dot 0$ (why is this a valid convex combination?). Use log-concavity and combine the above inequalities to obtain the result.
]
#proof[
    Write $x_m$ for the mode of $X$ (this is unique since $X$ is log-concave). WLOG, $x_m > 0$ (the proof is similar if $x_m < 0$).
    Define $x_0 := 2/rho(0) + x_m$. We have $x_0 >= x_m$ by @lem:lower-bound-for-middle-density-of-log-concave-isotropic-rv. First note that $
        1 = integral_(-oo)^oo rho(x) dif x >= integral_0^(x_m) rho(x) dif x >= x_m rho(0)
    $ by log-concavity. Hence, $x_m <= 1 \/ rho(0)$. Also, $
        1 = integral_(-oo)^oo rho(x) dif x >= integral_(x_m)^(x_0) rho(x) dif x >= rho(x_0)(x_0 - x_m) = rho(x_0) 2/rho(0)
    $ where the last inequality is because $rho$ has one mode (unimodal). Hence, $rho(x_0) <= rho(0) \/ 2$. So we have $x >= 3/rho(0) >= 2/rho(0) + x_m = x_0$, so we write $x_0 = x_0/x dot x + (1 - x_0/x) dot 0$. By log-concavity, $
        rho(x_0) >= rho(x)^(x_0 \/ x) dot rho(0)^(1 - x_0 \/ x).
    $ Exponentiating both sides by $x \/ x_0$, we get $
        rho(x) & <= rho(x_0)^(x \/ x_0) / rho(0)^(x \/ x_0 - 1) = rho(0) (rho(x_0)/rho(0))^(x \/ x_0) <= rho(0) (1/2)^(x \/ x_0) <= rho(0) 2^(-rho(0) x \/ 3) \
        & = rho(0) e^(-rho(0) log(2) x \/ 3).
    $ The final inequality is by @lem:lower-bound-for-middle-density-of-log-concave-isotropic-rv.
]
#remark[
    If $rho$ is log-concave and isotropic then so is $x |-> rho(-x)$, so we can obtain a left tail bound as well.
]
// TODO: exam comments:
/*
don't have to prove continuity of $psi_Z^* (lambda)$ or results on Taylor series of $EE[e^(lambda Z)]$, but may have to use these results

similarly for other sections, not expected to prove analytic properties of $psi$ and $psi^*$, but may have to use

otherwise, everything is examinable. (what we've proved is examinable, what we haven't is not)

the part on Markov chains _is_ examinable - but there won't be question on Markov chains, it would relate to Poincaré inequalities
|||?*/