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

Tower property of conditional expectation: $EE(EE(Z | X, Y) | Y) = EE(Z | Y)$.

= The Chernoff-Cramer method

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
#corollary("Chebyshev's Inequality")[
    For any RV $Y$ and $t > 0$, $
        PP(abs(Y - EE[Y]) >= t) <= Var(Y)/t^2.
    $
]<crl:chebyshevs-inequality>
#proofhints[
    Straightforward.
]
#proof[
    Take $Z = (Y - EE[Y])^2$ and use @thm:markovs-inequality.
]
#corollary[
    Let $phi: RR -> RR_+$ be non-decreasing, then $
        PP(phi(Y) >= phi(t)) <= EE[phi(Y)]/phi(t).
    $ For $phi(t) = t^2$, we can use $Var(sum_(i = 1)^n X_i) = sum_(i = 1)^n Var(X_i)$.
]<crl:generalised-markovs-inequality>
#exercise[
    Prove WLLN, assuming that $Var(X_1) < oo$, using Chebyshev's inequality.
]
#notation[
    For $lambda > 0$, let $phi_lambda (t) = e^(lambda t)$. Write $F(lambda) := EE[e^(lambda Z)] = sum_(k = 0)^oo (lambda^k EE[Z^k])/(k!)$, and let $phi_Z (lambda) = log(F(lambda))$.
    
    Note that $phi_Z (lambda)$ is additive: if $Z = sum_(i = 1)^n Z_i$, with $Z_1, ..., Z_n$ independent, then $
        phi_(Z) (lambda) = log(EE[e^(lambda Z)]) = sum_(i = 1)^n log EE[e^(lambda Z_i)] = sum_(i = 1)^n phi_(Z_i) (lambda).
    $
]
#definition[
    The *Cramer transform* of $Z$ is $
        phi_Z^* (t) = sup{lambda t - phi_Z (lambda): lambda > 0}.
    $
]<def:cramer-transform>
#proposition[
    Let $Z$ be an RV. For all $t > 0$, $
        PP(Z >= t) <= e^(-phi_Z^* (t)).
    $
]<prop:chernoff-bound>
#proof[
    We have $
        PP(Z >= t) = PP(e^(lambda Z) >= e^(lambda t)) <= EE[e^(lambda Z)]/(phi_lambda (t)) = e^(-(lambda t - phi_Z (lambda))).
    $ Taking the infimum over all $lambda > 0$ gives $PP(Z >= t) <= inf{e^(-(lambda t - phi_Z (lambda))): lambda > 0}$, which gives the result.
]
#remark[
    Our goal is to obtain an upper bound on $phi_Z (lambda)$, as this will give exponential concentration. The function $phi_(Z - EE[Z])(lambda)$ gives upper bounds on $PP(Z - EE[Z] >= t)$, the function $phi_(-Z + EE[Z])(lambda)$ gives upper bounds on $PP(Z - EE[Z] <= -t)$.
]
#proposition[
    + $phi_Z (lambda)$ is convex and infinitely differentiable on $(a, b)$, where $b = sup_(lambda > 0) {EE[e^(lambda Z)] < oo}$.
    + $phi_Z^* (t)$ is non-negative and convex.
    + If $t > EE[Z]$, then $phi_Z^* (t) = sup_(lambda in RR) {lambda t - phi_Z (lambda)}$, the *Fenchel-Legendre* dual.
]<prop:properties-of-phi-functions>