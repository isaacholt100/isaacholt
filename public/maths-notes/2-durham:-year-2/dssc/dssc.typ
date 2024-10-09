#import "../../template.typ": template
#show: template

= Introduction

- $29$
- By Central Limit Theorem, if sample $(x_1, ..., x_n)$ with each $X_i tilde.op D(mu, sigma^2)$ ($D$ is some distribution) then as $n -> oo$, $ overline(X) tilde.op N(mu, sigma^2 / n) $ So distribution of sample mean always tends to normal distribution, with standard deviation $sigma \/ sqrt(n)$.
- *Unbiased estimate of standard deviation of sample mean*: $ s = sqrt(1 / (n - 1) sum_(i = 1)^n (x_i - overline(x))^2) $
- *Standard error of sample mean*: estimate of standard deviation of sample mean: $s \/ sqrt(n)$.
- If $n$ too small then $s$ is poor estimator and mean may not be normally distributed.
- If population distribution is normal and $n$ small then sample mean is $t$-distributed: $ (X - mu) / (s \/ sqrt(n)) tilde.op t_(n - 1) $ $(X - mu) / (s \/ sqrt(n))$ is *pivotal quantity* as distribution doesn't depend on parameters of $X$.
- *Hypothesis test* for $underline(x)$:
	- Define *null hypothesis* which identifies distribution believed to have generated each $x_i$.
	- Choose *test statistic* $h$ (function of $underline(x)$), extreme when null is false, not extreme when null is true.
	- *Observed test statistic* is $t = h(underline(x))$.
	- Determine how extreme $t$ is as a realisation of $T = h(X_1, ..., X_N)$ (so need to know distribution of $T$).
- *One sided $p$-value*: $ PP(T >= t | H_0 "true") quad "or" quad PP(T <= t | H_0 "true") $
- *Two sided $p$-value*: $ PP(T >= |t| union T <= -|t| | H_0 "true") $

= Monte Carlo testing

- *Monte Carlo testing*: given observed test stat $t = h(underline(x))$, distribution $F(x | theta)$, hypotheses $H_0: theta = theta_0$, $H_1: theta > theta_0$:
	- For $j in {1, ..., N}$:
		- Simulate $n$ observations $(z_1, ..., z_n)$ from $F(dot.op | theta_0)$.
		- Compute $t_j = h(z_1, ..., z_n)$.
	- Estimate $p$-value by $ P(T >= t | H_0 "true") approx hat(p) = 1/N sum_(j = 1)^N II{t_j >= t} $
- *Resampling risk*: probability that Monte Carlo simulated $p$-value and true $p$-value are on different sides of significance threshold $alpha$ (situation where Monte Carlo test is incorrect): $ "resampling risk" = cases(
	PP(hat(p) > alpha) & "if" p <= alpha,
	PP(hat(p) <= alpha) & "if" p > alpha
) $

= The bootstrap

- *The non-parametric bootstrap estimate*: given independent data $underline(x) = (x_1, ..., x_n)$ and stat $S(dot.op)$, *resample* (draw samples of size $n$ with replacement) $underline(x)$ $B$ times to give $underline(x)^(* 1), ..., underline(x)^(* B)$. To compute *bootstrap estimate of standard error of $S$*, compute $ hat("Var")(S(underline(x))) = 1/(B - 1) sum_(b = 1)^B (S(underline(x)^(* b)) - overline(S)^*)^2 $ where $ overline(S)^* = 1/B sum_(b = 1)^B S(underline(x)^(* b)) $ The standard error estimate is then $sqrt(hat("Var")(S(underline(x))))$, i.e. the standard deviation of $S(underline(x)^(* 1)), ..., S(underline(x)^(* B))$ The *bootstrap estimate* of $S$ is simply $S(underline(x))$.
- For random variable $X$, *(cumulative) distribution function (cdf)* $F: RR -> [0, 1]$ is $ F_X(x) = F(x) := PP(X <= x) $
- Properties of cdf:
	- $lim_(x -> -oo) F(x) = 0$ and $lim_(x -> oo) F(x) = 1$.
	- *Monotonicity*: $x' < x ==> F(x') <= F(x)$.
	- *Right-continuity*: $lim_(t -> x^+) F(t) = F(x)$.
- Given data $(x_1, ..., x_n)$ with each sample i.i.d. realisation of random variable $X$, *empirical (cumulative) distribution function (ecdf)* is $ hat(F)(x) := 1/n sum_(i = 1)^n II{x_i <= x} $
- *Glivenko-Cantelli theorem*: Let $X_1, ..., X_n$ be random sample from distribution with cdf $F$. Then $ sup_(x in RR)|hat(F)(x) - F(x)| -> 0 quad "as" n -> oo $
- Given data $(x_1, ..., x_n)$, sampling uniformly at random from $underline(x)$ is equivalent to sampling from distribution with cdf defined as ecdf constructed from $underline(x)$.
- For mean of sample of $m$ draws from ecdf constructed from $n$ data points, expectation and variance are $ EE[overline(Y)] = overline(x), quad "Var"(overline(Y)) = (n - 1)/n s_x^2 / m $
- If $S$ is the mean, $hat("Var")(S(underline(x)) -> (n - 1)/n s^2 / n$ as $B -> oo$.
- If *sampling fraction* $f = n/N$ where $N$ population size, $n$ sample size, is $f >= 0.1$, can't assume infinite population.
- Given finite population of size $N$, mean $overline(X)$ of sample drawn uniformly at random without replacement has variance $ "Var"(overline(X)) = (N - n) / (N - 1) sigma^2 / n $ where $sigma^2$ is true population variance.
- Given finite population of size $N$, sample of size $n$ with variance $S^2$ drawn without replacement, $ EE[(1 - n/N) S^2/n] = "Var"(overline(X)) $ so it is unbiased estimator of $"Var"(overline(X))$
- *Population bootstrap*: given independent data $(x_1, ..., x_n)$ drawn from finite population of size $N$, assuming $N\/n = k$ is integer, construct new data set $ tilde(underline(x)) = (x_1, ..., x_n, x_1, ..., x_n, ..., x_1, ..., x_n) $ by repeating $underline(x)$ $k$ times. Then construct $B$ new samples $underline(x)^(* 1), ..., underline(x)^(* B)$ by sampling without replacement. Then compute $ hat("Var")(S(underline(x))) = 1/(B - 1) sum_(b = 1)^B (S(underline(x)^(* b)) - overline(S)^*)^2 $ where $ overline(S)^* = 1/B sum_(b = 1)^B S(underline(x)^(* b)) $ If $N \/ n$ not integer, $N = k n + m$ for $0 < m < n$, then before each of the $B$ samples, append to $tilde(underline(x))$ a sample without replacement of size $m$ from $underline(x)$.
- If data believed to follow type of distribution, can use *parametric bootstrap*: given independent data $(x_1, ..., x_n)$, believed to be drawn from distribution $F(dot.op, theta)$ with parameter $theta$:
	- Find maximum likelihood estimator $hat(theta)$.
	- Draw $B$ new samples of size $n$ from $F(dot.op, hat(theta))$ to give $underline(x)^(* 1), ..., underline(x)^(* B)$.
	- Compute $ hat("Var")(S(underline(x))) = 1/(B - 1) sum_(b = 1)^B (S(underline(x)^(* b)) - overline(S)^*)^2 $ where $ overline(S)^* = 1/B sum_(b = 1)^B S(underline(x)^(* b)) $
- For parameter $theta$ of distribution, estimated by statistic $S$, with $hat(theta) = S(underline(x))$, *bias* is $ "bias"(theta, hat(theta)) = EE[hat(theta)] - theta $
- *Basic bootstrap bias estimate*: $ hat("bias")(theta, hat(theta)) = overline(S)^* - hat(theta) = 1/B sum_(b = 1)^B S(underline(x)^(* b)) - S(underline(x)) $
- *Bias correction*: subtract bias from usual estimate: $ hat(theta) - hat("bias")(theta, hat(theta)) = 2 hat(theta) - overline(S)^* $ But often $2 hat(theta) - overline(S)^*$ has higher variance as estimator than $hat(theta)$.
- *Normal confidence interval for bootstrap estimate*: $100(1 - alpha)%$ confidence interval is $ hat(theta) plus.minus z_(alpha \/ 2) sqrt(hat("Var")(S(underline(x)))) $ where $z_(alpha \/ 2)$ is $100(alpha \/ 2)%$ percentile of standard normal distribution. *Note*: only valid if size of data large enough, need to check for normality of bootstrap samples using quantile plot.
- *Percentile confidence interval*: use if $hat(F)$ close to true distribution. $100(1 - alpha)%$ confidence interval is $ [S_(((alpha \/ 2) B))^*, S_(((1 - alpha \/ 2) B))^*] $ where $S_((i))^*$ is $i$th largest value of $S(underline(x)^(* b))$ for $b = 1, ..., B$. $B$ must be chosen to make $(alpha \/ 2) B$ and $(1 - alpha \/ 2) B$ integers. $B$ must be $> 2000$ for this to be good estimate. *Note*: inaccurate if bias or non-constant standard error or distribution of $S(X) | theta$ isn't symmetric.
- *BC (bias corrected)* and *BCa (bias corrected and accelerated)* confidence intervals make adjustments when bias is present or there is non-constant standard error.

= Monte Carlo integration

- Let random variable $Y$ take values in sample space $Omega$ with pdf $f_Y$, then $ mu := EE[Y] = integral_Omega y f_Y(y) dif y $
- $mu$ approximated by $ hat(mu)_n = 1/n sum_(i = 1)^n Y_i $ for i.i.d. samples $Y_i$.
- If $Y = g(X)$ with $X$ random variable with pdf $f_X$, then $ mu = EE[Y] = EE[g(X)] = integral g(x) f_X(x) dif x $
- To estimate $integral_a^b f(x) dif x$, use $X ~ "Unif"(a, b)$ $ mu = integral_a^b f(x) dif x = integral_a^b (b - a) f(x) 1/(b - a) dif x = integral_a^b (b - a) f(x) f_X(x) dif x = EE[(b - a) f(X)] $ which can be estimated by $ hat(mu)_n = (b - a) 1/n sum_(i = 1)^n f(X_i) $ for i.i.d. samples $X_i$.
- If $"Var"(Y) = sigma^2 < oo$, Monte Carlo integration unbiased as $EE[hat(mu)_n] = mu$.
- *Mean-square error*: $"Var"(hat(mu)_n) = EE[(hat(mu)_n - mu)^2] = sigma^2 / n$.
- *Root mean-square error*: $"RMSE" = sqrt(EE[(hat(mu)_n - mu)^2]) = sigma / sqrt(n)$.
- $"RMSE"$ is $O(n^(-1\/2))$.
- For functions $f, g$, $f(n) = O(g(n))$ as $n -> oo$ if exist $C, n_0 in RR$ such that $ forall n >= n_0, quad |f(n)| <= C g(n) $
- *Midpoint Riemann integral estimate*: $ integral_a^b f(x) dif x = (b - a) / n sum_(i = 1)^n f(x_i) $ where $ x_i = a + (b - a)/n (i - 1/2) $
- For $d$ dimensions, Riemann sum converges in $O(n^(-2\/d))$, Monte Carlo converges in $O(n^(-1\/2))$ regardless of $d$.
- $100(1 - alpha)%$ confidence interval for Monte Carlo integration: $ mu in hat(mu)_n plus.minus z_(alpha \/ 2) sigma / sqrt(n) $ where $sigma$ estimated with standard sample deviation of ${y_i} = {g(x_i)}$.
- If $g(x)$ constant multiple of indicator function, $g(x) = c II{A(x)}$ for condition $A$, then $ hat(p)_n = 1/n sum_(i = 1)^n II{A(x_i)} $ is estimator for $p = PP(A)$. Binomial confidence interval is $ p in hat(p)_n plus.minus z_(alpha \/ 2) sqrt((hat(p)_n (1 - hat(p)_n)) / n) $ so confidence interval for $mu$ is $ mu in hat(mu)_n plus.minus c z_(alpha \/ 2) sqrt((hat(p)_n (1 - hat(p)_n)) / n) $ ($hat(mu)_n = c hat(p)_n$).
- Probability of no $1$s in $n$ Monte Carlo samples is $(1 - p)^n$ so one-sided $100(1 - alpha)%$ confidence interval has upper bound $p <= 1 - alpha^(1\/n) approx -log(alpha) / n$ using Taylor expansion.
- If $hat(p)$ very small and non-zero, $ c z_(alpha \/ 2) sqrt((hat(p)_n (1 - hat(p)_n)) / n) approx c z_(alpha \/ 2) sqrt((hat(p)_n) / n) $ so relative error is $ delta := c z_(alpha \/ 2) sqrt((hat(p)_n) / n) \/ hat(p) = (c z_(alpha \/ 2)) / sqrt(hat(p)_n n) $ for relative error at most $delta$, $ n >= (c^2 z_(alpha \/ 2)^2) / (hat(p)_n delta^2) $ so $n$ grows inversely with $hat(p)_n$.
- To estimate probability of event $PP(X in E)$, Monte Carlo estimate $EE[II{X in E}]$.

= Simulation

- Let $F$ cdf, then *generalised inverse cdf* is $ F^(-1)(u) := inf{x: F(x) >= u} $
- *Inverse transform sampling algorithm*: let random variable $X$ with cdf $F$, with generalised inverse $F^(-1)$.
	- Simulate $U tilde.op "Unif"(0, 1)$.
	- Compute $X = F^(-1)(U)$.
	$X$ is then distributed with cdf $F$. Only works for 1D distributions.
- *Rejection sampling algorithm*: given *target density* function $f$, *proposal density* function $tilde(f)$ with $forall x in RR^d, f(x) <= c tilde(f)(x)$ for some $c < oo$,
	- Set $a = "false"$
	- While $a = "false"$:
		- Simulate $u tilde.op "Unif"(0, 1)$.
		- Simulate $x tilde.op tilde(f)(dot.op)$.
		- If $u <= f(x) / (c tilde(f)(x))$, set $a = "true"$.
	- Once while loop exited, return $x$, which is distributed with pdf $f$.
- *Note*: $f$ and $tilde(f)$ don't need to be normalised.
- When $f, tilde(f)$ normalised, expected number of iterations of rejection sampling algorithm is $c$.
- *Important*: when choosing value of $c$, always round *up* if inexact.
- When checking if rejection sampling can be used, check if ratio $f(x) \/ tilde(f)(x)$ tends to $0$ as $x -> plus.minus oo$ and differentiate ratio with respect to $x$ to find maximum.
- *Normalised importance sampling*: given normalised density function $f$ and normalised proposal density function $tilde(f)$, $n$ importance samples produced by: for $i in {1, ..., n}$:
	- Simulate $x_i tilde.op tilde(f)(dot.op)$.
	- Compute $w_i = f(x_i) \/ tilde(f)(x_i)$.
	This produces importance samples ${(x_i, w_i)}_(i = 1)^n$. $mu = EE_(tilde(f))[g(X)]$ estimated by *importance sampling estimator* $ hat(mu) = 1/n sum_(i = 1)^n w_i g(x_i) $ ($EE_(tilde(f))[hat(mu)] = mu$, provided $tilde(f)(x) > 0$ whenever $f(x) g(x) != 0$).
- Variance of importance sampling estimator is $ "Var"(hat(mu)) = (sigma_(tilde(f))^2) / n $ where $ sigma_(tilde(f))^2 = integral_(tilde(Omega)) (g(x) f(x) - mu tilde(f)(x))^2 / (tilde(f)(x)) dif x $ and $tilde(Omega)$ is support of $tilde(f)$.
- Can estimate variance with $ hat(sigma)_(tilde(f))^2 = 1/n sum_(i = 1)^n (w_i g(x_i) - hat(mu))^2 $
- Distribution which minimises estimator variance is $ tilde(f)_"opt"(x) = (|g(x)| f(x)) / (integral_Omega |g(x)| f(x) dif x) $
- *Self-normalised importance sampling*: same as normalised importance sampling, but compute $ hat(mu) = 1/(sum_(i = 1)^n w_i) sum_(i = 1)^n w_i g(x_i) $ Can use for unnormalised density functions $f, tilde(f)$. $hat(mu)$ is not unbiased.
- Approximate variance of self-normalised estimator: $ "Var"(hat(mu)) approx (hat(sigma)_(tilde(f))^2) / n $ where $ hat(sigma)_(tilde(f))^2 = sum_(i = 1)^n w_i'^2 (g(x_i) - hat(mu))^2 $ and $ w_i' = w_i / (sum_(j = 1)^n w_j) $
- *Effective sample size $n_e$*: size of sample for which variance of naive Monte Carlo average $(1/n_e sum_(i = 1)^(n_e) g(x_i))$ with sample size $n_e$, $sigma^2 \/ n_e$ ($sigma^2$ is variance of $g(X)$), is equal to variance of importance sampling estimator $hat(mu)$, $"Var"(hat(mu))$: $ n_e = (n overline(w)^2) / overline(w^2) $ where $ overline(w)^2 = (1/n sum_(i = 1)^n w_i)^2, quad overline(w^2) = 1/n sum_(i = 1)^n w_i^2 $
- Small $n_e$ means importance sampling is poor estimator.
- Poor estimator if proposal distribution has much less probability in tails than target distribution.