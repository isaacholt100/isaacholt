#import "../template.typ": template
#show: template

= Introduction

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

- *Monte Carlo testing*: given observed test stat $t = h(underline(x))$ distribution $F(x | theta)$ hypotheses $H_0: theta = theta_0$, $H_1: theta > theta_0$:
	- For $j in {1, ..., N}$:
		- Simulate $n$ observations $(z_1, ..., z_n)$ from $F(dot.op | theta_0)$.
		- Compute $t_j = h(z_1, ..., z_n)$.
	- Estimate $p$-value by $ P(T >= t | H_0 "true") approx 1/N sum_(j = 1)^N II{t_j >= t} $