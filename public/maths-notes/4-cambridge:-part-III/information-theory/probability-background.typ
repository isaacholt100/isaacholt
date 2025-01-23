#import "../../template.typ": *

#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Background Probability Notes",
    author: "Isaac Holt",
)

#theorem("Cauchy-Schwarz")[
    $EE[X Y]^2 <= EE[X^2] EE[Y]^2$.
]
#theorem("Markov's Inequality")[
    If $X >=0$, then for all $a$, $PP(X >= a) <= EE[X] / a$.
]
#theorem("Chebyshev's Inequality")[
    Let $X >= 0$, then $
        PP(X >= epsilon) <= EE[X^2] / epsilon^2.
    $
]
#corollary[
    Let $mu = EE[X]$. Then $
        PP(abs(X - mu) >= epsilon) <= "Var"(X) / epsilon^2.
    $
]
#theorem("Weak Law of Large Numbers")[
    Let $X_1, ..., X_n$ be IID RVs, mean $mu$. Let $S_n = sum X_i$. Then $
        PP(abs(S_n / n - mu) >= epsilon) -> 0 "as" n -> oo.
    $ i.e. $S_n / n$ tends to $mu$ in probability.
]
#theorem("Strong Law of Large Numbers")[
    $PP(S_n / n -> mu "as" n -> oo) = 1$, i.e. $S_n / n -> mu "as" n -> oo$ almost surely. Strong law implies weak law.
]
#definition[
    Covariance of $X$ and $Y$ is $
        "Cov"(X, Y) = EE[(X - EE[X])(Y - EE[Y])] = EE[X Y] - EE[X] EE[Y]
    $
]
Note that $"Cov"(X, Y) = 0$ does not imply $X$, $Y$ independent.
#definition[
    Correlation coefficient of $X$ and $Y$ is $
        "corr"(X, Y) = "Cov"(X, Y) / sqrt("Var"(X) "Var"(Y))
    $ It lies in $[-1, 1]$.
]
#definition[
    Marginal distribution of $X$ is $
        PP(X = x) = sum_y PP(X = x, Y = y)
    $
]
#definition[
    Conditional expectation of $X$ given $Y$ is $
        EE[X | Y = y] = sum_x x PP(X = x | Y = y)
    $ Can view $EE[X | Y]$ as random variable in $Y$.
]
#theorem("Tower Property of Conditional Expectation, Law of Total Expectation")[
    $EE_Y [EE_X [X | Y]] = EE_X [X]$. Equivalently, $
        EE[X] = sum_i EE[X | A_i] PP(A_i)
    $ where $A_1, ..., A_n$ is partition of $Omega$.
]
#definition[
    Let $X$ be RV on $NN_0$. Probability generating function (pgf) of $X$ is $
        p_X (z) = EE[z^X] = sum_(r = 0)^oo PP(X = r) z^r
    $ The pgf of $X$ uniquely determines (via derivatives) its distribution.
]
#theorem("Abel's Lemma")[
    $EE[X] = lim_(z -> 1) p'(z)$.
]
#theorem[
    $EE[X(X - 1)] = lim_(z -> 1) p''(z)$.
]
#theorem[
    If $X_1, ..., X_n$ independent, then pgf of $X_1 + dots.c + X_n$ is $p_(X_1) ... p_(X_n)$.
]
#definition[
    Moment generating function of $X$ is $m(theta) = EE[e^(theta X)]$.
]
#definition[
    mgf determines distribution of $X$, provided that $m(theta) < oo$ for all $theta$ in some interval containing the origin.
]
#definition[
    The $r$-th moment of $X$ is $EE[X^r]$.
]
#theorem[
    The $r$-th moment of $X$ is the coefficient of $theta^r / r!$ in $m(theta)$, i.e. $
        EE[X^r] = (dif^n)/(dif theta^n) m(theta)|_(theta = 0) = m^((n))(0)
    $
]
#theorem[
    If $X$, $Y$, independent, then $m_(X + Y)(theta) = m_X (theta) m_Y (theta)$.
]
#theorem("Central Limit Theorem")[
    Let $X_1, ..., X_n$ be IID RVs, $EE[X_i] = mu$, $"Var"(X_i) = sigma^2 < oo$. Let $S_n = X_1 + dots.c + X_n$. Then $
        lim_(n -> oo) PP(a <= (S_n - n mu)/(sigma sqrt(n)) <= b) = Phi(b) - Phi(a) = integral_a^b 1/sqrt(2 pi) e^(-1/2 t^2) dif t
    $ So $(S_n - n mu)/(sigma sqrt(n))$ converges in distribution, $->_D$, to the standard normal $N(0, 1)$.
]
#theorem("Continuity Theorem")[
    Let $X_1, ..., X_n$ have mgs $m_1 (theta), ..., m_n (theta)$ where $m_n (theta) -> m(theta)$ as $n -> oo$ pointwise. Then $X_n ->_D Y$ where $Y$ has mgf $m(theta)$.
]