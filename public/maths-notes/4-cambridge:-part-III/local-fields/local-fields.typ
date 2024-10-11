#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

= Basic theory

#example[
    Let $f(x_1, ..., x_r) in ZZ[x_1, ..., x_r]$, a Diophantine equation asks to solve $f(x_1, ..., x_r) = 0$. Easier questions are when is $f(x_1, ..., x_r) equiv 0 (mod p)$ and $f(x_1, ..., x_r) equiv 0 (mod p^n)$. Local fields "package" all this information together for all $n$.
]

== Absolute values

#definition[
    Let $K$ be a field. An *absolute value* on $K$ is a function $|dot|: K -> RR_(>=0)$ such that $forall x, y in K$:
    - $|x| = 0 <==> x = 0$.
    - $|x y| = |x| dot |y|$ (multiplicative).
    - $|x + y| <= |x| + |y|$ (triangle inequality).
    $(K, |dot|)$ is a *valued field*.
]<def:absolute-value>
#example[
    - $K = QQ, RR$ or $CC$ with usual absolute value $|a + i b| = sqrt(a^2 + b^2)$. We write $|dot|_oo$ for this absolute value.
    - The *trivial* absolute value is $|x| = 0$ if $x = 0$ and $|x| = 1$ otherwise.
]
#definition[
    Let $K = QQ$, $p$ be prime. For $0 != x in QQ$, write $x = p^n a/b$ where $p divides.not a, b$. The *$p$-adic absolute value* $|dot|_p$ is defined as $
        |x|_p = cases(
            0 & "if" x = 0,
            p^(-n) & "if" x = p^n a/b
        ).
    $
]<def:p-adic-absolute-value>
#proposition[
    The $p$-adic absolute value is an absolute value.
]
#proof[
    - The first axiom is trivial.
    - Let $y = p^m c/d$.
    - $|x y|_p = |p^(m + n) (a c)/(b d)|_p = p^(-m - n) = |x|_p dot |y|_p$.
    - WLOG, assume that $m >= n$. $|x + y|_p = |p^n (a d + p^(m - n) b c)/(b d)|_p <= p^(-n) = max{|x|_p, |y|_p}$.
]
#proposition[
    An absolute value $|dot|$ on $K$ induces a metric $d(x, y) = |x - y|$ (and hence a topology) on $K$.
]
#proof[
    Exercise.
]
#definition[
    Two absolute values on $K$ are *equivalent* if they induce the same topology.

    A *place* is an equivalence class of absolute values.
]
#proposition[
    Let $|dot|$ and $|dot|'$ be non-trivial absolute values on $K$. Then TFAE:
    + $|dot|$ and $|dot|'$ are equivalent.
    + $|x| < 1$ iff $|x|' < 1$ for all $x in K$.
    + There exists $c > 0$ such that $|x|^c = |x|'$ for all $x in K$.
]
#proof[
    - $(1 => 2)$:
        - $|x| < 1$ iff $x^n -> 0$ w.r.t $|dot|$ iff $x^n -> 0$ w.r.t $|dot|'$ iff $|x|' < 1$.
    - $(2 => 3)$:
        - Note $|x|^c = |x|'$ iff $c log |x| = log |x|'$.
        - Let $a in K^times$ such that $|a| > 1$ (this exists since $|dot|$ is non-trivial).
        - We show that $log |x| \/ log |a| = log |x|' \/ log |a|'$ for all $x in K^times$.
        - Assume not, then $log |x| \/ log |a| < log |x|' \/ log |a|'$.
        - Choose $m, n in ZZ$ such that $log |x| \/ log |a|  < m/n < log |x| \/ log |a|$.
        - Then $n log |x| < m log |a|$ and $n log |x|' > m log |a|'$, so $|x^n / a^m| < 1$ but $|x^n / a^m|' > 1$: contradiction.
        - Similarly for $log |x| \/ log|a| > log|x|' \/ log|a|'$.
    - $(3 => 1)$:
        - Trivial, as open balls they define are the same.
]
#remark[
    $|dot|_oo^2$ on $CC$ is not an absolute value by out definition since it violates the triangle inequality. Note some authors replace the triangle inequality axiom with $|x + y|^beta <= |x|^beta + |y|^beta$ for some fixed $beta > 0$.
]
#definition[
    An absolute value $|dot|$ on $K$ is *non-Archimedean* if it satisfies the *ultrametric inequality*: $
        |x + y| <= max{|x|, |y|}.
    $ Otherwise, it is *Archimedean*.
]<def:absolute-value.non-archimedean>
#example[
    - $|dot|_oo$ on $RR$ is Archimedean.
    - $|dot|_p$ on $QQ$ is non-Archimedean.
]
#lemma[
    Let $(K, |dot|)$ be non-Archimedean and $x, y in K$. If $|x| < |y|$, then $|x - y| = |y|$ (i.e. all triangles are isosceles).
]
#proof[
    For $<=$, use ultrametric inequality. For $>=$, use that $|y| = |x - y - x|$.
]
#proposition[
    Let $(K, |dot|)$ be non-Archimedean. Let $(x_n)$ be a sequence in $K$. If $|x_n - x_(n + 1)| -> 0$, then $x_n$ is Cauchy. In particular, if $K$ is complete with respect to $|dot|$, then $(x_n)$ converges.
]
#proof[
    - For $epsilon > 0$, choose $N$ such that $|x_n - x_(n + 1)| < epsilon$ for all $n > N$.
    - Then for $N < n < m$, $|x_n - x_m| = |(x_n - x_(n + 1)) + (x_(n + 1) - x_(n + 2)) + dots.c + (x_(m - 1) - x_m)| < epsilon$.
]
#example[
    Let $p = 5$ and consider the sequence $(x_n)$ in $ZZ$ satisfying:
    - $x_n^2 + 1 equiv 0 mod 5^n$.
    - $x_n equiv x_(n + 1) mod 5^n$.
    Take $x_1 = 2$. Suppose we have constructed $x_1, ..., x_n$. Then write $x_n^2 + 1 = a 5^n$ and set $x_(n + 1) = x_n + b 5^n$. Then $x_(n + 1)^2 + 1 = x_n^2 + 2b x_n 5^n + b^2 5^(2n) + 1 = a 5^n + 2b x_n 5^n + b^2 5^(2n)$. We choose $b$ such that $a + 2b x_n equiv 0 mod 5$ (this congruence is solvable). Then we have $x_(n + 1)^2 + 1 = 0 mod 5^(n + 1)$.

    Hence $(x_n)$ is Cauchy. Suppose $x_n -> l in QQ$. Then $x_n^2 -> l^2 in QQ$. But the first condition implies that $x_n^2 -> -1 = l^2$, contradiction. So $(x_n)$ doesn't converge in $QQ$. So $(QQ, |dot|_5)$ is not complete.
]
#definition[
    The set of *$p$-adic numbers* $QQ_p$ is the completion of $QQ$ with respect to $|dot|_p$.
]
#remark[
    There is an analogy with the construction of $RR$ with respect to $|dot|_oo$.
]