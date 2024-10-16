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
#definition[
    For $x in K$ and $r > 0$, define $
        B(x, r) & := {y in K: |x - y| < r}, \
        overline(B)(x, r) & = {y in K: |x - y| <= r}.
    $
]
#lemma[
    Let $(K, |dot|)$ be a non-Archimedean valued field.
    - If $z in B(x, r)$, then $B(z, r) = B(x, r)$, i.e. open balls don't have a centre.
    - If $z in overline(B)(x, r)$, then $overline(B)(z, r) = overline(B)(x, r)$. i.e. closed balls don't have a centre.
    - $B(x, r)$ is closed.
    - $overline(B)(x, r)$ is open.
]
#proof[
    - Let $y in B(x, r)$. Then $|x - y| < r$ so $|z - y| = |(z - x) + (x - y)| <= max{|z - x|, |x - y|} < r$. Hence $B(x, r) subset.eq B(z, r)$. Converse is obtained by symmetry.
    - Same as above.
    - Let $y in.not B(x, r)$. If $z in B(x, r) sect B(y, r)$ then $B(x, r) = B(z, r) = B(y, r)$ by above, hence $y in B(x, r)$: contradiction. Hence $B(x, r) sect B(y, r) = emptyset$.
    - Let $z in overline(B)(x, r)$, then $B(z, r) subset.eq overline(B)(z, r) = overline(B)(x, r)$ by above.
]

= Valuation rings

#definition[
    Let $K$ be a field. $t: K^times -> RR$ is a *valuation* on $K$ if:
    - $v(x y) = v(x) + v(y)$.
    - $v(x + y) >= min{v(x), v(y)}$.
    Fix $alpha in (0, 1)$. Then for a valuation $v$ on $K$, we can define a non-Archimedean absolute value $
        |x| = cases(
            alpha^(v(x)) & "if" x != 0,
            0 & "if" x = 0
        )
    $ Conversely, a non-Archimedean absolute value determines a valuation $
        v(x) = log_alpha |x|   
    $
]
#remark[
    - We ignore the trivial valuation $v(x) = 0$ (corresponds to trivial absolute value).
    - We say $v_1$ and $v_2$ are equivalent valuations if there exists $c > 0$ such that $v_1 (x) = c v_2 (x)$ for all $x in K^times$.
]
#example[
    - For $K = QQ$, $v_p (x) = -log_p |x|_p$ is the $p$-adic valuation.
    - Let $k$ be field, $K = k(t) = "Frac"(k[t])$ be the rational function field. Define the $t$-adic valuation $v(t^n f(t)/g(t)) = n$ where $f, g in k[t]$, $f(0), g(0) != 0$.
    - $K = k((t)) = "Frac"(k[[t]]) = \{sum_(i = n)^oo a_i t^i: a_i in k, n in ZZ\}$ is the field of formal Laurent series over $k$. Define the $t$-adic valuation $
        v(sum_i a_i t^i) = min{i in ZZ: a_i != 0}
    $
]
#definition[
    Let $(K, |dot|)$ be a non-Archimedean valued field. The *valuation ring* of $K$ is $
        cal(O)_K & = {x in K: |x| <= 1} = overline(B)(0, 1) \
        & = {x in K^times: v(x) >= 0} union {0}
    $
]
#proposition[
    - $cal(O)_K$ is an open subring of $K$.
    - The subsets ${x in K: |x| <= r}$ and ${x in K: |x| < r}$ are both open ideals in $cal(O)_K$ for $r <= 1$.
    - $cal(O)_K^times = {x in K: |x| = 1}$.
]
#proof[
    - To show ring:
        - $|0| = 0, |1| = 1 <= 1$ so $0, 1 in cal(O)_K$.
        - If $x in cal(O)_K$, then $|-x| = |x| <= 1$ so $-x in cal(O)_K$.
        - If $x, y in cal(O)_K$, then $|x + y| <= max{|x|, |y|} <= 1$ so $x + y in cal(O)_K$.
        - If $x, y in cal(O)_K$, then $|x y| = |x| |y| <= 1$ so $x y in cal(O)_K$.
    - $cal(O)_K$ is open since it is a "closed" ball.
    - Showing open ideals is similar to above.
    - $|x| |x^(-1)| = |x x^(-1)| = 1$ so $|x| = 1$ iff $|x^(-1)| = 1$, i.e. $x, x^(-1) in cal(O)_K$, i.e. $x in cal(O)_K^times$.
]
#notation[
    Write $m := {x in cal(O)_K: |x| < 1}$ which is a maximal ideal in $cal(O)_K$. $k = cal(O)_K\/m$ be the *residue field*.
]
#corollary[
    $cal(O)_K$ is a local ring (i.e. it has a unique maximal ideal) with unique maximal ideal $m$.
]
#proof[
    Let $m' != m$ be a maximal ideal, then there exists $x in m' \\ m$, hence $|x| = 1$ so $x$ is a unit, so $m' = R$: contradiction.
]
#example[
    - Let $K = QQ$ with $|dot|_p$. Then $cal(O)_K = ZZ_((p)) = {a/b in QQ: p divides.not b}$. $m = p ZZ_((p))$ and $k = FF_p$.
]
#definition[
    A valuation $v: K^times -> RR$ is *discrete* if $v(K^times) tilde.equiv ZZ$. In this case, $K$ is a *discretely valued field*, and element $pi in cal(O)_K$ is a *uniformiser* if $v(pi) > 0$ and $v(pi)$ generates $v(K^times)$.
]<def:valuation.discrete>
#example[
    - $K = QQ$ with the $p$-adic valuation is discretely valued.
    - $K = k(t)$ with the $t$-adic valuation is discretely valued.
    - $K = k(t)(t^(1\/2), t^(1\/4), ...)$ with the $t$-adic valuation is not discrete.
]
#remark[
    If $v$ is a discrete valuation, then we can replace it with an equivalent valuation such that $v(K^times) = ZZ$. Such valuations are called *normalised* valuations (in this case, $pi$ is a uniformiser iff $v(pi) = 1$).
]
#lemma[
    Let $v$ be a valuation on $K$. TFAE:
    + $v$ is discrete.
    + $cal(O)_K$ is a PID.
    + $cal(O)_K$ is Noetherian.
    + $m$ is principal.
]
#proof[
    - $(1 => 2)$:
        - $cal(O)_K$ is ID as subring of a field.
        - Let $I subset.eq cal(O)_K$ be a non-zero ideal, $x in I$ such that $v(x) = min{v(a): a in I}$ (which exists as valuation is discrete).
        - We claim $x cal(O)_K = {a in K: v(a) >= v(x)}$ is equal to $I$.
        - $subset.eq$: since $I$ is ideal.
        - $supset.eq$: let $y in I$, then $v(x^(-1) y) >= 0$ so $y = x (x^(-1) y) in x cal(O_K) $ TODO: finish.
    - $(2 => 3)$: clear.
    - $(3 => 4)$: write $m = x_1 cal(O)_K + dots.c + x_n cal(O)_K$. WLOG $v(x_1) <= dots.c <= v(x_n)$. Then $x_2, ..., x_n in x_1 cal(O)_K$ so $m = x cal(O)_K$.
    - $(4 => 1)$: let $m = pi cal(O)_K$ for some $pi in cal(O)_K$, let $c = v(pi)$. Then if $v(x) > 0$, $x in m$, hence $v(x) >= c$. Thus $v(K^times) sect (0, c) = emptyset$. Since $v(K^times)$ is a subgroup, we must have $v(K^times) = c ZZ$.
]