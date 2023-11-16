# Introduction

## Cubic equations over $\mathbb{C}$

-   For a polynomial equation, a **solution by radicals** is a formula
    for solutions using only addition, subtraction, multiplication,
    division and radicals $\sqrt[m]{\cdot}$ for $m \in {\mathbb{N}}$.

-   For general cubic equation
    $x^{3} + a_{2}x^{2} + a_{1}x + a_{0} = 0$:

    -   **Tschirnhaus transformation** is substitution
        $t = x + \frac{a_{2}}{3}$, giving
        $$t^{3} + pt + q = 0,\quad p = \frac{- a_{2}^{2} + 3a_{1}}{3},\quad q = \frac{2a_{2}^{3} - 9a_{1}a_{2} + 27a_{0}}{27}$$
        This is a **reduced** cubic equation.

    -   When $t = u + v$,
        $t^{3} - (3uv)t - \left( u^{3} + v^{3} \right) = 0$ which is in
        the reduced cubic form with
        $p = - 3uv,q = - \left( u^{3} + v^{3} \right)$.

    -   We have
        $$\left( y - u^{3} \right)\left( y - v^{3} \right) = y^{2} - \left( u^{3} + v^{3} \right)y + u^{3}v^{3} = y^{2} + qy - \frac{p^{3}}{27} = 0$$
        so
        $u^{3},v^{3} = - \frac{q}{2} \pm \sqrt{\frac{q^{2}}{4} + \frac{p^{3}}{27}}$.

    -   So a solution to $t^{3} + pt + q = 0$ is
        $$t = u + v = \sqrt[3]{\arg} + \sqrt[3]{\arg}$$ The other
        solutions are $\omega u + \omega^{2}v$ and
        $\omega^{2}u + \omega v$ where $\omega = e^{2\pi i/3}$ is the
        3rd root of unity. This is because $u$ and $v$ each have three
        solutions indepedently to
        $u^{3},v^{3} = - \frac{q}{2} \pm \sqrt{\frac{q^{2}}{4} + \frac{p^{3}}{27}}$,
        but also $uv = - \frac{p}{3}$.

-   **Remark**: the above method doesn't work for fields of
    characteristic $2$ or $3$ since the formulas involve division by $2$
    or $3$ (which is dividing by zero in these respective fields).

-   For general cubic equation
    $x^{3} + a_{3}x^{3} + a_{2}x^{2} + a_{1}x + a_{0} = 0$:

    -   Substitution $t = x + \frac{a_{3}}{4}$ gives **reduced** quartic
        equation $$t^{4} + pt^{2} + qt + r = 0$$

    -   We then manipulate the polynomial so that it is the sum or
        difference of two squares and use
        $a^{2} + b^{2} = (a + ib)(a - ib)$ or
        $a^{2} - b^{2} = (a + b)(a - b)$:
        $$\left( t^{2} + w \right)^{2} + (p - 2w)t^{2} + qt + \left( r - w^{2} \right) = 0$$

    -   $(p - 2w)t^{2} + qt + \left( r - w^{2} \right) = 0$ is a square
        iff its discriminant is zero:
        $$q^{2} - 4(p - 2w)\left( r - w^{2} \right) = 0 \Longleftrightarrow w^{3} - \frac{1}{2}pw^{2} - rw + \frac{1}{8}\left( 4pr - q^{2} \right) = 0$$

    -   This **cubic resolvent** is solvable by radicals. Taking any of
        the solutions and substituting for $w$ gives a sum or difference
        of two squares in $t$. The quadratic factors can then be solved.

## Galois theory for quadratic equations

# Fields and polynomials

## Basic properties of fields

-   **Definition**: ring $R$ is **field** if every element of
    $R - \left\{ 0 \right\}$ has mutliplicative inverse and
    $1 \neq 0 \in R$.

-   **Lemma**: every field is integral domain.

-   **Definition**: field homomorphism is a ring homomorphism
    $\varphi:K \rightarrow L$ between fields:

    -   $\varphi(a + b) = \varphi(a) + \varphi(b)$

    -   $\varphi(ab) = \varphi(a)\varphi(b)$

    -   $\varphi(1) = 1$

These imply $\varphi(0) = 0$, $\varphi( - a) = - \varphi(a)$,
$\varphi(a^{- 1}) = {\varphi(a)}^{- 1}$.

-   **Lemma**: let $\varphi:K \rightarrow L$ homomorphism.

    -   $\operatorname{im}(\varphi) = \left\{ \varphi(a):a \in K \right\}$
        is a field.

    -   $\ker(\varphi) = \left\{ a \in K:\varphi(a) = 0 \right\} = \left\{ 0 \right\}$,
        i.e. $\varphi$ is injective.

-   **Definition**: **subfield** $K$ of field $L$ is subring of $L$
    where $K$ is a field. $L$ is a **field extension** of $K$.

-   The above lemma shows the image of $\varphi:K \rightarrow L$ is a
    subfield of $L$.

-   **Lemma**: intersections of subfields are subfields.

-   **Prime subfield** of $L$: intersection of all subfields of field
    $L$.

-   **Definition**: **characteristic** $\operatorname{char}(K)$ of field
    $K$ is
    $$\operatorname{char}(K) ≔ \min(\left\{ 0 \right\} \cup \left\{ n \in {\mathbb{N}}:\chi(n) = 0 \right\})$$
    where $\chi:{\mathbb{Z}} \rightarrow K$, $\chi(m) = 1 + \cdots + 1$
    ($m$ times).

-   **Example**:
    $\operatorname{char}({\mathbb{Q}}) = \operatorname{char}({\mathbb{R}}) = \operatorname{char}({\mathbb{C}}) = 0$,
    $\operatorname{char}({\mathbb{F}}_{p}) = p$ for $p$ prime.

-   **Lemma**: for any field $K$, $\operatorname{char}(K)$ is either $0$
    or a prime.

-   **Theorem**:

    -   $\operatorname{char}(K) = 0$ iff $\mathbb{Q}$ is the prime
        subfield of $K$.

    -   $\operatorname{char}(K) = p > 0$ iff ${\mathbb{F}}_{p}$ is the
        prime subfield of $K$.

-   Note $p~|~\binom{p}{i}$ so $(a + b)^{p} = a^{p} + b^{p}$.

## Polynomials over fields

-   **Degree** of $f(x) = a_{0} + a_{1}x + \cdots + a_{n}x_{n}$,
    $a_{n} \neq 0$ is $\deg(f(x)) = n$.

-   $\deg(f(x)g(x)) = \deg(f(x)) + \deg(g(x))$ and
    $\deg(f(x) + g(x)) = \max\left\{ \deg(f(x)),\deg(g(x)) \right\}$
    with equality if $\deg(f(x)) \neq \deg(g(x))$.

-   Degree of zero polynomial is $\deg(0) = - \infty$.

-   Only invertible elements in $K\lbrack x\rbrack$ are non-zero
    constants $f(x) = a_{0} \neq 0$.

-   Similarities between $\mathbb{Z}$ and $K\lbrack x\rbrack$ for field
    $K$:

    -   $K\lbrack x\rbrack$ is integral domain.

    -   There is a division algorithm for $K\lbrack x\rbrack$: for
        $f(x),g(x) \in K\lbrack x\rbrack$,
        $\exists!q(x),r(x) \in K\lbrack x\rbrack$ with
        $\deg(r(x)) < \deg(g(x))$ such that $$f(x) = q(x)g(x) + r(x)$$

    -   Every $f(x),g(x) \in K\lbrack x\rbrack$ have greatest common
        divisor $\gcd(f(x),g(x))$ unique up to multiplication by
        non-zero constants. By Euclidean algorithm for polynomials,
        $$\exists a(x),b(x) \in K\lbrack x\rbrack:a(x)f(x) + b(x)g(x) = \gcd(f(x),g(x))$$

    -   Can construct field from $K\lbrack x\rbrack$: **field of
        fractions** of $K\lbrack x\rbrack$ is
        $$K(x) = \text{ Frac}\left( K\lbrack x\rbrack \right) = \left\{ \frac{f(x)}{g(x)}:f(x),g(x) \in K\lbrack x\rbrack,g(x) \neq 0 \right\}$$
        (We can construct the field of fractions for any integral
        domain).

    -   $K\lbrack x\rbrack$ is PID and UFD.

-   **Definition**: $f(x) \in K\lbrack x\rbrack$ **irreducible** in
    $K\lbrack x\rbrack$ if

    -   $\deg(f(x)) \geq 1$ and

    -   $f(x) = g(x)h(x) \Longrightarrow g(x)\text{ or }h(x)\text{ is constant}$

## Tests for irreducibility

-   If $f(x)$ has linear factor in $K\lbrack x\rbrack$, it has root in
    $K\lbrack x\rbrack$.

-   **Rational root test**: if
    $f(x) = a_{0} + \cdots + a_{n}x^{n} \in {\mathbb{Z}}\lbrack x\rbrack$
    has rational root $\frac{b}{c} \in {\mathbb{Q}}$ with
    $\gcd(b,c) = 1$ then $b~|~a_{0}$ and $c~|~a_{n}$. This doesn't show
    $f$ is irreducible for $\deg(f(x)) \geq 4$.

-   **Gauss's lemma**: let $f(x) \in {\mathbb{Z}}\lbrack x\rbrack$,
    $f(x) = g(x)h(x)$, $g(x),h(x) \in {\mathbb{Q}}\lbrack x\rbrack$.
    Then
    $\exists r \in {\mathbb{Q}}:rg(x),r^{- 1}h(x) \in {\mathbb{Z}}\lbrack x\rbrack$.

-   **Example**: let
    $f(x) = x^{4} - 3x^{3} + 1 \in {\mathbb{Q}}\lbrack x\rbrack$. Using
    the rational root test, $f( \pm 1) \neq 0$ so no linear factors in
    ${\mathbb{Q}}\lbrack x\rbrack$. Checking quadratic factors, let
    $$f(x) = \left( ax^{2} + bx + c \right)\left( rx^{2} + sx + t \right),\quad a,b,c,r,s,t \in {\mathbb{Z}}\text{ by Gauss's lemma }$$
    So $1 = ar \Rightarrow a = r = \pm 1$.
    $1 = ct \Rightarrow c = t = \pm 1$. $- 3 = b + s$ and
    $0 = c(b + s)$: contradiction. So $f(x)$ irreducible in
    ${\mathbb{Q}}\lbrack x\rbrack$.

-   **Example**: let
    $f(x) = x^{4} - 3x^{2} + 1 \in {\mathbb{Q}}\lbrack x\rbrack$. The
    rational root test shows there are no linear factors. Checking
    quadratic factors, let
    $$f(x) = \left( ax^{2} + bx + c \right)\left( rx^{2} + sx + t \right),\quad a,b,c,r,s,t \in {\mathbb{Z}}\text{ by Gauss's lemma }$$
    As before, $a = r = \pm 1$, $c = t = \pm 1$.
    $0 = b + s \Rightarrow b = - s$,
    $- 3 = at + bs + cr = - b^{2} \pm 2$. $b = 1$ works. So
    $f(x) = \left( x^{2} - x - 1 \right)\left( x^{2} + x - 1 \right)$.

-   **Proposition**: let
    $f(x) = a_{0} + \cdots + a_{n}x^{n} \in {\mathbb{Z}}\lbrack x\rbrack$.
    If exists prime $p \nmid a_{n}$ such that $\underset{¯}{f}(x)$ is
    irreducible in ${\mathbb{F}}_{p}\lbrack x\rbrack$, then $f(x)$
    irreducible in ${\mathbb{Q}}\lbrack x\rbrack$.

-   **Example**: let $f(x) = 8x^{3} + 14x - 9$. Reducing
    $\operatorname{mod}7$,
    $\underset{¯}{f}(x) = x^{3} - 2 \in {\mathbb{F}}_{7}\lbrack x\rbrack$.
    No roots exist for this, so $f(x)$ irreducible in
    ${\mathbb{Q}}\lbrack x\rbrack$. For polynomials, no $p$ is suitable,
    e.g. $f(x) = x^{4} + 1$.

-   Gauss's lemma works with any UFD $R$ instead of $\mathbb{Z}$ and
    field of fractions $\text{Frac}(R)$ instead of $\mathbb{Q}$: let $F$
    field, $R = F\lbrack t\rbrack$, $K = F(t)$, then
    $f(x) \in R\lbrack x\rbrack$ irreducible in $K\lbrack x\rbrack$ iff
    $f(x)$ has no proper factors in $R\lbrack x\rbrack$.

-   **Eisenstein's criterion**: let
    $f(x) = a_{0} + \cdots + a_{n}x^{n} \in {\mathbb{Z}}\lbrack x\rbrack$,
    prime $p \in {\mathbb{Z}}$ such that
    $p\left| a_{0},\ldots,p \right|a_{n - 1}$, $p \nmid a_{n}$,
    $p^{2} \nmid a_{0}$. Then $f(x)$ irreducible in
    ${\mathbb{Q}}\lbrack x\rbrack$.

-   Eisenstein's criterion generalises to UFD $R$ instead of
    $\mathbb{Z}$, $\text{Frac}(R)$ instead of $\mathbb{Q}$.

-   **Example**: let $f(x) = x^{3} - 3x + 1$. Consider
    $f(x - 1) = x^{3} - 3x^{2} + 3$. Then by Eisenstein's criterion with
    $p = 3$, $f(x - 1)$ irreducible in ${\mathbb{Q}}\lbrack x\rbrack$ so
    $f(x)$ is as well, since factoring $f(x - 1)$ is equivalent to
    factoring $f(x)$.

-   **Example**: **$p$-th cyclotomic polynomial** is
    $$f(x) = \frac{x^{p} - 1}{x - 1} = 1 + \cdots + x^{p - 1}$$ Now
    $$f(x + 1) = \frac{(1 + x)^{p} - 1}{1 + x - 1} = x^{p - 1} + px^{p - 2} + \cdots + \binom{p}{p - 2}x + p$$
    so can apply Eisenstein with $p$.

-   

# Field extensions

## Definitions and examples

-   **Definition**: **field extension** $L/K$ is field $L$ containing
    subfield $K$. Can specify homomorphism $\iota:K \rightarrow L$
    (which is injective)

-   **Example**:

    -   ${\mathbb{C}}/{\mathbb{R}}$, ${\mathbb{C}}/{\mathbb{Q}}$,
        ${\mathbb{R}}/{\mathbb{Q}}$.

    -   $L = {\mathbb{Q}}(\sqrt{2}) = \left\{ a + b\sqrt{2}:a,b \in {\mathbb{Q}} \right\}$
        is field extension of $\mathbb{Q}$. ${\mathbb{Q}}(\theta)$ is
        field extension of $\mathbb{Q}$ where $\theta$ is root of
        $f(x) \in Q\lbrack x\rbrack$.

    -   $L = {\mathbb{Q}}(\sqrt[3]{2}) = \left\{ a + b\sqrt[3]{2} + c\sqrt[3]{4}:a,b,c \in {\mathbb{Q}} \right\}$
        is smallest subfield of $\mathbb{R}$ containing $\mathbb{Q}$ and
        $\sqrt[3]{2}$.

    -   $L = K(t)$ is field extension of $K$.

-   **Definition**: let $L/K$ field extension, $S \subseteq L$. Then
    **$K$ with $S$ adjoined**, $K(S)$, is minimal subfield of $L$
    containing $K$ and $S$. If $|S| = 1$, $L/K$ is a **simple
    extension**.

-   **Example**:
    ${\mathbb{Q}}(\sqrt{2},\sqrt{7}) = \{ a + b\sqrt{2} + c\sqrt{7} + d\sqrt{14}:a,b,c,d, \in {\mathbb{Q}}\}$
    is $\mathbb{Q}$ with $S = \{\sqrt{2},\sqrt{7}\}$.

-   **Example**: ${\mathbb{R}}/{\mathbb{Q}}$ is not simple extension.

-   **Definition**: a **tower** if a chain of field extensions, e.g.
    $K \subset M \subset L$.

## Algebraic elements and minimal polynomials

-   **Definition**: let $L/K$ field extension, $\theta \in L$. Then
    $\theta$ is **algebraic over $K$** if
    $$\exists 0 \neq f(x) \in K\lbrack x\rbrack:f(\theta) = 0$$
    Otherwise, $\theta$ is **transcendental over $K$**.

-   **Example**: for $n \geq 1$, $\theta = e^{2\pi i/n}$ is algebraic
    over $\mathbb{Q}$ (root of $x^{n} - 1$).

-   **Example**: $t \in K(t)$ is transcendental over $K$.

-   **Lemma**: the algebraic elements in $K(t)/K$ are precisely $K$.

-   **Lemma**: let $L/K$ field extension, $\theta \in L$. Define
    $I_{K}(\theta) ≔ \left\{ f(x) \in K\lbrack x\rbrack:f(\theta) = 0 \right\}$.
    Then $I_{K}(\theta)$ is ideal in $K\lbrack x\rbrack$ and

    -   If $\theta$ transcendental over $K$,
        $I_{K}(\theta) = \left\{ 0 \right\}$

    -   If $\theta$ algebraic over $K$, then exists unique monic
        irreducible polynomial $m(x) \in K\lbrack x\rbrack$ such that
        $I_{K}(\theta) = \langle m(x)\rangle$.

-   **Definition**: for $\theta \in L$ algebraic over $K$, **minimal
    polynomial** of $\theta$ over $K$ is the unique monic polynomial
    $m(x) \in K\lbrack x\rbrack$ such that
    $I_{K}(\theta) = \langle m(x)\rangle$. The **degree** of $\theta$
    over $K$ is $\deg(m(x))$.

-   **Remark**: if $f(x) \in K\lbrack x\rbrack$ irreducible over $K$,
    monic and $f(\theta) = 0$ then $f(x) = m(x)$.

-   **Example**:

    -   Any $\theta \in K$ has minimal polynomial $x - \theta$ over $K$.

    -   $i \in {\mathbb{C}}$ has minimal polynomial $x^{2} + 1$ over
        $\mathbb{R}$.

    -   $\sqrt{2}$ has minimal polynomial $x^{2} - 2$ over $\mathbb{Q}$.
        $\sqrt[3]{2}$ has minimal polynomial $x^{3} - 2$ over
        $\mathbb{Q}$.

## Constructing field extensions

-   **Lemma**: let $K$ field, $f(x) \in K\lbrack x\rbrack$ non-zero.
    Then
    $$f(x)\text{ irreducible over }K \Longleftrightarrow K\lbrack x\rbrack/\langle f(x)\rangle\text{ is a field }$$

-   **Theorem**: let $m(x) \in K\lbrack x\rbrack$ irreducible, monic,
    $K_{m} ≔ K\lbrack x\rbrack/{\langle m(x)\rangle}$. Then

    -   $K_{m}/K$ is field extension.

    -   Let $\theta = \pi(x)$ where
        $\pi:K\lbrack x\rbrack \rightarrow K_{m}$ is canonical
        projection, then $\theta$ has minimal polynomial $m(x)$ and
        $K_{m} = K(\theta)$.

-   **Definition**: let $L_{1}/K$, $L_{2}/K$ field extensions,
    $\varphi:L_{1} \rightarrow L_{2}$ field homomorphism. $\varphi$ is
    **$K$-homomorphism** if $\forall a \in K,\varphi(a) = a$ ($\varphi$
    fixes elements of $K$).

    -   If $\varphi$ is isomorphism then it is **$K$-isomorphism**.

    -   If $L_{1} = L_{2}$ then $\varphi$ is **$K$-automorphism**.

-   **Example**:

    -   Complex conjugation ${\mathbb{C}} \rightarrow {\mathbb{C}}$ is
        $\mathbb{R}$-automorphism.

    -   Let $K$ field, $\operatorname{char}(K) \neq 2$,
        $\sqrt{2} \notin K$, so $x^{2} - 2$ is minimal polynomial of
        $\sqrt{2}$ over $K$, then
        $K\left( \sqrt{2} \right) \cong K\lbrack x\rbrack/{\langle x^{2} - 2\rangle}$
        is field extension of $K$ and
        $a + b\sqrt{2} \rightarrow a - b\sqrt{2}$ is $K$-automorphism.

-   **Proposition**: let $L/K$ field extension, $\tau \in L$ with
    $m(\tau) = 0$ and $K_{L}(\tau)$ be minimal subfield of $L$
    containing $K$ and $\tau$. Then exists unique $K$-isomorphism
    $\varphi:K_{m} \rightarrow K_{L}(\tau)$ such that
    $\varphi(\theta) = \tau$.

-   **Proposition**: let $\theta$ transcendental over $K$, then exists
    unique $K$-isomorphism $\varphi:K(t) \rightarrow K(\theta)$ such
    that $\varphi(t) = \theta$:
    $$\varphi(\frac{f(g)}{g(t)}) = \varphi(\frac{f(\theta)}{g(\theta)})$$

## Explicit examples of simple extensions

-   Let $r \in K^{\times}$ non-square in $K$, then $x^{2} - r$
    irreducible in $K\lbrack x\rbrack$. E.g. for $K = {\mathbb{Q}}(t)$,
    $x^{2} - t \in K\lbrack x\rbrack$ irreducible. Then
    $K(\sqrt{t}) = {\mathbb{Q}}(\sqrt{t}) = \cong K\lbrack x\rbrack/{\langle x^{2} - t\rangle}$.
    Then for $s = \sqrt{3}$, we have an extension
    ${\mathbb{Q}}(s)/{\mathbb{Q}}(s^{2})$.

-   Define
    ${\mathbb{F}}_{9} = {\mathbb{F}}_{3}\lbrack x\rbrack/{\langle x^{2} - 2\rangle} \cong {\mathbb{F}}_{3}(\theta) = \left\{ a + b\theta:a,b \in {\mathbb{F}}_{3} \right\}$
    for $\theta$ a root of $x^{2} - 2$.

-   **Proposition**: let $K(\theta)/K$ where $\theta$ has minimal
    polynomial $m(x) \in K\lbrack x\rbrack$ of degree $n$. Then
    $$K\lbrack x\rbrack/{\langle m(x)\rangle} \cong = K(\theta) = \left\{ c_{0} + c_{1}\theta + \cdots + c_{n - 1}\theta^{n - 1}:c_{i} \in K \right\}$$
    and its elements are written uniquely: $K(\theta)$ is vector space
    over $K$ of dimension $n$ with basis
    $\left\{ 1,\theta,\ldots,\theta^{n - 1} \right\}$.

-   **Example**:
    ${\mathbb{Q}}(\sqrt[3]{\arg}) = \left\{ a + b\sqrt[3]{\arg} + c\sqrt[3]{\arg}:a,b,c \in {\mathbb{Q}} \right\} \cong {\mathbb{Q}}\lbrack x\rbrack/{\langle x^{3} - 2\rangle}$.
    ${\mathbb{Q}}(\omega\sqrt[3]{\arg})$ and
    ${\mathbb{Q}}(w^{2}\sqrt[3]{\arg})$ where $\omega = e^{2\pi i/3}$
    are isomorphic to ${\mathbb{Q}}(\sqrt[3]{\arg})$ as
    $\omega\sqrt[3]{\arg}$, $\omega\sqrt[3]{\arg}$ have same minimal
    polynomial.

## Degrees of field extensions

-   **Definition**: **degree** of field extension $L/K$ is
    $$\lbrack L:K\rbrack ≔ \dim_{L}(F)$$ Write
    $\lbrack L:K\rbrack < \infty$ if degree is finite.

-   **Example**:

    -   When $\theta$ algebraic over $K$ of degree $n$,
        $\left\lbrack K(\theta):K \right\rbrack = n$.

    -   Let $\theta$ transcendental over $K$, then
        $\left\lbrack K(\theta):K \right\rbrack = \infty$, so
        $\left\lbrack K(t):K \right\rbrack = \infty$,
        $\left\lbrack {\mathbb{Q}}(\pi):{\mathbb{Q}} \right\rbrack$,
        $\lbrack{\mathbb{R}}:{\mathbb{Q}}\rbrack = \infty$.

-   **Proposition**: let $\lbrack L:K\rbrack < \infty$, then every
    element in $L/K$ is algebraic over $K$ (in this case, $L/K$ is
    **algebraic extension**).

-   **Tower theorem**: let $K \subseteq M \subseteq L$ **tower** of
    field extensions. Then

    -   $\lbrack L:K\rbrack < \infty \Longleftrightarrow \lbrack L:M\rbrack < \infty \land \lbrack M:K\rbrack < \infty$.

    -   $\lbrack L:K\rbrack = \lbrack L:M\rbrack\lbrack M:K\rbrack$.

-   **Example**:

    -   $K = {\mathbb{Q}} \subset M = {\mathbb{Q}}(\sqrt{2}) \subset L = {\mathbb{Q}}(\sqrt{2},\sqrt{7})$.
        $M/K$ has basis $\left\{ 1,\sqrt{2} \right\}$ so
        $\lbrack M:K\rbrack = 2$. Let
        $\sqrt{7} \in {\mathbb{Q}}(\sqrt{2})$, then
        $\sqrt{7} = c + d\sqrt{2}$, $c,d \in {\mathbb{Q}}$ so
        $7 = \left( c^{2} + 2d^{2} \right) + 2cd\sqrt{2}$ so
        $7 = c^{2} + 2d^{2}$, $0 = 2cd$ so $d^{2} = \frac{7}{2}$ or
        $c^{2} = 7$, which are both contradictions. So
        $\lbrack L:K\rbrack = 4$ with basis
        $\{ 1,\sqrt{2},\sqrt{7},\sqrt{14}\}$.

    -   Let
        $K = {\mathbb{Q}} \subset M = {\mathbb{Q}}(i) \subset {\mathbb{Q}}(i,\sqrt{2})$.
        We know
        $\left\lbrack {\mathbb{Q}}(i):{\mathbb{Q}} \right\rbrack = 2$,
        and $\lbrack{\mathbb{Q}}(\sqrt{2}):{\mathbb{Q}}\rbrack = 2$,
        $\lbrack{\mathbb{Q}}(i,\sqrt{2}):{\mathbb{Q}}\rbrack = 2$ (since
        $i \notin {\mathbb{R}}$) so
        $\lbrack{\mathbb{Q}}(i,\sqrt{2}):{\mathbb{Q}}(\sqrt{2})\rbrack = 2$.

    -   Let
        $K = {\mathbb{Q}} \subset M = {\mathbb{Q}}(\sqrt{2}) \subset L = {\mathbb{Q}}(\sqrt{2},\sqrt[3]{\arg})$.
        Then $\lbrack{\mathbb{Q}}(\sqrt{2}):{\mathbb{Q}}\rbrack = 2$,
        $\lbrack{\mathbb{Q}}(\sqrt[3]{\arg}):{\mathbb{Q}}\rbrack = 3$ so
        $2~|~\lbrack L:K\rbrack$ and $3~|~\lbrack L:K\rbrack$ so
        $6~|~\lbrack L:K\rbrack$ so $\lbrack L:K\rbrack \geq 6$. But
        $\lbrack L:M\rbrack \leq 3$ and $\lbrack M:K\rbrack \leq 2$ so
        $\lbrack L:K\rbrack \leq 6$ hence $\lbrack L:K\rbrack = 6$.

-   More generally, we have
    $\left\lbrack K(\alpha,\beta):K \right\rbrack \leq \left\lbrack K(\alpha):K \right\rbrack\left\lbrack K(\beta):K \right\rbrack$.

-   **Example**:

    -   Let $\theta = \sqrt[3]{\arg} + 1$.
        ${\mathbb{Q}}(\theta) = {\mathbb{Q}}(\sqrt[3]{\arg})$ so minimal
        polynomial over $\mathbb{Q}$, $m$, has $\deg(m) = 3$.
        $(\theta - 1)^{3} = 4$ so minimal polynomial is
        $x^{3} - 3x^{2} + 3x - 5$.

    -   Let $\theta = \sqrt{2} + \sqrt{3}$.
        ${\mathbb{Q}}(\sqrt{2},\theta) = {\mathbb{Q}}(\sqrt{2},\sqrt{3})$
        which has degree $2$ over ${\mathbb{Q}}(\sqrt{2})$ so minimal
        polynomial of $\theta$ over ${\mathbb{Q}}(\sqrt{2})$ has degree
        $2$, $\left( \theta - \sqrt{2} \right) = \sqrt{3}$ so minimal
        polynomial is $x^{2} - 2\sqrt{2}x - 1$.

    -   Let $\theta = \sqrt{2} + \sqrt{3}$.
        ${\mathbb{Q}} \subset {\mathbb{Q}}(\theta) \subset {\mathbb{Q}}(\sqrt{2},\sqrt{7})$
        so
        $\left\lbrack {\mathbb{Q}}(\theta):{\mathbb{Q}} \right\rbrack~|~\lbrack{\mathbb{Q}}(\sqrt{2},\sqrt{3}):{\mathbb{Q}}\rbrack = 4$
        so
        $\left\lbrack {\mathbb{Q}}(\theta):{\mathbb{Q}} \right\rbrack \in \left\{ 1,2,4 \right\}$.
        Can't be $1$ as $\theta \notin {\mathbb{Q}}$. If it was $2$ then
        $1,\theta,\theta^{2}$ are linearly dependent over $\mathbb{Q}$
        which leads to a contradiction. So degree of minimal polynomial
        of $\theta$ over $\mathbb{Q}$ is $4$.
        $\theta^{2} = 5 + 2\sqrt{6} \Rightarrow \left( \theta^{2} - 5 \right)^{2} = 24$
        so minimal polynomial is $x^{4} - 10x^{2} + 1$.
