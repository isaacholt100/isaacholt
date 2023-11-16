# Quantum mechanics essentials

## States and wave functions

-   A particle's position on the real line is given by a wave function
    $\psi(x,t) \rightarrow {\mathbb{C}}$.

-   Probability of finding particle in $(a,b)$ is
    $$P(a,b) = \int_{a}^{b}\left| \psi(x,t) \right|^{2}dx$$

-   Time-evolution of wave function given by **Schrodinger equation**:
    $$i\hslash\frac{\partial\psi(x,t)}{\partial t} = - \frac{\hslash^{2}}{2m}\frac{\partial^{2}}{\partial x^{2}}\psi(x,t) + V(x)\psi(x,t) = \hat{H}\psi(x,t)$$
    where $$\hat{H} = \hat{K} + \hat{V}$$ is the Hamiltonian operator.

-   Schrodinger equation is **linear**, so any linear combination of
    solutions is another solution (**principle of superposition**).

-   An inner product is defined on the space of solutions to the
    Schrodinger equation:
    $${\langle\psi,\varphi\rangle} = \int_{- \infty}^{\infty}\psi^{\ast}(x,t)\varphi(x,t)dx$$

-   **Hilbert space**: vector space with inner product satisfying
    $${\langle\psi,a\varphi_{1} + b\varphi_{2}\rangle} = a{\langle\psi,\varphi_{1}\rangle} + b{\langle\psi,\varphi_{2}\rangle}\text{  and  }{\langle\psi,\varphi\rangle} = {\langle\varphi,\psi\rangle}^{\ast}$$

-   Write $\left| \arg \right\rangle$ (a **ket**) for vector in Hilbert
    space $\mathcal{H}$ corresponding to wave function $\psi$.

-   Write $\left\langle \arg \right|$ (a **bra**) for **dual** vector in
    $\mathcal{H^{\ast}}$.

-   **Dirac (bra-ket) notation**:
    $$\left\langle \varphi|\psi \right\rangle ≔ {\langle\varphi,\psi\rangle} = \int_{- \infty}^{\infty}\varphi^{\ast}(x,t)\psi(x,t)dx$$

-   **Dual** of vector space $V$ is set of linear functionals from $V$
    to $\mathbb{C}$:
    $$V^{\ast} ≔ \left\{ \Phi:V \rightarrow {\mathbb{C}}:\forall(a,b) \in {\mathbb{C}}^{2},\forall(z,w) \in V^{2},\quad\Phi(a\underline{z} + b\underline{w}) = a\Phi(\underline{z}) + b\Phi(\underline{w}) \right\}$$
    We have $\dim(V^{\ast}) = \dim(V)$.

-   If $V = {\mathbb{C}}^{n}$, can think of vectors in $V$ as
    $n \times 1$ matrices and vectors in $V^{\ast}$ as $1 \times n$
    matrices.

-   A quantum mechanical system is described by a ket
    $\left| \arg \right\rangle$ in Hilbert space $\mathcal{H}$. For all
    $\left| \arg \right\rangle,\left| \arg \right\rangle \in \mathcal{H}$:

    -   $\forall(a,b) \in {\mathbb{C}}^{2},a\left| \arg \right\rangle + b\left| \arg \right\rangle \in \mathcal{H}$

    -   Inner product of $\left| \arg \right\rangle$ with
        $\left| \arg \right\rangle$ is a complex number written as
        $\left\langle \psi|\varphi \right\rangle$. It is Hermitian:
        $\left\langle \psi|\varphi \right\rangle = \left\langle \varphi|\psi \right\rangle^{\ast}$.

    -   Inner product is **sesquilinear** (linear in the second factor,
        anti-linear in the first). For
        $\left| \arg \right\rangle = c_{1}\left| \arg \right\rangle + c_{2}\left| \arg \right\rangle$:

    $$\begin{aligned}
    \left\langle \psi|\varphi \right\rangle & = c_{1}\left\langle \psi|\varphi_{1} \right\rangle + c_{2}\left\langle \psi|\varphi_{2} \right\rangle \\
    \left\langle \varphi|\psi \right\rangle & = c_{1}^{\ast}\left\langle \varphi_{1}|\psi \right\rangle + c_{2}^{\ast}\left\langle \varphi_{2}|\psi \right\rangle
    \end{aligned}$$

    -   $\left\langle \psi|\psi \right\rangle \geq 0$ and
        $\left\langle \psi|\psi \right\rangle = 0 \Longleftrightarrow \left| \arg \right\rangle = 0$.

    -   States which differ by only a normalisation factor are
        physically equivalent:
        $$\forall c \in {\mathbb{C}}^{\ast},\quad\left| \arg \right\rangle \sim c\left| \arg \right\rangle$$
        So we normally assume that a state $\left| \arg \right\rangle$
        has norm $1$:
        $\left. \parallel\left| \arg \right\rangle \right.\parallel = 1$.

-   Note that the state labelled zero, $\left| \arg \right\rangle$, is
    not equal to the zero state (the $0$ vector).

-   If $\hat{A}$ is linear opearator then
    $\hat{A}\left( a\left| \arg \right\rangle + b\left| \arg \right\rangle \right) = a(\hat{A}\left| \arg \right\rangle) + b(\hat{A}\left| \arg \right\rangle)$

-   Products and combinations of linear operators are also linear
    operators.

-   **Adjoint (Hermitian conjugate)** of $\hat{A}$,
    ${\hat{A}}^{\dagger}$ is defined by
    $$\left\langle \arg \right|\left( {\hat{A}}^{\dagger}\left| \arg \right\rangle \right) = \arg^{\ast}$$

-   $\hat{A}$ is **self-adjoint (Hermitian)** if
    ${\hat{H}}^{\dagger} = \hat{H}$. Self-adjoint operators correspond
    to **observables** (measurable quantities) since they have real
    eigenvalues. Similarly, a **hermitian matrix** $H$ satisfies
    $H^{\dagger} = \left( H^{T} \right)^{\ast} = H$.

-   $\hat{U}$ is **unitary** if ${\hat{U}}^{\dagger}\hat{U} = \hat{I}$.
    Unitary operators describe time-evolution in quantum mechanics.
    Similarly, a unitary matrix $U$ satisfies
    $U^{\dagger}U = UU^{\dagger} = I$.

-   If we have $\left\langle n|m \right\rangle = \delta_{nm}$, the basis
    is orthonormal.

-   **Qubit system**: Hilbert space
    $\mathcal{H} = \text{ span}\left( \left| \arg \right\rangle,\left| \arg \right\rangle \right)$.
    Any $\left| \arg \right\rangle \in \mathcal{H}$ can be written as
    $a_{0}\left| \arg \right\rangle + a_{1}\left| \arg \right\rangle$.
    If
    $\left| \arg \right\rangle = b_{0}\left| \arg \right\rangle + b_{1}\left| \arg \right\rangle$,
    $$\begin{aligned}
    \left\langle \varphi|\psi \right\rangle & = \left( b_{0}^{\ast}\left\langle \arg \right| + b_{1}^{\ast}\left| \arg \right\rangle \right)\left( a_{0}\left| \arg \right\rangle + a_{1}\left| \arg \right\rangle \right) \\
     & = \arg^{\ast}a_{0}\left\langle 0|0 \right\rangle + \arg^{\ast}a_{1}\left\langle 1|1 \right\rangle + \arg^{\ast}a_{1}\left\langle 0|1 \right\rangle + \arg^{\ast}a_{0}\left\langle 1|0 \right\rangle = \arg^{\ast}a_{0} + \arg^{\ast}a_{0} \\
     & = \begin{pmatrix}
    \arg^{\ast} & \arg^{\ast}
    \end{pmatrix}\begin{pmatrix}
    1 & 0 \\
    0 & 1
    \end{pmatrix}\begin{pmatrix}
    a_{0} \\
    a_{1}
    \end{pmatrix}
    \end{aligned}$$ If
    $\left| \arg \right\rangle,\left| \arg \right\rangle$ is an energy
    eigenbasis, then
    $\hat{H}\left| \arg \right\rangle = E_{0}\left| \arg \right\rangle$
    and
    $\hat{H}\left| \arg \right\rangle = E_{1}\left| \arg \right\rangle$
    where $E_{0},E_{1}$ are eigenvalues.
    ${\mathbb{P}}(\text{measuring  }E_{0}) = a_{0}^{2} = \left| \left\langle 0|\psi \right\rangle \right|^{2},{\mathbb{P}}(\text{measuring  }E_{1}) = a_{1}^{2} = \left| \left\langle 1|\psi \right\rangle \right|^{2}$.
    If $a_{0}^{2} + a_{1}^{2} = 1$, then
    $\left\langle \psi|\psi \right\rangle = 1$ so $\psi$ is normalised.
    The expected energy measurement is
    ${\langle\arg\rangle} = E_{0}\left| a_{0} \right|^{2} + E_{1}\left| a_{1} \right|^{2}$.

-   **Matrix form** of operator $\hat{A}$:
    $$A_{nm} = \left\langle n|\hat{A}|m \right\rangle$$ For
    ${\hat{A}}^{\dagger}$,
    $\left\langle n|{\hat{A}}^{\dagger}|m \right\rangle = \arg^{\ast}$.

-   **Change of basis**: $B = S^{- 1}AS$.

-   **Schrodinger equation in braket notation**:
    $$i\hslash\frac{\partial}{\partial t}\left| \arg \right\rangle = \hat{H}\left| \arg \right\rangle$$
    If $\hat{H}$ independent of $t$, then
    $\left| \arg \right\rangle = e^{- \frac{i}{\hslash}\hat{H}t}$.

-   **Exponential of operator**:
    $$\exp(\hat{A}) = \sum_{n = 0}^{\infty}\frac{{\hat{A}}^{n}}{n!}$$

-   If $\hat{A} = \text{ diag}\left( a_{1},\ldots,a_{n} \right)$ is
    diagonal, then
    $\exp(\hat{A}) = \text{ diag}\left( e^{a_{1}},\ldots,e^{a_{n}} \right)$.

-   If $J^{2} = - I$ ($I$ is identity matrix) then
    $$\exp(Jt) = \cos(t)I + \sin(t)J$$

-   $\hat{A}$ **diagonalisable** if
    $\hat{A} = \hat{S}\hat{D}{\hat{S}}^{- 1}$ where $\hat{D}$ is
    diagonal and $\hat{S}$ has columns corresponding to eigenvectors of
    $\hat{A}$.

-   For $\hat{A}$ diagonalisable,
    $$\exp(\hat{A}) = \sum_{n = 0}^{\infty}\frac{\left( \hat{S}\hat{D}{\hat{S}}^{- 1} \right)^{n}}{n!} = \hat{S}\left( \sum_{n = 0}^{\infty}\frac{{\hat{D}}^{n}}{n!} \right){\hat{S}}^{- 1} = \hat{S}\exp(\hat{D}){\hat{S}}^{- 1}$$

-   For an orthonormal basis
    $\left\{ \left| \arg \right\rangle \right\}$, the identity operator
    is given by
    $$I = \sum_{n}\left| \arg \right\rangle\left\langle \arg \right|$$

-   **Spectral representation of operator**:
    $$\hat{A} = \sum_{n}\lambda_{n}\left| \arg \right\rangle\left\langle \arg \right|$$
    for orthonomal eigenvectors
    $\left\{ \left| \arg \right\rangle \right\}$. We can view a function
    $f$ acting on real numbers as acting on $\hat{A}$ by
    $$f\left( \hat{A} \right) = \sum_{n}f\left( \lambda_{n} \right)\left| \arg \right\rangle\left\langle \arg \right|$$

## Pure states and mixed states

-   **Pure state**: linear combination of states
    $\left| \arg \right\rangle = \left| \arg \right\rangle + \cdots + \left| \arg \right\rangle n)$.
    Probability of being in this state is $1$.

-   For a **density matrix** describing a **pure state**
    ${\hat{\rho}}_{\psi} = \left| \arg \right\rangle\left\langle \arg \right|$,
    $$\begin{aligned}
    \operatorname{tr}({\hat{\rho}}_{\psi}) & = \sum_{n}\left\langle n|\hat{\rho}|n \right\rangle = \sum_{n}\left\langle n|\psi \right\rangle\left\langle \psi|n \right\rangle \\
     & = \sum_{n}\left\langle \psi|n \right\rangle\left\langle n|\psi \right\rangle = \left\langle \arg \right|\left( \sum_{n}\left| \arg \right\rangle\left\langle \arg \right| \right)\left| \arg \right\rangle = \left\langle \psi|\psi \right\rangle = 1
    \end{aligned}$$ Also
    $\operatorname{tr}({\hat{\rho}}_{\psi}^{2}) = 1$.

-   $$\begin{aligned}
    {\langle\arg\rangle}_{\psi} & = \left\langle \psi|\hat{H}|I|\psi \right\rangle = \sum_{n}\left\langle \psi|\hat{H}|n \right\rangle\left\langle n|\psi \right\rangle \\
     & = \sum_{n}\left\langle n|\psi \right\rangle\left\langle \psi|\hat{H}|n \right\rangle = \sum_{n}\left\langle n|{\hat{\rho}}_{\psi}|\hat{H}|n \right\rangle = \operatorname{tr}({\hat{\rho}}_{\psi}\hat{H})
    \end{aligned}$$

-   **Mixed state**: probability $p_{i}$ for each state
    $\left| \arg \right\rangle$.
    ${\hat{\rho}}_{i} = \left| \arg \right\rangle\left\langle \arg \right|$
    and $$\hat{\rho} = \sum_{i}p_{i}{\hat{\rho}}_{i}$$ For observable
    $\hat{A}$ expressed in matrix form with basis as the states
    $\left| \arg \right\rangle$, then
    ${\langle\arg\rangle} = \operatorname{tr}(\hat{\rho}\hat{A})$. For
    mixed state, we still have $\operatorname{tr}(\hat{\rho}) = 1$ but
    $\operatorname{tr}({\hat{\rho}}^{2}) = \sum_{i}p_{i}^{2} \leq 1$
    with equality only when some $p_{i} = 1$ (i.e. a pure state). It
    conveys how "mixed" the state is.

-   **Example**: for ensemble
    $\left\{ \left( \frac{3}{4},\left| \arg \right\rangle \right),\left( \frac{1}{4},\left| \arg \right\rangle \right) \right\}$,
    $$\hat{\rho} = \frac{3}{4}\left| \arg \right\rangle\left\langle \arg \right| + \frac{1}{4}\left| \arg \right\rangle\left\langle \arg \right| = \begin{pmatrix}
    3/4 & 0 \\
    0 & 1/4
    \end{pmatrix}$$ This ensemble is **not** unique:
    $$\left\{ \left( \frac{1}{2},\sqrt{\frac{3}{4}}\left| \arg \right\rangle + \sqrt{\frac{1}{4}}\left| \arg \right\rangle \right),\left( \frac{1}{2},\sqrt{\frac{3}{4}}\left| \arg \right\rangle - \sqrt{\frac{1}{4}}\left| \arg \right\rangle \right) \right\}$$
    gives an equivalent density matrix: $$\begin{aligned}
    {\hat{\rho}}_{1} & = \left( \sqrt{\frac{3}{4}}\left| \arg \right\rangle + \sqrt{\frac{1}{4}}\left| \arg \right\rangle \right)\left( \sqrt{\frac{3}{4}}\left\langle \arg \right| + \sqrt{\frac{1}{4}}\left\langle \arg \right| \right) \\
     & = \frac{3}{4}\left| \arg \right\rangle\left\langle \arg \right| + \frac{1}{4}\left| \arg \right\rangle\left\langle \arg \right| + \ldots,{\hat{\rho}}_{2} = \ldots,\frac{1}{2}{\hat{\rho}}_{1} + \frac{1}{2}{\hat{\rho}}_{2} = \begin{pmatrix}
    3/4 & 0 \\
    0 & 1/4
    \end{pmatrix}
    \end{aligned}$$

-   **Definition**: **trace distance** between two density matrices:
    $$D\left( {\hat{\rho}}_{1},{\hat{\rho}}_{2} \right) = \frac{1}{2}\operatorname{tr}\left| {\hat{\rho}}_{1} - {\hat{\rho}}_{2} \right| = \sum_{i}\left| \lambda_{i} \right|$$
    where $\left| \hat{A} \right| = \sqrt{{\hat{A}}^{\dagger}\hat{A}}$
    and $\lambda_{i}$ are the eigenvalues of
    ${\hat{\rho}}_{1} - {\hat{\rho}}_{2}$.

# Bipartite systems

## Tensor products

-   **Tensor product**
    $\left| \arg \right\rangle \otimes \left| \arg \right\rangle$ in
    $H_{1} \otimes H_{2}$ satisfies:

    -   **Scalar multiplication**:
        $c\left( \left| \arg \right\rangle \otimes \left| \arg \right\rangle \right) = \left( c\left| \arg \right\rangle \right) \otimes \left| \arg \right\rangle = \left| \arg \right\rangle \otimes \left( c\left| \arg \right\rangle \right)$

    -   **Linearity**:

        -   $a\left| \arg \right\rangle \otimes \left| \arg \right\rangle + b\left| \arg \right\rangle \otimes \left| \arg \right\rangle = \left| \arg \right\rangle \otimes \left( a\left| \arg \right\rangle + b\left| \arg \right\rangle \right)$

        -   $a\left| \arg \right\rangle \otimes \left| \arg \right\rangle + b\left| \arg \right\rangle \otimes \left| \arg \right\rangle = \left( a\left| \arg \right\rangle + b\left| \arg \right\rangle \right) \otimes \left| \arg \right\rangle$

-   Inner products of $H_{1}$ and $H_{2}$ induce an inner product on
    $H_{1} \otimes H_{2}$: for
    $\left| \arg \right\rangle,\left| \arg \right\rangle \in H_{1}$,
    $\left| \arg \right\rangle,\left| \arg \right\rangle \in H_{2}$,
    $$\left( \left\langle \arg \right| \otimes \left\langle \arg \right| \right)\left( \left| \arg \right\rangle \otimes \left| \arg \right\rangle \right) = \left\langle \psi_{1}|\psi_{2} \right\rangle\left\langle \varphi_{1}|\varphi_{2} \right\rangle$$

-   For bases $\left\{ \left| \arg \right\rangle \right\}$ for $H_{1}$
    and $\left\{ \left| \arg \right\rangle \right\}$ for $H_{2}$,
    $\left\{ \left| \arg \right\rangle \otimes \left| \arg \right\rangle \right\}$
    is basis for $H_{1} \otimes H_{2}$: for
    $\left| \arg \right\rangle \in H_{1}$,
    $\left| \arg \right\rangle \in H_{2}$,
    $$\left| \arg \right\rangle \otimes \left| \arg \right\rangle = \left( \sum_{i}a_{i}\left| \arg \right\rangle \right) \otimes \left( \sum_{j}b_{j}\left| \arg \right\rangle \right) = \sum_{i,j}a_{i}b_{j}\left| \arg \right\rangle \otimes \left| \arg \right\rangle$$

-   The most general vector
    $\left| \arg \right\rangle \in H_{1} \otimes H_{2}$ is
    $$\left| \arg \right\rangle = \sum_{i,j}c_{i,j}\left| \arg \right\rangle \otimes \left| \arg \right\rangle$$
    Generally, this cannot be written as a tensor product
    $\left| \arg \right\rangle \otimes \left| \arg \right\rangle$. If it
    can be, it is a **separable** state. If not, it is **entangled**
    (e.g. a linear combination of separable states is generally
    entangled).

-   If $\left\{ \left| \arg \right\rangle \right\}$,
    $\left\{ \left| \arg \right\rangle \right\}$ orthonormal then the
    inner product in $H_{1} \otimes H_{2}$ is given by $$\begin{aligned}
    \left\langle \varphi|\psi \right\rangle & = \left( \sum_{i,j}d_{i,j}^{\ast}\left\langle \arg \right| \otimes \left\langle \arg \right| \right)\left( \sum_{m,n}c_{m,m}\left| \arg \right\rangle \otimes \left| \arg \right\rangle \right) \\
     & = \sum_{i,j,m,n}d_{i,j}^{\ast}c_{m,n}\left\langle i|m \right\rangle\left\langle j|n \right\rangle = \sum_{i,j}c_{i,j}^{\ast}d_{i,j}
    \end{aligned}$$
