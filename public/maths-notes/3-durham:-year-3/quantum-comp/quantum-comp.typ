#import "../../template.typ": *
#show: doc => template(doc, hidden: ("proof", ), slides: false)

// FIND: - \*(\w+)\*: ([\s\S]*?)(?=\n-|\n\n)\n
// REPLACE: #$1[\n    $2\n]\n

#let hbar = $planck.reduce$
#let ip(a, b) = $angle.l #a, #b angle.r$
#let ket(arg) = $#h(0.2pt) | #h(0.2pt) arg #h(0.2pt) angle.r$
#let bra(arg) = $angle.l #h(0.2pt) arg #h(0.2pt) | #h(0.2pt)$
#let braket(..args) = $angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r$
#let Ket(arg) = $lr(| #h(1pt) arg #h(1pt) angle.r)$
#let Bra(arg) = $lr(angle.l #h(1pt) arg #h(1pt) |)$
#let Braket(..args) = $lr(angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r)$
#let span = $op("span")$
#let conj(arg) = $arg^*$
#let expected(arg) = $angle.l arg angle.r$
#let vd(vector) = $bold(vector)$
#let nl = [\ ]
#let End = $"End"$
#let tp = $times.circle$ // tensor product

= Quantum mechanics essentials

== States and wave functions

- Probability of finding particle in $(a, b)$ is $ P(a, b; t) = integral_a^b |psi(x, t)|^2 dif x $ Wave function is normalised so that $P(-oo, +oo; t) = 1$.

== Dirac notation

#definition[
    *Dual* of vector space $V$ is set of linear functionals from $V$ to $CC$: $ V^* := {Phi: V -> CC: forall a, b in CC, forall z, w in V, quad Phi(a vd(z) + b vd(w)) = a Phi(vd(z)) + b Phi(vd(w)) } $ We have $dim(V^*) = dim(V)$.
]
#remark[
    If $V$ has inner product $ip(dot.op, dot.op)$, then an isomorphism is given by $vd(z) |-> Phi_(vd(z)) (dot.op) = ip(vd(z), dot.op)$.
]
#definition[
    *Dual* of $vd(z) in V$ is the corresponding element in $V^*$, i.e. $Phi_(vd(z))$.
]
#remark[
    If $V = CC^n$, can think of vectors in $V$ as $n times 1$ matrices and vectors in $V^*$ as $1 times n$ matrices.
]
#definition[
    *Dirac notation* denotes vectors in a Hilbert space or its dual:
    - Write $ket(psi)$ (a *ket*) for vector in Hilbert space $cal(H)$ corresponding to wave function $psi$.
    - Write $bra(phi)$ (a *bra*) for dual vector in $cal(H)^*$.
    - A *bra-ket* denotes an inner product: $ braket(phi, psi) := ip(phi, psi) = integral_(-oo)^oo phi^* (x, t) psi(x, t) dif x $
]

== Hilbert spaces

#definition[
    *Hilbert space* is real or complex vector space with Hermitian inner product that is also a complete metric space with metric induced by the inner product. In particular, inner product satisfies:
    // - $forall (a, b) in CC^2, a ket(psi) + b ket(phi) in cal(H)$
    - *Hermiticity*: $braket(psi, phi) = braket(phi, psi)^*$.
    - *Sesquilinearity* (linear in the second factor, anti-linear in the first). For $ket(phi) = c_1 ket(phi_1) + c_2 ket(phi_2)$:
    $ braket(psi, phi) & = c_1 braket(psi, phi_1) + c_2 braket(psi, phi_2) \ braket(phi, psi) & = c_1^* braket(phi_1, psi) + c_2^* braket(phi_2, psi) $
    - *Positive definiteness*: $braket(psi, psi) >= 0$ and $braket(psi, psi) = 0 <==> ket(psi) = 0$ (this corresponds with a *physical state* condition).
]
#definition[
    A quantum mechanical system is described by a *state* $ket(psi)$ in Hilbert space $cal(H)$.
]
#remark[
    States which differ by only a normalisation factor are physically equivalent: $ forall c in CC^*, quad ket(psi) tilde.op c ket(psi) $ For this reason, pure quantum mechanical states are called *rays* in the Hilbert space, and we normally assume that a state $ket(psi)$ has norm $1$: $norm(ket(psi)) = 1$.
]
#remark[
    Note that the state labelled zero, $ket(0)$, is not equal to the zero state (the $0$ vector).
]

== Operators

#definition[
    $hat(A): cal(H) -> cal(H)$ is *linear operator* if $ forall a, b in CC, forall ket(psi), ket(phi) in cal(H), quad hat(A) (a ket(psi) + b ket(phi)) = a \(hat(A) ket(psi)\) + b \(hat(A) ket(phi)\) $
]
#proposition[
    Products and linear combinations of linear operators are also linear operators.
]
#definition[
    *Adjoint (Hermitian conjugate)* of $hat(A)$, $hat(A)^dagger$, is defined by $ bra(psi) hat(A)^dagger ket(phi) = conj((bra(phi) hat(A) ket(psi))) $ for all states $ket(psi)$ and $ket(phi)$.
]
#definition[
    $hat(H)$ is *self-adjoint (Hermitian)* if $hat(H)^dagger = hat(H)$. Self-adjoint operators correspond to *observables* (measurable quantities) since they have real eigenvalues.
]
#definition[
    $hat(U)$ is *unitary* if $hat(U)^dagger hat(U) = hat(I)$. Unitary operators describe time-evolution in quantum mechanics.
]
#definition[
    *Commutator* of operators $hat(A)$ and $hat(B)$ is $ \[hat(A), hat(B)\] = hat(A) hat(B) - hat(B) hat(A) $
]
#definition[
    *Anti-commutator* of operators $hat(A)$ and $hat(B)$ is $ \{hat(A), hat(B)\} = hat(A) hat(B) + hat(B) hat(A) $
]
#definition[
    *Expectation value* of observable $hat(A)$ on state $ket(psi)$ is $ expected(A)_psi := braket(psi, hat(A), psi) $ Interpreted as average outcome of many measurements of $hat(A)$ on same state $ket(psi)$.
]

== Matrix representation

#definition[
    *Matrix form* of operator $hat(A)$ with respect to orthonormal basis ${ket(n)}$ is given by $ A_(i j) = braket(i, hat(A), j)$.
]
#proposition[
    For operator $hat(A)$ with matrix representation $A$ in basis ${ket(n)}$, matrix representation of $hat(A)$ in basis ${ket(m)}$ is $B = S A S^(-1)$ where $S$ is change of basis matrix from old basis ${ket(n)}$ to new basis ${ket(m)}$.
]

== Time-evolution

#theorem[
    Time-evolution of state is given by *Schrodinger equation*: $ i hbar dif / (dif t) ket(psi(t)) = hat(H) ket(psi(t)) ==> ket(psi(t)) = hat(U)_t ket(psi(0)) $ where $hat(H) = hat(K) + hat(V)$ is Hamiltonian operator, $hat(U)_t$ is unitary operator. If $hat(H)$ independent of $t$, then $hat(U)_t = exp(-i/planck.reduce t hat(H))$.
]
- *Principle of superposition*: Schrodinger equation is linear, so any linear combination of solutions is another solution.
#definition[
    *Exponential* of operator $hat(A)$ is $ exp\(hat(A)\) := sum_(n in NN_0) hat(A)^n / n! $
]

= Measurement and uncertainty

== Observables

#proposition[
    For Hilbert space of finite dimension $N$, operator $hat(A)$ has $N$ eigenvalues (counting multiplicities). Eigenvalues of Hermitian operator $hat(M)$ correspond to possible values of the measurable quantity it represents.
]
#definition[
    *Spectrum* of operator $hat(H)$ is $ "Spec"\(hat(H)\) := \{lambda in CC: hat(H) - lambda hat(I) "non invertible"\} $ For finite-dimensional Hilbert space, this is equal to the set of eigenvalues of $hat(H)$.
]
#proposition[
    Eigenstates $ket(n)$ of Hermitian operator $hat(H)$ corresponding to different eigenvalues $lambda_n$ are orthogonal. If eigenvalue is degenerate (multiplicity greater than one) then for each eigenspace (vector space spanned by the eigenvectors) with dimension greater than one, we can choose an orthogonal basis of eigenstates.
]
#definition[
    Let $hat(A)$ have orthonormal eigenstates ${ket(v_i): i in [N]}$ and corresponding eigenvalues ${lambda_i: i in [N]}$. *Spectral representation* of $hat(A)$ is $ hat(A) = sum_(i = 1)^N lambda_i ket(v_i) bra(v_i) $ In particular, only eigenvalue of $hat(I)$ is $1$ with degeneracy $N$, so for any orthonormal basis ${ket(v_i): i in [N]}$  of $cal(H)$: $ hat(I) = sum_(i = 1)^N ket(v_i) bra(v_i) $
]
#definition[
    When measurement is made on state $ket(psi) = sum_(i = 1)^N c_i ket(v_i)$, result is $lambda$ with probability $ p = sum_(i in [N], lambda_i = lambda) |braket(v_i, psi)|^2 = sum_(i in [N], lambda_i = lambda) |c_i|^2 $ If result is $lambda$, measuring again immediately after the measurement will yield $lambda$, so state collapses (up to irrelevant phase $e^(i alpha)$, $alpha in RR$) to $ 1/sqrt(p) sum_(i in [N], lambda_i = lambda) c_i ket(v_i) $ This is *collapse of the wavefunction* and cannot be represented by unitary transformation, so is not reversible.
// - *Definition*: $hat(A)$ *diagonalisable* if $hat(A) = hat(S) hat(D) hat(S)^(-1)$ where $hat(D)$ is diagonal and $hat(S)$ has columns corresponding to eigenvectors of $hat(A)$.
// - For $hat(A)$ diagonalisable, $ exp(hat(A)) = sum_(n = 0)^oo (hat(S) hat(D) hat(S)^(-1))^n / (n!) = hat(S) (sum_(n = 0)^oo hat(D)^n / (n!)) hat(S)^(-1) = hat(S) exp(hat(D)) hat(S)^(-1) $
]
#definition[
    Linear operator $hat(P)$ is *projector* if $hat(P)^dagger = hat(P)$ and $hat(P)^2 = hat(P)$.
]
#definition[
    For orthonormal eigenstates ${ket(v_i): i in [N]}$ of operator $hat(A)$ and corresponding eigenvalues ${lambda_i: i in [N]}$, define projection operator $ hat(P)_lambda = sum_(i in [N], lambda_i = lambda) ket(v_i) bra(v_i) $
]
#proposition[
    Probability of measurement $hat(A)$ on state $ket(psi)$ yielding $lambda$ is $p_lambda = braket(psi, hat(P)_lambda, psi)$ and state collapses to $1/sqrt(p_lambda) hat(P)_lambda ket(psi)$.
]
#definition[
    $hat(A)$ and $hat(B)$ are *compatible* if $\[hat(A), hat(B)\] = 0$.
]
#remark[
    State can only have definite values for observables $A$ and $B$ if it is simultaneous eigenstate of both $hat(A)$ and $hat(B)$. There always exist simultaneous eigenstates for compatible operators.
]
#remark[
    If $hat(A)$ and $hat(B)$ not compatible, measuring $A$ then $B$ then $A$ again will not always give same result for both measurements of $A$.
]

== Density matrices

#definition[
    A state is *pure state* if it is definite, i.e. state of system is completely known, and only uncertainties are due to inherent uncertain nature of quantum mechanics.
]
#definition[
    *Density matrix (density operator)* of *pure state* $ket(psi)$ is $ hat(rho) := ket(psi) bra(psi) $
]
#theorem[
    There is bijection between density matrices and pure states, and $ hat(M) ket(psi) = lambda ket(psi) quad & <==> quad hat(M) hat(rho) = lambda hat(rho) \ ket(psi) -> hat(U) ket(psi) quad & <==> quad hat(rho) -> hat(U) hat(rho) hat(U)^dagger $ i.e. transforming state $ket(psi)$ by unitary operator $hat(U)$ is equivalent to transforming density matrix $hat(rho)$ to $hat(U) hat(rho) hat(U)^dagger$.
]
#definition[
    For any orthonormal basis states ${ket(v_i): i in [N]}$, *trace* of $hat(A)$ is $ tr\(hat(A)\) = sum_(i = 1)^N braket(v_i, hat(A), v_i) $
]
#proposition[
    Trace satisfies *cyclicity*: $ tr(A B C) = tr(B C A) = tr(C A B) $
]
#proposition[
    Density matrix of pure state is a projector.
]
#proposition[
    Density matrix $hat(rho)$ of pure state satisfies $tr\(hat(rho)\) = tr\(hat(rho)^2\) = 1$.
]
#definition[
    *Mixed state* is one where state of system is not known. It is ensemble of pure states, each with associated probability of system being in that state: ${(p_i, ket(v_i)): i in [M]}$, where each $ket(v_i)$ is normalised. This is classical uncertainty rather than quantum uncertainty.
]
#definition[
    *Density matrix* of *mixed state* is linear combination of density matrices for each pure state weighted by probability: $ hat(rho) := sum_(i = 1)^M p_i ket(v_i) bra(v_i) $ Can generalise definition to include possibility of ensembles containing mixed states: $hat(rho) = sum_(i = 1)^M p_i hat(rho)_i$ where $hat(rho)_i$ are mixed and/or pure density matrices.
]
#note[
    One density matrix may be given by multiple mixed states.
]
#proposition[
    Let $hat(A)$ observable, then expected value of measuring $hat(A)$ on $hat(rho)$ is $expected(hat(A)) = tr\(hat(rho) hat(A)\)$.
]
#proposition[
    $hat(rho)$ is a density matrix of a pure/mixed state iff it satisfies:
    - *Normalised*: $tr(hat(rho)) = 1$
    - *Hermitian*: $hat(rho)^dagger = hat(rho)$
    - *Semi-positive-definite*: for every state $ket(phi)$, $braket(phi, hat(rho), phi) >= 0$ (can be $= 0$ when $ket(phi) != 0$). This holds if $hat(rho)$ has non-negative eigenvalues, or if $tr\(hat(rho)^2\) <= 1$.
]
#proposition[
    After taking measurement of pure or mixed state $hat(rho)$:  
    - Result is $lambda$ with probability $p_lambda = tr\(hat(P)_lambda hat(rho) hat(P)_lambda\) = tr\(hat(P)_lambda hat(rho)\) = tr\(hat(rho) hat(P)_lambda\)$.
    - Density matrix after measuring value of $lambda$ is $1/p_lambda hat(P)_lambda hat(rho) hat(P)_lambda$.
]
#theorem[
    Let $hat(rho)$ be density matrix, then $hat(rho)$ corresponds to pure state iff $tr\(hat(rho)^2\) = 1$.
]

= Qubits and the Bloch sphere

== Qubits

#definition[
    A *qubit* is state in two-dimensional Hilbert space. Usually *computational basis* ${ket(0), ket(1)}$ denotes basis for such a Hilbert space.
]
#proposition[
    General pure state in qubit system is of the form $ ket(psi) = cos(theta / 2) ket(0) + e^(i phi) sin(theta / 2) ket(1), quad 0 <= theta <= pi, 0 <= phi < 2pi $ So there is bijection between pure qubit states and points on $S^2$, called the *Bloch sphere*. Any point on Bloch sphere can be labelled by its position vector: $ vd(r) = vec(x, y, z), quad x = sin(theta) cos(phi), y = sin(theta) sin(phi), z = cos(theta) $
]
#definition[
    We define six special states on the Bloch sphere: $ 
ket(+) := 1/sqrt(2) (ket(0) + ket(1)) <-> 1/sqrt(2) (1, 1)^T: & quad vd(r) = (1, 0, 0)^T, quad (theta, phi) = (pi\/2, 0) \
ket(-) := 1/sqrt(2) (ket(0) - ket(1)) <-> 1/sqrt(2) (1, -1)^T: & quad vd(r) = (-1, 0, 0)^T, quad (theta, phi) = (pi\/2, pi) \
ket(L) := 1/sqrt(2) (ket(0) + i ket(1)) <-> 1/sqrt(2) (1, i)^T: & quad vd(r) = (0, 1, 0)^T, quad (theta, phi) = (pi\/2, pi\/2) \
ket(R) := 1/sqrt(2) (ket(0) - i ket(1)) <-> 1/sqrt(2) (1, -i)^T: & quad vd(r) = (0, -1, 0)^T, quad (theta, phi) = (pi\/2, 3pi\/2) \
ket(0) <-> (1, 0)^T: & quad vd(r) = (0, 0, 1)^T, quad (theta, phi) = (0, dot.op) \
ket(1) <-> (0, 1)^T: & quad vd(r) = (0, 0, -1)^T, quad (theta, phi) = (pi, dot.op) $
]

== Inside the Bloch sphere

#definition[
    *Pauli $sigma$-matrices* are $ sigma_1 := mat(0, 1; 1, 0), quad sigma_2 := mat(0, -i; i, 0), quad sigma_3 := mat(1, 0; 0, -1) $
]
#definition[
    For pure state $ket(psi)$, *Bloch vector* $vd(r)$ is corresponding point on Bloch sphere. For mixed state ${(p_i, ket(v_i)): i in [M]}$, *Bloch vector* is $ vd(r) := sum_(i = 1)^M p_i vd(r_i) $ where $vd(r_i)$ is Bloch vector corresponding to pure state $ket(v_i)$.
]
#proposition[
    Density matrix for state with Bloch vector $vd(r)$ is $ rho = 1/2 (I_2 + vd(r) dot.op sigma) $ where $vd(r) dot.op sigma = r_1 sigma_1 + r_2 sigma_2 + r_3 sigma_3 = x sigma_1 + y sigma_2 + z sigma_3$.
]
#proposition[
    State is mixed iff its Bloch vector $vd(r)$ satisfies $|vd(r)| < 1$.
]
#proposition[
    For any density matrix $rho$ defined by Bloch vector $vd(r)$, $ tr\(rho^2\) = 1/2 (1 + |vd(r)|^2) $
]

== Time evolution of a qubit

#remark[
    Unitary transformations of a qubit correspond to rotations of points on/in Bloch sphere about the origin, representing the fact that unitary transformations cannot transform pure states to mixed states.
]
#remark[
    Measurements transform any state to a pure state.
]
#proposition[
    $tr(rho^2)$ is invariant under unitary transformations (time evolution).
]
- $tr(rho^2)$ measures how mixed a state is: $tr(rho^2) = 1$ for pure states, $tr(rho^2) = 1/2$ for the most mixed single qubit state, corresponding to the origin: $vd(r) = vd(0)$, $rho = 1/2 I$.
#proposition[
    Mixing states can never produce a state further from origin than furthest initial state.
]
#note[
    There are an infinite number of ways of writing a mixed state as an ensemble of two pure states: any line passing through the point represented by the mixed states intersects with the Bloch sphere twice - the intersection points give the pure states in the ensemble.
]
#definition[
    *Trace distance* between density matrices $hat(rho)_1$ and $hat(rho)_2$ is $ D\(hat(rho)_1, hat(rho)_2\) := 1/2 tr |hat(rho)_1 - hat(rho)_2| = 1/4 tr |(vd(r_1) - vd(r_2)) dot.op sigma| = 1/2 |vd(r_1) - vd(r_2)| = 1/2 sum_(i = 1)^N |lambda_i| $ where $|hat(A)| = sqrt(hat(A)^dagger hat(A))$, $lambda_i$ are the eigenvalues of $hat(rho)_1 - hat(rho)_2$ (trace distance is equal to sum of eigenvalues since $hat(rho)_1 - hat(rho)_2$ is Hermitian).
]
#remark[
    Trace distance gives notion of distance between two states.
]
#proposition[
    Trace distance defines a *metric* on set of density matrices:
    - *Non-negative*: $D\(hat(rho)_1, hat(rho)_2\) >= 0$.
    - *Separates points*: $D\(hat(rho)_1, hat(rho)_2\) = 0 <==> hat(rho)_1 = hat(rho)_2$.
    - *Symmetric*: $D\(hat(rho)_1, hat(rho)_2\) = D\(hat(rho)_2, hat(rho)_1\)$.
    - *Triangle inequality*: $D\(hat(rho)_1, hat(rho)_3\) <= D\(hat(rho)_1, hat(rho)_2\) + D\(hat(rho)_2, hat(rho)_3\)$
]

== Pauli matrices

#definition[
    *Levi-Cevita* tensor $epsilon_(i j k)$ is defined for ${i, j, k} subset.eq {1, 2, 3}$ as:
    - $epsilon_(1 2 3) := epsilon_(2 3 1) := epsilon_(3 1 2) := 1$.
    - $epsilon_(3 2 1) := epsilon_(1 3 2) := epsilon_(2 1 3) := -1$.
    - $epsilon_(i j k) := 0$ otherwise.
]
#proposition[
    Pauli matrices satisfy following properties:
    - *Hermitian*: $sigma_i^dagger = sigma_i$.
    - *Traceless*: $tr(sigma_i) = 0$.
    - $[sigma_i, sigma_j] = sigma_i sigma_j - sigma_j sigma_i = 2i epsilon_(i j k) sigma_k$.
    - ${sigma_i, sigma_j} = sigma_i sigma_j + sigma_j sigma_i = 2 delta_(i j) I_2$.
    - $sigma_i sigma_j = delta_(i j) I_2 + i epsilon_(i j k) sigma_k$.
    - They form a basis for vector space of $2 times 2$ Hermitian traceless matrices over $RR$.
]
#proposition[
    Define measurement operators $X, Y, Z$ as $ X & := 1/2 (I_2 - sigma_1), quad Y := 1/2 (I_2 - sigma_2), quad Z := 1/2 (I_2 - sigma_3) $
    $X$, $Y$ and $Z$ have their eigenvectors as the six special Bloch states, with eigenvalues $0$ or $1$: $ X ket(+) & = 0 ket(+), quad X ket(-) = 1 ket(-), \ Y ket(L) & = 0 ket(L), quad Y ket(R) = 1 ket(R), \ Z ket(0) & = 0 ket(0), quad Z ket(1) = 1 ket(1) $
]
#proposition[
    Exponentials of Pauli matrices are unitary matrices: $forall alpha in RR$, $ exp(i alpha sigma_1) & = cos(alpha) I_2 + i sin(alpha) sigma_1, \ exp(i alpha sigma_2) & = cos(alpha) I_2 + i sin(alpha) sigma_2, \ exp(i alpha sigma_3) & = cos(alpha) I_2 + i sin(alpha) sigma_3 $
]
#proposition[
    For $alpha in RR$, $vd(n) in RR^3$, $|vd(n)|^2 = 1$, $ U_alpha (vd(n)) := exp(i alpha vd(n) dot.op sigma) = cos(alpha) I_2 + i sin(alpha) vd(n) dot.op sigma $ is unitary transformation. If density matrix $rho = 1/2 (I_2 + vd(r) dot.op sigma)$ evolves with time according to this operator, then $ rho -> U_alpha (vd(n)) rho U_alpha (vd(n))^dagger = 1/2 (I_2 + (R_alpha (vd(n)) vd(r)) dot.op sigma) $ where $R_alpha (vd(n))$ is $3 times 3$ orthogonal matrix corresponding to rotation of angle $2 alpha$ about axis in the direction of $vd(n)$.
]

= Bipartite systems

== Tensor products

#definition[
    *Tensor product* $ket(phi) tp ket(psi)$ in $H_1 tp H_2$ satisfies:
    - *Scalar multiplication*: $c(ket(phi) tp ket(psi)) = (c ket(phi)) tp ket(psi) = ket(phi) tp (c ket(psi))$.
    - *Linearity*:
        - $a ket(psi) tp ket(phi_1) + b ket(psi) tp ket(phi_2) = ket(psi) tp (a ket(phi_1) + b ket(phi_2))$.
        - $a ket(psi_1) tp ket(phi) + b ket(psi_2) tp ket(phi) = (a ket(psi_1) + b ket(psi_2)) tp ket(phi)$.
]
#definition[
    Induced inner product on $H_1 tp H_2$ is defined as $ (bra(psi_1) tp bra(phi_1))(ket(psi_2) tp ket(phi_2)) = braket(psi_1, psi_2) braket(phi_1, phi_2) $
]
#proposition[
    For bases $\{ket(v_i): i in [N_1]\}$ for $H_1$ and $\{ket(w_j): j in [N_2]\}$ for $H_2$, ${ket(v_i) tp ket(w_j), i in [N_1], j in [N_2]}$ is basis for $H_1 tp H_2$ and is orthonormal if $\{ket(v_i)\}$ and $\{ket(v_j)\}$ are orthonormal.
]
#definition[
    Most general vector $ket(psi) in H_1 tp H_2$ can be expressed as $ ket(psi) = sum_(i in [N_1], thick j in [N_2]) c_(i, j) ket(v_i) tp ket(v_j) $ Generally, this cannot be written as a tensor product $ket(psi) tp ket(phi)$. If it can be, it is a *separable* state. If not, it is *entangled*.
]
#definition[
    Hilbert space of $N$-qubit system is $2^N$-dimensional Hilbert space $H_N = H_q^(tp N)$ where $H_q$ is a single qubit Hilbert space.
]
#example[
    Let $H_3 = H_q tp H_q tp H_q$. Operator $hat(I) tp hat(sigma_1) tp hat(I)$ acts on the second qubit and leaves the other two invariant.
]

== Linear operators and local unitary operations

#definition[
    Linear operators on $H_1 tp H_2$ are linear combinations of $hat(A) tp hat(B)$, where $ \(hat(A) tp hat(B)\) (ket(psi) tp ket(phi)) := \(hat(A) ket(psi)\) tp \(hat(B) ket(phi)\) $
]
#proposition[
    Properties of tensor product of linear operators:
    - $hat(A) tp hat(B) + hat(C) tp hat(B) = \(hat(A) + hat(C)\) tp hat(B)$.
    - $hat(A) tp hat(B) + hat(A) tp hat(D) = hat(A) tp \(hat(B) + hat(D)\)$.
    - $\(hat(A) tp hat(B)\)^dagger = hat(A)^dagger tp hat(B)^dagger$.
    - $\(hat(A) tp hat(B)\)\(hat(C) tp hat(D)\) = \(hat(A) hat(C) tp hat(B) hat(D)\)$.
    - $tr_(cal(H)_A tp cal(H)_B) \(hat(A) tp hat(B)\) = tr_(cal(H)_A) \(hat(A)\) tr_(cal(H)_B) \(hat(B)\)$.
    In particular, tensor product of linear operators preserves unitarity, Hermiticity, positivity, and tensor product of two projectors is a projector.
]
#definition[
    Bipartite system is system described Hilbert space $cal(H)_A tp cal(H)_B$ which can be partitioned (separated) into two subsystems $A$ and $B$, described by Hilbert spaces $cal(H)_A$ and $cal(H)_B$. Alice has full control over system $A$, Bob has full control over system $B$, neither can control the other's system.
]
#definition[
    For bipartite system, *local operations (LO)* are of the form $hat(U)_A tp hat(I)$ (for Alice) or $hat(I) tp hat(U)_B$ (for Bob) where $hat(U)_A$ and $hat(U)_B$ are unitary operators or measurement operators.
]
#proposition[
    $hat(U)_A tp hat(I)$ and $hat(I) tp hat(U)_B$ commute: $\[hat(U)_A tp hat(I), hat(I) tp hat(U)_B\] = 0$, and their product is $hat(U)_A tp hat(U)_B$.
]
#theorem[
    Any unitary transformation $hat(U)_A tp hat(U)_B$ (i.e. using LO) acting on separable state $ket(psi) tp ket(phi)$ produces another separable state: $hat(U)_A ket(psi) tp hat(U)_B ket(phi)$. In particular, an entangled state cannot be created from a separable state.
]
#definition[
    A mixed state is *separable* iff it is an ensemble of separable states, and *entangled* otherwise.
]
#definition[
    *Density matrix* of *separable pure state* $ket(Psi) = ket(psi) tp ket(phi)$ is $ hat(rho) := ket(Psi) bra(Psi) = (ket(psi) tp ket(phi)) (bra(psi) tp bra(phi)) = (ket(psi) bra(psi)) tp (ket(phi) bra(phi)) = hat(rho)_A tp hat(rho)_B $ where $hat(rho)_A = ket(psi) bra(psi)$ and $hat(rho)_B = ket(phi) bra(phi)$.
]
#definition[
    *Density matrix* of *separable mixed state* is $ hat(rho) := sum_(i = 1)^M p_i hat(rho)_A^((i)) tp hat(rho)_B^((i)) $ where $\{hat(rho)_A^((i))\}$ are mixed or pure states of first system, $\{hat(rho)_B^((i))\}$ are mixed or pure states of second system.
]

== Matrix representation

#definition[
    *Tensor product* of two vectors is given by e.g. $ vec(1, 2, 3) tp vec(4, 5) = vec(1 vec(4, 5), 2 vec(4, 5), 3 vec(4, 5)) = vec(4, 5, 8, 10, 12, 15) $ The expression is similar for matrices: $ mat(1, 2; 3, 4) tp mat(5, 6; 7, 8) = mat(1 mat(5, 6; 7, 8), 2 mat(5, 6; 7, 8); 3 mat(5, 6; 7, 8), 4 mat(5, 6; 7, 8)) = mat(5, 6, 10, 12; 7, 8, 14, 16; 15, 18, 20, 24; 21, 24, 28, 36) $
]
#definition[
    *Controlled `NOT` (`CNOT`)* operator acts on $H_2 = H_q tp H_q$ and is defined as $ U = (I_2 + sigma_3) / 2 tp I_2 + (I_2 - sigma_3) / 2 tp sigma_1 $ We have $U ket(00) = ket(00)$, $U ket(01) = ket(01)$, $U ket(10) = ket(11)$, $U ket(11) = ket(10)$.
]

== Local measurements

#definition[
    For bipartite system, *local measurements* are Hermitian operators of the form $hat(F) = hat(F)_A tp hat(I)$ for Alice and $hat(G) = hat(I) tp hat(G)_B$ for Bob.
]
#notation[
    Projection operators of $hat(F)_A$ and $hat(G)_B$ for eigenvalues $lambda_i$ and $mu_j$ are denoted $hat(F)_(A i)$ and $hat(G)_(B j)$.
]
#remark[
    In the full system $H_A tp H_B$, $hat(F)$ and $hat(G)$ are degenerate, with degeneracy given by dimension of other subsystem, i.e. $dim(cal(H)_B)$ for Alice's observable and $dim(cal(H)_A)$ for Bob's. Assuming no degeneracy in their own system, corresponding projection operators in full system are
$
hat(F)_i & = hat(F)_(A i) tp hat(I) = sum_(j = 1)^(N_2) ket(v_i) bra(v_i) tp ket(w_j) bra(w_j) \
hat(G)_j & = hat(I) tp hat(G)_(B j) = sum_(i = 1)^(N_1) ket(v_i) bra(v_i) tp ket(w_j) bra(w_j)
$
]
#note[
    Since $\[hat(F), hat(G)\] = 0$, these measurements are compatible so final state is eigenstate of both $hat(F)$ and $hat(G)$. Probability of an outcome occuring is not affected by whether Alice or Bob measures first (or simultaneously).
]
#example[
    Let $\{ket(v_i)\}, \{ket(w_j)\}$ be orthonormal eigenstates of operators $hat(F)_A$ and $hat(G)_B$ with non-degenerate eigenvalues $\{lambda_i\}$ and $\{mu_j\}$, $ket(Psi) = sum_(i in [N_1], med j in [N_2]) gamma_(i j) ket(v_i) tp ket(w_j)$ be entangled state, define $
alpha_i := (sum_(j = 1)^N_2 |gamma_(i j)|^2)^(1\/2), quad beta_j := (sum_(i = 1)^(N_1) |gamma_(i j)|^2)^(1\/2)
$ and define auxiliary states (set $ket(psi_j) = vd(0)$ when $beta_j = 0$ and $ket(phi_i) = vd(0)$ when $alpha_i = 0$): $
ket(psi_j) := 1/beta_j sum_(i = 1)^(N_1) gamma_(i j) ket(v_i) in cal(H)_A, quad ket(phi_i) := 1/alpha_i sum_(j = 1)^(N_2) gamma_(i j) ket(w_j) in cal(H)_B \
==> ket(Psi) = sum_(i = 1)^(N_1) alpha_i ket(v_i) tp ket(phi_i) = sum_(j = 1)^(N_2) beta_j ket(psi_j) tp ket(w_j)
$ If Alice measures $hat(F)$ with result $lambda_i$, entangled state $ket(Psi)$ collapses to separable state $
ket(Psi) -> hat(F)_i ket(Psi) = \(hat(F)_(A i) tp hat(I)\) ket(Psi) tilde ket(v_i) tp ket(phi_i)
$ So Bob's state depends on the result of Alice's measurement.
]

== Reduced density matrix

#definition[
    For operator $hat(C) tp hat(D) in End(cal(H)_A tp cal(H)_B)$, *partial trace* over $cal(H)_A$ and $cal(H)_B$, $tr_A: End(cal(H)_A tp cal(H)_B) -> End(cal(H)_B)$ and $tr_B: End(cal(H)_A tp cal(H)_B) -> End(cal(H)_A)$, are $ tr_A \(hat(C) tp hat(D)\) := tr\(hat(C)\) hat(D), quad tr_B \(hat(C) tp hat(D)\) := tr\(hat(D)\) hat(C) $
]
#definition[
    For bipartite system, the *reduced density matrix* of a subsystem is partial trace of density matrix over other subsystem. So for bipartite system, $ hat(rho)_A := tr_B \(hat(rho)\), quad hat(rho)_B := tr_A \(hat(rho)\) $
]
#proposition[
    We have $tr\(hat(A) tp hat(B)\) = tr_A tr_B \(hat(A) tp hat(B)\) = tr_B tr_A \(hat(A) tp hat(B)\)$.
]
#note[
    A reduced matrix describes one subsystem, assuming no knowledge of the other system.
]
#proposition[
    - $hat(rho)_A$ is invariant under all local operations in system $B$ (for measurements, this is provided Alice does not learn about the result of the measurement in system B).
    - Under unitary transformations $hat(U)$ in system $A$, $hat(rho)_A$ transforms as normal: $hat(rho)_A -> hat(U) hat(rho)_A hat(U)^dagger$.
    - Local measurements in system $A$ can be described by $hat(rho)_A$ and operators acting on $cal(H)_A$: $tr_B \(hat(F)_i hat(rho) hat(F)_i\) = hat(F)_(A i) hat(rho)_A hat(F)_(A i)$.
]
#theorem[
    If $ket(Psi) in cal(H)_A tp cal(H)_B$ is pure state, then $hat(rho)_A$ is pure iff $ket(Psi)$ is separable.
]
#corollary[
    If spectrum of $hat(F)_A$ is non-degenerate then measuring $hat(F)_A$ in system $cal(H)_A$ produces separable state on system $cal(H)_A tp cal(H)_B$, i.e. *measurement destroys entanglement*.
]
#note[
    Entanglement does not violate causality (does not allow communication faster than the speed of light). i.e., if Alice makes a local measurement on an entangled system, Bob cannot detect this, even though the reduced density matrix for his system has changed.
]

== Classical communication

- Alice and Bob can use classical communication (CC) to communicate results of measurements of their own subsystem. If the state was initially entangled, Bob communicating a measurement to Alice would give Alice information about her subsystem.
#definition[
    *LOCC* is when Alice and Bob can use local operations (LO) and classical communication.
]

= Entanglement applications

== Bell states

#proposition[
    Measurements of entanglement:
    - Let $ket(Psi) in cal(H)_A tp cal(H)_B$. If $ket(Psi) = a ket(0) tp ket(phi) + b ket(1) tp ket(phi)$ for some $a, b in CC$, $ket(phi) in cal(H)_B$, then $ket(Psi)$ is separable, otherwise entangled.
    - If reduced density matrix of either subsystem gives a pure state ($tr(rho^2) = 1$) then state is separable. If it gives a mixed state ($tr(rho^2) < 1$), state is entangled.
    - $tr\(rho_A^2\) = tr\(rho_B^2\)$ gives measure of entanglement, with max value $1$ for no entanglement, min value $1\/2$ (for single qubit subsystem) for maximally entangled states.
]
#definition[
    *Bell states* are defined as, for $x, y in {0, 1}$, $ ket(beta_(x y)) := 1/sqrt(2) (ket(0) tp ket(y) + (-1)^x ket(1) tp ket(overline(y))) $
]
#proposition[
    Bell states are maximally entangled (trace of reduced density matrix of both sides is $1/2$) and form an orthonormal basis.
]
- Bell state basis is related to standard basis by unitary transformation, but Bell states can't be created from the separable standard basis by any LOCC process, since unitary transformations between them are not of form $hat(U)_A tp hat(U)_B$ (since this preserves separability), and measurements always produce a separable state.
- Alice and Bob can individually transform any Bell state to any other Bell state by the unitary operators $hat(U)_(x y) tp hat(I)$ and $hat(I) tp hat(U)_(x y)$ respectively: $ (hat(U)_(x y) tp hat(I)) ket(beta_(0 0)) = (hat(I) tp hat(U)_(x y)) ket(beta_(0 0)) = ket(beta_(x y)) $ where $ U_(0 0) = I_2, quad U_(0 1) = sigma_1, quad U_(1 0) = sigma_3, quad U_(1 1) = i sigma_2 $

== Superdense coding

- Qubit can be used instead of classical bit: $ket(0)$ corresponds to the bit $0$, $ket(1)$ corresponds to the bit $1$. In this case, the qubit can be measured with probability $1$ with the measurement operator $Z = 1/2 (I_2 - sigma_3)$, since $Z ket(0) = 0 ket(0)$, $Z ket(1) = 1 ket(1)$ so measurement with outcome $0$ means state is $ket(0)$ with probability $1$, measurement with outcome $1$ means state is $ket(1)$ with probability $1$.
- Alice can prepare the qubit to represent the classical bit to send to Bob: prepare any state $ket(psi)$ and measure on it with operator $1/2 (I_2 - sigma_3)$. Outcome is $0$ or $1$ - if outcome is equal to the bit $x$ she wants to send, $ket(psi)$ has been projected to $ket(x)$, so send this state to Bob. Otherwise, perform unitary transformation $sigma_1 ket(overline(x)) = ket(x)$ and send this state to Bob.
- *Superdense coding*:
    - Superdense coding allows one qubit to transmit two classical bits of information.
    - Alice and Bob share state $ket(beta_00)$.
    - Alice applies operation $hat(U)_(x y) tp hat(I)$ to whole system where $(x y)_2$ is the two bit message she wants to send (this just acts on her qubit). Note that this does not transmit any information to Bob, as his reduced density matrix is $rho_B = 1/2 I$ before and after the transformation.
    - Alice sends her qubit to Bob. Then Bob has the full Bell state $ket(beta_(x y))$ (he has both qubits). Bob then applies a measurement which has the four Bell states as eigenstates, which gives him the eigenvalue with probability $1$, e.g. he measures $ hat(B) = 0 ket(beta_00) bra(beta_00) + 1 ket(beta_01) bra(beta_01) + 2 ket(beta_10) bra(beta_10) + 3 ket(beta_11) bra(beta_11) $

== No-cloning theorem

#theorem("No-cloning theorem")[
    In quantum mechanics, it is impossible to clone an unknown state $ket(psi)$. More precisely, it is impossible to perform transformation $ket(psi) tp ket(phi) -> ket(psi) tp ket(psi)$ for an arbitrary unknown state $ket(psi)$ and fixed initial state $ket(phi)$.
]

== Teleportation

#definition[
    *Hadamard gate* is transformation given by operator $
U_H := 1/sqrt(2) mat(1, 1; 1, -1) = 1/sqrt(2) (sigma_1 + sigma_3)
$ We have $hat(U)_H ket(0) = ket(+)$, $hat(U)_H ket(1) = ket(-)$.
]
#definition[
    *Teleportation* is process of transferring quantum state $ket(psi)$ without using quantum communication (i.e. only using LOCC). It is as follows:
    - Alice has state $ket(psi) = a ket(0) + b ket(1)$, Alice and Bob share Bell state $ket(beta_00)$, so full system state is $
    ket(psi) tp ket(beta_00) & = 1/sqrt(2) ket(psi) tp ket(0) tp ket(0) + 1/sqrt(2) ket(psi) tp ket(1) tp ket(1) \
    & = 1/sqrt(2) (a ket(000) + a ket(011) + b ket(100) + b ket(111))
    $ Alice has first two qubits, Bob has third.
    - Alice performs `CNOT` on her two qubits, transforming state to $ 1/sqrt(2) (a ket(000) + a ket(011) + b ket(110) + b ket(101)) $ `CNOT` operator is not of form $A tp B$ so it entangles Alice's qubits.
    - Alice applies Hadamard gate to her system: $ hat(U)_H tp hat(I) tp hat(I) 1/sqrt(2) (a ket(000) + a ket(011) + b ket(100) + b ket(111)) = 1/2 sum_(x, y) ket(x) tp ket(y) tp hat(U)_(x y) ket(psi) $
    - Alice measures with operator $Z$ on both her qubits, giving measurement $(x y)_2$, causing state to collapse to $ket(x) tp ket(y) tp hat(U)_(x y) ket(psi)$.
    - Alice uses CC to send $(x y)_2$ to Bob. Bob then performs transformation $hat(U)_(x y)^(-1) = hat(U)_(x y)^dagger$ so his state becomes $ket(psi)$.
]

== Quantum key distribution (QKD)

#definition[
    Let message $M$ and secret key $K$ be $n$-bit integers, $K$ is shared by Alice and Bob, where each bit of $k$ has value $0$ or $1$ with equal probability. *One-time pad encryption* is as follows:
    - Alice produces encrypted message $C = M plus.circle K$, where $plus.circle$ is bitwise addition $mod 2$ (also bitwise `XOR`).
    - Alice transmits $C$ to Bob. Bob decrypts message by calculating $ C plus.circle K = (M plus.circle K) plus.circle K = M plus.circle (K plus.circle K) = M plus.circle 0 = M $
    - It is important that $K$ is at least as long as $M$ and is never reused.
    - Drawback is that $K$ might be very long, and must be transmitted securely prior to communication.
]
#definition[
    *BB84* protocol for transmitting secret key is as follows:
    - Alice chooses random bit $x in {0, 1}$ with equal probability, makes random choice of $X$ or $Z$ with equal probability, then prepares qubit state according to the outcome: $ (0, Z) |-> ket(0), quad (1, Z) |-> ket(1), quad (0, X) |-> ket(+), quad (1, X) |-> ket(-) $ and sends this qubit to Bob using quantum communication.
    - Bob randomly chooses $X$ or $Z$ with equal probability, then measures qubit with measurement operator $1/2 (I - sigma_X)$ or $1/2 (I - sigma_Z)$.
    - This process is repeated enough to generate a sufficiently long key.
    - Alice and Bob publicly reveal their choices of $X$ or $Z$ for each qubit (must be after Bob receives the qubit), discarding all qubits for which same choice was not made. When same choice is made for qubit, Alice's choice of qubit will match with Bob's measurement.
]
- *Security of BB84*:
    - If Eve intercepts qubit, she must measure it to obtain information from it. But the four possible states are not all orthogonal, so Eve cannot make measurement which is guaranteed to distinguish them.
    - If Eve measures with $Z$ and Alice chose $Z$, Eve would correctly measure the qubit. But if Alice chose $X$, Eve would measure $0$ or $1$ with equal probability, and forward the same random qubit $ket(0)$ or $ket(1)$ to Bob. If Bob measures with $X$, result is discarded anyway. If Bob measures with $Z$, measurement is same random result as Eve's measurement, so differs from Alice's key half the time.
    - So for each (non-discarded) bit of key Eve intercepts and measures, probability that Alice and Bob's value differs is $1/4$, so currently Eve expects to know $3/4$ of the key, which is insecure. So Alice and Bob compare random subset of their keys and estimate error rate.
    - If rate too high, they assume interference from Eve, discard the key and repeat entire process again.

== Bell inequalities

#definition[
    *Local realism* is a property of a system:
    - *Locality*: an effect at one point can be detected at another point only if something travels between those two points (no faster than the speed of light).
    - *Realism*: measurements must be deterministic, i.e. measurements tell us a property of the system.
]
- *CHSH Bell-inequality*:
    - Let system have observables $Q, R, S, T$ which takes values $plus.minus 1$. Realism states that any system state must have specific values for these, $(q, r, s, t)$.
    - Take large number of system states and measure $Q S + R S + Q T - R T$ for each, calculate mean which gives estimate of expectation $EE(Q S + R S + Q T - R T)$.
    - Now $Q = plus.minus R$, so either $(Q + R)S = 0$ and $(Q - R)T = plus.minus 2$ or $(Q + R)S = plus.minus 2$ and $(Q - R)T = 0$, hence $Q S + R S + Q T - R T = plus.minus 2$, and $ -2 <= EE(Q S + R S + Q T - R T) = EE(Q S) + EE(R S) + EE(Q T) - EE(R T) <= 2 $
- Consider following experiment:
    - Charlie is in middle of Alice and Bob, who are separated arbitrarily.
    - Charlie prepares many Bell states $ket(beta_11)$ and sends one qubit of each simultaneously to Alice and Bob, so they receive them at same time.
    - Alice randomly chooses $Q$ or $R$ and makes that measurement on her qubit, Bob does same for random $S$ or $T$. Assuming locality, it is impossible that Alice or Bob's measurement affects the other by an influence of finite speed.
    - If quantum mechanics satisfied local realism, Alice's and Bob's results are predetermined by a hidden variable describing Charlie's Bell state.
    - Alice and Bob record measurement operator and result for each qubit, then compute $EE(Q S)$, $EE(R S)$, $EE(Q T)$, $EE(R T)$.
    - Measurement operators are given by $ Q = sigma_1 tp I_2, R = sigma_3 tp I_2, quad S = I_2 tp (-1)/sqrt(2) (sigma_1 + sigma_3), T = I_2 tp (-1)/sqrt(2) (sigma_1 - sigma_3) $
    - These give $EE(Q S) = EE(R S) = EE(Q T) = -EE(R T) = 1/sqrt(2)$, giving $EE(Q S) + EE(R S) + EE(Q T) - EE(R T) = 2 sqrt(2) > 2$, violating CHSH inequality.
    - Experimental data confirms this violation, showing nature isn't described by theory obeying local realism, and nature is consistent with quantum mechanics.

= Information theory

== Classical information and Shannon entropy

#definition[
    Let $X$ be random variable representing a message, $p(x) = PP(X = x)$ *Shannon entropy* is $
H(X) := -sum_x p(x) log_2 (p(x))
$ where conventionally $0 log 0 = 0$.
]
#theorem("Shannon's noiseless coding theorem")[
    $H(X)$ gives lower bound on average number of bits needed to encode message $X$.
]
#definition[
    *Joint entropy* is $ H(X, Y) := -sum_(x, y) p(x, y) log_2 (p(x, y)) $
]
#proposition[
    Joint entropy obeys *subadditivity*: $ H(X, Y) <= H(X) + H(Y) $ with equality iff $X$ and $Y$ are independent variables, i.e. when $p(x, y) = PP(X = x) PP(Y = y)$.
]
#definition[
    *Relative entropy of $p(x)$ to $q(x)$* is defined for two random variables which take same values but with different distributions $p(x)$ and $q(x)$: $ H(p(x) || q(x)) & := sum_x (p(x) log_2 (p(x)) - p(x) log_2 (q(x))) \ & = -H(X) - sum_x p(x) log_2 (q(x)) $
]
#proposition[
    Relative entropy is non-negative and $ H(p(x) || q(x)) = 0 <==> forall x, p(x) = q(x) $
]
#remark[
    Relative entropy can diverge if for some $x$, $q(x) = 0$ and $p(x) != 0$
]
#definition[
    *Conditional entropy* is $ H(X|Y) := H(X, Y) - H(Y) <= H(X) $
]
#definition[
    *Mutual information* of $X$ and $Y$ is $ H(X : Y) := H(X) + H(Y) - H(X, Y) >= 0 $
]

== Quantum entropy

#definition[
    *Von Neumann entropy* of quantum state with density operator $hat(rho)$ is $ S\(hat(rho)\) := -tr(hat(rho) log_2 (hat(rho))) = -sum_i p_i log_2 (p_i) $ where $hat(rho) = sum_i p_i ket(i) bra(i)$, $ket(i)$ are eigenstates of $hat(rho)$, $p_i$ are eigenvalues of $hat(rho)$. $S\(hat(rho)\)$ is Shannon entropy of ensemble of pure states described by $hat(rho)$.
]
#note[
    To compute $log_2 \(hat(rho)\)$, diagonalise $hat(rho)$ (use spectral decomposition) and take $log_2$ of each diagonal element (use here the convention $log_2 (0) = 0$).
]
#remark[
    For pure state, $S\(hat(rho)\) = -1 log_2 (1) = 0$.
]
#definition[
    *(quantum) relative entropy* is measure of distance between two states: $
S\(hat(rho)_1 || hat(rho)_2\) := tr\(hat(rho)_1 log_2 \(hat(rho)_1\)\) - tr\(hat(rho)_1 log_2 \(hat(rho)_2\)\)
$
]
#proposition[
    $S\(hat(rho)_1 || hat(rho)_2\) >= 0$ with equality iff $hat(rho)_1 = hat(rho)_2$.
]
#definition[
    For bipartite system $cal(H) = cal(H)_A tp cal(H)_B$ described by density matrix $hat(rho)$ and reduced density matrices $hat(rho)_A$ and $hat(rho)_B$, define $ S(A) := S\(hat(rho)_A\), quad S(B) := S\(hat(rho)_B\), quad S(A, B) := S\(hat(rho)\) $ where $S(A, B)$ is *(quantum) joint entropy* of $A$ and $B$.
]
#definition[
    *(quantum) conditional entropy* of $A$ and $B$ is $ S(A | B) := S(A, B) - S(B) $
]
#remark[
    Unlike classical conditional entropy, quantum conditional entropy can be negative, e.g. if $hat(rho)$ describes pure state, $S(A, B) = 0$ but if entangled, $hat(rho)_B$ is not pure state so $S(B) > 0$.
]
#definition[
    *(Quantum) mutual information* is $ I(A: B) = S(A: B) := S(A) + S(B) - S(A, B) $
]
#remark[
    When $hat(rho)$ is pure state, $S(A) = S(B)$ so $I(A: B) = 2 S(A)$. So entanglement can be interpreted as mutual information: information shared by $A$ and $B$ and not in either one alone.
]
#definition[
    *Entanglement entropy* is $S(A) = S(B)$ (these are equal since both reduced density matrices have same non-zero eigenvalues).
]

#import "@preview/quill:0.2.0": *

#let logicalop(o) = $op(#o)$

#let AND = logicalop("AND")
#let OR = logicalop("OR")
#let CNOT = logicalop("CNOT")
#let FANOUT = logicalop("FANOUT")
#let NOT = logicalop("NOT")
#let CnNOT(n) = logicalop($"C"^n #h(0pt) "NOT"$)
#let CCNOT = logicalop("CCNOT")
#let NAND = logicalop("NAND")

= Classical computing

== Basic gates

#notation[
    Input for circuit diagrams has most significant bit at the top, circuits are read left to right, with last operation on the right.
]
#definition[
    *(logical) gate* is function mapping bits to bits.
]
#definition[
    Simplest gates are $f: {0, 1} -> {0, 1}$:
    - *Identity gate*: $id(x) := x$.
    - $c_0(x) := 0$.
    - $c_1(x) := 1$.
    - *#NOT gate*: $NOT(x) = overline(x)$.
]
#definition[
    *#FANOUT gate* is defined as $
FANOUT: {0, 1} -> {0, 1}^2, quad FANOUT(x) := (x, x)
$
#figure(quantum-circuit(
    row-spacing: 2pt,
    setwire(1, stroke: 0pt), 2, ctrl(2, show-dot: false), setwire(1, stroke: 1pt), 1, rstick($x$), [\ ],
    lstick($x$), 2, [\ ],
    setwire(1, stroke: 0pt), 2, ctrl(0, show-dot: false), setwire(1, stroke: 1pt), 1, rstick($x$)
))
]
#definition[
    *#AND gate* is given by its *truth table*:
#figure(table(align: center,columns: (auto, auto, auto), inset: 5pt, [], $0$, $1$, $0$, $0$, $0$, $1$, $0$, $1$))
#figure(quantum-circuit(
    row-spacing: 2pt,
    setwire(1, stroke: 1pt),
    lstick($x$), 1, mqgate($#h(40pt)$, n: 3, radius: (right: 100%)), [\ ],
    setwire(1, stroke: 0pt), 3, setwire(1, stroke: 1pt), 2, rstick($AND(x, y)$), [\ ],
    lstick($y$), 2,
))
]
#definition[
    *OR gate* is given by its *truth table*: $ #table(columns: (auto, auto, auto), inset: 5pt, [], $0$, $1$, $0$, $0$, $1$, $1$, $1$, $1$) $
]
#remark[
    #AND and #OR are not reversible (invertible) so cannot be implemented by unitary operators.
]
- *Landauer's principle*: energy $E$ required to erase one bit satisfies $ E >= k_B T log(2) $ where $k_B$ is Boltzmann's constant, $T$ is temperature at which system operates.
#definition[
    *Controlled #NOT (#CNOT) gate*, $CNOT: {0, 1}^2 -> {0, 1}^2$, is $ CNOT(x, y) := cases((x, y) & "if" x = 0, (x, NOT(y)) & "if" x = 1) quad = (x, x xor y) = (x, x + y mod 2) $ Inverse of #CNOT is #CNOT. $x$ is *control bit*, $y$ is *target bit*.
#figure(quantum-circuit(
    lstick($y$), 2, targ(), 2, rstick($x xor y$), [\ ],
    lstick($x$), 2, ctrl(-1), 2, rstick($x$)
))
]
#definition[
    *#CnNOT(1) gate* is defined as $ CnNOT(1)(x_1, ..., x_n, y) := (x_1, ..., x_n, y xor "AND"(x_1, ..., x_n)) $ #CnNOT($n$) is reversible for all $n in NN$ and $(CnNOT(n))^(-1) = CnNOT(n)$. For $n = 2$, #CCNOT gate is called a *Toffoli gate*.
]
#figure(quantum-circuit(
    lstick($y$), 2, targ(), 2, rstick($AND(x_1, x_2) xor y$), [\ ],
    lstick($x_2$), 2, ctrl(-1), 2, rstick($x_2$), [\ ],
    lstick($x_1$), 2, ctrl(-1), 2, rstick($x_1$)
))
#definition[
    *#NAND gate* is defined as $ NAND(x, y) := NOT(AND(x, y)) $
]
#example[
    Circuit diagram for $f: ZZ\/8 -> ZZ\/8$, $f(x) = x + overline(1)$.
#figure(quantum-circuit(
    lstick($x_2$), 1, targ(), 4, [\ ],
    lstick($x_1$), 1, ctrl(-1), 1, targ(), 2, [\ ],
    lstick($x_0$), 1, ctrl(-1), 1, ctrl(-1), 1, gate("NOT")
))
]

== Universal gate sets

#notation[
    For $f: {0, 1}^m -> {0, 1}^n$, can write as $ f(x_(m - 1), ..., x_0) = (f_(n - 1)(x_(m - 1), ..., x_0), ..., f_0 (x_(m - 1), ..., x_0)) $
]
#remark[
    Can "copy" bits by introducing extra "ancillary" bits and using #CNOT gates:
#figure(quantum-circuit(
    lstick($0$), 1, targ(), 1, rstick($x xor 0 = x$), [\ ],
    lstick($x$), 1, ctrl(-1), 1, rstick($x$)
))
]
#definition[
    A *universal gate set (UGS)* is finite set of gates which can construct an arbitrary function $f: {0, 1}^n -> {0, 1}^m$.
]
#proposition[
    ${NOT, AND, OR, CNOT}$ is a universal gate set.
]
#corollary[
    ${CNOT, AND}$ is a universal gate set.
]
#proposition[
    ${CCNOT}$ is a minimal ($1$-gate) UGS for reversible classical computation.
]
#remark[
    There is an infinite number of UGSs.
]

== Computational resources and complexity

#definition[
    An *algorithm* is a set of instructions (systematic procedure) for computing some output for a given input.
]
#definition[
    Resources considered in complexity:
    - *Time*: corresponds to numbers of gates in any UGS needed for implementing the circuit.
    - *Space*: corresponds to number of bits (lines) in the circuit.
    - $n$ denotes size in bits of input.
]
#example[
    Computing $gcd(a, b)$ (assuming WLOG $a >= b$, $2^(n - 1) <= b < 2^n$ so $b$ has $n$ bits).
    - Brute-force algorithm: try all $1 <= c <= b$, check if $c | a$ and $c | b$, return largest such $c$. Time complexity: $O(2^n)$.
    - Euclid's algorithm has time complexity $O(n^3)$ (assuming division and remainder algorithm is $O(n^2)$) (since $r_(i + 2) < r_i\/2$).
]
#definition[
    - *P* is complexity class of algorithms whose run time is at most polynomial time in $n$.
    - *EXP* is complexity class of algorithms whose run time is at most exponential time in $n$. $"P" subset "EXP"$.
    - *PSPACE* is class of algorithms which require space at most polynomial in $n$. $"P" subset.eq "PSPACE"$ (e.g. each line in circuit diagram is assumed to involve at least one gate).
    - *NP* is complexity class of algorithms whose output can be verified to be correct in polynomial time, e.g. integer factorisation. Clearly $P subset.eq "NP"$.
    - *NP-hard* problem is one such that, if you have an oracle for solving them, you can solve any NP problem in polynomial time (NP problems reduce polynomially to NP-hard problems).
    - *NP-complete* is complexity class of problems which are NP-hard, e.g. travelling salesman.
    - *PP* is class of algorithms which require time at most polynomial in $n$ to return correct answer with probability $> 1\/2$.
    - *BPP* is class of algorithms which require time at most polynomial in $n$ to return correct answer with probability $> c > 1\/2$. $"P" subset.eq "BPP"$.
]

= Quantum circuits

#definition[
    A *qubit* is a quantum system whose Hilbert space $H_1$ is $2$-dimensional, with basis ${ket(0), ket(1)}$. An $n$-qubit system has $2^n$-dimensional Hilbert space $H_n = H_1 tp dots.h.c tp H_1$. The *computational basis* for $H_n$ is $ {ket(0), ..., ket(2^n - 1)} $ where $ket(k) = ket((k_(n - 1)...k_0)_2)$ corresponds to $ket(k_(n - 1)) tp dots.h.c tp ket(k_0)$.
]
#definition[
    *Quantum gate* is unitary map from $H_n$ to $H_n$.
]
#notation[
    Let $X, Y, Z$ denote Pauli matrices $sigma_1, sigma_2, sigma_3$ respectively.
]
#notation[
    A unitary $U: H_1 -> H_1$ is denoted
#quantum-circuit(
    1, gate($U$), 1
)
]
#definition[
    Define the gates $ S := mat(1, 0; 0, i), quad T := mat(1, 0; 0, e^(i pi\/4)), quad H := 1/sqrt(2) mat(1, 1; 1, -1) $ where $H$ is *Hadamard gate*. $S^2 = Z$, $T^2 = S$, $H^2 = I$. $H ket(0) = ket(+)$, $H ket(1) = ket(-)$.
]
#example[
    Hadamard gate is useful when constructing uniform superpositions of all basis states: $ (H ket(0)) tp (H ket(0)) = 1/2 (ket(00) + ket(01) + ket(10) + ket(11)) $ and in general, $ (H ket(0)) tp dots.h.c tp (H ket(0)) = 1/(2^(n\/2)) sum_(k = 0)^(2^n - 1) ket(k) $
]
#definition[
    *#CNOT* gate is $mat(I, 0; 0, X)$. Most significant bit is control bit, least significant bit is target bit.
#figure(quantum-circuit(
    1, ctrl(1), 1, [\ ],
    1, targ(), 1
))
]
#definition[
    *Controlled-$U$* gate, $C$-$U$ maps $ket(0) tp ket(psi) = ket(0) tp ket(psi)$ and $ket(1) tp ket(psi) = ket(1) tp (U ket(psi))$.
#figure(quantum-circuit(
    1, ctrl(1), 1, [\ ],
    1, gate($U$), 1
))
]
#definition[
    *CCNOT (Toffoli) gate* is $ mat(I, 0, 0, 0; 0, I, 0, 0; 0, 0, I, 0; 0, 0, 0, X) $
#figure(quantum-circuit(
    1, ctrl(1), 1, [\ ],
    1, ctrl(1), 1, [\ ],
    1, targ(), 1
))
Note: Toffoli gate maps computational basis elements to computational basis elements, and computational basis elements are orthonormal.
]
#notation[
    Measurement and classical bits are shown as e.g.
#figure(quantum-circuit(
    1, meter(), setwire(2), 1, rstick($001$)
))
]

== Universal quantum computation

#proposition[
    Every $N times N$ unitary can be written in terms of $U_(i j)$: "elementary" unitaries acting on $(i, i)$, $(i, j)$, $(j, i)$ and $(j, j)$ entries only, i.e. they are non-trivial in only one $2 times 2$ block (they act non-trivially on a two-dimensional subspace of the Hilbert space, spanned by two basis states $ket(i - 1)$ and $ket(j - 1)$).
]
#proposition[
    $U$ is unitary iff its rows are orthonormal iff its columns are orthonormal (with respect to Hermitian inner product).
]
#example[
    For unitary $ U = mat(a, d, g; b, e, h; c, f, j) $ we can find unitaries $U_1, U_2, U_3$ with $U_3 U_2 U_1 U = I$. Choose $U_1$ to have upper left $2 times 2$ block non-trivial and such that $ U_1 U = mat(a', d', g'; 0, e', h'; c', f', j') $ If $b = 0$, set $U_1 = I$. If $b != 0$, set $ U_1 = mat(alpha^*, beta^*, 0; beta, -alpha, 0; 0, 0, 1), quad alpha := a/sqrt(|a|^2 + |b|^2), beta = b/sqrt(|a|^2 + |b|^2) ==> beta a - alpha b = 0 $ Then set $ gamma = (a')/sqrt(|a'|^2 + |c'|^2), delta = (c')/sqrt(|a'|^2 + |c'|^2), quad U_2 = mat(gamma^*, 0, delta^*; 0, 1, 0; delta, 0, -gamma) ==> U_2 U_1 U = mat(1, 0, 0; 0, e'', h''; 0, f'', j'') =: U_3^dagger $ If $U in U(N)$ is unitary, then can find $N - 1$ unitaries $U_1, ..., U_(N - 1)$ where $U_i$ is non-trivial in first and $(i + 1)$th row such that $U_(N - 1) dots.h.c U_1 U$ has first row and first column $(1, 0, ..., 0)$ and non-trivial bottom-right $(N - 1) times (N - 1)$ block. So it can be reduced entirely by induction, to $1/2 N (N - 1)$ unitaries.
]
#remark[
    $U$ acts on $n$ qubits so $N = 2^n$, so we need $approx 4^n$ elementary matrices, so complexity is exponential in number of qubits.
]
#example[
    Any $4 times 4$ unitary can be written as product of 6 elementary unitaries: $ U = mat(*, *, 0, 0; *, *, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1) mat(*, 0, *, 0; 0, 1, 0, 0; *, 0, *, 0; 0, 0, 0, 1) mat(*, 0, 0, *; 0, 1, 0, 0; 0, 0, 1, 0; *, 0, 0, *) mat(1, 0, 0, 0; 0, *, *, 0; 0, *, *, 0; 0, 0, 0, 1) mat(1, 0, 0, 0; 0, *, 0, *; 0, 0, 1, 0; 0, *, 0, *) mat(1, 0, 0, 0; 0, 1, 0, 0; 0, 0, *, *; 0, 0, *, *) $
]
#definition[
    A *multiply-controlled unitary* is an $N times N$ unitary acting on subspace $"span"{ket(1...10), ket(1...11)}$. It applies a $2 times 2$ unitary to last qubit if all other qubits are $1$ and the identity otherwise.
]
#example[
    Unitary acting on subspace $span{ket(1110), ket(1111)}$ is implemented as
#figure(quantum-circuit(
    lstick($ket(q_3)$), 1, ctrl(1), 2, nl,
    lstick($ket(q_2)$), 1, ctrl(1), 2, nl,
    lstick($ket(q_1)$), 1, ctrl(1), 2, nl,
    lstick($ket(q_0)$), 1, gate($U$), 2, nl,
))
]
#example[
    If $i - 1$ and $j - 1$ differ in single bit, with all other bits $1$, this is multiply-controlled unitary with that bit as target, e.g. unitary acting on subspace $span{ket(1101), ket(1111)}$ is implemented as
#figure(quantum-circuit(
    lstick($ket(q_3)$), 1, ctrl(1), 2, nl,
    lstick($ket(q_2)$), 1, ctrl(1), 2, nl,
    lstick($ket(q_1)$), 1, gate($U$), 2, nl,
    lstick($ket(q_0)$), 1, ctrl(-1), 2, nl,
))
]
#example[
    If $i - 1$ and $j - 1$ differ in single bit but others are not all $1$, use NOT gates to reverse the control bits which are $0$, e.g. unitary acting on $span{ket(0100), ket(0110)}$ is implemented as
#figure(quantum-circuit(
    lstick($ket(q_3)$), 1, gate($X$), ctrl(1), gate($X$), 1, nl,
    lstick($ket(q_2)$), 2, ctrl(1), 2, nl,
    lstick($ket(q_1)$), 2, gate($U$), 2, nl,
    lstick($ket(q_0)$), 1, gate($X$), ctrl(-1), gate($X$), 1, nl,
))
]
#definition[
    *Gray code* between $(p_(n - 1)...p_0)$ and $(q_(n - 1)...q_0)$ is sequence of single bit flips that maps from $(p_(n - 1)...p_0)$ to $(q_(n - 1)...q_0)$, e.g. a Gray code for $111$ and $000$ is $111, 101, 001, 000$.
]
#remark[
    Gray codes are not unique. (For practical reasons, it is easier to preserve the ordering between first and last, and penultimate and last items in the code.)
]
#example[
    If $i - 1$ and $j - 1$ differ in multiple bits (e.g. $U_(i, j) = U_(8, 1)$, $i - 1 = 7 = (111)_2$, $j - 1 = 1 = (000)_2$), then use a Gray code to flip bits so that all apart from one are the same as $j - 1$. First bit flip $111 -> 101$ is implemented as #CCNOT. Second bit flip $101 -> 001$ is implemented as #CCNOT but if second qubit is $0$ instead of $1$. Then act with $U$ on subspace $span{ket(001), ket(000)}$ (i.e. on third qubit), then "undo" these CCNOT in reverse order:
#figure(quantum-circuit(
    lstick($ket(q_2)$), ctrl(1), 1, targ(), 1, gate($X$), ctrl(1), gate($X$), 1, targ(), 1, ctrl(1), 1, nl,
    lstick($ket(q_1)$), targ(), gate($X$), ctrl(-1), gate($X$), gate($X$), ctrl(1), gate($X$), gate($X$), ctrl(-1), gate($X$), targ(), 1, nl,
    lstick($ket(q_0)$), ctrl(-1), 1, ctrl(-1), 2, gate($U$), 2, ctrl(-1), 1, ctrl(-1), 1
))
]
#example[
    We can implement any multiply-controlled unitary with controlled-unitary (single control qubit) and CCNOT gates, by introducing ancillary bits. e.g. to implemented the multiply-controlled unitary acting on $q_0$ if $q_1 = q_2 = q_3 = 1$, use ancillary qubits $ket(a_1)$, $ket(a_2)$ (initially set to $0$):
#figure(quantum-circuit(
    lstick($ket(q_3)$), ctrl(1), 3, ctrl(1), 1, nl,
    lstick($ket(q_2)$), ctrl(2), 3, ctrl(2), 1, nl,
    lstick($ket(q_1)$), 1, ctrl(1), 1, ctrl(1), 2, nl,
    lstick($ket(a_2)$), targ(), ctrl(1), 1, ctrl(1), targ(), 1, nl,
    lstick($ket(a_1)$), 1, targ(), ctrl(1), targ(), 2, nl,
    lstick($ket(q_0)$), 2, gate($U$), 3
))
]
#proposition[
    CCNOT can be implemented with $H$ (Hadamard) and $T$ gates (and their Hermitian conjugates).
]
#lemma[
    Any single qubit unitary $U$ can be written as $U = e^(i alpha) A X B X C$ with $A, B, C$ single-qubit ($2 times 2$) unitaries, $A B C = 1$, $alpha in RR$. In particular, C-$U$ can be implemented as
#figure(quantum-circuit(
    lstick($ket(q_1)$), 1, ctrl(1), 1, ctrl(1), gate($mat(1, 0; 0, e^(i alpha))$), 1, nl,
    lstick($ket(q_0)$), gate($C$), targ(), gate($B$), targ(), gate($A$), 1
))
]
#corollary[
    Any unitary can be implemented with single-qubit unitaries and CNOT.
]
#remark[
    Number of elementary unitaries $U_i$ needed is $O(2^(2n))$. Gray code requires $O(n)$ $CnNOT(n - 1)$ gates, and representing these multiply-controlled unitaries as controlled-unitaries requires $O(n)$ CCNOT gates, so overall $U$ is represented as $O(n^2 2^(2n))$ operations.
]
#definition[
    *BQP (bounded-error quantum polynomial)* decision problems are those which a unitary operation solves with probability of success $p > c$, with $c > 1/2$ a fixed constant (conventionally, $c = 2/3$), with polynomial growth in resources (i.e. number of CNOT and single-qubit unitary gates) as $n$ (number of qubits) is increased.
]
#note[
    $"BPP" subset.eq "BQP"$, since any classical computation can be written in terms of CCNOT and CCNOT has fixed quantum cost. A source of randomness is the following circuit, giving $0$ and $1$ each with probability $1\/2$:
#figure(quantum-circuit(
    lstick(ket(0)), 2, gate($H$), 2, meter(), setwire(2), 2
))
]

== Measurement

#note[
    We can always measure using the Pauli $Z$ operator (so measure in the computational basis). To measure in different basis, act with a unitary to transform desired basis into computational basis, then measure in computational basis, then transform back to desired basis.
]
#example[
    Let $U$ be single-qubit operator, with eigenvalues $plus.minus 1$, so it is Hermitian and unitary. Measuring $U$ can be achieved with the following circuit:
    #figure(quantum-circuit(
        lstick($ket(0)$), 1, gate($H$), 1, ctrl(1), 1, gate($H$), 1, meter(), setwire(2), 1, nl,
        lstick($ket(psi)$), 3, gate($U$), 5
    ))
    Acting with $H$ maps $ket(0) tp ket(psi) |-> 1/sqrt(2) (ket(0) + ket(1)) tp ket(psi)$. Acting with controlled-$U$ gives $1/sqrt(2) (ket(0) tp ket(psi) + ket(1) tp U ket(psi))$. Acting with $H$ again gives output $ 1/2 ((ket(0) + ket(1)) tp ket(psi) + (ket(0) - ket(1)) tp U ket(psi)) = 1/2 ket(0) tp (I + U) ket(psi) + 1/2 ket(1) tp (I - U) ket(psi) $ But $1/2 (I + U)$ is projector to $+1$ eigenspace of $U$, $1/2 (1 - U)$ is projector to $-1$ eigenspace of $U$, so if $ket(psi) = alpha ket(U_+) + beta ket(U_-)$, with $U ket(U_(plus.minus)) = plus.minus U_(plus.minus)$ then output is $ alpha ket(0) tp ket(U_+) + beta ket(1) tp ket(U_-) $ So result of measurement is $0$ with probability $|alpha|^2$, which collapses state to $ket(0) tp ket(U_+)$, and $1$ with probability $|beta|^2$, which collapses state to $ket(1) tp ket(U_-)$.
]

= Quantum error correction

#note[
    We assume that an error only affects a single qubit.
]

== Correcting single bit flips

#definition[
    A *code subspace* is a two-dimensional subspace of an $n$-qubit Hilbert space, in which the logical qubits live, such that each possible error (being considered) maps states in the code subspaces into a distinct two-dimensional subspace, and all of these error subspaces and the codespace are orthogonal.
]
#example[
    Assume only error that can occur is flip of single qubit (same as classical case), i.e. each qubit has probability $p$ of $X$ gate being applied. We encode the state in a *code subspace*. Each qubit is encoded as 3 qubits: the *logical qubit* $ket(overline(0))$ is encoded as the _physical_ state $ket(000)$, $ket(overline(1))$ is encoded as $ket(111)$. So $ket(psi) = alpha ket(0) + beta ket(1)$ is mapped to $alpha ket(000) + beta ket(111)$, in the subspace $span{ket(000), ket(111)}$ of the Hilbert space of 3 qubits. The embedding is implemented as
    #figure(quantum-circuit(
        lstick($ket(q_2) = ket(psi)$), ctrl(1), ctrl(2), 1, nl,
        lstick($ket(q_1) = ket(0)$), targ(), 2, nl,
        lstick($ket(q_0) = ket(0)$), 1, targ(), 1
    ))
    Single bit flip can map this state to $ alpha ket(001) + beta ket(110), quad alpha ket(010) + beta ket(101), quad alpha ket(100) + beta ket(011) $ which are all orthogonal to original state and each other. So different errors map to different orthogonal subspaces, hence we can make measurement to determine which subspace it is without affecting the $alpha$, $beta$ coefficients.

    *Error syndromes* are operators with eigenspaces as the different subspaces, each with distinct eigenvalue. In this case, choose syndromes formed from $Z$ operator (this has eigenvalue $1$ for $ket(0)$, $-1$ for $ket(1)$). Let $Z_0 = I tp I tp Z$, $Z_1 = I tp Z tp I$, $Z_2 = Z tp I tp I$, then $
        Z_0 Z_1 ket(000) = ket(000), quad Z_0 Z_1 ket(111) = ket(111), & quad Z_0 Z_2 ket(000) = ket(000), quad Z_0 Z_2 ket(111) = ket(111) \
        Z_0 Z_1 ket(001) = -ket(001), quad Z_0 Z_1 ket(110) = -ket(110), & quad Z_0 Z_2 ket(001) = -ket(001), quad Z_0 Z_2 ket(110) = -ket(110) \
        Z_0 Z_1 ket(010) = -ket(010), quad Z_0 Z_1 ket(101) = -ket(101), & quad Z_0 Z_2 ket(010) = ket(010), quad Z_0 Z_2 ket(101) = ket(101) \
        Z_0 Z_1 ket(100) = ket(100), quad Z_0 Z_1 ket(011) = ket(011), & quad Z_0 Z_2 ket(100) = -ket(100), quad Z_0 Z_2 ket(011) = -ket(011)
    $ So $span{ket(000), ket(111)}$ is $(1, 1)$ eigenspace, $span{ket(001), ket(110)}$ is $(-1, -1)$ eigenspace, $span{ket(010), ket(101)}$ is $(-1, 1)$ eigenspace, $span{ket(100), ket(011)}$ is $(1, -1)$ eigenspace. So if $ket(psi)$ is mapped to $ (1 - epsilon) ket(psi) + delta_2 X_2 ket(psi) + delta_1 X_1 ket(psi) + delta_0 X_0 ket(psi) $ then we measure $Z_0 Z_1$ and $Z_0 Z_2$, which collapses state to either $ ket(psi), quad X_2 ket(psi), quad X_1 ket(psi), quad X_0 ket(psi) $ Since the eigenvalues for this combination of measurements are distinct, they tell us which state $ket(psi)$ has been projected to. So can apply $I, X_2, X_1$ or $X_0$ to map back to $ket(psi)$. This can be implemented as
    #figure(quantum-circuit(
        lstick($ket(q_2)$), 3, ctrl(4), 6, targ(), targ(), 2, nl,
        lstick($ket(q_1)$), 1, ctrl(2), 5, targ(), targ(), 5, nl,
        lstick($ket(q_0)$), ctrl(1), 1, ctrl(2), 2, targ(), 8, nl,
        lstick($ket(a_1) = ket(0)$), targ(), targ(), 3, ctrl(-1), 1, ctrl(-2), ctrl(-2), 2, ctrl(-3), meter(), setwire(2), rstick($Z_1 Z_0$), nl,
        lstick($ket(a_0) = ket(0)$), 2, targ(), targ(), 1, ctrl(-1), 2, ctrl(-1), 1, ctrl(-4), ctrl(-4), meter(), setwire(2), rstick($Z_2 Z_0$)
    ))
    where the measurements are to reset the ancilla so they can be reused.
]
#note[
    We cannot use less than 3 qubits, since to encode with $n$ qubits, we need $n + 1$ orthogonal two-dimensional subspaces, which is possible in $2^n$-dimensional $n$ qubit Hilbert space iff $2^n >= 2(n + 1)$.
]

== Correcting general single qubit errors

#remark[
    General error consists of acting with unitary operation $U_i$ on single physical qubit. Can use Bloch sphere rotation representation to write $ U_i = e_i I + a_i X_i + b_i Y_i + c_i Z_i $ So if state $ket(psi)$ is single logical qubit encoded in $n$-qubit Hilbert space, action of single qubit error on qubit $i$ transforms $ket(psi)$ to $ (1 - epsilon) ket(psi) + a_i X_i ket(psi) + b_i Y_i ket(psi) + c_i Z_i ket(psi) quad "for some" i $ If error depends of state of environment, state after errors occurs is entangled: $ ket(e_1) tp ket(psi) + sum_(i = 1)^n ket(e_(2i)) tp X_i ket(psi) + ket(e_(3i)) tp Y_i ket(psi) + ket(e_(4i)) tp Z_i ket(psi) $ (This is linear superpositon of single qubit errors). Measuring chosen error syndromes projects qubits to one of the subspaces, so state becomes one of $ ket(psi), quad X_i ket(psi), quad Y_i ket(psi), quad Z_i ket(psi) $ $3n + 1$ 2d subspaces are needed (corresponding to $3n$ single-qubit errors and original state), so we require $ 2^n >= 2(3n + 1) $ which is saturated by $n = 5$.
]
#remark[
    In terms of errors, $X$ is a single bit flip, $Z$ is a phase flip ($alpha ket(0) + beta ket(1) -> alpha ket(0) - beta ket(1)$), $Y = i X Z$ is composition of both.
]
#definition[
    We define a *coding* $c: H_1 -> H_n$, $ket(overline(0)) = c(ket(0))$, $ket(overline(1)) = c(ket(1))$.
]
#definition[
    *Steane code* is coding using $7$ qubits, which uses the syndromes $ M_0 := X_0 X_4 X_5 X_6, quad M_1 & := X_1 X_3 X_5 X_6, quad M_2 := X_2 X_3 X_4 X_6, \ N_0 := Z_0 Z_4 Z_5 Z_6, quad N_1 & := Z_1 Z_3 Z_5 Z_6, quad N_2 := Z_2 Z_3 Z_4 Z_6 $ which all commute, so have simultaneous eigenstates. Code subspace is spanned by $
        ket(overline(0)) & = 1/(2^(3\/2)) (1 + M_0)(1 + M_1)(1 + M_2) ket(0000000), \
        ket(overline(1)) & = 1/(2^(3\/2)) (1 + M_0)(1 + M_1)(1 + M_2) ket(1111111)
    $
]
#remark[
    $M_j^2 = I$ so $M_j (1 + M_j) = 1 + M_j$ so $ket(overline(0)), ket(overline(1))$ are eigenstates of each $M_j$ with eigenvalue $1$. $ket(overline(0)), ket(overline(1))$ are also eigenstates of each $N_k$ with eigenvalue $1$. Each $M_j$ commutes with each $X_i$, and $ X_i Z_j = cases(Z_j X_i & "if" i != j, -Z_j X_i & "if" i = j) quad ==> quad X_i N_j = cases(N_j X_i & "if" N_j "does not contain" Z_i, -N_j X_i & "if" N_j "contains" Z_i) $ Hence $M_j X_i (alpha ket(overline(0)) + beta ket(overline(1))) = X_i M_j (alpha ket(overline(0)) + beta ket(overline(1))) = X_i (alpha ket(overline(0)) + beta ket(overline(1)))$ so this has eigenvalue $1$ for all $M_j$, and $ N_j X_i (alpha ket(overline(0)) + beta ket(overline(1))) = cases(X_i N_j (alpha ket(overline(0)) + beta ket(overline(1))) = X_i (alpha ket(overline(0)) + beta ket(overline(1))) & "if" Z_i in.not N_j ==> "eigenvalue" 1, -X_i N_j (alpha ket(overline(0)) + beta ket(overline(1))) = -X_i (alpha ket(overline(0)) + beta ket(overline(1))) & "if" Z_i in N_j ==> "eigenvalue" -1) $
    For bit flips $X_i$:
    #figure(table(
        columns: (auto, auto, auto, auto, auto, auto, auto, auto),
        $i$, $0$, $1$, $2$, $3$, $4$, $5$, $6$,
        $(M_0, M_1, M_2)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$,
        $(N_0, N_1, N_2)$, $(-1, 1, 1)$, $(1, -1, 1)$, $(1, 1, -1)$, $(1, -1, -1)$, $(-1, 1, -1)$, $(-1, -1, 1)$, $(-1, -1, -1)$
    ))
    For phase flips (sign errors) $Z_i$:
    #figure(table(
        columns: (auto, auto, auto, auto, auto, auto, auto, auto),
        $i$, $0$, $1$, $2$, $3$, $4$, $5$, $6$,
        $(M_0, M_1, M_2)$, $(-1, 1, 1)$, $(1, -1, 1)$, $(1, 1, -1)$, $(1, -1, -1)$, $(-1, 1, -1)$, $(-1, -1, 1)$, $(-1, -1, -1)$,
        $(N_0, N_1, N_2)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$, $(1, 1, 1)$,
    ))
    Since $X Y = -Y X$, $Z Y = -Y Z$, $ M_j Y_i = cases(Y_i M_j & "if" X_i in.not M_j, -Y_i M_j & "if" X_i in M_j), quad cases(Y_i N_j & "if" Z_i in.not M_j, -Y_i M_j & "if" Z_i in M_j) $ For errors $Y_i$:
    #figure(table(
        columns: (auto, auto, auto, auto, auto, auto, auto, auto),
        $i$, $0$, $1$, $2$, $3$, $4$, $5$, $6$,
        $(M_0, M_1, M_2)$, $(-1, 1, 1)$, $(1, -1, 1)$, $(1, 1, -1)$, $(1, -1, -1)$, $(-1, 1, -1)$, $(-1, -1, 1)$, $(-1, -1, -1)$,
        $(N_0, N_1, N_2)$, $(-1, 1, 1)$, $(1, -1, 1)$, $(1, 1, -1)$, $(1, -1, -1)$, $(-1, 1, -1)$, $(-1, -1, 1)$, $(-1, -1, -1)$,
    ))
]
#example[
    If $(M_j, N_j)$ measured and eigenvalues are $(1, 1, 1)$, $(1, -1, -1)$ then error is $X_3$, and we correct it by applying $X_3^(-1) = X_3$.
]

== Fault-tolerant gates

#definition[
    A gate $overline(U)$ is *fault-tolerant* if, when there is error $U_i$ on single physical qubit before the unitary operation, acting with the unitary produces state which differs from desired state only by a single-qubit error $V_j$, i.e. $ overline(U) U_i ket(psi) = V_j overline(U) ket(psi) $ This equivalent to $overline(U)$ mapping each eigenspace of the error syndromes to some eigenspace of the error syndromes.
]
#definition[
    A logical gate $overline(G)$ is *transversal* if it is a tensor product of single qubit gates.
]
#proposition[
    Every transversal gate is fault tolerant.
]
#example[
    The operation $overline(X)$, acting on the logical Hilbert space $H_7$, acts as the #NOT operator on the code subspace $span{ket(0), ket(1)}$: $ overline(X) = X_6 X_5 X_4 X_3 X_2 X_1 X_0, quad ==> overline(X) ket(overline(0)) = ket(overline(1)), quad overline(X) ket(overline(1)) = ket(overline(0)) $
]
#example[
    The operation $overline(Z) = Z_6 Z_5 Z_4 Z_3 Z_2 Z_1 Z_0$ commutes with each $M_i$ and leaves $ket(0000000)$ invariant so leaves $ket(overline(0))$ invariant. $overline(Z)$ anti-commutes with $overline(X)$ so acts within the code subspace and $overline(Z) ket(overline(0)) = ket(overline(1))$, $overline(Z) ket(overline(1)) = -ket(overline(1))$, so acts as Pauli $Z$ on logical qubits.
]
#example[
    $overline(H) = H_6 H_5 H_4 H_3 H_2 H_1 H_0$ realises the Hadamard gate on logical qubits: $ overline(H) ket(overline(0)) = 1/sqrt(2) (ket(overline(0)) + ket(overline(1))), quad overline(H) ket(overline(1)) = 1/sqrt(2) (ket(overline(0)) - ket(overline(1))) $ We have $H X H = Z$ so $H_i X_i = Z_i H_i$, thus $ M_j overline(H) ket(psi) = overline(H) N_j ket(psi), quad N_j overline(H) ket(psi) = overline(H) M_j ket(psi) $ Hence if $ket(psi)$ is in an eigenspace of $M_j$ and $N_j$, $overline(H) ket(psi)$ also lies in an eigenspace of $M_j$ and $N_j$ but with the eigenvalues of $M_j$ and $N_j$ swapped. This means $overline(H)$ preserves the code subspace, so $overline(H) ket(overline(0))$ and $overline(H) ket(overline(1))$ lie in the code subspace. Now $ overline(H) ket(overline(0)) = overline(H) 1/2^(3\/2) (1 + M_0)(1 + M_1)(1 + M_2) ket(0000000) = 1/2^(3\/2) (1 + N_0)(1 + N_1)(1 + N_2) overline(H) ket(0000000) $ $overline(H)$ maps $ket(0000000)$ to uniform superposition of all computational basis states, and $1 + N_j$ is projector onto $+1$ eigenspace of $N_j$, so we have the component of the uniform superposition which lies in the code subspace, i.e. $ overline(H) ket(overline(0)) = 1/sqrt(2) (ket(overline(0)) + ket(overline(1))) $ Similarly, $ overline(H) ket(overline(1)) = overline(H) 1/2^(3\/2) (1 + M_0)(1 + M_1)(1 + M_2) ket(1111111) = 1/2^(3\/2) (1 + N_0)(1 + N_1)(1 + N_2) overline(H) ket(1111111) $ $overline(H)$ maps $ket(1111111)$ to uniform superposition of all computational basis states, with each state with an odd number of $1$'s negated, hence $ overline(H) ket(overline(1)) = 1/sqrt(2) (ket(overline(0)) - ket(overline(1))) $ as all computational basis states in $ket(overline(1))$ have odd number of $1$'s.
]
#example[
    If two logical qubits are encoded with 14 physical qubits using Steane code, a logical #CNOT can be implemented as $ overline(CNOT) = product_(i = 1)^7 C_i "NOT"_i $ where $C_i "NOT"_i$ is #CNOT with $i$th qubit in first logical qubit as control and $i$th qubit in second logical qubit as target.
]
#theorem("Eastin, Knill")[
    Not all gates in a UGS can be transversal.
]

= Quantum algorithms

== Simon's algorithm

#definition[
    *Bitwise addition* of $a$ and $b$ is $a xor b = c$ where $c_i = a_i + b_i mod 2$.
]
#definition[
    *Simon's problem* is: given an $n$-bit function $f: {0, 1}^n -> {0, 1}^n$, with $f(x xor a) = f(x)$ for all $x$ ($a != 0$) and $f(x) != f(y)$ otherwise, determine the period $a$.
]
#example[
    Let $f: {0, 1}^n -> {0, 1}^n$ be $n$-bit function with period $a != 0$, so $f(x xor a) = f(x)$ and $f(x) != f(y)$ otherwise. To determine $a$ classically, we compute $f(x_i)$ until we find two values with $f(x_i) = f(x_j)$, then $a = x_i xor x_j$. After $m$ values are computed, we know $a != x_i xor x_j$ for all $i, j <= m$, so at most $1/2 m(m - 1)$ values are eliminated. There are $2^n - 1$ values for $a$, so this has complexity $O(2^(n\/2))$.
]
#definition[
    *Bitwise product* of $x = (x_(n - 1)...x_0)_2$ and $y = (y_(n - 1)...y_0)_2$ is $ x dot.op y = x_(n - 1) y_(n - 1) dots.h.c + x_0 y_0 quad mod 2 $
]
#proposition[
    $ H^(tp n) ket(0) & = 1/2^(n\/2) sum_(k = 0)^(2^n - 1) ket(k) quad "and" \ H^(tp n) ket(x) & = times.circle.big_(i = 0)^(n - 1) 1/sqrt(2) ((-1)^(0 dot.op x_i) ket(0) + (-1)^(1 dot.op x_i) ket(1)) = 1/2^(n\/2) sum_(k = 0)^(2^n - 1) (-1)^(k dot x) ket(k) $
]
#algorithm("Simon's algorithm")[
    Define the unitary operator $U_f$ acting on $n$ input qubits $ket(x)$ and $n$ output qubits $ket(m)$: $ U_f ket(x) ket(m) = ket(x) ket(m xor f(x)) $
    + Start with system in state $ket(0)_n tp ket(0)_n$ where $ket(0)_n = ket(00...0)$.
    + Apply $H^(tp n) tp I$ (i.e. acting on input qubits) to give $ 1/(2^(n\/2)) sum_(k = 0)^(2^n - 1) ket(k) tp ket(0)_n $
    + Apply $U_f$ to give $ 1/2^(n\/2) sum_(k = 0)^(2^n - 1) ket(k) tp ket(0 xor f(k)) = 1/2^(n\/2) sum_(k = 0)^(2^n - 1) ket(k) tp ket(f(k)) $
    + Measure the ancillary bits (the $ket(f(k))$) in the computational basis, yielding a random $f(x_0)$. The state collapses to $ 1/sqrt(2) (ket(x_0) + ket(x_0 xor a)) tp ket(f(x_0)) $
    + Discard ancillary bits and apply $H^(tp n)$ to input bits $1/sqrt(2) (ket(x_0) + ket(x_0 xor a))$ to give $
        H^(tp n) 1/sqrt(2) (ket(x_0) + ket(x_0 xor a)) & = 1/sqrt(2) (H^(tp n) ket(x_0) + H^(tp n) ket(x_0 xor a)) \
        & = 1/sqrt(2) 1/2^(n\/2) (sum_(k = 0)^(2^n - 1) (-1)^(k dot.op x_0) ket(k) + sum_(k = 0)^(2^n - 1) (-1)^(k dot.op (x_0 xor a)) ket(k)) \
        & = 1/2^((n + 1)\/2) sum_(k = 0)^(2^n - 1) (-1)^(k dot.op x_0) (1 + (-1)^(k dot.op a)) ket(k) \
        & = 1/2^((n - 1)\/2) sum_(k = 0: \ k dot a = 0)^(2^n - 1) (-1)^(k dot.op x_0) ket(k)
    $
    + Measure the state in the computational basis, which gives $k in {0, ..., 2^n - 1}$ such that $k dot a = 0 thick mod 2$.
    + $a$ satisfies $n$ linearly independent equations of the form $k dot a = 0 thick mod 2$, so $O(n)$ measurements ($O(n)$ values of $k$) are needed to obtain all bits of $a$.
    This can be implemented as
    #figure(quantum-circuit(
        lstick($ket(q_1)$), gate($H$), mqgate($U_f$, n: 2), gate($H$), meter(), setwire(2), 1, nl,
        lstick($ket(q_0) = ket(0)$), 2, meter(), setwire(2), 2
    ))
]
#example[
    Let $f: {0, 1}^3 -> {0, 1}^3$, $a = 010$, and $ f(000) & = f(010) = x, quad f(001) = f(011) = y, \ f(100) & = f(110) = z, quad f(101) = f(111) = w $ Using Simon's algorithm:
    - Applying $H^(tp 3)$ to $ket(000) tp ket(000)$ gives $ 1/(2 sqrt(2)) (ket(000) + ket(001) + ket(010) + ket(011) + ket(100) + ket(101) + ket(110) + ket(111)) tp ket(000) $
    - Applying $U_f$ gives $ 1/(2 sqrt(2)) ((ket(000) + ket(010)) tp ket(x) + (ket(001) + ket(011)) tp ket(y) + (ket(100) + ket(110)) tp ket(z) + (ket(101) + ket(111)) tp ket(w)) $
    - Measure the ancillary bits, assuming it yields value corresponding to $ket(x)$, so state has collapsed to $ 1/sqrt(2) (ket(000) + ket(010)) tp ket(x) $
    - Apply $H^(tp 3)$ to the input bits, giving $ 1/2^((3 - 1)\/2) sum_(k = 0: \ k dot a = 0)^(2^3 - 1) ket(k) = 1/2 (ket(000) + ket(001) + ket(101) + ket(100)) $
    - Measuring $000$ gives no information. Measuring $001$ implies that $a_0 = 0$. Measuring $010$ implies that $a_1 = 0$. Measuring $101$ implies that $a_0 + a_2 = 0$. So measuring the last three imply $a = 010$ (since $a != 000$).
]

== Quantum Fourier transform

#definition[
    *Quantum Fourier transform* is unitary operation $U_"FT"$ acting on the $n$ qubit space $H_n$, given by action on computational basis states: $ U_"FT" ket(x) = 1/2^(n\/2) sum_(y = 0)^(2^n - 1) e^(2 pi i x y \/ 2^n) ket(y) $ It is quantum version of the discrete Fourier transform: by linearity, if $ket(psi) = sum_(x = 0)^(2^n - 1) psi_x ket(x)$ and $ket(phi) = U_"FT" ket(psi) = sum_(y = 0)^(2^n - 1) phi_y ket(y)$, then $ phi_y = 1/2^(n\/2) sum_(x = 0)^(2^n - 1) e^(2pi i x y \/2^n) psi_x $ Note this is precisely the discrete Fourier transform on the vector $psi_x$.
]
#note[
    Can check $U_"FT"$ is unitary by checking $U_"FT" ket(x)$ has norm $1$ and $U_"FT" ket(x)$ orthogonal to $U_"FT" ket(x')$ for $x != x'$ (i.e. it preserves the inner product).
]
#example[
    Note that classically, computing $phi_y$ requires $2^n$ additions. If $y = y_(n - 1)...y_0$, i.e. $y = y_(n - 1) 2^(n - 1) + dots.h.c + y_0$, then $ e^(2 pi i x y\/2^n) = product_(l = 0)^(n - 1) e^(2pi i x y_l \/ 2^(n - l)) $ which gives $ U_"FT" ket(x) = 1/2^(n\/2) sum_(y = 0)^(2^n - 1) e^(2pi i x y\/2^n) ket(y) = 1/2^(n\/2) times.circle.big_(l = 0)^(n - 1) (ket(0) + e^(2pi i x \/2^(n - l)) ket(1)) $ Note this is similar to $ H^(tp n) ket(x) = times.circle.big_(i = 0)^(n - 1) 1/sqrt(2) (ket(0)_i + (-1)^(x_i) ket(1)_i) = sum_(y = 0)^(2^n - 1) (-1)^(x dot y) ket(y) $ However, for $U_"FT"$, phases in individual qubit states depend on $x$, not just $x_l$, so $U_"FT"$ cannot be realised only by single-qubit operations. Now also $ e^(2pi x \/2^(n - l)) = e^(2pi i(x_(n - 1) 2^(l - 1) + dots.h.c + x_0 2^(l - n))) = product_(m = 0)^(n - 1) e^(2pi i x_m \/2^(n - l - m)) = product_(m = 0)^(n - l - 1) e^(2pi i x_m\/2^(n - l - m)) $ since $e^(2pi i r) = 1$ for $r in ZZ$. So phase for $l = n - 1$ only depends on $x_0$, phase for $l = n - 2$ only depends on $x_0$ and $x_1$: $ U_"FT" ket(x) = 1/2^(n\/2) (ket(0) + e^(i pi x_0) ket(1)) tp (ket(0) + e^(i pi x_1) e^(i pi x_0 \/2)) tp dots.c $ When $U_"FT"$ is realised, order of qubits is reversed. QFT can be implemented of controlled-phase gates, where we apply unitaries $ R_k = mat(1, 0; 0, e^(i pi\/2^k)) $ Each qubit $i$ has controlled-$R_k$ applied, controlled by each qubit $j < i$, where $k = i - j$. E.g. for $n = 3$,
    #figure(quantum-circuit(
        lstick($ket(q_2)$), gate($H$), gate($S$), gate($T$), 3, swap(2), 1, nl,
        lstick($ket(q_1)$), 1, ctrl(-1), 1, gate($H$), gate($S$), 3, nl,
        lstick($ket(q_0)$), 2, ctrl(-2), 1, ctrl(-1), gate($H$), swap(-2), 1
    ))
    where $times$ indicates swapping qubits. One gate is applied to qubit $0$, two gates applied to qubit $1$, ..., $n$ gates applied to qubit $n - 1$, so total number of gates required to implemented QFT is $O(n^2)$
]

== Shor's algorithm

#example[
    Given $N in NN$, pick random $1 < y < N$. If $gcd(y, N) != 1$, we can find a divisor of $N$. If $gcd(y, N) = 1$, define $ f_y: ZZ -> ZZ\/N, quad f_y (a) = y^a quad mod N $ Period of $f_y$ is smallest $r in NN$ such that $f_y (r) = 1$. We have $f_y (a) = f_y (b)$ iff $a - b = 0 mod r$. Let $r$ be even (if $r$ odd, start again with different $y$). Now $ y^r - 1 = 0 mod N ==> (y^(r\/2) - 1)(y^(r\/2) + 1) = 0 mod N $ If either factor on LHS is multiple of $N$, start again with different $y$. Otherwise, we know $y^(r\/2) - 1$ and $N$ have common factor $< N$, and so use Euclid's algorithm to find $gcd(y^(r\/2) - 1, N)$.
]
#algorithm("Shor's algorithm")[
    - Shor's algorithm finds the smallest $r > 0$ such that $y^r equiv 1 mod N$.
    - Start with state $ket(0)_n ket(0)_(n_0)$ where $n_0 = ceil(log_2 (N))$, $n = 2n_0$.
    - Act with $H^(tp n)$ on input bits, giving $ 1/2^(n\/2) sum_(x = 0)^(2^n - 1) ket(x) tp ket(0) $
    - Act with $U_f$ (where $U_f ket(x) ket(m) = ket(x) ket(m xor f(x))$), giving $ 1/2^(n\/2) sum_(x = 0)^(2^n - 1) ket(x) tp ket(f(x)) $
    - Measure the output bits, yielding a random value $f(x_0)$ (assume WLOG that $x_0 < r$), which projects the state to $ 1/sqrt(Q + 1) sum_(m = 0)^Q ket(x_0 + m r) ket(f(x_0)) $ where $Q = |{i in {0, ..., 2^n - 1}: f(i) = f(x_0)}|$ which is approximately the largest integer strictly less than $2^n\/r$. Shift by random $x_0$ means we can't learn anything about $r$ by measuring input bits. Discard output bits.
    - Perform QFT on input bits, giving $ U_"FT" 1/sqrt(Q + 1) sum_(m = 0)^Q ket(x_0 + m r) & = 1/sqrt(Q + 1) sum_(m = 0)^Q 1/2^(n\/2) sum_(y = 0)^(2^n - 1) e^(2pi i(x_0 + m r)y\/2^n) ket(y) \ & = 1/2^(n\/2) sum_(y = 0)^(2^n - 1) e^(2pi i x_0 y\/2^n) (1/sqrt(Q + 1) sum_(m = 0)^Q e^(2pi i m r y\/2^n)) ket(y) $
    - Measure input bits in the computational basis. Probability that this yields value $y$ is $ p(y) & = abs(1/sqrt(Q + 1) 1/2^(n\/2) e^(2pi i x_0 y\/2^n) (sum_(m = 0)^Q e^(2pi i m r y\/2^n)))^2 \ & = 1/(2^n (Q + 1)) abs(sum_(m = 0)^Q e^(2pi i m r y\/2^n))^2 \ & = 1/(2^n (Q + 1)) abs((e^(2 pi i r y (Q + 1)\/2^n) - 1)/(e^(2 pi i r y\/2^n) - 1))^2 \ & = 1/(2^n (Q + 1)) abs((e^(pi i r y (Q + 1)\/2^n) (e^(pi i r y (Q + 1)\/2^n) - e^(-pi i r y(Q + 1)\/2^n)))/(e^(pi i r y\/2^n) (e^(pi i r y\/2^n) - e^(-pi i r y\/2^n))))^2 \ & = 1/(2^n (Q + 1)) (sin^2 (pi r y(Q + 1)\/2^n))/(sin^2 (pi r y\/2^n)) $
    - When $r y\/2^n in ZZ$, we have $p(y) = 1/(2^n (Q + 1)) abs(sum_(m = 0)^Q 1)^2 = (Q + 1)\/2^n$. Now $Q + 1 approx 2^n\/r$ so $p(y) approx 1\/r$.
    - If $r y\/2^n in.not ZZ$ (and not close to being an integer), then $sum_(m = 0)^Q e^(2pi i m r y\/2^n) < 1$ (typically a small value since phases do not add coherently) and $p(y) approx 1\/(2^n (Q + 1)) approx r\/4^n$. Note $r <= N < 2^(n_0) << 2^n$ implies that summing over all the approximately $2^n$ possibly values of $y$ gives $ sum_(y: r y\/2^n in.not ZZ) p(y) approx 2^n r\/4^n approx r\/2^n << 1 $
    - Hence it is likely to measure $y$ such that $r y\/2^n$ is approximately an integer. Equivalently, $y\/2^n = j\/r$ for some $j in ZZ$.
    - With high probability, $y$ will be the nearest integer to a multiple of $2^n\/r$, i.e. within $1\/2$ of $j 2^n\/r$, so $ abs(y/2^n - j/r) <= 1/2^(n + 1) <= 1/(2N^2) $ since $N <= 2^(n_0) = 2^(n\/2)$. There is unique fraction $j\/r$ with $r < N$ satisfying this (by triangle inequality), as $ abs(j_1/r_1 - j_2/r_2) >= 1/(r_1 r_2) > 1/N^2 $ unless $j_1/r_1 = j_2/r_2$ (this is why $n = 2n_0$ is chosen). $j/r$ can be obtained from $y\/2^n$ via continued fractions.
    - If $j$ and $r$ have common divisor, we obtain $r_0 = r\/gcd(j, r)$ instead of $r$. But given the guess $r_0$, we can check if $r_0$ is the period by checking if $f(r_0) = 1$, and if not try $f(2r_0), f(3r_0), ...$. If these fail, run algorithm again. Probability of $j$ and $r$ having common divisor is $< 1\/2$.
]