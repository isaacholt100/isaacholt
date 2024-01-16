#import "../../template.typ": template
#show: template

#let hbar = $planck.reduce$
#let ip(a, b) = $angle.l #a, #b angle.r$
#let ket(arg) = $| #h(1pt) arg #h(1pt) angle.r$
#let bra(arg) = $angle.l #h(1pt) arg #h(1pt) |$
#let braket(..args) = $angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r$
#let Ket(arg) = $lr(| #h(1pt) arg #h(1pt) angle.r)$
#let Bra(arg) = $lr(angle.l #h(1pt) arg #h(1pt) |)$
#let Braket(..args) = $lr(angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r)$
#let conj(arg) = $arg^*$
#let expected(arg) = $angle.l arg angle.r$
#let vd(vector) = $bold(vector)$
#let End = $"End"$
#let tp = $times.circle$ // tensor product

= Quantum mechanics essentials

== States and wave functions

- Probability of finding particle in $(a, b)$ is $ P(a, b; t) = integral_a^b |psi(x, t)|^2 dif x $ Wave function is normalised so that $P(-oo, +oo; t) = 1$.

== Dirac notation

- *Definition*: *dual* of vector space $V$ is set of linear functionals from $V$ to $CC$: $ V^* := {Phi: V -> CC: forall a, b in CC, forall z, w in V, quad Phi(a vd(z) + b vd(w)) = a Phi(vd(z)) + b Phi(vd(w)) } $ We have $dim(V^*) = dim(V)$.
- *Remark*: if $V$ has inner product $ip(dot.op, dot.op)$, then an isomorphism is given by $vd(z) |-> Phi_(vd(z)) (dot.op) = ip(vd(z), dot.op)$.
- *Definition*: *dual* of $vd(z) in V$ is the corresponding element in $V^*$.
- *Remark*: if $V = CC^n$, can think of vectors in $V$ as $n times 1$ matrices and vectors in $V^*$ as $1 times n$ matrices.
- *Definition*: *Dirac notation* denotes vectors in a Hilbert space or its dual:
    - Write $ket(psi)$ (a *ket*) for vector in Hilbert space $cal(H)$ corresponding to wave function $psi$.
    - Write $bra(phi)$ (a *bra*) for dual vector in $cal(H)^*$.
    - A *bra-ket* denotes an inner product: $ braket(phi, psi) := ip(phi, psi) = integral_(-oo)^oo phi^* (x, t) psi(x, t) dif x $

== Hilbert spaces

- *Definiton*: *Hilbert space* is real or complex vector space with Hermitian inner product that is also a complete metric space with metric induced by the inner product. In particular, inner product satisfies:
    // - $forall (a, b) in CC^2, a ket(psi) + b ket(phi) in cal(H)$
    - *Hermiticity*: $braket(psi, phi) = braket(phi, psi)^*$.
    - *Sesquilinearity* (linear in the second factor, anti-linear in the first). For $ket(phi) = c_1 ket(phi_1) + c_2 ket(phi_2)$:
    $ braket(psi, phi) & = c_1 braket(psi, phi_1) + c_2 braket(psi, phi_2) \ braket(phi, psi) & = c_1^* braket(phi_1, psi) + c_2^* braket(phi_2, psi) $
    - *Positive definiteness*: $braket(psi, psi) >= 0$ and $braket(psi, psi) = 0 <==> ket(psi) = 0$ (this corresponds with a *physical state* condition).
- *Definition*: a quantum mechanical system is described by a *state* $ket(psi)$ in Hilbert space $cal(H)$.
- *Remark*: states which differ by only a normalisation factor are physically equivalent: $ forall c in CC^*, quad ket(psi) tilde.op c ket(psi) $ For this reason, pure quantum mechanical states are called *rays* in the Hilbert space, and we normally assume that a state $ket(psi)$ has norm $1$: $norm(ket(psi)) = 1$.
- *Remark*: note that the state labelled zero, $ket(0)$, is not equal to the zero state (the $0$ vector).

== Operators

- *Definition*: $hat(A): cal(H) -> cal(H)$ is *linear operator* if $ forall a, b in CC, forall ket(psi), ket(psi) in cal(H), quad hat(A) (a ket(psi) + b ket(phi)) = a \(hat(A) ket(psi)\) + b \(hat(A) ket(phi)\) $
- *Proposition*: products and linear combinations of linear operators are also linear operators.
- *Definition*: *adjoint (Hermitian conjugate)* of $hat(A)$, $hat(A)^dagger$, is defined by $ bra(psi) hat(A)^dagger ket(phi) = conj((bra(phi) hat(A) ket(psi))) $
- *Definition*: $hat(H)$ is *self-adjoint (Hermitian)* if $hat(H)^dagger = hat(H)$. Self-adjoint operators correspond to *observables* (measurable quantities) since they have real eigenvalues.
- *Definition*: $hat(U)$ is *unitary* if $hat(U)^dagger hat(U) = hat(I)$. Unitary operators describe time-evolution in quantum mechanics.
- *Definition*: *commutator* of operators $hat(A)$ and $hat(B)$ is $ \[hat(A), hat(B)\] = hat(A) hat(B) - hat(B) hat(A) $
- *Definition*: *anti-commutator* of operators $hat(A)$ and $hat(B)$ is $ \{hat(A), hat(B)\} = hat(A) hat(B) + hat(B) hat(A) $
- *Definition*: *expectation value* of observable $hat(A)$ on state $ket(psi)$ is $ expected(A)_psi := braket(psi, hat(A), psi) $ Interpreted as average outcome of many measurements of $hat(A)$ on same state $ket(psi)$.

== Matrix representation

- *Definition*: *matrix form* of operator $hat(A)$ with respect to orthonormal basis ${ket(n)}$ is given by $ A_(i j) = braket(i, hat(A), j)$.
- *Proposition*: for operator $hat(A)$ with matrix representation $A$ in basis ${ket(n)}$, matrix representation of $hat(A)$ in basis ${ket(m)}$ is $B = S A S^(-1)$ where $S$ is change of basis matrix from old basis ${ket(n)}$ to new basis ${ket(m)}$.

== Time-evolution

- *Theorem*: time-evolution of state is given by *Schrodinger equation*: $ i hbar dif / (dif t) ket(psi(t)) = hat(H) ket(psi(t)) ==> ket(psi(t)) = hat(U)_t ket(psi(0)) $ where $hat(H) = hat(K) + hat(V)$ is Hamiltonian operator, $hat(U)_t$ is unitary operator. If $hat(H)$ independent of $t$, then $hat(U)_t = exp(-i/planck.reduce t hat(H))$.
- *Principle of superposition*: Schrodinger equation is linear, so any linear combination of solutions is another solution.
- *Definition*: *exponential* of operator $hat(A)$ is $ exp\(hat(A)\) := sum_(n in NN_0) hat(A)^n / n! $

= Measurement and uncertainty

== Observables

- *Proposition*: for Hilbert space of finite dimension $N$, operator $hat(A)$ has $N$ eigenvalues (counting multiplicities). Eigenvalues of Hermitian operator $hat(M)$ correspond to possible values of the measurable quantity it represents.
- *Definition*: *spectrum* of operator $hat(H)$ is $ "Spec"\(hat(H)\) := \{lambda in CC: hat(H) - lambda hat(I) "non invertible"\} $ For finite-dimensional Hilbert space, this is equal to the set of eigenvalues of $hat(H)$.
- *Proposition*: eigenstates $ket(n)$ of Hermitian operator $hat(H)$ corresponding to different eigenvalues $lambda_n$ are orthogonal. If eigenvalue is degenerate (multiplicity greater than one) then for each eigenspace (vector space spanned by the eigenvectors) with dimension greater than one, we can choose an orthogonal basis of eigenstates.
- *Definition*: let $hat(A)$ have orthonormal eigenstates ${ket(v_i): i in [N]}$ and corresponding eigenvalues ${lambda_i: i in [N]}$. *Spectral representation* of $hat(A)$ is $ hat(A) = sum_(i = 1)^N lambda_i ket(v_i) bra(v_i) $ In particular, only eigenvalue of $hat(I)$ is $1$ with degeneracy $N$, so for any orthonormal basis ${ket(v_i): i in [N]}$  of $cal(H)$: $ hat(I) = sum_(i = 1)^N ket(v_i) bra(v_i) $
- *Definition*: when measurement is made on state $ket(psi) = sum_(i = 1)^N c_i ket(v_i)$, result is $lambda$ with probability $ p = sum_(i in [N], lambda_i = lambda) |braket(v_i, psi)|^2 = sum_(i in [N], lambda_i = lambda) |c_i|^2 $ If result is $lambda$, measuring again immediately after the measurement will yield $lambda$, so state collapses (up to irrelevant phase $e^(i alpha)$, $alpha in RR$) to $ 1/sqrt(p) sum_(i in [N], lambda_i = lambda) c_i ket(v_i) $ This is *collapse of the wavefunction* and cannot be represented by unitary transformation, so is not reversible.
// - *Definition*: $hat(A)$ *diagonalisable* if $hat(A) = hat(S) hat(D) hat(S)^(-1)$ where $hat(D)$ is diagonal and $hat(S)$ has columns corresponding to eigenvectors of $hat(A)$.
// - For $hat(A)$ diagonalisable, $ exp(hat(A)) = sum_(n = 0)^oo (hat(S) hat(D) hat(S)^(-1))^n / (n!) = hat(S) (sum_(n = 0)^oo hat(D)^n / (n!)) hat(S)^(-1) = hat(S) exp(hat(D)) hat(S)^(-1) $
- *Definition*: linear operator $hat(P)$ is *projector* if $hat(P)^dagger = hat(P)$ and $hat(P)^2 = hat(P)$.
- *Definition*: for orthonormal eigenstates ${ket(v_i): i in [N]}$ of operator $hat(A)$ and corresponding eigenvalues ${lambda_i: i in [N]}$, define projection operator $ hat(P)_lambda = sum_(i in [N], lambda_i = lambda) ket(v_i) bra(v_i) $
- *Proposition*: probability of measurement $hat(A)$ on state $ket(psi)$ yielding $lambda$ is $p_lambda = braket(psi, hat(P)_lambda, psi)$ and state collapses to $1/sqrt(p_lambda) hat(P)_lambda ket(psi)$.
- *Definition*: $hat(A)$ and $hat(B)$ are *compatible* if $\[hat(A), hat(B)\] = 0$.
- *Remark*: state can only have definite values for observables $A$ and $B$ if it is simultaneous eigenstate of both $hat(A)$ and $hat(B)$. There always exist simultaneous eigenstates for compatible operators.
- *Remark*: if $hat(A)$ and $hat(B)$ not compatible, measuring $A$ then $B$ then $A$ again will not always give same result for both measurements of $A$.

== Density matrices

- *Definition*: a state is *pure state* if it is definite, i.e. state of system is completely known, and only uncertainties are due to inherent uncertain nature of quantum mechanics.
- *Definition*: *density matrix (density operator)* of *pure state* $ket(psi)$ is $ hat(rho) := ket(psi) bra(psi) $
- *Theorem*: there is bijection between density matrices and pure states, and $ hat(M) ket(psi) = lambda ket(psi) quad & <==> quad hat(M) hat(rho) = lambda hat(rho) \ ket(psi) -> hat(U) ket(psi) quad & <==> quad hat(rho) -> hat(U) hat(rho) hat(U)^dagger $ i.e. transforming state $ket(psi)$ by unitary operator $hat(U)$ is equivalent to transforming density matrix $hat(rho)$ to $hat(U) hat(rho) hat(U)^dagger$.
- *Definition*: for any orthonormal basis states ${ket(v_i): i in [N]}$, *trace* of $hat(A)$ is $ tr\(hat(A)\) = sum_(i = 1)^N braket(v_i, hat(A), v_i) $
- *Proposition*: trace satisfies *cyclicity*: $ tr(A B C) = tr(B C A) = tr(C A B) $
- *Proposition*: density matrix of pure state is a projector.
- *Proposition*: density matrix $hat(rho)$ of pure state satisfies $tr\(hat(rho)\) = tr\(hat(rho)^2\) = 1$.
- *Definition*: *mixed state* is one where state of system is not known. It is ensemble of pure states, each with associated probability of system being in that state: ${(p_i, ket(v_i)): i in [M]}$, where each $ket(v_i)$ is normalised. This is classical uncertainty rather than quantum uncertainty.
- *Definition*: *density matrix* of *mixed state* is linear combination of density matrices for each pure state weighted by probability: $ hat(rho) := sum_(i = 1)^M p_i ket(v_i) bra(v_i) $ Can generalise definition to include possibility of ensembles containing mixed states: $hat(rho) = sum_(i = 1)^M p_i hat(rho)_i$ where $hat(rho)_i$ are mixed and/or pure density matrices.
- *Note*: one density matrix may be given by multiple mixed states.
- *Proposition*: let $hat(A)$ observable, then expected value of measuring $hat(A)$ on $hat(rho)$ is $expected(hat(A)) = tr\(hat(rho) hat(A)\)$.
- *Proposition*: density matrix $hat(rho)$ of any pure/mixed state satisfies:
    - *Normalised*: $tr(hat(rho)) = 1$
    - *Hermitian*: $hat(rho)^dagger = hat(rho)$
    - *Semi-positive-definite*: for every state $ket(psi)$, $braket(psi, hat(rho), psi) >= 0$ (can be $= 0$ when $ket(psi) != 0$).
- *Proposition*: after taking measurement of pure or mixed state $hat(rho)$:  
    - Result is $lambda$ with probability $p_lambda = tr\(hat(P)_lambda hat(rho) hat(P)_lambda\) = tr\(hat(P)_lambda hat(rho)\)$.
    - Density matrix after measuring value of $lambda$ is $1/p_lambda hat(P)_lambda hat(rho) hat(P)_lambda$.
- *Theorem*: let $hat(rho)$ be density matrix, then $hat(rho)$ corresponds to pure state iff $tr\(hat(rho)^2\) = 1$.

= Qubits and the Bloch sphere

== Qubits

- *Definition*: a *qubit* is state in two-dimensional Hilbert space. Usually *computational basis* ${ket(0), ket(1)}$ denotes basis for such a Hilbert space.
- *Proposition*: general pure state in qubit system is of the form $ ket(psi) = cos(theta / 2) ket(0) + e^(i phi) sin(theta / 2) ket(1), quad 0 <= theta <= pi, 0 <= phi < 2pi $ So there is bijection between pure qubit states and points on $S^2$, called the *Bloch sphere*. Any point on Bloch sphere can be labelled by its position vector: $ vd(r) = vec(x, y, z), quad x = sin(theta) cos(phi), y = sin(theta) sin(phi), z = cos(theta) $
- *Definition*: we define six special states on the Bloch sphere: $ 
ket(+) := 1/sqrt(2) (ket(0) + ket(1)) <-> 1/sqrt(2) (1, 1)^T: & quad vd(r) = (1, 0, 0)^T, quad (theta, phi) = (pi\/2, 0) \
ket(-) := 1/sqrt(2) (ket(0) - ket(1)) <-> 1/sqrt(2) (1, -1)^T: & quad vd(r) = (-1, 0, 0)^T, quad (theta, phi) = (pi\/2, pi) \
ket(L) := 1/sqrt(2) (ket(0) + i ket(1)) <-> 1/sqrt(2) (1, i)^T: & quad vd(r) = (0, 1, 0)^T, quad (theta, phi) = (pi\/2, pi\/2) \
ket(R) := 1/sqrt(2) (ket(0) - i ket(1)) <-> 1/sqrt(2) (1, -i)^T: & quad vd(r) = (0, -1, 0)^T, quad (theta, phi) = (pi\/2, 3pi\/2) \
ket(0) <-> (1, 0)^T: & quad vd(r) = (0, 0, 1)^T, quad (theta, phi) = (0, dot.op) \
ket(1) <-> (0, 1)^T: & quad vd(r) = (0, 0, -1)^T, quad (theta, phi) = (pi, dot.op) $

== Inside the Bloch sphere

- *Definition*: *Pauli $sigma$-matrices* are $ sigma_1 := mat(0, 1; 1, 0), quad sigma_2 := mat(0, -i; i, 0), quad sigma_3 := mat(1, 0; 0, -1) $
- *Definition*: for pure state $ket(psi)$, *Bloch vector* $vd(r)$ is corresponding point on Bloch sphere. For mixed state ${(p_i, ket(v_i)): i in [M]}$, *Bloch vector* is $ vd(r) := sum_(i = 1)^M p_i vd(r_i) $ where $vd(r_i)$ is Bloch vector corresponding to pure state $ket(v_i)$.
- *Proposition*: density matrix for state with Bloch vector $vd(r)$ is $ rho = 1/2 (I_2 + vd(r) dot.op sigma) $ where $vd(r) dot.op sigma = r_1 sigma_1 + r_2 sigma_2 + r_3 sigma_3 = x sigma_1 + y sigma_2 + z sigma_3$.
- *Proposition*: state is mixed iff its Bloch vector $vd(r)$ satisfies $|vd(r)| < 1$.
- *Proposition*: for any density matrix $rho$ defined by Bloch vector $vd(r)$, $ tr\(rho^2\) = 1/2 (1 + |vd(r)|^2) $

== Time evolution of a qubit

- *Remark*: unitary transformations of a qubit correspond to rotations of points on/in Bloch sphere about the origin, representing the fact that unitary transformations cannot transform pure states to mixed states.
- *Remark*: measurements and transform any state to a pure state.
- *Proposition*: $tr(rho^2)$ is invariant under unitary transformations (time evolution).
- $tr(rho^2)$ measures how mixed a state is: $tr(rho^2) = 1$ for pure states, $tr(rho^2) = 1/2$ for the most mixed single qubit state, corresponding to the origin: $vd(r) = vd(0)$, $rho = 1/2 I$.
- *Proposition*: mixing states can never produce a state further from origin than furthest initial state.
- *Note*: there are an infinite number of ways of writing a mixed state as an ensemble of two pure states: any line passing through the point represented by the mixed states intersects with the Bloch sphere twice - the intersection points give the pure states in the ensemble.
- *Definition*: *trace distance* between density matrices $hat(rho)_1$ and $hat(rho)_2$ is $ D\(hat(rho)_1, hat(rho)_2\) := 1/2 tr |hat(rho)_1 - hat(rho)_2| = 1/4 tr |(vd(r_1) - vd(r_2)) dot.op sigma| = 1/2 |vd(r_1) - vd(r_2)| = 1/2 sum_(i = 1)^N |lambda_i| $ where $|hat(A)| = sqrt(hat(A)^dagger hat(A))$, $lambda_i$ are the eigenvalues of $hat(rho)_1 - hat(rho)_2$ (trace distance is equal to sum of eigenvalues since $hat(rho)_1 - hat(rho)_2$ is Hermitian).
- *Remark*: trace distance gives notion of distance between two states.
- *Proposition*: trace distance defines a *metric* on set of density matrices:
    - *Non-negative*: $D\(hat(rho)_1, hat(rho)_2\) >= 0$.
    - *Separates points*: $D\(hat(rho)_1, hat(rho)_2\) = 0 <==> hat(rho)_1 = hat(rho)_2$.
    - *Symmetric*: $D\(hat(rho)_1, hat(rho)_2\) = D\(hat(rho)_2, hat(rho)_1\)$.
    - *Triangle inequality*: $D\(hat(rho)_1, hat(rho)_3\) <= D\(hat(rho)_1, hat(rho)_2\) + D\(hat(rho)_2, hat(rho)_3\)$

== Pauli matrices

- *Definition*: *Levi-Cevita* tensor $epsilon_(i j k)$ is defined for ${i, j, k} subset.eq {1, 2, 3}$ as:
    - $epsilon_(1 2 3) := epsilon_(2 3 1) := epsilon_(3 1 2) := 1$.
    - $epsilon_(3 2 1) := epsilon_(1 3 2) := epsilon_(2 1 3) := -1$.
    - $epsilon_(i j k) := 0$ otherwise.
- *Proposition*: Pauli matrices satisfy following properties:
    - *Hermitian*: $sigma_i^dagger = sigma_i$.
    - *Traceless*: $tr(sigma_i) = 0$.
    - $[sigma_i, sigma_j] = sigma_i sigma_j - sigma_j sigma_i = 2i epsilon_(i j k) sigma_k$.
    - ${sigma_i, sigma_j} = sigma_i sigma_j + sigma_j sigma_i = 2 delta_(i j) I_2$.
    - $sigma_i sigma_j = delta_(i j) I_2 + i epsilon_(i j k) sigma_k$.
    - They form a basis for vector space of $2 times 2$ Hermitian traceless matrices over $RR$.
- *Definition*: define measurement operators $X, Y, Z$ as $ X & := 1/2 (I_2 - sigma_1), quad Y := 1/2 (I_2 - sigma_2), quad Z := 1/2 (I_2 - sigma_3) $
- *Proposition*: $X$, $Y$ and $Z$ have their eigenvectors as the six special Bloch states, with eigenvalues $0$ or $1$: $ X ket(+) & = 0 ket(+), quad X ket(-) = 1 ket(-), \ Y ket(L) & = 0 ket(L), quad Y ket(R) = 1 ket(R), \ Z ket(0) & = 0 ket(0), quad Z ket(1) = 1 ket(1) $
- *Proposition*: exponentials of Pauli matrices are unitary matrices: $forall alpha in RR$, $ exp(i alpha sigma_1) & = cos(alpha) I_2 + i sin(alpha) sigma_1, \ exp(i alpha sigma_2) & = cos(alpha) I_2 + i sin(alpha) sigma_2, \ exp(i alpha sigma_3) & = cos(alpha) I_2 + i sin(alpha) sigma_3 $
- *Proposition*: for $alpha in RR$, $vd(n) in RR^3$, $|vd(n)|^2 = 1$, $ U_alpha (vd(n)) := exp(i alpha vd(n) dot.op sigma) = cos(alpha) I_2 + i sin(alpha) vd(n) dot.op sigma $ is unitary transformation. If density matrix $rho = 1/2 (I_2 + vd(r) dot.op sigma)$ evolves with time according to this operator, then $ rho -> U_alpha (vd(n)) rho U_alpha (vd(n))^dagger = 1/2 (I_2 + (R_alpha (vd(n)) vd(r)) dot.op sigma) $ where $R_alpha (vd(n))$ is $3 times 3$ orthogonal matrix corresponding to rotation of angle $2 alpha$ about axis in the direction of $vd(n)$.

= Bipartite systems

== Tensor products

- *Definition*: *tensor product* $ket(phi) tp ket(psi)$ in $H_1 tp H_2$ satisfies:
    - *Scalar multiplication*: $c(ket(phi) tp ket(psi)) = (c ket(phi)) tp ket(psi) = ket(phi) tp (c ket(psi))$.
    - *Linearity*:
        - $a ket(psi) tp ket(phi_1) + b ket(psi) tp ket(phi_2) = ket(psi) tp (a ket(phi_1) + b ket(phi_2))$.
        - $a ket(psi_1) tp ket(phi) + b ket(psi_2) tp ket(phi) = (a ket(psi_1) + b ket(psi_2)) tp ket(phi)$.
- *Definition*: induced inner product on $H_1 tp H_2$ is defined as $ (bra(psi_1) tp bra(phi_1))(ket(psi_2) tp ket(phi_2)) = braket(psi_1, psi_2) braket(phi_1, phi_2) $
- *Proposition*: for bases $\{ket(v_i): i in [N_1]\}$ for $H_1$ and $\{ket(w_j): j in [N_2]\}$ for $H_2$, ${ket(v_i) tp ket(w_j), i in [N_1], j in [N_2]}$ is basis for $H_1 tp H_2$ and is orthonormal if $\{ket(v_i)\}$ and $\{ket(v_j)\}$ are orthonormal.
- *Definition*: most general vector $ket(psi) in H_1 tp H_2$ can be expressed as $ ket(psi) = sum_(i in [N_1], thick j in [N_2]) c_(i, j) ket(v_i) tp ket(v_j) $ Generally, this cannot be written as a tensor product $ket(psi) tp ket(phi)$. If it can be, it is a *separable* state. If not, it is *entangled*.
- *Definition*: Hilbert space of $N$-qubit system is $2^N$-dimensional Hilbert space $H_N = H_q^(tp N)$ where $H_q$ is a single qubit Hilbert space.
- *Example*: let $H_3 = H_q tp H_q tp H_q$. Operator $hat(I) tp hat(sigma_1) tp hat(I)$ acts on the second qubit and leaves the other two invariant.

== Linear operators and local unitary operations

- *Definition*: linear operators on $H_1 tp H_2$ are linear combinations of $hat(A) tp hat(B)$, where $ \(hat(A) tp hat(B)\) (ket(psi) tp ket(phi)) := \(hat(A) ket(psi)\) tp \(hat(B) ket(phi)\) $
- *Proposition*: properties of tensor product of linear operators:
    - $hat(A) tp hat(B) + hat(C) tp hat(B) = \(hat(A) + hat(C)\) tp hat(B)$.
    - $hat(A) tp hat(B) + hat(A) tp hat(D) = hat(A) tp \(hat(B) + hat(D)\)$.
    - $\(hat(A) tp hat(B)\)^dagger = hat(A)^dagger tp hat(B)^dagger$.
    - $\(hat(A) tp hat(B)\)\(hat(C) tp hat(D)\) = \(hat(A) hat(C) tp hat(B) hat(D)\)$.
    - $tr_(cal(H)_A tp cal(H)_B) \(hat(A) tp hat(B)\) = tr_(cal(H)_A) \(hat(A)\) tr_(cal(H)_B) \(hat(B)\)$.
    In particular, tensor product of linear operators preserves unitarity, Hermiticity, positivity, and tensor product of two projectors is a projector.
- *Definition*: bipartite system is system described Hilbert space $cal(H)_A tp cal(H)_B$ which can be partitioned (separated) into two subsystems $A$ and $B$, described by Hilbert spaces $cal(H)_A$ and $cal(H)_B$. Alice has full control over system $A$, Bob has full control over system $B$, neither can control the other's system.
- *Definition*: for bipartite system, *local operations (LO)* are of the form $hat(U)_A tp hat(I)$ (for Alice) or $hat(I) tp hat(U)_B$ (for Bob) where $hat(U)_A$ and $hat(U)_B$ are unitary operators or measurement operators.
- *Proposition*: $hat(U)_A tp hat(I)$ and $hat(I) tp hat(U)_B$ commute: $\[hat(U)_A tp hat(I), hat(I) tp hat(U)_B\] = 0$, and their product is $hat(U)_A tp hat(U)_B$.
- *Theorem*: any unitary transformation $hat(U)_A tp hat(U)_B$ (i.e. using LO) acting on separable state $ket(psi) tp ket(phi)$ produces another separable state: $hat(U)_A ket(psi) tp hat(U)_B ket(phi)$. In particular, an entangled state cannot be created from a separable state.
- *Definition*: a mixed state is *separable* iff it is an ensemble of separable states, and *entangled* otherwise.
- *Definition*: *density matrix* of *separable pure state* $ket(Psi) = ket(psi) tp ket(phi)$ is $ hat(rho) := ket(Psi) bra(Psi) = (ket(psi) tp ket(phi)) (bra(psi) tp bra(phi)) = (ket(psi) bra(psi)) tp (ket(phi) bra(phi)) = hat(rho)_A tp hat(rho)_B $ where $hat(rho)_A = ket(psi) bra(psi)$ and $hat(rho)_B = ket(phi) bra(phi)$.
- *Definition*: *density matrix* of *separable mixed state* is $ hat(rho) := sum_(i = 1)^M p_i hat(rho)_A^((i)) tp hat(rho)_B^((i)) $ where $\{hat(rho)_A^((i))\}$ are mixed or pure states of first system, $\{hat(rho)_B^((i))\}$ are mixed or pure states of second system.

== Matrix representation

- *Definition*: *tensor product* of two vectors is given by e.g. $ vec(1, 2, 3) tp vec(4, 5) = vec(1 vec(4, 5), 2 vec(4, 5), 3 vec(4, 5)) = vec(4, 5, 8, 10, 12, 15) $ The expression is similar for matrices: $ mat(1, 2; 3, 4) tp mat(5, 6; 7, 8) = mat(1 mat(5, 6; 7, 8), 2 mat(5, 6; 7, 8); 3 mat(5, 6; 7, 8), 4 mat(5, 6; 7, 8)) = mat(5, 6, 10, 12; 7, 8, 14, 16; 15, 18, 20, 24; 21, 24, 28, 36) $
- *Definition*: *controlled `NOT` (`CNOT`)* operator acts on $H_2 = H_q tp H_q$ and is defined as $ U = (I_2 + sigma_3) / 2 tp I_2 + (I_2 - sigma_3) / 2 tp sigma_1 $ We have $U ket(00) = ket(00)$, $U ket(01) = ket(01)$, $U ket(10) = ket(11)$, $U ket(11) = ket(10)$.

== Local measurements

- *Definition*: for bipartite system, *local mesaurements* are Hermitian operators of the form $hat(F) = hat(F)_A tp hat(I)$ for Alice and $hat(G) = hat(I) tp hat(G)_B$ for Bob.
- *Notation*: projection operators of $hat(F)_A$ and $hat(G)_B$ for eigenvalues $lambda_i$ and $mu_j$ are denoted $hat(F)_(A i)$ and $hat(G)_(B j)$.
- *Remark*: in the full system $H_A tp H_B$, $hat(F)$ and $hat(G)$ are degenerate, with degeneracy given by dimension of other subsystem, i.e. $dim(cal(H)_B)$ for Alice's observable and $dim(cal(H)_A)$ for Bob's. Assuming no degeneracy in their own system, corresponding projection operators in full system are
$
hat(F)_i & = hat(F)_(A i) tp hat(I) = sum_(j = 1)^(N_2) ket(v_i) bra(v_i) tp ket(w_j) bra(w_j) \
hat(G)_j & = hat(I) tp hat(G)_(B j) = sum_(i = 1)^(N_1) ket(v_i) bra(v_i) tp ket(w_j) bra(w_j)
$
- *Note*: since $\[hat(F), hat(G)\] = 0$, these measurements are compatible so final state is eigenstate of both $hat(F)$ and $hat(G)$. Probability of an outcome occuring is not affected by whether Alice or Bob measures first (or simultaneously).
- *Example*: let $\{ket(v_i)\}, \{ket(w_j)\}$ be orthonormal eigenstates of operators $hat(F)_A$ and $hat(G)_B$ with non-degenerate eigenvalues $\{lambda_i\}$ and $\{mu_j\}$, $ket(Psi) = sum_(i in [N_1], med j in [N_2]) gamma_(i j) ket(v_i) tp ket(w_j)$ be entangled state, define $
alpha_i := (sum_(j = 1)^N_2 |gamma_(i j)|^2)^(1\/2), quad beta_j := (sum_(i = 1)^(N_1) |gamma_(i j)|^2)^(1\/2)
$ and define auxiliary states (set $ket(psi_j) = vd(0)$ when $beta_n = 0$ and $ket(phi_i) = vd(0)$ when $alpha_m = 0$): $
ket(psi_n) := 1/beta_j sum_(i = 1)^(N_1) gamma_(i j) ket(v_i) in cal(H)_A, quad ket(phi_i) := 1/alpha_i sum_(j = 1)^(N_2) gamma_(i j) ket(w_j) in cal(H)_B \
==> ket(Psi) = sum_(i = 1)^(N_1) alpha_i ket(v_i) tp ket(phi_i) = sum_(j = 1)^(N_2) beta_j ket(psi_j) tp ket(w_j)
$ If Alice measures $hat(F)$ with result $lambda_i$, entangled state $ket(Psi)$ collapses to separable state $
ket(Psi) -> hat(F)_i ket(Psi) = \(hat(F)_(A i) tp hat(I)\) ket(Psi) tilde ket(v_i) tp ket(phi_i)
$ So Bob's state depends on the result of Alice's measurement.

== Reduced density matrix

- *Definition*: for operator $hat(C) tp hat(D) in End(cal(H)_A tp cal(H)_B)$, *partial trace* over $cal(H)_A$ and $cal(H)_B$, $tr_A: End(cal(H)_A tp cal(H)_B) -> End(cal(H)_B)$ and $tr_B: End(cal(H)_A tp cal(H)_B) -> End(cal(H)_A)$, are $ tr_A \(hat(C) tp hat(D)\) := tr\(hat(C)\) hat(D), quad tr_B \(hat(C) tp hat(D)\) := tr\(hat(D)\) hat(C) $
- *Definition*: for bipartite system, the *reduced density matrix* of a subsystem is partial trace of density matrix over other subsystem. So for bipartite system, $ hat(rho)_A := tr_B \(hat(rho)\), quad hat(rho)_B := tr_A \(hat(rho)\) $
- *Note*: a reduced matrix describes one subsystem, assuming no knowledge of the other system.
- *Proposition*:
    - $hat(rho)_A$ is invariant under all local operations in system $B$.
    - Under unitary transformations $hat(U)$ in system $A$, $hat(rho)_A$ transforms as normal: $hat(rho)_A -> hat(U) hat(rho)_A hat(U)^dagger$.
    - Local measurements in system $A$ can be described by $hat(rho)_A$ and operators acting on $cal(H)_A$: $tr_B \(hat(F)_i hat(rho) hat(F)_i\) = hat(F)_(A i) hat(rho)_A hat(F)_(A i)$.
- *Theorem*: if $ket(Psi) in cal(H)_A tp cal(H)_B$ is pure state, then $hat(rho)_A$ is pure iff $ket(Psi)$ is separable.
- *Corollary*: if spectrum of $hat(F)_A$ is non-degenerate then measuring $hat(F)_A$ in system $cal(H)_A$ produces separable state on system $cal(H)_A tp cal(H)_B$, i.e. *measurement destroys entanglement*.
- *Note*: entanglement does not violate causality (does not allow communication faster than the speed of light). i.e., if Alice makes a local measurement on an entangled system, Bob cannot detect this, even though the reduced density matrix for his system has changed.

== Classical communication

- Alice and Bob can use classical communication (CC) to communicate results of measurements of their own subsystem. If the state was initially entangled, Bob communicating a measurement to Alice would give Alice information about her subsystem.
- *Definition*: *LOCC* is when Alice and Bob can use local operations (LO) and classical communication.

= Entanglement applications

== Bell states

- *Proposition*: measurements of entanglement:
    - Let $ket(Psi) in cal(H)_A tp cal(H)_B$. If $ket(Psi) = a ket(0) tp ket(phi) + b ket(1) tp ket(phi)$ for some $a, b in CC$, $ket(phi) in cal(H)_B$, then $ket(Psi)$ is separable, otherwise entangled.
    - If reduced density matrix of either subsystem gives a pure state ($tr(rho^2) = 1$) then state is separable. If it gives a mixed state ($tr(rho^2) < 1$), state is entangled.
    - $tr\(rho_A^2\) = tr\(rho_B^2\)$ gives measure of entanglement, with max value $1$ for no entanglement, min value $1\/2$ (for single qubit subsystem) for maximally entangled states.
- *Definition*: *Bell states* are defined as, for $x, y in {0, 1}$, $ ket(beta_(x y)) := 1/sqrt(2) (ket(0) tp ket(y) + (-1)^x ket(1) tp ket(overline(y))) $
- *Proposition*: Bell states are maximally entangled (trace of reduced density matrix of both sides is $1/2$) and form an orthonormal basis.
- Bell state basis is related to standard basis by unitary transformation, but Bell states can't be created from the separable standard basis by any LOCC process, since unitary transformations between them are not of form $hat(U)_A tp hat(U)_B$ (since this preserves separability), and measurements always produce a separable state.
- Alice and Bob can individually transform any Bell state to any other Bell state by the unitary operators $hat(U)_(x y) tp hat(I)$ and $hat(I) tp hat(U)_(x y)$ respectively: $ (hat(U)_(x y) tp hat(I)) ket(beta_(0 0)) = (hat(I) tp hat(U)_(x y)) ket(beta_(0 0)) = ket(beta_(x y)) $ where $ U_(0 0) = I_2, quad U_(0 1) = sigma_1, quad U_(1 0) = sigma_3, quad U_(1 1) = i sigma_2 $

== Superdense coding

- Qubit can be used instead of classical bit: $ket(0)$ corresponds to the bit $0$, $ket(1)$ corresponds to the bit $1$. In this case, the qubit can be measured with probability $1$ with the measurement operator $Z$, since $Z ket(0) = 0 ket(0)$, $Z ket(1) = 1 ket(1)$ so measurement with outcome $0$ means state is $ket(0)$ with probability $1$, measurement with outcome $1$ means state is $ket(1)$ with probability $1$.
- Alice can prepare the qubit to represent the classical bit to send to Bob: prepare any state $ket(psi)$ and measure on it with operator $1/2 (I_2 - sigma_3)$. Outcome is $0$ or $1$ - if outcome is equal to the bit $x$ she wants to send, $ket(psi)$ has been projected to $ket(x)$, so send this state to Bob. Otherwise, perform unitary transformation $sigma_1 ket(overline(x)) = ket(x)$ and send this state to Bob.
- *Superdense coding*:
    - Superdense coding allows one qubit to transmit two classical bits of information.
    - Alice and Bob share state $ket(beta_00)$.
    - Alice applies operation $hat(U)_(x y) tp hat(I)$ to whole system where $(x y)_2$ is the two bit message she wants to send (this just acts on her qubit). Note that this does not transmit any information to Bob, as his reduced density matrix is $rho_B = 1/2 I$ before and after the transformation.
    - Alice sends her qubit to Bob. Then Bob has the full Bell state $ket(beta_(x y))$ (he has both qubits). Bob then applies a measurement which has the four Bell states as eigenstates, which gives him the eigenvalue with probability $1$, e.g. he measures $ hat(B) = 0 ket(beta_00) bra(beta_00) + 1 ket(beta_01) bra(beta_01) + 2 ket(beta_10) bra(beta_10) + 3 ket(beta_11) bra(beta_11) $

== No-cloning theorem

- *No-cloning theorem*: in quantum mechanics, it is impossible to clone an unknown state $ket(psi)$. More precisely, it is impossible to perform transformation $ket(psi) tp ket(phi) -> ket(psi) tp ket(psi)$ for an arbitrary unknown state $ket(psi)$ and fixed initial state $ket(phi)$.

== Teleportation

- *Definition*: *Hadamard gate* is transformation given by operator $
U_H := 1/sqrt(2) mat(1, 1; 1, -1) = 1/sqrt(2) (sigma_1 + sigma_3)
$ We have $hat(U)_H ket(0) = ket(+)$, $hat(U)_H ket(1) = ket(-)$.
- *Definition*: *teleportation* is process of transferring quantum state $ket(psi)$ without using quantum communication (i.e. only using LOCC). It is as follows:
    - Alice has state $ket(psi) = a ket(0) + b ket(1)$, Alice and Bob share Bell state $ket(beta_00)$, so full system state is $
    ket(psi) tp ket(beta_00) & = 1/sqrt(2) ket(psi) tp ket(0) tp ket(0) + 1/sqrt(2) ket(psi) tp ket(1) tp ket(1) \
    & = 1/sqrt(2) (a ket(000) + a ket(011) + b ket(100) + b ket(111))
    $ Alice has first two qubits, Bob has third.
    - Alice performs `CNOT` on her two qubits, transforming state to $ 1/sqrt(2) (a ket(000) + a ket(011) + b ket(110) + b ket(101)) $ `CNOT` operator is not of form $A tp B$ so it entangles Alice's qubits.
    - Alice applies Hadamard gate to her system: $ hat(U)_H tp hat(I) tp hat(I) 1/sqrt(2) (a ket(000) + a ket(011) + b ket(100) + b ket(111)) = 1/2 sum_(x, y) ket(x) tp ket(y) tp hat(U)_(x y) ket(psi) $
    - Alice measures with operator $Z$ on both her qubits, giving measurement $(x y)_2$, causing state to collapse to $ket(x) tp ket(y) tp hat(U)_(x y) ket(psi)$.
    - Alice uses CC to send $(x y)_2$ to Bob. Bob then performs transformation $hat(U)_(x y)^(-1) = hat(U)_(x y)^dagger$ so his state becomes $ket(psi)$.

== Quantum key distribution (QKD)

- *Definition*: let message $M$ and secret key $K$ be $n$-bit integers, $K$ is shared by Alice and Bob, where each bit of $k$ has value $0$ or $1$ with equal probability. *One-time pad encryption* is as follows:
    - Alice produces encrypted message $C = M plus.circle K$, where $plus.circle$ is bitwise addition $mod 2$ (also bitwise `XOR`).
    - Alice transmits $C$ to Bob. Bob decrypts message by calculating $ C plus.circle K = (M plus.circle K) plus.circle K = M plus.circle (K plus.circle K) = M plus.circle 0 = M $
    - It is important that $K$ is at least as long as $M$ and is never reused.
    - Drawback is that $K$ might be very long, and must be transmitted securely prior to communication.
- *Definition*: *BB84* protocol for transmitting secret key is as follows:
    - Alice chooses random bit $x in {0, 1}$ with equal probability, makes random choice of $X$ or $Z$ with equal probability, then prepares qubit state according to the outcome: $ (0, Z) |-> ket(0), quad (1, Z) |-> ket(1), quad (0, X) |-> ket(+), quad (1, X) |-> ket(-) $ and sends this qubit to Bob using quantum communication.
    - Bob randomly chooses $X$ or $Z$ with equal probability, then measures qubit with this measurement operator.
    - This process is repeated enough to generate a sufficiently long key.
    - Alice and Bob publicly reveal their choices of $X$ or $Z$ for each qubit (must be after Bob receives the qubit), discarding all qubits for which same choice was not made. When same choice is made for qubit, Alice's choice of qubit will match with Bob's measurement.
- *Security of BB84*:
    - If Eve intercepts qubit, she must measure it to obtain information from it. But the four possible states are not all orthogonal, so Eve cannot make measurement which is guaranteed to distinguish them.
    - If Eve measures with $Z$ and Alice chose $Z$, Eve would correctly measure the qubit. But if Alice chose $X$, Eve would measure $0$ or $1$ with equal probability, and forward the same random qubit $ket(0)$ or $ket(1)$ to Bob. If Bob measures with $X$, result is discarded anyway. If Bob measures with $Z$, measurement is same random result as Eve's measurement, so differs from Alice's key half the time.
    - So for each (non-discarded) bit of key Eve intercepts and measures, probability that Alice and Bob's value differs is $1/4$, so currently Eve expects to know $3/4$ of the key, which is insecure. So Alice and Bob compare random subset of their keys and estimate error rate.
    - If rate too high, they assume interference from Eve, discard the key and repeat entire process again.

== Bell inequalities

- *Definition*: *local realism* is a property of a system:
    - *Locality*: influences cannot happen faster than speed of light.
    - *Realism*: measurements must be deterministic, i.e. measurements tell us a property of the system.
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

- *Definition*: let $X$ be random variable representing a message, $p(x) = PP(X = x)$ *Shannon entropy* is $
H(X) := -sum_x p(x) log_2 (p(x))
$ where conventionally $0 log 0 = 0$.
- *Shannon's noiseless coding theorem*: $H(X)$ gives lower bound on average number of bits needed to encode message $X$.
- *Definition*: *joint entropy* is $ H(X, Y) := -sum_(x, y) p(x, y) log_2 (p(x, y)) $
- *Proposition*: joint entropy obeys *subadditivity*: $ H(X, Y) <= H(X) + H(Y) $ with equality iff $X$ and $Y$ are independent variables, i.e. when $p(x, y) = PP(X = x) PP(Y = y)$.
- *Definition*: *relative entropy of $p(x)$ to $q(x)$* is defined for two random variables which take same values but with different distributions $p(x)$ and $q(x)$: $ H(p(x) || q(x)) & := sum_x (p(x) log_2 (p(x)) - p(x) log_2 (q(x))) \ & = -H(X) - sum_x p(x) log_2 (q(x)) $
- *Proposition*: relative entropy is non-negative and $ H(p(x) || q(x)) = 0 <==> forall x, p(x) = q(x) $
- *Remark*: relative entropy can diverge if for some $x$, $q(x) = 0$ and $p(x) != 0$
- *Definition*: *conditional entropy* is $ H(X|Y) := H(X, Y) - H(Y) <= H(X) $
- *Definition*: *mutual information* of $X$ and $Y$ is $ H(X : Y) := H(X) + H(Y) - H(X, Y) >= 0 $

== Quantum entropy

- *Definition*: *von Neumann entropy* of quantum state with density operator $hat(rho)$ is $ S\(hat(rho)\) := -tr(hat(rho) log_2 (hat(rho))) = -sum_i p_i log_2 (p_i) $ where $hat(rho) = sum_i p_i ket(i) bra(i)$, $ket(i)$ are eigenstates of $hat(rho)$. $S\(hat(rho)\)$ is Shannon entropy of ensemble of pure states described by $hat(rho)$.
- *Remark*: for pure state, $S\(hat(rho)\) = -1 log_2 (1) = 0$.
- *Definition*: *(quantum) relative entropy* is measure of distance between two states: $
S\(hat(rho)_1 || hat(rho)_2\) := tr\(hat(rho)_1 log_2 \(hat(rho)_1\)\) - tr\(hat(rho)_1 log_2 \(hat(rho)_2\)\)
$
- *Proposition*: $S\(hat(rho)_1 || hat(rho)_2\) >= 0$ with equality iff $hat(rho)_1 = hat(rho)_2$.
- *Definition*: for bipartite system $cal(H) = cal(H)_A tp cal(H)_B$ described by density matrix $hat(rho)$ and reduced density matrices $hat(rho)_A$ and $hat(rho)_B$, define $ S(A) := S\(hat(rho)_A\), quad S(B) := S\(hat(rho)_B\), quad S(A, B) := S\(hat(rho)\) $ where $S(A, B)$ is *(quantum) joint entropy* of $A$ and $B$.
- *Definition*: *(quantum) conditional entropy* of $A$ and $B$ is $ S(A | B) := S(A, B) - S(B) $
- *Remark*: unlike classical conditional entropy, quantum conditional entropy can be negative, e.g. if $hat(rho)$ describes pure state, $S(A, B) = 0$ but if entangled, $hat(rho)_B$ is not pure state so $S(B) > 0$.
- *Definition*: *(quantum) mutual information* is $ I(A: B) = S(A: B) := S(A) + S(B) - S(A, B) $
- *Remark*: entanglement can be interpreted as mutual information: information shared by $A$ and $B$ and not in either one alone.

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

- *Convention*: input for circuit diagrams has most significant bit at the top, circuits are read left to right, with last operation on the right.
- *Definition*: *(logical) gate* is function acting on bits.
- *Definition*: simplest gates are $f: {0, 1} -> {0, 1}$:
    - *Identity gate*: $id(x) := x$.
    - $c_0(x) := 0$.
    - $c_1(x) := 1$.
    - *#NOT gate*: $NOT(x): overline(x)$.
- *Definition*: *#FANOUT gate* is defined as $
FANOUT: {0, 1} -> {0, 1}^2, quad FANOUT(x) := (x, x)
$
#figure(quantum-circuit(
    row-spacing: 2pt,
    setwire(1, stroke: 0pt), 2, ctrl(2, show-dot: false), setwire(1, stroke: 1pt), 1, rstick($x$), [\ ],
    lstick($x$), 2, [\ ],
    setwire(1, stroke: 0pt), 2, ctrl(0, show-dot: false), setwire(1, stroke: 1pt), 1, rstick($x$)
))
- *Definition*: *#AND gate* is given by its *truth table*:
#figure(table(align: center,columns: (auto, auto, auto), inset: 5pt, [], $0$, $1$, $0$, $0$, $0$, $1$, $0$, $1$))
#figure(quantum-circuit(
    row-spacing: 2pt,
    setwire(1, stroke: 1pt),
    lstick($x$), 1, mqgate($#h(40pt)$, n: 3, radius: (right: 100%)), [\ ],
    setwire(1, stroke: 0pt), 3, setwire(1, stroke: 1pt), 2, rstick($AND(x, y)$), [\ ],
    lstick($y$), 2,
))
- *Definition*: *OR gate* is given by its *truth table*: $ #table(columns: (auto, auto, auto), inset: 5pt, [], $0$, $1$, $0$, $0$, $1$, $1$, $1$, $1$) $
- *Remark*: #AND and #OR are not reversible (invertible) so cannot be implemented by unitary operators.
- *Landauer's principle*: energy $E$ required to erase one bit satisfies $ E >= k_B T log(2) $ where $K_B$ is Boltzmann's constant, $T$ is temperature at which system operates.
- *Definition*: *controlled #NOT (#CNOT) gate*, $CNOT: {0, 1}^2 -> {0, 1}^2$, is $ CNOT(x, y) := cases((x, y) & "if" x = 0, (x, NOT(y)) & "if" x = 1) quad = (x, x xor y) = (x, x + y mod 2) $ Inverse of #CNOT is #CNOT. $x$ is *control bit*, $y$ is *target bit*.
#figure(quantum-circuit(
    lstick($y$), 2, targ(), 2, rstick($x xor y$), [\ ],
    lstick($x$), 2, ctrl(-1), 2, rstick($x$)
))
- *Definition*: *#CnNOT(1) gate* is defined as $ CnNOT(1)(x_1, ..., x_n, y) := (x_1, ..., x_n, y xor "AND"(x_1, ..., x_n)) $ For $n = 2$, #CCNOT gate is called a *Toffoli gate*. #CnNOT($n$) is reversible for all $n in NN$ and $(CnNOT(n))^(-1) = CnNOT(n)$.
#figure(quantum-circuit(
    lstick($y$), 2, targ(), 2, rstick($AND(x_1, x_2) xor y$), [\ ],
    lstick($x_2$), 2, ctrl(-1), 2, rstick($x_2$), [\ ],
    lstick($x_1$), 2, ctrl(-1), 2, rstick($x_1$)
))
- *Definition*: *#NAND gate* is defined as $ NAND(x, y) := NOT(AND(x, y)) $