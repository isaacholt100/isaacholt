#import "@preview/quill:0.2.0": *
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.1" as cetz: canvas, draw
#let name-abbrvs = (
    "Hidden Subgroup Problem (HSP)": "HSP",
    "Discrete Logarithm Problem (DLP)": "DLP",
    "Amplitude Amplification Theorem/2D-subspace Lemma": "Amplitude Amplification Theorem",
    "Lie-Trotter Product Formula": "Lie-Trotter"
)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)
#set document(
    title: "Quantum Computation Notes",
    author: "Isaac Holt",
    keywords: ("quantum computing", "quantum", "quantum computation", "algorithms", "complexity")
)

#let poly = math.op("poly")
#let polylog = math.op("polylog")
#let ip(a, b) = $angle.l #a, #b angle.r$
#let ket(arg) = $lr(| #h(0.2pt) arg #h(0.2pt) angle.r, size: #0%)$
#let bra(arg) = $lr(angle.l #h(0.2pt) arg #h(0.2pt) |, size: #0%)$
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
#let tp = $times.circle$
#let QFT = math.op("QFT")
#let Pr = math.op("Pr")
#let Ctrl(U) = $C dash.en #h(0pt) #U$
#let Aut = math.op("Aut")
#let Rot = math.op("Rot")

#set terms(indent: 16pt)

= Basic notions in quantum information theory

The field is motivated by the fact that we want to control quantum systems.
+ Can we construct and manipulate quantum systems?
+ If so, which are the scientific and technological applications?
Entanglement frontier: highly complex quantum systems, which are more complex and richer than classical systems. However, quantum systems have _decoherence_, which classical systems don't. "Quantum advantage" gives speed up over classical systems.

Quantum vs classical information theory:
- True randomness.
- Uncertainty.
- Entanglement.

Note we always work with finite-dimensional Hilbert spaces, so take $HH = CC^N$.

== Qubits and basic operations

#notation[
    Vectors are denoted by $ket(psi) in CC^n$, dual vectors by $bra(psi) in (CC^n)^*$, and inner products by $braket(psi, phi) in CC$. $ket(psi) bra(psi): CC^n -> CC^n$ are rank-one projectors.
]
#definition[
    Another important basis of $CC^2$ is ${ket(+), ket(-)}$, where $ket(+) = 1/sqrt(2) (ket(0) + ket(1))$ and $ket(-) = 1/sqrt(2) (ket(0) - ket(1))$.
]<def:plus-minus-basis>
#definition[
    For an operator $T: HH -> HH$, the *operator norm* of $T$ is $
        norm(T) = norm(T)_(HH -> HH) := sup_(x in H) norm(T(x))_HH / norm(x)_HH
    $
]<def:operator-norm>
#notation[
    Let $B(HH)$ denote the space of bounded linear operators, i.e. $T$ such that $norm(T) < oo$.
]
#notation[
    Denote the dual of the operator $T$ by $T^*$, i.e. the operator that satisfies $braket(y, T(x)) = braket(T^* (y), x)$ for all $x, y in HH$.
]
#definition[
    A *quantum measurement* is a collection of measurement operators ${M_n}_n subset.eq B(HH)$ which satisfies $sum_n M_n^* M_n = II$, the identity operator.

    Given $ket(phi)$, the probability that $ket(n)$ occurs after this operation is $p(n) = braket(phi, M_n^* M_n, phi)$. After performing this operation, the state of the system is $1/sqrt(p(n)) M_n ket(phi)$.
]<def:measurement>
#example[
    A measurement in the computational basis is $M_0 = ket(0) bra(0)$, $M_1 = ket(1) bra(1)$. Note $M_0$ and $M_1$ are self-adjoint. Let $ket(psi) = alpha_0 ket(0) + alpha_1 ket(1)$. Then $p(i) = braket(phi, M_i, phi) = abs(alpha_i)^2$. The state after measurement is $alpha_i / abs(alpha_i) ket(i)$, which is equivalent to $ket(i)$.

    Note that $ket(psi)$ and $e^(i theta) ket(psi)$ are operationally identical: the phase does not affect the measurement probabilities.
]
#definition[
    A quantum measurement ${M_n}_n subset.eq B(HH)$ is *projective measurement* if the $M_n$ are orthogonal projections (i.e. they are self-adjoint (Hermitian) and $M_n M_m = delta_(n m) M_n$).
]<def:measurement.projective>
#definition[
    An *observable* is a Hermitian operator, which we can express as its spectral decomposition $
        M = sum_n lambda_n M_n,
    $ where ${M_n}_n$ is a projective measurement. The possible outcomes of the measurement correspond to its eigenvalues $lambda_n$ of the observable. Note that the expected value of the measurement is $
        sum_n lambda_n p(n) = sum_n lambda_n braket(phi, M_n, phi) = braket(phi, M, phi).
    $
]<def:observable>
#definition[
    $T: HH -> HH$ is *positive (semi-definite)* if $braket(psi, T, psi) >= 0$ for all $ket(psi) in H$.
]
#definition[
    A *POVM (positive operator valued measurement)* is a collection ${E_n}_n$ where $E_n = M_n^* M_n$ for a general measurement ${M_n}_n$. Note that each $E_n$ is positive.

    Note that $sum_n E_n = II$ and the probability of obtaining outcome $m$ on $ket(psi)$ is $p(m) = braket(psi, E_m, psi)$. We use POVMs when we care only about the probabilities of the different measurement outcomes, and not the post-measurement states.

    Conversely, given a POVM ${E_n}_n$, we can define a general measurement $\{sqrt(E_n)\}_n$.
]<def:povm>
#remark[
    Note that any operation transforming a normalised quantum state must map it to a normalised quantum state, and so the operation must be unitary.
]
#definition[
    The *Pauli matrice* are $
        sigma_0 & = II = mat(1, 0; 0, 1), quad sigma_X = X = mat(0, 1; 1, 0), \
        sigma_Y & = Y = mat(0, -i; i, 0), quad sigma_Z = Z = mat(1, 0; 0, -1).
    $
]<def:pauli-matrices>
#definition[
    The *trace* of $T: HH -> HH$ is $
        tr T = tr M = sum_i M_(i i) in CC,
    $ where $M$ is a matrix representation of $T$ in any basis (this is well-defined since the trace is cyclic and linear).
]
#proposition[
    For any state $ket(phi)$ and any operator $A$, $
        tr(A ket(phi) bra(phi)) = braket(phi, A, phi).
    $
]
#proof[
    Straightforward.
]
#definition[
    A *density matrix/operator* is a Hermitian linear operator $rho in B(HH)$ which is positive semi-definite and satisfies $tr rho = 1$.
]

== Postulates of quantum mechanics (Heisenberg picture)

#postulate[
    Given an isolated physical system, there exists a complex (separable) Hilbert space $HH$ associated with it, called *state space*. The physical system is described by a *state vector*, which is a normalised vector in $HH$.
]
#postulate[
    Given an isolated physical system, its evolution is described by a unitary. If the state of the system at time $t_1$ is $ket(phi_1)$ and at time $t_2$ is $ket(phi_2)$, then there exists a unitary $U_(t_1, t_2)$ such that $ket(phi_2) = U_(t_1, t_2) ket(phi_1)$.
]
This can be generalised with the Schrodinger equation: the time evolution of a closed quantum system is given by $i planck.reduce dif / (dif t) ket(phi(t)) = H ket(phi(t))$. $H$ is called the *Hamiltonian* and is generally time-dependent. Let the spectral decomposition of $H$ be $
    H = sum_i E_i ket(E_i) bra(E_i),
$ where the $E_i$ are the energy eigenvalues and the $ket(E_i)$ are the energy eigenstates (stationary states).

The minimum energy is called the *ground state energy* and its associated eigenstate is called the *ground state*. The *gap* of $H$ is the (absolute) difference between the ground state energy and the next largest energy eigenvalue. The states $ket(E_i)$ are called stationary, since they evolve as $ket(E_i) -> exp(-i E_i t \/ planck.reduce) ket(E_i)$.

We have $ket(phi(t_2)) = U(t_1, t_2) ket(phi(t_1))$ where $U(t_1, t_2) = exp(-i H(t_2 - t_1) \/ planck.reduce)$ which is a unitary. In fact, any unitary $U$ can be written in the form $U = exp(i K)$ for some Hermitian $K$.

#postulate[
    Given a physical system with associated Hilbert space $HH$, quantum measurements in the system are described by a collection of measurements ${M_n}_n subset.eq B(HH)$ such that $sum_n M_n^* M_n = II$, as in @def:measurement. The index $n$ refers to the measurement outcomes that may occur in the experiment, and given a state $ket(phi)$ before measurement, the probability that $ket(n)$ occurs is $
        p(n) = braket(phi, M_n^* M_n, phi).
    $ The state of the system after measurement is $1/sqrt(p(n)) M_n ket(phi)$
]
#postulate[
    Given a composite physical system, its state space $HH$ is also composite and corresponds to the tensor product of the individual state spaces $HH_i$ of each component: $HH = HH_1 tp cdots tp HH_N$. If the state in each system $i$ is $ket(phi_i)$, then the state in the composite system is $ket(phi_1) tp cdots tp ket(phi_N)$.
]
#definition[
    Given $ket(phi) in H_1 tp cdots tp H_N$, $ket(phi)$ is *entangled* if it cannot be written as a tensor product of the form $ket(phi_1) tp cdots tp ket(phi_n)$. Otherwise, it is *separable* or a *product state*.
]
#example[
    The *EPR pair* (*Bell state*) $ket(phi^+) = 1/sqrt(2) (ket(00) + ket(11))$ is entangled.
]

== Postulates of quantum mechanics (Schrodinger picture)

#postulate[
    Given an isolated physical system, the state of the system is completely described by its density operator, which is Hermitian, positive semi-definite and has trace one.
]
*Pure states* are of the form $rho = ket(phi) bra(phi)$, *mixed states* are of the form $rho = sum_i p_i ket(phi_i) bra(phi_i)$.
#postulate[
    Given an isolated physical system, its evolution is described by a unitary. If the state of the system is at $t_1$ is $rho_1$ and is $rho_2$ at time $t_2$, then there is a unitary $U$ depending only on $t_1, t_2$ such that $rho_2 = U rho_1 U^*$.
]
#postulate[
    After measurement ${M_n}_n$, the probability of observing $n$ is $p(n) = tr (M_n^* M_n rho)$ and the state after measurement is $1/p(n) M_n rho M_n^*$.
]