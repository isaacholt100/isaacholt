#import "@preview/quill:0.2.0": *
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.1" as cetz: canvas, draw

#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: (:))
#set document(
    title: "Quantum Information Theory Notes",
    author: "Isaac Holt",
    keywords: ("quantum information")
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

    Given $ket(phi)$, the probability that $ket(n)$ occurs after this operation is $p(n) = braket(phi, M_n^* M_n, phi)$. After performing this operation, the state of the system is $1/sqrt(p(n)) M_n ket(phi)$. This is the *Born rule*.
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
    $T: HH -> HH$ is *positive (semi-definite)* (written $T >= 0$) if $braket(psi, T, psi) >= 0$ for all $ket(psi) in H$.
]
#definition[
    A *POVM (positive operator valued measurement)* is a collection ${E_n}_n$ where each $E_n = M_n^* M_n$ for a general measurement ${M_n}_n$ (i.e. each $E_n$ is positive and Hermitian, and $sum_n E_n = II$).

    Note that the probability of obtaining outcome $m$ on $ket(psi)$ is $p(m) = braket(psi, E_m, psi)$. We use POVMs when we care only about the probabilities of the different measurement outcomes, and not the post-measurement states.

    Conversely, given a POVM ${E_n}_n$, we can define a general measurement $\{sqrt(E_n)\}_n$.
]<def:povm>
#remark[
    Any transformation on a normalised quantum state must map it to a normalised quantum state, and so the operation must be unitary.
]
#definition[
    The *Pauli matrice* are $
        sigma_0 & = II = mat(1, 0; 0, 1), quad sigma_X = X = mat(0, 1; 1, 0), \
        sigma_Y & = Y = mat(0, -i; i, 0), quad sigma_Z = Z = mat(1, 0; 0, -1).
    $ The Pauli matrices are unitaries, and we can think of them as quantum logical gates.
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
#proofhints[
    Straightforward.
]
#proof[
    $tr(A ket(phi) bra(phi)) = sum_i braket(i, A, phi) braket(phi, i)$ for an orthonormal basis ${ket(i)}$. Any basis where $ket(phi) = ket(j)$ for some $j$ instantly yields the result. Alternatively, we have $
        tr(A ket(phi) bra(phi)) = sum_i braket(i, A, phi) braket(phi, i) = sum_i braket(phi, i) braket(i, A, phi) = braket(phi, I, A, phi) = braket(phi, A, phi).
    $
]
Suppose we don't fully know the state of the system, but know that it is $ket(phi_i)$ with probability $p_i$. We want to be able to consider the $sum_i p_i ket(phi_i)$ as a state, but this isn't normalised (except when some $p_i = 1$). To solve this issue, we assume each $ket(phi_i)$ to the rank-one projector $ket(phi_i) bra(phi_i)$, and we describe the unknown state by $rho = sum_i p_i ket(phi_i) bra(phi_i)$. This gives rise to the following definition:
#definition[
    A *density matrix/operator* is a linear operator $rho in B(HH)$ which is:
    - Hermitian,
    - Positive semi-definite, and
    - Satisfies $tr rho = 1$.
]

== Postulates of quantum mechanics (Heisenberg picture)

#postulate[
    Given an isolated physical system, there exists a complex (separable) Hilbert space $HH$ associated with it, called *state space*. The physical system is described by a *state vector*, which is a normalised vector in $HH$.
]
#postulate[
    Given an isolated physical system, its evolution is described by a unitary. If the state of the system at time $t_1$ is $ket(phi_1)$ and at time $t_2$ is $ket(phi_2)$, then there exists a unitary $U_(t_1, t_2)$ such that $ket(phi_2) = U_(t_1, t_2) ket(phi_1)$.
]
This can be generalised with the Schrodinger equation: the time evolution of a closed quantum system is given by $i planck.reduce dif / (dif t) ket(phi(t)) = H ket(phi(t))$. The Hermitian operator $H$ is called the *Hamiltonian* and is generally time-dependent.
#definition[
    Let the spectral decomposition of $H$ be $
        H = sum_i E_i ket(E_i) bra(E_i),
    $ where the $E_i$ are the *energy eigenvalues* and the $ket(E_i)$ are the *energy eigenstates* (or *stationary states*).

    The minimum energy is called the *ground state energy* and its associated eigenstate is called the *ground state*. The *(spectral) gap* of $H$ is the (absolute) difference between the ground state energy and the next largest energy eigenvalue. When the gap is strictly positive, we say the system is *gapped*. The states $ket(E_i)$ are called *stationary*, since they evolve as $ket(E_i) -> exp(-i E_i t \/ planck.reduce) ket(E_i)$.
]<def:hamiltonian-ground-state>

We have $ket(phi(t_2)) = U(t_1, t_2) ket(phi(t_1))$ where $U(t_1, t_2) = exp(-i H(t_2 - t_1) \/ planck.reduce)$ which is a unitary. In fact, any unitary $U$ can be written in the form $U = exp(i K)$ for some Hermitian $K$.

#postulate[
    Given a physical system with associated Hilbert space $HH$, quantum measurements in the system are described by a collection of measurements ${M_n}_n subset.eq B(HH)$ such that $sum_n M_n^* M_n = II$, as in @def:measurement. The index $n$ refers to the measurement outcomes that may occur in the experiment, and given a state $ket(phi)$ before measurement, the probability that $n$ occurs is $
        p(n) = braket(phi, M_n^* M_n, phi).
    $ The state of the system after measurement is $1/sqrt(p(n)) M_n ket(phi)$
]<pst:heisenberg-measurement>
#postulate[
    Given a composite physical system, its state space $HH$ is also composite and corresponds to the tensor product of the individual state spaces $HH_i$ of each component: $HH = HH_1 tp cdots tp HH_N$. If the state in each system $i$ is $ket(phi_i)$, then the state in the composite system is $ket(phi_1) tp cdots tp ket(phi_N)$.
]<pst:heisenberg-composite-system>
#definition[
    Given $ket(phi) in H_1 tp cdots tp H_N$, $ket(phi)$ is *entangled* if it cannot be written as a tensor product of the form $ket(phi_1) tp cdots tp ket(phi_n)$. Otherwise, it is *separable* or a *product state*.
]
#example[
    The *EPR pair* (*Bell state*) $ket(phi^+) = 1/sqrt(2) (ket(00) + ket(11))$ is entangled.
]

== Postulates of quantum mechanics (Schrodinger picture)

#postulate[
    Given an isolated physical system, the state of the system is completely described by its density operator, which is Hermitian, positive semi-definite and has trace one.

    If we know the system is in state $rho_i$ with probability $p_i$, then the state of the system is $sum_i p_i rho_i$.
]
*Pure states* are of the form $rho = ket(phi) bra(phi)$, *mixed states* are of the form $rho = sum_i p_i ket(phi_i) bra(phi_i)$.
#postulate[
    Given an isolated physical system, its evolution is described by a unitary. If the state of the system is $rho_1$ at time $t_1$ and is $rho_2$ at time $t_2$, then there is a unitary $U$ depending only on $t_1, t_2$ such that $rho_2 = U rho_1 U^*$.
]
#postulate[
    The same as @pst:heisenberg-measurement, except we specify that after measurement ${M_n}_n$, the probability of observing $n$ is $p(n) = tr (M_n^* M_n rho)$ and the state after measurement is $1/p(n) M_n rho M_n^*$.
]
#postulate[
    The same as @pst:heisenberg-composite-system, except that the state of the composite system is $rho = rho_1 tp cdots tp rho_n$, where $rho_i$ is the state of $i$th individual system.
]
#remark[
    The Heisenberg and Schrodinger postulates are mathematically equivalent.
]

// == Quantum projective measurements and the Born rule

// Let $A in B(HH)$ be Hermitian, with spectral decomposition $A = sum_n a_n P_n$. If the eigenvalue $a_n$ is non-degenerate, then $P_n$ is a rank-one projector: $P_n = ket(phi_n) bra(phi_n)$. The outcome of the measurement is $a_n$. If the system is in state $ket(psi)$ before the measurement, then the probability that the outcome is $a_n$ is given by $p(a_n) = braket(psi, P_n, psi)$, and as a result of the measurement, the state of the system becomes $1/sqrt(p(a_n)) P_n ket(psi)$. This is the *Born rule*.

== States, entanglement and measurements

#theorem("Schmidt Decomposition")[
    Let $ket(psi)$ be a pure state in a bipartite system $HH_(A B) = HH_A tp HH_B$, where $HH_A$ has dimension $N_A$ and $HH_B$ has dimension $N_B >= N_A$. Then there exist orthonormal states ${ket(e_i): i in [N_A]} subset.eq HH_A$ and ${ket(f_i): i in [N_A]} subset.eq HH_B$ such that $
        ket(psi) = sum_(i = 1)^(N_A) lambda_i ket(e_i) tp ket(f_i),
    $ where $lambda_i >= 0$ and $sum_i lambda_i^2 = 1$.
    
    The $lambda_i$ are unique up to re-ordering. The $lambda_i$ are called the *Schmidt coefficients* and the number of $lambda_i > 0$ is the *Schmidt rank* of the state.
]<thm:schmidt-decomposition>
#proof[
    Let $ket(psi) = sum_(k = 1)^(N_A) sum_(ell = 1)^(N_B) beta_(k ell) ket(phi_k) tp ket(phi_ell)$ for orthonormal bases ${ket(phi_k): k in [N_A]} subset.eq HH_A$, ${ket(chi_ell): ell in [N_B]} subset.eq HH_B$. Let $(beta_(k ell))$ have singular value decomposition $
        U mat(Sigma, 0) V,
    $ where $U$ is an $N_B times N_B$ unitary, $Sigma$ is an $N_A times N_A$ diagonal matrix with non-negative entries, and $V$ is an $N_A times N_A$ unitary. So $
        beta_(k ell) = sum_(i = 1)^(N_A) sum_(j = 1)^(N_B) U_(k i) Sigma_(i j) V_(j ell) = sum_(i = 1)^(N_A) Sigma_(i i) U_(k i) V_(i ell).
    $ Hence, $
        ket(psi) = sum_(k, ell) sum_i Sigma_(i i) U_(k i) ket(phi_k) tp V_(i ell) ket(chi_ell) = sum_i Sigma_(i i) underbrace((sum_k U_(k i) ket(phi_k)), ket(e_i)) tp underbrace((sum_ell V_(j ell) ket(chi_ell)), ket(j_B)).
    $
]
#proposition[
    $ket(psi)$ is entangled iff its Schmidt rank is $> 1$. Otherwise, it is separable (i.e. a product state).
]
#definition[
    Let $ket(psi)$ be a pure state in a bipartite system $HH_(A B) = HH_A tp HH_B$, where $HH_A$ has dimension $N_A$ and $HH_B$ has dimension $N_B >= N_A$. $ket(psi)$ is *maximally entangled* if all its Schmidt coefficients are equal (to $1 \/ sqrt(N_A)$).
]
#notation[
    Write $S(HH) = {rho in B(HH): rho = rho^dagger, rho >= 0, tr p = 1}$ for the set of density matrices on $HH$.
]
#definition[
    The *partial trace* over $B$, $tr_B$, on the bipartite system $HH_(A B) = HH_A tp HH_B$ is the operator defined linearly by $
        tr_B: S(HH_(A B)) & -> S(HH_A), \
        ket(a_1) bra(a_2) tp ket(b_1) bra(b_2) & |-> tr (ket(b_1) bra(b_2)) dot ket(a_1) bra(a_2).
    $ Note that if $rho_(A B) = rho_A tp rho_B$, then $tr_B rho_(A B) = tr(rho_B) dot rho_A = rho_A$.
]<def:partial-trace>
#definition[
    Let $rho_(A B)$ be a density matrix in $S(HH_(A B))$. $rho_A = tr_B (rho_(A B))$ is called the *reduced density matrix* or *marginal* of $rho_(A B)$ in $A$
]<def:reduced-density-matrix>
#proposition[
    Let $M_A in B(HH_A)$. We have $
        tr (M_A rho_A) = tr((M_A tp II_B) rho_(A B)).
    $ for all $rho_(A B) in S(HH_(A B))$, $rho_A = tr_B (rho_(A B))$. In fact, this can be taken to be an equivalent definition of partial trace.
]
#remark[
    Let $rho_(A B) = ket(psi) bra(psi) in S(HH_(A B))$ be a pure state and let $r_psi$ be its Schmidt rank. Then $
        rho_A = tr_B (ket(psi) bra(psi)) = sum_(k = 1)^(r_psi) p_k ket(u_k) bra(u_k).
    $ So $rho_A$ is pure iff $r_psi = 1$, i.e. iff $ket(psi)$ is separable.
]
#proposition[
    Let $rho_(A B) in B(HH_(A B))$ and $rho_A = tr_B (rho_(A B))$. Then:
    + $tr rho_A = tr rho_(A B)$.
    + If $rho_(A B) >= 0$, then $rho_A >= 0$.
    + If $rho_(A B)$ is a density matrix then $rho_A$ is a density matrix.
    + We have $
        braket(phi_i, rho_A, phi_i) = sum_k braket(phi_i tp psi_k, rho_(A B), phi_i tp psi_k),
    $ for an orthonormal bases ${ket(phi_i)}$ and ${ket(psi_k)}$.
    + If $rho_(A B) = sigma_A tp sigma_B$ and $tr(sigma_B) = 1$, then $sigma_A = rho_A$.
]
#proof[
    + This follows from linearity of trace and the fact that $tr(rho tp sigma) = tr(rho) dot tr(sigma)$.
    + By 1, $braket(psi, rho_A, psi) = tr(rho_A ket(psi) bra(psi)) = tr(rho_(A B) (ket(psi) bra(psi) tp II)) >= 0$.
    + From 1 and 2, by definition.
    // + $braket(psi_i, rho_A, rho_i) = tr(rho_A ket(phi_i) bra(phi_i)) = tr(rho_(A B) (ket(phi_i) bra(phi_i) tp II)) =$
]
#definition[
    Let $rho_A in SS(H_A)$ be a (pure or mixed) state. We may introduce an auxiliary space $HH_R$ of dimension $"rank"(rho_A)$ and construct a pure state $ket(psi_(A R)) in HH_A tp HH_R$ such that $rho_A = tr_R (ket(psi_(A R)) bra(psi_(A R)))$.
]
#remark[
    Let ${M_n^A}_n$ be a POVM in $HH_A$. Then ${M_n^A tp II_B}_n$ is a POVM in $HH_(A B)$.
]
#theorem("Naimark")[
    For every POVM ${E_n}_(n = 1)^m subset.eq B(HH)$, there is a state $ket(psi) in CC^m$ and a projective measurement ${P_n}_(n = 1)^m subset.eq B(HH tp CC^m)$ such that $
        tr (rho E_n) = tr((rho tp ket(psi) bra(psi)) P_n) quad forall n in [m], forall rho in S(HH).
    $
]