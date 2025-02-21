#import "@preview/quill:0.2.0": *
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.1" as cetz: canvas, draw
#import "../../diagram-style.typ": *

#let line-style(color) = (fill: color, stroke: color, mark: (end: ">"))

#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: (:))
#set document(
    title: "Quantum Information Theory Notes",
    author: "Isaac Holt",
    keywords: ("quantum information")
)

#let Cor = math.op("Cor")
#let phi = sym.phi.alt
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
    Let $rho_A in SS(H_A)$ be a (pure or mixed) state. We may introduce an auxiliary space $HH_R$ of dimension $"rank"(rho_A)$ and construct a pure state $ket(psi_(A R)) in HH_A tp HH_R$ such that $rho_A = tr_R (ket(psi_(A R)) bra(psi_(A R)))$. This is called *purification*.
]
#remark[
    Let ${M_n^A}_n$ be a POVM in $HH_A$. Then ${M_n^A tp II_B}_n$ is a POVM in $HH_(A B)$.
]
#theorem("Naimark")[
    For every POVM ${E_n}_(n = 1)^m subset.eq B(HH)$, there is a state $ket(psi) in CC^m$ and a projective measurement ${P_n}_(n = 1)^m subset.eq B(HH tp CC^m)$ such that $
        tr (rho E_n) = tr((rho tp ket(psi) bra(psi)) P_n) quad forall n in [m], forall rho in S(HH).
    $
]


= Quantum channels and open systems

== Quantum channels

#definition[
    A *quantum channel* is a linear map $T: S(HH_"in") -> S(HH_"out")$ which satisfies:
    - *Preserves trace*: $tr(T(rho)) = tr(rho)$ for all $rho in S(HH_"in")$.
    - *Positive*: if $rho >= 0$, then $T(rho) >= 0$.
    - *Completely positive*: for all $rho, sigma$ if $rho tp sigma >= 0$, then $(T tp II_n)(rho tp sigma) = T(rho) tp sigma >= 0$ (note that this implies the second condition, but the converse is false).
    So quantum channels are completely positive trace-preserving (CPTP) maps. We may depict a quantum channel $T$ as follows:
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                line((0, 0), (2, 0), mark: (end: ">"), name: "in")
                content("in.start", box(inset: (right: 1em))[$rho$], anchor: "east")
                line((6, 0), (8, 0), mark: (end: ">"), name: "out")
                content("out.end", box(inset: (left: 1em))[$rho' = T(rho)$], anchor: "west")
                rect((2, -1), (6, 1), name: "channel", ..line-style(diagram-colors.red), fill: diagram-colors.light-red)
                content("channel.center", $T$)
            })
        )
    ]
]<def:quantum-channel>
#example[
    Examples of quantum channels:
    - Unitary evolution: $rho |-> U rho U^*$.
    - Adding an ancilla: $rho |-> rho tp rho_E$ (the $E$ denotes "environment").
    - Partial trace: $rho |-> tr_B (rho)$ or $rho |-> tr_A (rho)$.
    We will see that in fact, any quantum channel is a combination of these three.
]
#definition[
    We define the *maximally entangled state* in $(CC^d)^(tp 2)$ as $
        ket(phi) = 1/sqrt(d) sum_(k = 1)^d ket(k k).
    $
]<def:maximally-entangled-state>
#definition[
    Recall the transposition map is defined as $
        Theta: A & -> A^T, quad braket(i, A^T, j) = braket(j, A, i).
    $ We define the *partial transpose* by its action on the maximally entangled state $ket(phi) = 1/d sum_(i = 1)^d ket(i i)$: $
        (ket(phi) bra(phi))^(T_A) = (ket(phi) bra(phi))^(T_1) = (Theta tp id) (ket(phi) bra(phi)) = 1/d F,
    $ where $F = sum_(i, j = 1)^n ket(i j) bra(j i)$ is the flip operator. Note the partial transpose is positive but not CP. Alternatively, we can define it by its action on an orthonormal basis: $
        braket(i j, X^(T_A), k ell) = braket(k j, X, i ell).
    $
]<def:partial-transpose>
#remark[
    Note that the partial transpose is useful for detecting entanglement but is not physically implementable (as not CP).
]
#definition[
    Let $T: B(CC^(d times d)) -> B(CC^(d' times d'))$ be a linear map. The *Choi-Jamiolkowski matrix* $C in B(CC^(d') tp CC^d)$ of $T$ is defined as $
        C := (T tp id_d) ket(phi) bra(phi).
    $ Note that in fact, $C in S(CC^d' tp CC^d)$ is a density matrix if $T$ is a quantum channel.
]<def:choi-jamiolkowski-matrix>
#remark[
    Note that the Choi-Jamiolkowski matrix completely determines $T$: since $ket(phi) bra(phi) = 1/d sum_(n, m = 1)^d ket(n n) bra(m m)$, we have $
        braket(i j, C, k ell) & = 1/d sum_(m,n = 1)^d braket(i j, (T (ket(n) bra(m)) tp ket(n) bra(m)), k ell) \
        & = 1/d sum_(m, n = 1)^d braket(j, n) dot braket(m, ell) dot braket(i, T(ket(n) bra(m)), k) = 1/d braket(i, T(ket(j) bra(ell)), k),
    $ and so we can determine any entry of any $T(rho)$ by linearity. This state-channel duality is called the *Choi-Jamiolkowski isomorphism*, and can be expressed as $
        tr(A T(B)) = d tr (C A tp B^T) quad forall A in B(CC^(d')), B in B(CC^d).
    $ Indeed, let $FF ket(i j) = ket(j i)$ be the flip operator: note that $FF^(T_2) = d ket(phi) bra(phi)$, then if $d = d'$, $
        d tr(C (A tp B^T)) & = d tr((T tp id_d) (ket(phi) bra(phi)) (A tp B^T)) \
        & = tr(FF^(T_2) (T^* (A) tp B^T)) = tr(T^* (A) tp B) = tr(A T(B)). // TODO: I don't understand the first and third equalities on this line
    $
]
#definition[
    The *Hilbert-Schmidt inner product* of $A, B in B(CC^d)$ is $
        braket(A, B)_"HS" := tr(A^* B).
    $
]<def:hilbert-schmidt-inner-product>
#theorem("Characterisation of Quantum Channels")[
    Let $T: B(CC^d) -> B(CC^d')$ be a linear map. TFAE:
    + $T$ is a quantum channel.
    + Let $C = (T tp II_d) (ket(phi) bra(phi))$ be the Choi-Jamiolkowski matrix of $T$, then $C >= 0$ and $tr_1 (C) = 1/d II_d$.
    + *Kraus decomposition*: There exists ${A_k}_(k = 1)^(d d') subset.eq CC^(d' times d)$ with $sum_(k = 1)^(d d') A_k^* A_k = II_d$ such that $
        T(rho) = sum_(k = 1)^(d d') A_k rho A_k^* quad forall rho in S(CC^d).
    $ We call the number of non-trivial $A_k$ in the Kraus decomposition the *Kraus rank* of $T$.
    + *Stinespring dilation*: there exists a unitary $U$ on $CC^d tp CC^(d d')$ and a state $ket(psi) in CC^(d d')$ such that $T(rho) = tr_2 (U(rho tp ket(psi) bra(psi)) U^*)$ for all $rho in S(CC^d)$.
]<thm:characterisation-of-quantum-channels>
#proofhints[
    - $1 => 2$: straightforward.
    - $4 => 1$: use that compositions of quantum channels are quantum channels.
]
#proof[
    - $1 => 2$: $C >= 0$ follows from the completely positive property of $T$ and linearity. Also, $
        tr_1 (C) & = 1/d sum_(n, m = 1)^d tr(T ket(n) bra(m)) dot ket(n) bra(m) \
        & = 1/d sum_(n, m = 1)^d tr(ket(n) bra(m)) dot ket(n) bra(m) quad "since" T "preserves trace" \
        & = 1/d sum_(n, m) delta_(m n) ket(n) bra(m) = 1/d sum_(n = 1)^d ket(n) bra(n) = 1/d II_d.
    $
    // TODO: don't understand 2 => 3
    - $2 => 3$: we use that (verify this) $(A tp II) ket(phi) = (II tp A^T) ket(phi)$ for all $A in B(CC^d)$, where $ket(phi)$ is the maximally entangled state, and that $forall ket(psi) in CC^(d^2)$, there exists $A$ such that $ket(psi) = (A tp II) ket(phi)$. Since $C >= 0$, we can write $C = sum_(k = 1)^(d d') ket(psi_k) bra(psi_k)$ ($ket(psi_k)$ are not necessarily normalised). So $
        C & = sum_(k = 1)^(d d') (A_k tp II) ket(phi) bra(phi) (A_k^* tp II) \
        & = (T tp II) ket(phi) bra(phi).
    $ Also, $
        1/d II & = tr_1 (C) = sum_(n = 1)^d braket(n_1, C_(1 2), n_1) \
        & = 1/d sum_(n = 1)^d sum_(m = 1)^(d d') (II tp A_m^T) (ket(phi) bra(phi)) (II tp overline(A)_k) ket(n) \
        & = sum_(n = 1)^d braket(n, sum_(k = 1)^(d d') (II tp A_m^T) 1/d (sum_(k, ell = 1)^d ket(k k) bra(ell ell)) (II tp overline(A)_k), n) \
        & = 1/d sum_(n = 1)^d sum_(m = 1)^(d d') sum_(k, ell = 1)^d braket(n, k) braket(ell, n) A_m^T ket(k) bra(ell) overline(A)_k \
        & = 1/d sum_(n = 1)^d sum_(m = 1)^(d d') A_m^T ket(n) bra(n) overline(A)_m \
        & = 1/d sum_(m = 1)^(d d') A_m^T overline(A)_m
    $ So we set $tilde(A)_m := overline(A)_m$.
    - $3 => 4$: let $V = sum_(k = 1)^(d d') A_k tp ket(k)$, where ${ket(k)}_(k = 1)^(d d')$ is an orthonormal basis of $CC^(d d')$. $V$ is an isometry, i.e. $V^* V = sum_(k = 1)^(d d') A_k^* A_k = II_d$. Then for all $rho in S(CC^(d d'))$, since $(A_k tp ket(k)) rho = (A_k rho) tp ket(k)$, $
        tr_2 (V rho V^*) & = tr_2 (sum_(k, ell = 1)^(d d') (A_k rho A_ell^*) tp ket(k) bra(ell)) \
        & = sum_(k, ell = 1)^(d d') (A_k rho A_ell^*) tr(ket(k) bra(ell)) \
        & = sum_(k = 1)^(d d') A_k rho A_k^* = T(rho).
    $ Now choose $V = U(II tp ket(psi))$ for some pure state $ket(psi)$ and unitary $U$. // TODO: don't get how we can just make this final step?
    - $4 => 1$: the maps $
        rho |-> rho tp ket(psi) bra(psi) |-> U(rho tp ket(psi) bra(psi)) U^* |-> tr_2 (U(rho tp ket(psi) bra(psi)) U^*)
    $ are all quantum channels, and so their composition is also a quantum channel.
]
#remark[
    - The number $k$ in the Kraus decomposition is called the *Kraus rank* of $T$, which is the same as the Choi rank (rank of the Choi-Jamiolkowski matrix). Note: this is not the same as the rank of $T$ as a map.
    - We can always express $T$ with $r = "rank"(C)$ Kraus operators which are orthogonal (w.r.t Hilbert-Schmidt inner product), since $T$ is a completely positive linear map.
    - Two sets of Kraus operator ${K_j}$ and ${J_ell}$ represent the same map $T$ iff there exists a unitary $U$ such that $K_j = sum_ell U_(j ell) J_ell$. // TODO: does the number of K_j and J_ell need to be the same?
]

== Examples of quantum channels

#definition[
    In two dimensions, there are three kinds of errors:
    + Bit flip errors, modelled by the Pauli $X$: $ket(0) |-> ket(1)$, $ket(1) |-> ket(0)$.
    + Phase flip error: modelled by Pauli $Z$: $ket(0) |-> ket(0)$, $ket(1) |-> -ket(1)$.
    + Combination of bit and phase flip errors: modelled by Pauli $Y$.

    A map describing the depolarising channel is $ // TODO: what happens to the environment qubits when we pass to Kraus representation? (same question for next example)
        U_(A -> A E): ket(psi)_A |-> sqrt(1 - p) ket(psi)_A tp ket(0)_E + sqrt(p/3) (X ket(psi)_A tp ket(1)_E + Y ket(psi)_A tp ket(2)_E + Z ket(psi)_A tp ket(3)_E)
    $ (the environment $H_E$ has dimension $4$). We can express this in the Kraus decomposition: let $M_a := bra(a)_E U_(A -> A E)$, $a in {0, 1, 2, 3}$, and $M_0 = sqrt(1 - p) II$, $M_1 = sqrt(p \/ 3) X$, $M_2 = sqrt(p \/ 3) Y$, $M_3 = sqrt(p \/ 3) Z$. It is straightforward to see that $
        sum_(a = 0)^3 M_a^dagger M_a = (1 - p + p/3 + p/3 + p/3) II = II.
    $ The channel is $T(rho) = (1 - p) rho + p/3 (X rho X + Y rho Y + Z rho Z)$. For arbitrary dimensions $D$, the depolarising channel is $rho |-> (1 - p) rho + p sigma$, where $sigma in S(CC^D)$, usually $sigma = II \/ d$.
]<def:depolarising-channel>

#definition[
    The *phase damping channel* is the map $
        rho = mat(rho_00, rho_01; rho_10, rho_11) |-> mat(rho_00, (1 - p) rho_01; (1 - p) rho_10, rho_11).
    $ Let the environment have orthonormal basis ${ket(0), ket(1), ket(2)}$, then the state representation is $
        ket(0)_A & |-> sqrt(1 - p) ket(0)_A tp ket(0)_E + sqrt(p) ket(0)_A tp ket(1)_E \
        ket(1)_A & |-> sqrt(1 - p) ket(1)_A tp ket(0)_E + sqrt(p) ket(1)_A tp ket(2)_E
    $ The Kraus operators are $M_0 = sqrt(1 - p) dot II$, $M_1 = sqrt(p) ket(0) bra(0)$, $M_2 = sqrt(p) ket(1) bra(1)$. We have $M_0^2 + M_1^2 + M_2^2 = II$. The map is $T(rho) = (1 - p \/ 2) rho + 1/2 p Z rho Z$.
]
#definition[
    A density matrix $rho in S(HH_A tp HH_B)$ is *separable* if it can be expressed as a convex combination $
        rho = sum_i p_i rho_i^A tp sigma_i^B,
    $ where $p_i >= 0$, $sum_i p_i = 1$, and $rho_i^A in S(HH_A)$ and $sigma_i^B in S(HH_B)$.
]<def:separable-density-matrix>
#definition[
    A quantum channel $T$ is *entanglement breaking* if its Choi-Jamiolkowski matrix is separable. This is equivalent to the existence of a POVM ${M_k}$ and a set of density matrices ${rho_k}$ such that $T(rho) = sum_k tr(M_k rho) rho_k$.
]<def:entanglement-breaking>

== Properties of channels

#remark[
    Let $ket(psi) in HH_A tp HH_B$, $d = min{dim H_A, dim H_B}$, not necessarily normalised. The Schmidt decomposition is $
        ket(psi) = sum_(j = 1)^d lambda_j ket(e_j) tp ket(f_j),
    $ $lambda_j >= 0$, $sum_j lambda_j^2 = braket(psi, psi)$, ${e_j}$, ${f_j}$ orthonormal bases.

    The reduced density operators of $ket(psi)$ are diagonal in the bases ${ket(e_j)}$, ${ket(f_j)}$, with eigenvalues $lambda_j^2$. Conversely, if $rho_A in S(HH_A)$ has spectral decomposition $rho_A = sum_j lambda_j ket(e_j) bra(e_j)$, then $ket(psi)$ provides a purification for $rho_A = tr_B (ket(psi) bra(psi))$; the minimal dilation space we can choose, $HH_min$ has dimension $"rank"(rho_A)$. If $ket(psi) in HH_A tp HH_min$, then all other purifications of $rho_A$ are of the form $ket(psi') = (II_A tp V) ket(psi)$, with $V in B(HH_min, HH_B)$ an isometry. Hence, all purifications are related by $II_A tp U$ with $U$ an isometry.
]
#proposition("Equivalence of Ensembles")[
    Let ${ket(psi_j): j in [M]}$ and ${ket(phi_ell): ell in [N]}$ be (not necessarily normalised) ensembles. Then $
        sum_(j = 1)^M ket(psi_j) bra(psi_j) = sum_(ell = 1)^N ket(phi_ell) bra(phi_ell)
    $ iff there is an isometry $U in CC^(M times N)$ such that $ket(psi_j) = sum_(ell = 1)^N U_(j ell) ket(phi_ell)$.
]<prop:equivalence-of-ensembles>
#proofhints[
    - $<==$: straightforward.
    - $==>$: explain why we can assume that $rho = sum_j ket(psi_j) bra(psi_j)$ and $sigma = sum_ell ket(phi_ell) bra(phi_ell)$ are density matrices. Consider purifications of $rho$ and $sigma$ which use the same orthonormal basis in the dilation space.
]
#proof[
    - $<==$: this is straightforward to show.
    - $==>$: WLOG (by rescaling $rho$), we can assume $rho := sum_j ket(psi_j) bra(psi_j)$ is a density matrix. We have $rho = tr_B (ket(psi) bra(psi))$ (through purification), where $ket(psi) = sum_j ket(psi_j) tp ket(j)$. Similarly, let $ket(phi) = sum_ell ket(phi_ell) tp ket(ell)$ (so we use the same orthonormal basis ${ket(ell)} = {ket(j)}$). So $ket(psi)$ and $ket(phi)$ differ by a unitary (or an isometry if the dimensions are not equal), hence $ket(psi) = (1 tp U) ket(phi)$. Taking the scalar product with $bra(j)$, we obtain $ket(psi_j) = sum_ell U_(j ell) ket(phi_ell)$.
]
#notation[
    Let $T_1, T_2$ be linear maps. Write $T_2 >= T_1$ to mean $T_2 - T_1$ is completely positive. By the Choi-Jamiolkowski isomorphism, this is equivalent to $C_2 >= C_1$ where $C_i$ is the Choi matrix of $T_i$ (i.e. $C_2 - C_1$ is positive semi-definite). // TODO: I don't get why this is equivalent?
]
#theorem[
    Let $T_1, T_2: CC^(d' times d') -> CC^(d times d)$ be completely positive maps, with $T_2 >= T_1$. Let $V_i: CC^d -> CC^(d') tp CC^(r_i)$ be Stinespring representations for $T_i$ (i.e. $T_i (A) = V_i^* (A tp II_(r_i)) V_i$), then there is a contraction (i.e. $W^* W <= II$) $W: CC^(r_2) -> CC^(r_1)$ such that $V_1 = (II_(d') tp W) V_2$.

    Moreover, if $V_2$ belongs to a minimal dilation, then $W$ is unique.
]
#proofhints[

]
#proof[
    We use the equivalence $T_2 >= T_1 <=> C_2 >= C_1$. Define the map $
        R_i = (II_(r_i) tp bra(phi)) (V_i tp II_(d')) in B(CC^d tp CC^(d'), CC^(r_i))
    $ Let $ket(psi) in CC^d tp CC^(d')$. We want to show $norm(R_2 ket(psi))^2 >= norm(R_1 ket(psi))^2$. Indeed, $
        norm(R_2 ket(psi))^2 & = braket(psi, R_2^* R_2, psi) \
        & = braket(psi, (V_2^* tp II_(d'))(II_(r_2) tp ket(phi))(II_(r_2) tp bra(phi))(V_2 tp II_(d')), psi) \
        & = braket(psi, (T_2 tp id)(ket(phi) bra(phi))) \ // TODO: I don't get this line
        & = braket(psi, C_2, psi) >= braket(psi, C_1, psi).
    $ And $braket(psi, C_1, psi) = norm(R_1 ket(psi))^2$ by the same argument. So there exists a contraction $W: CC^(r_2) -> CC^(r_1)$, such that $R_1 = W R_2$. // TODO: I don't get why the contraction exists
    So $V_1 = (II_(d') tp W) V_2$. If $r_2 = "rank"(C_2)$, then $R_2$ is surjective, and so $W$ is uniquely determined. // TODO: I don't get either of these last two points
]
#theorem("Radon-Nikodym")[
    Let ${T_i}$ be a set of CP maps such that $sum_i T_i = T in B(CC^(d' times d'), CC^(d times d))$ with Stinespring representation $T(A) = V^* (A tp II_r) V$. Then there exists a set of non-negative operators $P_i in CC^(r times r)$ such that $sum_i P_i = II_r$ and $T_i (A) = V^* (A tp P_i) V$.
]
#remark[
    Since $T = sum_i T_i$, this gives $T(A) = sum_i V^* (A tp P_i) V$, where ${P_i}$ is a POVM. This gives an identification between quantum channels of this form and POVMs.
]
#definition[
    An *instrument* is a set of CP maps ${T_i}$ whose sum is trace-preserving.
]<def:instrument>
TODO: insert diagram.
#remark[
    Instruments encompass the notions of quantum channels and POVMs:
    - We can assing a quantum channel $T: rho |-> sum_i T_i (rho)$. (Measurement outcome ignored.)
    - By contrast, POVMs ignore the quantum system: $p_i = tr(T_i (rho)) = tr(T_i (rho) II) = tr(rho T_i^* (II)) =: tr(rho M_i)$: ${M_i}$ is a POVM.
]
#remark[
    Instruments can viewed as a special case of quantum channels by assigning to them the quantum channel $
        rho |-> sum_i T_i (rho) tp ket(i) bra(i), // TODO: why do we need the tensor product here?
    $ where ${ket(i)}$ is an orthonormal basis.
]
#proposition("Quantum Steering")[
    Let $rho in B(HH_A)$ be a density operator with purification $ket(psi) in HH_A tp HH_B$. Let $rho = sum_i lambda_i rho_i$ be a convex combination. Then there is an instrument ${T_i}$ with each $T_i: B(HH_B) -> B(HH_B)$, such that $lambda_i rho_i = tr_B ((II tp T_i) (ket(psi) bra(psi)))$.
]

== Description of open quantum many-body systems

Assume evolution is $
    rho_(S E)(t) = rho_S (t) tp rho_E |->^(dif t) rho_(S E)(t + dif t) = rho_S (t + dif t) tp rho_E (t + dif t) = rho_S (t + dif t) tp rho_E
$
#definition[
    A *quantum Markov semigroup* is a $1$-parameter continuous semigroup ${T_t: t >= 0}$ of quantum channels (so each $T_t: S(HH) -> S(HH)$).

    Note that $T_0 = II$ and $T_s compose T_t = T_(t + s)$. We have $
        dif / (dif t) T_t = cal(L) compose T_t = T_t compose cal(L),
    $ where $cal(L)$ is the infinitesimal generator of the semigroup, called the *Liouvillian* or *Lindbladian*. This equation is called the *master equation* or *Liouville equation*. This gives $
        T_t = e^(t cal(L)).
    $
]

// weak-coupling approximationn section not examinable

== Separability criteria

#notation[
    Let $A(HH)$ denote the set of bounded linear Hermitian operators on $HH$.
]
#definition[
    The *covariance* (or *operator correlation*) of $rho$ between subsystems $A$ and $B$ is $
        Cor_rho (A: B) = sup_(norm(M_A), norm(M_B) <= 1) abs(tr(rho M_A T_B) - tr(rho M_A) tr(rho M_B)),
    $ where $M_A in A(H_A)$, $M_B in A(H_B)$, and $norm(dot)$ is the standard operator norm.
]<def:operator-correlation>
#example[
    If $rho$ is separable, then $Cor_rho (A: B)$ measures classical correlation. If $rho = rho_A tp rho_B$, then $Cor_rho (A: B) = 0$.
]
#definition[
    Let $ket(psi) = sum_(i = 1)^d sqrt(p_i) ket(e_i) tp ket(f_i)$ be the Schmidt decomposition of $ket(psi) in HH_A tp HH_B$. Let $rho = ket(psi) bra(psi)$. The *entanglement entropy* of $rho$ is the Shannon entropy of the probability distribution $(p_1, ..., p_d)$: $
        S_"ENT" (rho) := -sum_(i = 1)^d p_i log(p_i).
    $
]<def:entanglement-entropy>
#proposition[
    - $S_"ENT"(rho) = 0$ iff the Schmidt rank of $ket(psi)$ is $1$.
    - The maximum value of $S_"ENT" (rho)$ is $log(d)$, and is achieved iff $ket(psi)$ is maximally entangled, i.e. $lambda_i = 1 \/ d$ for all $i in [d]$.
]<prop:properties-of-entanglement-entropy>
#proposition("PPT Criterion")[
    Let $rho in S(HH_A tp HH_B)$. If $rho^(T_A)$ has a negative eigenvalue, then $rho$ is entangled.
]<prop:ppt-criterion>
#proofhints[
    Prove the contrapositive.
]
#proof[
    Assume $rho$ is separable, so $rho = sum_j p_j rho_j^A tp rho_j^B$. Then $
        rho^(T_A) = (Theta tp id)(rho) = sum_j p_j (rho_j^A)^T tp rho_j^B,
    $ and so $rho^(T_A) >= 0$, as it is a sum of positive matrices.
]
#definition[
    Write $S_"SEP" = {"separable density matrices"}$, which is convex and compact. By the Hahn-Banach theorem, for all $rho in.not S_"SEP"$, there exists a hyperplane determined by a Hermitian operator $omega$ such that $tr(rho omega) < 0$ and $tr(sigma omega) >= 0$ for all $sigma in S_"SEP"$. $omega$ is called an *entanglement witness* for $rho$.

    By the Choi-Jamiolkowski isomorphism, // TODO: I don't get how this applies, since omega isn't necessarily a state?
    $omega$ corresponds to a map $Lambda$ via the following: $
        omega = (Lambda tp id_B)(ket(phi) bra(phi)).
    $
]<def:entanglement-witness>
#remark[
    The entanglement witness corresponding to the transposition map is the flip operator $F$.
]
#proposition[
    Let $HH_(A B) = HH_A tp HH_B$ and let $rho in S(HH_(A B))$. Then $rho$ is separable iff $(Lambda tp id_B)(rho) >= 0$ for every positive map $Lambda: B(HH_A) -> B(HH_A)$.
]<prop:positive-map-criterion-for-separability>
#proofhints[
    - $==>$: straightforward.
    - $<==$: TODO.
]
#proof[
    $==>$: let $rho$ be separable, so we can write $rho = sum_j p_j rho_j tp sigma_j$. Then for every positive $Lambda: B(HH_A) -> B(HH_A)$, $
        (Lambda tp id_B)(rho) = sum_j lambda_j Lambda(rho_j) tp sigma_j >= 0,
    $ since each $Lambda(rho_j) >= 0$.

    $<==$: let $rho$ be entangled. We want to find a positive map $Lambda: B(HH_A) -> B(HH_A)$ such that $(Lambda tp id_B)(rho)$ has a negative eigenvalue. By @def:entanglement-witness, $rho$ has an entanglement witness $omega$, with $tr(rho omega) < 0$. By the Choi-Jamiolkowski isomorphism, // TODO: again, why does it not matter that omega is not an density matrix?
    this defines a map $Lambda$ such that $
        omega = (Lambda^* tp id_B)(ket(phi) bra(phi)). // TODO: clarify whether it should be Lambda or Lambda^*
    $ Since $tr(X Y) = tr(FF(X tp Y))$, and $F = d ket(phi) bra(phi)$, we have for all $A in B(HH_A)$, $B in B(HH_B)$, $
        tr(B^T Lambda(A)) & = tr(F(Lambda(A) tp B^T)) \
        & = d tr((Lambda tp id_B)(A tp B) (ket(phi) bra(phi))) \
        & = d braket(phi, (Lambda tp id_B)(A tp B), phi).
    $ TODO: finish.
]
#remark[
    - In the above proof, we use that $tr(rho omega) = d braket(phi, (Lambda tp id_B)(rho), phi) < 0$ implies that $(Lambda tp id_B)$ has a negative eigenvalue. However, the converse is false. Hence, the positive map $Lambda$ corresponding to a witness $omega$ in fact "detects more entanglement" than $omega$.
    - It can be shown that $Lambda$ constructed from $omega$ detects an entangled state $rho$ iff $rho$ is detected by a witness of the form $(II tp XX) omega (II tp X^*)$ for some $X in B(HH_B)$.
]
#remark[
    Note that @prop:positive-map-criterion-for-separability is a theoretical result but is not implementable (in a lab) since $Lambda$ is only required to be positive (but not CP). However, the map $
        T(rho) = p/d^2 II_d tp II_d + (1 - p)(Lambda tp id_B)(rho)
    $ is a CP map. If $rho$ is separable, then the minimal eigenvalue of $T(rho)$ must exceed a certain threshold. If it doesn't exceed this threshold, then $rho$ is entangled.
]
#remark[
    Note that by using a change of abasis via a unitary $U$, we can obtain a different partial transpose $tilde(T)_A$ from the "usual" partial transpose $T_A$: $
        rho^(tilde(T)_A) = (U tp II)((U^* tp II) rho (U tp II))^(T_A) (U^* tp II) = ((U U^T) tp II) rho^(T_A) ((U U^T)^* tp II) != rho^(T_A).
    $ Note that this non-uniqueness of the partial transpose does not affect the previous criteria, as they only deal with the eigenvalues, which are invariant under basis changes. Also, we have $rho^(tilde(T)_A) <==> rho^(T_A) >= 0 <==> rho^(T_B) >= 0$, // TODO: check this, as what you have in notes differs from lecture notes (my notes have the equivalence with the tilde and T_A, not T_B)
    since $rho^(T_A)$ and $rho^(T_B)$ differ only by a global transposition.
]
#definition[
    A map $Lambda: B(HH) -> B(HH)$ is called *decomposable* if $Lambda = Lambda_1 + Lambda_2 compose Theta$, where $Lambda_1$ and $Lambda_2$ are positive maps and $Theta$ is a partial transpose. Otherwise, it is called *non-decomposable*.
]<def:decomposable-map>
#example[
    The entanglement witness corresponding to a decomposable map $Lambda = Lambda_1 + Lambda_2 compose Theta$ is $omega = Q_1 + Q_2^T$, where $Q_i = d(Lambda_i tp II)(ket(phi) bra(phi))$ is the entanglement witness of $Lambda_i$ // TODO: my notes have Lambda^*_i instead here?
]
#proposition("Reduction Criterion")[
    Let $Lambda_"red" (A) = tr(A) II - A$. Note that $Lambda_"red"$ is positive. @prop:positive-map-criterion-for-separability gives us $
        (Lambda_"red" tp II)(rho) ==> cases(rho_A tp II_B >= rho_(A B), II_A tp rho_B >= rho_(A B).)
    $ The entanglement witness corresponding to $Lambda_"red"$ is $(II - F)^(T_A) = 2 P_-^(T_A)$, where $P_-$ is the projector onto the anti-symmetric subspace (the space of anti-Hermitian operators). In this case, we obtain $
        tr(rho omega) < 0 quad "iff" quad braket(phi, rho, phi) <= 1/d,
    $ where $ket(phi)$ is the maximally entangled state.
]<prop:reduction-criterion>
#proof[
    Omitted.
]
#remark[
    If $HH = CC^2 tp CC^2$, $P_-^(T_A)$ is $1$-dimensional, which gives that entanglement being detected by $omega$ is equivalent to the PPT criterion.
]
#proposition[
    Entangled states with positive partial transpose exist iff there are non-decomposable maps. Specifically, there exists a non-decomposable map $T: B(HH_A) -> B(HH_B)$ iff there exists an entangled state $rho in B(HH_A) tp B(HH_B)$ with positive partial transpose $rho^(T_A) >= 0$.
]<prop:entangled-states-with-ppt-exist-iff-non-decomposable-maps-exist>
#proof[
    Omitted.
]
#proposition[
    Let $rho in S(CC^2 tp CC^3)$ or $S(CC^2 tp CC^2)$. Then $rho$ is separable iff $rho^(T_A) >= 0$.
]<prop:separability-criterion-in-small-dimensions>
#proofhints[
    Use the fact that every positive $Lambda$ on a Hilbert space of dimension $2 tp 2$ or $2 tp 3$ is decomposable.
]
#proof[
    This follows from the @prop:ppt-criterion and @prop:entangled-states-with-ppt-exist-iff-non-decomposable-maps-exist combined with the fact that every positive $Lambda$ on a Hilbert space of dimension $2 tp 2$ or $2 tp 3$ is decomposable.
]