#import "@preview/quill:0.2.0": *
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.4" as cetz: canvas, draw
#let name-abbrvs = (:)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)
#set document(
    title: "Quantum Entanglement in Many-Body Physics Notes",
    author: "Isaac Holt",
    keywords: ("quantum entanglement")
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

== Measurements

von Neumann measurements: $sum_i P_i = II$, $P_i P_j = delta_(i j) P_i$. Then when measuring $rho_A$, it collapses to $1/tr(P_i rho_A) P_i rho_A P_i$. If we measure system $C$ on the state $U_(A C) (ket(0) bra(0) tp rho_A ) U_(A C)^dagger$ gives $tr_C ((P_i^((C)) tp II) U_(A C) (ket(0) bra(0) tp rho_A) U_(A C)^dagger (P_i^((c)) tp II))$

Let $A_0 = sqrt(II - dif t sum_i L_i^dagger L_i)$, ${L_i}$ are Limdblod operators, $A_i = sqrt(dif t) L_i$. This gives $
    (dif rho)/(dif t) = i [H, rho] + sum_i L_i rho L_i^dagger - 1/2 sum_i (L_i^dagger L_i rho + rho L_i^dagger L_i).
$

Ky-Fan principle for Hermitian matrices: $lambda_1 = max_(P_1) tr(P_1 rho) = max_(ket(psi)) braket(psi, rho, psi)$, $lambda_1 + lambda_2 = max_(P_2) tr(P_2 rho)$, $lambda_1 + lambda_2 + lambda_3 = max_(P_3) tr(P_3 rho)$. $P_i$ are projectors.

#theorem("Quantum Steering")[
    Let $ket(psi)$ be a pure state in $HH = HH_A tp HH_B$ and let $rho_B = tr_A (ket(psi) bra(psi))$. A POVM measurement on system $A$ can produce the ensemble ${(p_i, rho_i): i in [M]}$ at system $B$ iff $rho_B = sum_(i = 1)^M p_i rho_i$.
]<thm:quantum-steering>
#remark[
    The @thm:quantum-steering theorem is also known as the Hughston, Jozsa, Wootters theorem.
]
#definition[
    An *entanglement monotone* is a function on the set of quantum states in $HH_A tp HH_B$ which does not increase, on average, under local transformations on $HH_A$ and $HH_B$. In particular, it is invariant under local unitary operations.
]<def:entanglement-monotone>
#theorem("Vidal")[
    A function of a bipartite pure state is an entanglement monotone iff it is a concave unitarily invariant function of its local density matrix.
]<thm:vidal>
#example[
    Let $HH = HH_A tp HH_B$ with $n = min{dim HH_A, dim HH_B}$. A family of entanglement monotones on $HH$ is given by $
        mu_m (ket(psi)) = -sum_(i = 1)^m lambda_i,
    $ for each $m in [n]$, where $lambda_1, ..., lambda_n$ are the Schmidt coefficients of $ket(psi)$ in decreasing order.
]
#definition[
    Let $x, y in RR^n$, and let $x^((i))$ denote the $i$-th largest element of $x$. We say $x$ *weakly majorises* $y$, written $y prec_w x$, if $
        sum_(i = 1)^m y^((i)) <= sum_(i = 1)^m x^((i)) quad forall m in [n].
    $ $x$ *majorises* $y$, $x prec y$, if it weakly majorises $y$ and $sum_(i = 1)^n x_i = sum_(i = 1)^n y_i$.
]<def:majorisation>
#theorem[
    The probabilistic transformation $ket(psi) |-> {(p_i, ket(psi_i)): i in [M]}$ can be accomplished using LOCC iff $
        lambda(ket(psi)) prec sum_(i = 1)^M p_i lambda(ket(psi_i)),
    $ where $lambda(ket(phi))$ denotes the vector of Schmidt coefficients of $ket(phi)$.
]
#theorem("Bennett")[
    Given an asymptotic number $N$ of copies of a bipartite pure state $ket(psi)_(A B)$ with local density operator $rho$, there exists a local transformation that transforms $N dot S(rho)$ Bell states with fidelity tending to $1$. Conversely, $N dot S(rho)$ Bell states can be diluted into $N$ copies of the original state with fidelity tending to $1$.
]
#definition[
    The *entanglement of formation* of a mixed state is the minimal number of EPR pairs needed to construct the state: $
        E_f (rho) = min_{p_i, ket(psi_i)} sum_i p_i E(ket(psi_i)),
    $ where $E(ket(psi_i))$ is the von-Neumann entropy of the local density operator of $ket(psi_i)$, and the minimum is taken over all ensembles ${(p_i, ket(psi_i))}$ such that $rho = sum_i p_i ket(psi_i) bra(psi_i)$.

    Note that $rho$ is separable iff $E_f (rho) = 0$.
]
#definition[
    For $n in NN$, the *entanglement cost* of $rho$ is $E_f (rho^(tp n))$.
]
#theorem[
    Let $rho$ be a bipartite pure state. The *negativity* of $rho$ is twice the sum of the absolute values of values of all negative eigenvalues of $rho^(T_B)$, where $T_B$ is the partial transpose with respect to system $B$. The negativity is an entanglement monotone.
]
#definition[
    The *entanglement of distillation* is the maximal fraction of EPR pairs that ca be distilled out of a large number of copies of the state.
]
#definition[
    A *ground state* of a Hamiltonian $H$ is an eigenstate of $H$ corresponding to the smallest eigenvalue $E_0$ of $H$.

    An *excited state* of $H$ is an eigenstate corresponding to a non-minimal eigenvalue of $H$. The smallest energy of an excited state is called the *mass gap* $E_1$ of the Hamiltonian.

    When the number of qubits $N -> oo$, $H$ is *gapped* if there is $delta$ independent of $N$ such that $E_1 - E_0 > delta$.
]
#definition[
    A *symmetry* of a Hamiltonian $H$ is a unitary operator $U$ such that $[H, U] = 0$, i.e. $U H U^* = H$.
]
#proposition[
    If $H$ has a symmetry $U$ and $ket(psi_"GS")$ is the unique ground state of $H$, then $ket(psi_"GS")$ is invariant under $U$, i.e. $U ket(psi_"GS") = ket(psi_"GS")$ (up to a phase).
]
#theorem[
    Fundamental theorem of MPS: $ket(psi(A)) = ket(psi(B))$ iff $exists phi, X$ such that $B^i = e^(i phi) X A^i X^(-1)$.
]
Smith normal form: if matrix $M$ has integer entries, can write $M = U Sigma V^T$, where $det(U), det(V) = plus.minus 1$, $U, V$ have integer entries, $Sigma$ is diagonal with entries 

// TODO:
/*
for exam:
- entanglement theory (first chapter):
    - Schmidt numbers/entanglement spectrum, eigenvalues of rho_A are entanglement monotones, gives entanglement entropy S(rho)
    - mixed states and their evolutions, CP maps $sum_k A_k rho A_k^dagger$, A_k are Kraus operators. continuous version of this: (d rho)/(d t) = -i H, rho] + sum_i L_i rho L_i^dagger - 1/2 {L_i^dagger L_i, rho}_+ (the Lindblad equation)
    - CP maps and Lindblad equation give dual description of matrix product states (MPS): unravellings and purification (can imagine system interacting with light modes with escape)
    - fixed points of CP maps and Lindblad equation (quantum version of stochastic matrix and master equation)

- monogamy of entanglement (second chapter):
    - if two qubits are maximally entangled, then they cannot be entangled with another qubit; conversely, if three are pairwise entangled, then none of them are maximally entangled
    - example: Heisenberg Hamiltonian: H = sum_i X_i X_(i + 1) + Y_i Y_(i + 1) + Z_i Z_(i + 1). it is sum of terms which don't pairwise commute with each other.
    - monogamy leads to frustration
    - monogamy means manifold (called the Kaihler manifold) of physical states (within full Hilbert space of dimension 2^m) is low dimensional. we have an area law for entanglement entropy within this manifold. the MPS span this manifold (note the manifold is not a Hilbert space)

- Lieb-Robinson bounds (third chapter)
    - there will be no (or at most superficial) questions about the bounds themselves
    - bounds show that there is finite speed at which correlations can spread
    - gives notion of locality: local effect takes time to affect points far away from it
    - bounds allow you to prove that in gapped phase, all ground states satisfy an area law
    - phase of matter define in terms of adiabatic evolution. H = sum_alpha x_alpha h_alpha, [h_a, U(g)^(tp L)] = 0
    - states in different phases can be transformed into each other by quasi-adiabatic evolution (sub linear quantum circuit that connects the ground states to each other)
    - means we can consider states instead of Hamiltonians
    - in 1D, manifold is spanned by MPS

- tensor networks (fourth chapter)
    - can characterise states in terms of entangled pairs. o~o o~o o~o ... o~o. sum_(i = 1)^chi ket(tau) ket(i) (MPS). 1D case
    - in 2D case, analogue is PEPS (projected entangled pair states)
    - motivation is for solving many-body schrodinger equation
    - can encode Hamiltonian H(x) into tensor A^i with three legs (1D) or 5 legs (2D)
    - Landau paradigm: all about symmetries. all information of system is encoded in entanglement features of the tensor networks
    - fundamental theorem of MPS: ket(psi(A)) = ket(psi(B)) iff exists phi, X s.t. X A X^(-1) = e^(i phi) B.
    - symmetries can be realised in a projective way (symmetry protected topological phases of matter (SPT) - simplest example is cluster state, another example is AKLT state)
    - dualities: H(x) <-> hat(H)(x) are dual. dualities given by intertwiners in matrix product operator form. matrix product operator preserves the spectrum of the Hamiltonians
    - landau paradigm says there is global symmetry (group G), there is subgroup H which characterises unbroken symmetries
    - projective representations, second homology H^2 (H, U(1))
    - should be able to reproduce Kramers-Wa... : G = ZZ_2 symmetry.
    - building blocks: GHZ state: 4 legs: sum_i ket(i i i i) (GHZ in Z basis). can also get GHZ in X basis by applying Hadamard transformation

exam questions will be very simple. it's important that you get the ideas and able to reproduce toy examples (e.g. AKLT), reproducing FT of MPS. these notes are based on exam questions
*/

NOTE: might be helpful to go through some parts of (particularly first two chapters of) QIT notes before exam as well

= Entanglement theory

#theorem("Schmidt Decomposition")[
    Let $ket(psi)$ be a pure state in a bipartite system $HH_(A B) = HH_A tp HH_B$, where $HH_A$ has dimension $N_A$ and $HH_B$ has dimension $N_B >= N_A$. Then there exist orthonormal states ${ket(e_i): i in [N_A]} subset.eq HH_A$ and ${ket(f_i): i in [N_A]} subset.eq HH_B$ such that $
        ket(psi) = sum_(i = 1)^(N_A) lambda_i ket(e_i) tp ket(f_i),
    $ where $lambda_i >= 0$ and $sum_i lambda_i^2 = 1$.
    
    The $lambda_i$ are unique up to re-ordering. The $lambda_i$ are called the *entanglement spectrum*, *Schmidt coefficients*, *Schmidt weights* or *Schmidt numbers* of $ket(psi)$ and the number of $lambda_i > 0$ is the *Schmidt rank* or *entanglement rank* of the state.
]<thm:schmidt-decomposition>
#proofhints[
    Use the singular value decomposition of the matrix of amplitudes of $ket(psi)$.
]
#proof[
    Let $ket(psi) = sum_(k = 1)^(N_A) sum_(ell = 1)^(N_B) beta_(k ell) ket(phi_k) tp ket(phi_ell)$ for orthonormal bases ${ket(phi_k): k in [N_A]} subset.eq HH_A$, ${ket(chi_ell): ell in [N_B]} subset.eq HH_B$. Let $(beta_(k ell))$ have singular value decomposition $
        U mat(Sigma, 0) V,
    $ where $U$ is an $N_A times N_A$ unitary, $Sigma$ is an $N_A times N_A$ diagonal matrix with non-negative entries, and $V$ is an $N_B times N_B$ unitary. So $
        beta_(k ell) = sum_(i = 1)^(N_A) sum_(j = 1)^(N_B) U_(k i) Sigma_(i j) V_(j ell) = sum_(i = 1)^(N_A) Sigma_(i i) U_(k i) V_(i ell).
    $ Hence, $
        ket(psi) = sum_(k, ell) sum_i Sigma_(i i) U_(k i) ket(phi_k) tp V_(i ell) ket(chi_ell) = sum_i Sigma_(i i) underbrace((sum_k U_(k i) ket(phi_k)), ket(e_i)) tp underbrace((sum_ell V_(j ell) ket(chi_ell)), ket(j_B)).
    $
]
#proposition[
    The squared Schmidt coefficients of $ket(psi) in HH_A tp HH_B$ are the eigenvalues of the reduced density operators $rho_A = tr_B (ket(psi) bra(psi))$ and $rho_B = tr_A (ket(psi) bra(psi))$.
]
#proofhints[
    Straightforward.
]
#proof[
    We have $
        ket(psi) bra(psi) = sum_(i, j) lambda_i lambda_j^* ket(e_i) bra(e_j) tp ket(f_i) bra(f_j).
    $ Since $tr(ket(f_i) bra(f_j)) = braket(f_j, f_i) = delta_(i j)$, the result for $rho_A$ follows. The result for $rho_B$ follows similarly.
]
#definition[
    An *entanglement monotone* is a non-negative function on the set of quantum states in $HH_A tp HH_B$ which does not increase, on average, under local transformations on $HH_A$ and $HH_B$. In particular, it is invariant under local unitary operations.

    More specifically, an *entanglement monotone* $mu$ is a function from the set $S(HH_A tp HH_B)$ of quantum states in $HH_A tp HH_B$ to $RR$ which satisfies:
    - *Non-negativity*: $mu(rho) >= 0$ for all $rho in S(HH_A tp HH_B)$.
    - $mu(rho) = 0$ if $rho$ is separable.
    - *Monotonicity under LOCC*: $mu$ does not increase on average under LOCC operations. More precisely, if ${(p_i, rho_i)}$ is an ensemble arising from applying an LOCC operation to $rho$ (i.e. $rho = sum_i p_i rho_i$), then $
        mu(rho) = mu(sum_i p_i rho_i) >= sum_i p_i mu(rho_i).
    $

    Entanglement monotones quantify the amount of entanglement in a quantum state.
]<def:entanglement-monotone>
#theorem("Vidal")[
    A function of a bipartite pure state is an entanglement monotone iff it is a concave unitarily invariant function of its local density matrix.
]<thm:vidal>
#example[
    Let $HH = HH_A tp HH_B$ with $n = min{dim HH_A, dim HH_B}$. A family of entanglement monotones on $HH$ is given by $
        mu_m (ket(psi)) = -sum_(i = 1)^m lambda_i,
    $ for each $m in [n]$, where $lambda_1, ..., lambda_n$ are the Schmidt coefficients of $ket(psi)$ in decreasing order.
]
#definition[
    Let $rho in S(HH)$ be a quantum state with spectral decomposition $rho = sum_(i = 1)^n lambda_i ket(e_i) bra(e_i)$. The *von-Neumann entropy* of $rho$ is $
        S(rho) = -sum_(i = 1)^n lambda_i log(lambda_i) = -tr(rho log(rho)).   
    $ The von-Neumann entropy is a measure of how mixed the state $rho$ is: it is non-negative and is zero iff $rho$ is a pure state.
]<def:von-neumann-entropy>
#definition[
    Let $ket(psi) in S(HH_A tp HH_B)$ be a bipartite pure state. The *entanglement entropy* of $ket(psi)$ is the von-Neumann entropy of either of its reduced density operators. So the entanglement entropy is $
        S(rho_A) = S(rho_B) = -sum_(i = 1)^n lambda_i^2 log(lambda_i^2),
    $ where $rho_A = tr_B (ket(psi) bra(psi))$, $rho_B = tr_A (ket(psi) bra(psi))$ and $lambda_1, ..., lambda_n$ are the Schmidt coefficients of $ket(psi)$.
]<def:entanglement-entropy>
#definition[
    A *completely positive (CP)* map is a linear map $T: B(HH) -> B(HH)$ such that for all $n in NN$, $T tp II_n$ is positive (i.e. if $A >= 0$, then $(T tp id_n)(A) >= 0$).

    CP maps can be expressed in their *Kraus decomposition* as $
        T(rho) = sum_k A_k rho A_k^dagger,
    $ where the ${A_k}$ are *Kraus operators*.
]<def:cp-map>
#definition[
    A *completely positive trace preserving (CPTP)* map is a CP map $T$ such that $tr(T(A)) = tr(A)$ for all $A in B(HH)$. In particular, CPTP maps map density operators to density operators, and describe the most general evolution of a quantum system.

    If $A$ has Kraus decomposition $T(rho) = sum_k A_k rho A_k^dagger$, then the Kraus operators satisfy $sum_k A_k^dagger A_k = II$.
]<def:cptp-map>
#definition[
    The *transfer matrix* of a quantum channel with Kraus operators ${A_k}$ is $
        E = sum_k A_k overline(A_k),
    $ where $overline(A_k)$ is the entry-wise complex conjugate of $A_k$.
]
#definition[
    A matrix $U in CC^(m times n)$ is called an *isometry* if $U^dagger U = II_n$.
]<def:isometry>
#remark[
    The Kraus decomposition of a CPTP map is not unique: given a set of Kraus operators ${A_k: k in [K]}$, we can define an equivalent set of Kraus operators ${B_ell: ell in [L]}$ for the same map by $B_ell = sum_(k = 1)^K U_(ell k) A_k$, where $U$ is an isometry. Moreover, two sets of Kraus operators are equivalent if and only if they are related by such an isometry.
]
#definition[
    Given a set of *Lindblad operators* ${L_i: i in [M]}$ (which are arbitrary square matrices), define the Kraus operators $
        A_0 & = sqrt(I - dif t sum_(i = 1)^M L_i^dagger L_i), \
        A_i & = sqrt(dif t) L_i, quad i in [M].
    $ The CP map $T$ defined by these Kraus operators satisfies $T(rho) = rho + O(dif t)$, which gives $
        (dif rho)/(dif t) & = sum_i L_i rho L_i^dagger - 1/2 (sum_i L_i^dagger L_i rho + rho sum_i L_i^dagger L_i) \
        & = sum_i (L_i rho L_i^dagger - 1/2 {L_i^dagger L_i, rho})
    $ Given that the system evolves according to a Hamiltonian $H$, we obtain the *Lindblad equation* $
        (dif rho)/(dif t) = -i [H, rho] + sum_i (L_i rho L_i^dagger - 1/2 {L_i^dagger L_i, rho}).
    $
]<def:lindblad-equation>
#remark[
    Physically, evolution according to the Lindblad equation corresponds to when we the system of interest to an ancilla through an infinitesimal interaction / evolution with a Hamiltonian which couple both systems, then take the trace over the ancilla. This only makes sense when the ancillary system cannot interact with the system of interest anymore at later times.
]
#remark[
    CPTP maps and the Lindblad equation are the two ways of describing the evolution of a quantum system: the Lindblad equation is the continuous version of a CPTP map. They are the most general evolution of a many-body quantum system coupled to a part (the environment) which we take the trace over.
]
#definition[
    A quantum channel $T$ is called *ergodic* if for all $rho in S(HH)$, ${T^n (rho): n >= 0}$ spans $S(HH)$.
]
#proposition[
    Quantum channels (or more generally CP maps) always have at least one fixed point (i.e. eigenstate with eigenvalue $1$). If the quantum channel is ergodic, then the fixed point $rho_0$ is unique (all other eigenvalues have modulus $< 1$).

    If the quantum channel is ergodic, then the system evolves to the steady state $rho_0$.
]
#example[
    Let $T(rho) = sum_i A_i rho A_i^dagger$ be a quantum channel with Kraus operators $A_i$. Say we start with an initial state $rho_0 = ket(psi_0) bra(psi_0)$. Then a purification of the channel applied $N$ times to $rho_0$, $T^N (rho_0)$ is $
        ket(psi_N) = sum_(i_1, ..., i_N) A_(i_1) cdots A_(i_N) ket(psi_0) tp ket(i_1 ... i_N).
    $ The channel acts as $ket(psi_0) |-> sum_i A_i ket(psi_0) tp ket(i)_E$ followed by taking the partial trace over the environment $E$ (this is easy to check). $ket(psi_N)$ is the resulting state if we apply the channel $N$ times without taking the trace.
    
    Note that $ket(psi_N)$ has the form of a matrix product state (MPS). This is called an *unravelling/purification* of the channel $T$. The physical interpretation of unravelling is: consider an atom in a cavity coupled (interacting with) to an electromagnetic field. Every time a Kraus operator $A_i$ is applied, a photon (light mode) in the state $ket(i)$ escapes the cavity.
]




= Tensor networks

#definition[
    A *rank-$r$* tensor of dimension $d_1 times d_2 times ... times d_r$ is an element of $CC^(d_1 times cdots times d_r)$.

    In tensor network notation (TNN), a rank-$r$ tensor is represented by a box with $r$ legs, with each leg corresponding to an index.
]<def:tensor>
#example[
    - A scalar is a rank-$0$ tensor.
    - A vector is a rank-$1$ tensor.
    - A matrix is a rank-$2$ tensor.
]
#definition[
    The *tensor product* $A tp B$ of a rank-$r$ tensor $A$ and a rank-$s$ tensor $B$ is given by $
        (A tp B)_(i_1, ..., i_r, j_1, ..., j_s) = A_(i_1, ..., i_r) dot B_(j_1, ..., j_s).
    $ In TNN, the tensor product is represented by placing two tensors next to each other without joining them.
]<def:tensor-product>
#definition[
    Let $A$ be a tensor of dimension $d_1 times d_2 times ... times d_r$ and suppose the $k$-th and $ell$-th indices have the same dimension $d = d_k = d_ell$. The *partial trace* $tr_(k, ell) A$ of $A$ over the $k$-th and $ell$-th indices is given by jointly summing over those indices: $
        (tr_(k, ell) A)_(i_1, ..., i_(k - 1), i_(k + 1), ..., i_(ell - 1), i_(ell + 1), ..., i_r) = sum_(j = 1)^d A_(i_1, ..., i_(k - 1), j, i_(k + 1), ..., i_(ell - 1), j, i_(ell + 1), ..., i_r).
    $ In TNN, the partial trace is represented by joining the legs corresponding to the indices being traced out.
]<def:partial-trace>
#definition[
    A *tensor contraction* is a tensor product followed by a partial trace.

    In TNN, a tensor contraction is represented by joining the legs corresponding to the indices being summed over.
]<def:tensor-contraction>
#example[
    Vector inner products, matrix-vector multiplication, matrix multiplication, and the trace of a matrix are all examples of tensor contractions.
]
#remark[
    It is easy to see that the matrix trace is cyclic by writing it in tensor network notation, and "sliding" one of the matrices around.
]
#definition[
    Using the fact that the vector spaces $CC^(a_1 times cdots times a_r)$ and $CC^(b_1 times cdots times b_s)$ are isomorphic iff $a_1 times cdots times a_r = b_1 times cdots times b_s$, we can *group* or *split* indices to respectively increase or decrease the rank of a tensor.

    As a concrete example, if $T$ is a rank $r + s$ tensor, we can group its first $r$ indices together and its last $s$ indices together to form a matrix: $
        T_(I, J) = T_(i_1, ..., i_r, j_1, ..., j_s),
    $ where the group indices have been defined as $
        I & = i_1 + d_1 i_2 + ... + d_1 d_2 ... d_(r - 1) i_r, \
        J & = j_1 + d_(r + 1) j_2 + ... + d_(r + 1) d_(r + 2) ... d_(r + s - 1) j_s.
    $ Such a partioning of the indices into two sets is called a *bisection* of the tensor.
]<def:grouping-splitting>
#example[
    For a general contraction of two tensors, we can group the indices involved in the contraction, and the indices not involved in the contraction, to simplify this contraction to a matrix multiplication.
]
#example[
    The singular value decomposition (SVD) of a matrix $T$ indexed by $I$ and $J$ is given by $
        T_(I, J) = sum_k U_(I, k) S_(k, k) V^dagger_(k, J).
    $ By grouping and splitting, we obtain a higher-dimensional version of the SVD: $
        T_(i_1, ..., i_r, j_1, ..., j_s) = sum_k U_(i_1, ..., i_r, k) S_(k, k) V^dagger_(k, j_1, ..., j_s).
    $
]
#remark[
    The rank of a tensor given in a tensor network diagram is the number of unmatched legs in the diagram. The value of the tensor is independent of the order in which the constituent tensors are contracted.
]
#definition[
    Let $ket(psi) = sum_(i_1, ..., i_N = 0)^(d - 1) psi_(i_1, ..., i_N) ket(i_1 ... i_N)$ be a general pure $N$-qudit state. $ket(psi)$ is completely determined by the rank-$N$ tensor $psi$. By splitting the first index from the rest and performing an SVD, we obtain $
        ket(psi) = sum_(i_1 = 0)^(d - 1) lambda_(i_1) ket(L_(i_1)) tp ket(R_(i_1)).
    $ Iterating this process, we obtain $
        ket(psi) = sum_(i_1, ..., i_N = 0)^(d - 1) lambda_(i_1, ..., i_(N - 1)) ket(L_(i_1)) tp ket(L_(i_2)) tp cdots tp ket(L_(i_N)),
    $ For example, in TNN,
    #figure(
        image("mps-1.png")
    ) or more simply,
    #figure(
        image("mps-2.png")
    ) This is called a *matrix product state (MPS)*. We often write this as $
        ket(psi(A^((1)), ..., A^((N)))) = sum_(i_1, ..., i_N = 0)^(d - 1) tr(A^((1))_(i_1) A^((2))_(i_2) ... A^((N))_(i_N)) ket(i_1 ... i_N).
    $ If $ket(psi)$ is translation-invariant (meaning that the coefficient of $ket(i_1 ... i_N)$ is invariant under cyclic shifts of $i_1, ..., i_N$), we write $
        ket(psi(A)) = sum_(i_1, ..., i_N = 0)^(d - 1) tr(A_(i_1) cdots A_(i_N)) ket(i_1 ... i_N).
    $ This can be represented in TNN as
    #figure(
        image("mps-3.png")
    )
]<def:matrix-product-state>
#remark[
    Note that most tensors involved in an MPS are not matrices, but have rank $3$. The uncountrated index is called the *physical index*, the other two are called the *virtual/bond/matrix* indices.
]
#definition[
    The *bond dimension* of an MPS is the dimension of any of the virtual indices. The bond dimension controls the precision of the low-rank approximation of the MPS to the original state: by increasing the bond dimension, we can approximate any state to arbitrary precision.
]
#definition[
    A *1D projected entangled pair state (PEPS)* is given by laying out entangled pair state $ket(psi)$ (e.g. $ket(phi) = ket(00) + ket(11)$) on a (here, 1D) lattice, then applying some projector $cal(P)$ _between_ the pairs:
    #figure(
        image("1d-peps.png")
    )
    where
    #figure(
        image("peps-pair-state.png", width: 20%)
    )
    Note that generally, $cal(P)$ is not a unitary, so a PEPS construction does not give a practical way of preparing the state: the fact $cal(P)$ is a projector means that generally post-selected measurements are required to construct the state this way.
]

== Examples of MPS states

#example[
    Let $A_0 = mat(0)$ and $A_1 = mat(1)$. Then the MPS is $
        ket(psi(A)) = sum_(i_1, ..., i_N = 0)^1 tr(A_(i_1) ... A_(i_N)) ket(i_1 ... i_N) = ket(0)^(tp N).
    $ We can also express $ket(0)^(tp N)$ as the MPS $ket(psi(A))$ with $
        A_0 = mat(1, 0; 0, 0), quad A_1 = mat(0, 0; 0, 0).
    $
]
#example[
    Let $
        A_0 = mat(1, 0; 0, 1), quad A_1 = mat(0, 1; 0, 0).
    $ Choose the boundary conditions of the MPS to be
    #figure(
        image("mps-4.png")
    )
    Since $A_0 A_0 = A_0$, $A_0 A_1 = A_1 A_0 = A_1$, $A_1 A_1 = 0$, $tr(A_1 X) = 1$, and $tr(A_0 X) = 0$, we have $
        ket(psi(A)) = sum_(i_1, ..., i_N = 0)^1 tr(A_(i_1) ... A_(i_N)) ket(i_1 ... i_N) = sum_(j = 1)^N ket(0)_1 cdots ket(0)_(j - 1) ket(1)_j ket(0)_(j + 1) cdots ket(0)_N,
    $ which is the *$W$-state* $ket(W)$.
]
#example[
    Let $
        A_0 = mat(1, 0; 0, 0), quad A_1 = mat(0, 0; 0, 1).
    $ Then the MPS is the *Greenberger-Horne-Zeilinger (GHZ) state* $
        ket("GHZ") = ket(0)^(tp N) + ket(1)^(tp N).
    $ Equivalently, we can construct the GHZ state as a PEPS with $ket(phi) = ket(00) + ket(11)$ and $cal(P) = ket(0) bra(00) + ket(1) bra(11)$, so that $cal(P) ket(00) = ket(0)$, $cal(P) ket(01) = cal(P) ket(1) = 0$, $cal(P) ket(11) = ket(1)$.
]
#example[
    The *cluster state* is the MPS $ket(psi(A))$, where $
        A_00 = mat(1, 0; 1, 0), quad A_01 = mat(0, 1; 0, 1), quad A_10 = mat(1, 0; -1, 0), quad A_11 = mat(0, -1; 0, 1).
    $ Alternatively, we can construct the cluster state as a PEPS with $ket(phi) = ket(00) + ket(11)$ and $
        cal(P) = mat(1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, -1, 0, 1)
    $ $cal(P)$ can be implemented as the quantum circuit
    #figure(
        image("cluster-state-circuit.png", width: 15%)
    ) Note that the initial state constructed from entangled pairs $product_j ket(phi)_(2j, 2j + 1)$ is the unique ground state of the Hamiltonian $
        H' = -sum_j (X_(2j) X_(2j + 1) + Z_(2j) Z_(2j + 1))
    $ Applying the circuit between each qubit pair (with first qubit odd and second even) transforms this Hamiltonian the *cluster state Hamiltonian* $
        H & = -sum_j (Z_(2j - 1) X_(2j) Z_(2j + 1) + Z_(2j) X_(2j + 1) Z_(2j + 2)) \
        & = -sum_k Z_(k - 1) X_k Z_(k + 1)
    $
]
#example[
    The *AKLT state* is the 1D PEPS with entangled pair state $ket(phi) = ket(01) - ket(10)$ and projector $cal(P): CC^(2 times 2) -> CC^3$ given by $
        cal(P) = ket(tilde(1)) bra(00) + ket(tilde(0)) 1/sqrt(2) (bra(01) + bra(10)) + ket(-tilde(1)) bra(11)
    $ The AKLT state is $"SO"(3)$ symmetric: the spin vector on the spin-1 particle $(S_X, S_Y, S_Z)$ is given by $
        S_X & = 1/sqrt(2) (ket(tilde(0)) (bra(tilde(1)) + bra(-tilde(1))) + (ket(tilde(1)) + ket(-tilde(1))) bra(tilde(0))) = 1/sqrt(2) mat(0, 1, 0; 1, 0, 1; 0, 1, 0) \
        S_Y & = 1/sqrt(2) i (ket(tilde(0)) (bra(tilde(1)) - bra(-tilde(1))) + (ket(tilde(1)) - ket(-tilde(1))) bra(tilde(0))) = 1/sqrt(2) mat(0, -i, 0; i, 0, -i; 0, i, 0) \
        S_Z & = ket(tilde(1)) bra(tilde(1)) - ket(-tilde(1)) bra(-tilde(1)) = mat(1, 0, 0; 0, 0, 0; 0, 0, -1)
    $ Then it is straightforward to show that $
        S_Z cal(P) & = cal(P) 1/2 (Z_1 + Z_2) \
        S_X cal(P) & = cal(P) 1/2 (X_1 + X_2) \
        S_Y cal(P) & = cal(P) 1/2 (Y_1 + Y_2)
    $ TODO: finish this

    The AKLT state can also be written as the MPS $ket(psi(A))$, where $A_i = sigma_i$ for each $i in [3]$ (and $sigma_i$ are the Pauli matrices).
]

TODO: 2D PEPS

The bond dimension $D$ of a PEPS is the dimension of either of the subsystems in which one of the qubits of the entangled pair lives.

== Properties of MPS

#definition[
    Given an MPS $ket(psi(A))$ and an observable $cal(O)$, the *$cal(O)$-transfer matrix* is defined as $
        EE_cal(O) = sum_(i, j = 0)^(d - 1) cal(O)_(i j) A_i tp overline(A_j).
    $ In TNN, $EE_cal(O)$ is represented as
    #figure(
        image("o-transfer-matrix.png", width: 8%)
    )
]
#definition[
    Given an MPS $ket(psi(A))$, the *transfer matrix* $EE$ is the transfer matrix $EE_II$ of the identity operator: $
        EE = sum_(i = 0)^(d - 1) A_i tp overline(A_i).
    $
]
#definition[
    An MPS $ket(psi(A))$ is in *left-canonical form* if $
        sum_(j = 0)^(d - 1) A_j^dagger A_j = II_D
    $ In TNN, this is written as
    #figure(
        image("left-canonical-tnn.png", width: 20%)
    )
]<def:mps.left-canonical-form>
#definition[
    Let $ket(psi(A))$ be an MPS in left-canonical form. $ket(psi(A))$ is *injective* if the identity matrix is the left eigenstate of the transfer matrix with eigenvalue $1$. Equivalently, the leading (largest in absolute value) eigenvalue of the transfer matrix is $1$, and all other eigenvalues have modulus $< 1$.
]
#definition[
    A *gauge transformation* is a transformtion on the tensors of an MPS that leaves the state invariant. They are given by basis changes on the virtual indices.
]
#theorem("Fundamental Theorem of MPS")[
    Any two translationally invariant MPS represent the same quantum state iff their tensors are related by a gauge transformation.
    Let $ket(psi(A))$ and $ket(psi(B))$ be two MPS with the same bond dimension. Then for all system sizes $N$, $ket(psi(A)) = ket(psi(B))$ iff there exists a phase $phi$ and an invertible matrix $X$ such that for each virtual index $i$, $
        B^i = e^(i phi) X A^i X^(-1).
    $ Note that $X$ need only have a left inverse, so may be rectangular and enlarge the bond dimension.
]

// TODO: questions to ask:
// explain unravellings of quantum channels/Lindblad equation leading to MPS/continuous MPS
// 

= Monogamy of entanglement

#definition[
    *Monogamy of entanglement* is the property that if two qubits are maximally entangled, then they cannot be entangled with another qubit. Conversely, if three qubits are pairwise entangled, then none of them are maximally entangled. This leads to *frustration* effects: certain local interactions cannot be satisfied simultaneously.
]
#example[
    The *Heisenberg Hamiltonian* is given by $
        H = sum_i X_i X_(i + 1) + Y_i Y_(i + 1) + Z_i Z_(i + 1).
    $ If the system size is two qubits, then the ground state is $1/sqrt(2) (ket(0) ket(1) - ket(1) ket(0))$. This is maximally entangled since its reduced density matrix is maximally mixed. Here, there is frustration in the system due to the fact that the Hamiltonian is a sum of local terms, some of which do not commute.
]
#remark[
    Monogamy of entanglement means that the manifold (called the *Kaihler manifold*) of phyiscal states, within the full Hilbert space of possible states, is low dimensional. In a gapped phase of matter (meaning there is gap between leading and sub-leading eigenvalues in the limit as system size $-> oo$), we have an area law for entanglement: entanglement entropy of qubits in a region scales with the size of the boundary of the region.

    Tensor network states (e.g. MPS, PEPS) parametrise this manifold.
]

= Lieb-Robinson bounds

#remark[
    Lieb-Robinson bounds show that there is a finite speed at which correlations can propagate in a quantum system. This gives a notion of locality in a quantum system: a local effect takes time to affect points far away from it.

    Locality means an effect affects far away spins noticeably after a time related to the speed of the correlation propagation.
]
#remark[
    Lieb-Robinson bounds allow us to prove that in a gapped phase, all ground states satisfy an area law of entanglement.
]
#example[
    In a one-dimensional spin chain (just a one-dimensional lattice of qudits), if $A$ is a region of the one-dimensional lattice, the Lieb-Robinson bounds give the area law: $S(rho_A) <= r abs(partial A)$, where $rho_A$ is the density matrix of the qudits in $A$, $r$ is a constant and $partial A$ is the boundary of the region $A$. In 1D, $abs(partial A)$ is bounded by a constant independent of $A$.
]
#remark[
    Lieb-Robinson bounds show that in 1D, the Kaihler manifold of physical states is spanned by the set of matrix product states; hence, we can completely characterise 1D quantum spin systems by MPS.
]