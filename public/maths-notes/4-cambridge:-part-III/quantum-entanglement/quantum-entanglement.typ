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
#let tp = sym.times.circle
#let QFT = math.op("QFT")
#let Pr = math.op("Pr")
#let Ctrl(U) = $C dash.en #h(0pt) #U$
#let Aut = math.op("Aut")
#let Rot = math.op("Rot")

// == Measurements

// Ky-Fan principle for Hermitian matrices: $lambda_1 = max_(P_1) tr(P_1 rho) = max_(ket(psi)) braket(psi, rho, psi)$, $lambda_1 + lambda_2 = max_(P_2) tr(P_2 rho)$, $lambda_1 + lambda_2 + lambda_3 = max_(P_3) tr(P_3 rho)$. $P_i$ are projectors.

// #definition[
//     Let $x, y in RR^n$, and let $x^((i))$ denote the $i$-th largest element of $x$. We say $x$ *weakly majorises* $y$, written $y prec_w x$, if $
//         sum_(i = 1)^m y^((i)) <= sum_(i = 1)^m x^((i)) quad forall m in [n].
//     $ $x$ *majorises* $y$, $x prec y$, if it weakly majorises $y$ and $sum_(i = 1)^n x_i = sum_(i = 1)^n y_i$.
// ]<def:majorisation>
// #theorem[
//     The probabilistic transformation $ket(psi) |-> {(p_i, ket(psi_i)): i in [M]}$ can be accomplished using LOCC iff $
//         lambda(ket(psi)) prec sum_(i = 1)^M p_i lambda(ket(psi_i)),
//     $ where $lambda(ket(phi))$ denotes the vector of Schmidt coefficients of $ket(phi)$.
// ]
// #definition[
//     The *entanglement of formation* of a mixed state is the minimal number of EPR pairs needed to construct the state: $
//         E_f (rho) = min_{p_i, ket(psi_i)} sum_i p_i E(ket(psi_i)),
//     $ where $E(ket(psi_i))$ is the von-Neumann entropy of the local density operator of $ket(psi_i)$, and the minimum is taken over all ensembles ${(p_i, ket(psi_i))}$ such that $rho = sum_i p_i ket(psi_i) bra(psi_i)$.

//     Note that $rho$ is separable iff $E_f (rho) = 0$.
// ]
// #definition[
//     For $n in NN$, the *entanglement cost* of $rho$ is $E_f (rho^(tp n))$.
// ]
// #theorem[
//     Let $rho$ be a bipartite pure state. The *negativity* of $rho$ is twice the sum of the absolute values of values of all negative eigenvalues of $rho^(T_B)$, where $T_B$ is the partial transpose with respect to system $B$. The negativity is an entanglement monotone.
// ]
// #definition[
//     The *entanglement of distillation* is the maximal fraction of EPR pairs that ca be distilled out of a large number of copies of the state.
// ]

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

= Entanglement theory

#theorem("Quantum Steering")[
    Let $ket(psi)$ be a pure state in $HH = HH_A tp HH_B$ and let $rho_B = tr_A (ket(psi) bra(psi))$. A POVM measurement on system $A$ can produce the ensemble ${(p_i, rho_i): i in [M]}$ at system $B$ iff $rho_B = sum_(i = 1)^M p_i rho_i$.
]<thm:quantum-steering>
#remark[
    The @thm:quantum-steering theorem is also known as the Hughston, Jozsa, Wootters theorem.
]
#theorem("Schmidt Decomposition")[
    Let $ket(psi)$ be a pure state in a bipartite system $HH_(A B) = HH_A tp HH_B$, where $HH_A$ has dimension $N_A$ and $HH_B$ has dimension $N_B >= N_A$. Then there exist orthonormal states ${ket(e_i): i in [N_A]} subset.eq HH_A$ and ${ket(f_i): i in [N_A]} subset.eq HH_B$ such that $
        ket(psi) = sum_(i = 1)^(N_A) lambda_i ket(e_i) tp ket(f_i),
    $ where $lambda_i >= 0$ and $sum_i lambda_i^2 = 1$.
    
    The $lambda_i$ are unique up to re-ordering. The $lambda_i$ are called the *entanglement spectrum*, *Schmidt coefficients*, *Schmidt weights* or *Schmidt numbers* of $ket(psi)$ and the number of $lambda_i > 0$ is the *Schmidt rank*, *Schmidt number* or *entanglement rank* of the state.
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
]<prop:squared-schmidt-coeffs-are-eigenvalues-of-reduced-density-matrices>
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
        E = sum_k A_k tp overline(A_k),
    $ where $overline(A_k)$ is the entry-wise complex conjugate of $A_k$.
]
#definition[
    An eigenvector $rho_i$ of a quantum channel $T$ satisfies $T(rho) = lambda rho$ for some $lambda in CC$. $T$ is *injective (or primitive)* if exactly one eigenvalue is $1$, and the others have modulus $< 1$. Equivalently, there exists $n in NN$ such that $T^n (rho) > 0$ for all $rho in S(HH)$.
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
    Quantum channels (or more generally CP maps) always have at least one fixed point (i.e. eigenstate with eigenvalue $1$). If the quantum channel is ergodic, then the fixed point $rho_0$ is unique (all other eigenvalues are roots of unity (corresponding to limit cycles) or have modulus $< 1$).

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
    For an MPS $ket(psi(A))$, the density matrix $rho(A) = ket(psi(A)) bra(psi(A))$ of $ket(psi(A))$ can be written in TNN as
    #figure(
        image("density-matrix-tnn.png", width: 50%)
    ) Similarly, the reduced density matrix over some subset of qudits $R$ can be written in TNN as
    #figure(
        image("reduced-density-matrix-tnn.png", width: 30%)
    )
    These are both examples of *matrix product operators (MPO)*. The most general MPO we consider are of the form
    #figure(
        image("mpo-tnn.png", width: 50%)
    )
]
#definition[
    A *1D projected entangled pair state (PEPS)* is given by laying out entangled pair states $ket(psi) in CC^D tp CC^D$ (e.g. $ket(phi) = ket(00) + ket(11)$) on a (here, 1D) lattice, then applying some projector $cal(P): CC^D tp CC^D -> CC^d$ _between_ the pairs:
    #figure(
        image("1d-peps.png")
    )
    where
    #figure(
        image("peps-pair-state.png", width: 20%)
    )
    Note that generally, $cal(P)$ is not a unitary, so a PEPS construction does not give a practical way of preparing the state: the fact $cal(P)$ is a projector means that generally post-selected measurements are required to construct the state this way.

    Any 1D PEPS can be expressed as an MPS, and vice versa; however, higher-dimensional PEPS cannot be expressed as MPS, so PEPS is more general.
]
#remark[
    We can transform the local basis of each qudit in the entangled pair of a PEPS by any (left) invertible matrix: $ket(phi) |-> (A tp B) ket(phi)$ and modify the projector $cal(P)$ accordingly: $cal(P) |-> cal(P) (B^(-1) tp A^(-1))$. This produces the same state. This is called a *gauge transformation*.

    Note $ket(phi)$ need not be normalised.
]
#definition[
    1D PEPS are easily generalised to 2 (and higher) dimensions. As before, a *2D PEPS* is given by laying out entangled pair states $ket(phi) in CC^D tp CC^D$ on a 2D lattice, then applying some projector $cal(P): (CC^D)^(tp 4) -> CC^d$ between the pairs:
    #figure(
        image("2d-peps.png", width: 80%)
    )
    where
    #figure(
        image("peps-pair-state.png", width: 20%)
    )
]
#remark[
    Note that using different entangled states $ket(phi)$ (e.g. with more than two qudits) does not generally give more descriptive power than PEPS. E.g. if
    #figure(
        image("4-qudit-peps.png")
    )
    then we can prepare the 4-qudit resource state as a PEPS, so the entire state can be prepared as a PEPS.
]
#remark[
    The motivation for introducing MPS and PEPS is to solve the many-body Schrödinger equation, since the classical complexity of this problem scales exponentially with the system size. Tensor networks give a new angle to tackle this problem.
]

== Examples of MPS and PEPS states

#example[
    Let $A_0 = mat(1)$ and $A_1 = mat(0)$. Then the MPS is $
        ket(psi(A)) = sum_(i_1, ..., i_N = 0)^1 tr(A_(i_1) ... A_(i_N)) ket(i_1 ... i_N) = ket(0)^(tp N).
    $ We can also express $ket(0)^(tp N)$ as the MPS $ket(psi(A))$ with $
        A_0 = mat(1, 0; 0, 0), quad A_1 = mat(0, 0; 0, 0).
    $ Equivalently, we can construct a product state on a 2D lattice as a 2D PEPS with $ket(phi) = ket(00) + ket(11)$ and
    #figure(
        image("2d-product-projector.png", width: 20%)
    )
]
#example[
    Let $
        A_0 = mat(1, 0; 0, 1), quad A_1 = mat(0, 1; 0, 0).
    $ Choose the boundary conditions of the MPS to be
    #figure(
        image("mps-4.png")
    )
    Since $A_0 A_0 = A_0$, $A_0 A_1 = A_1 A_0 = A_1$, $A_1 A_1 = 0$, $tr(A_1 X) = 1$, and $tr(A_0 X) = 0$, we have $
        ket(psi(A)) = sum_(i_1, ..., i_N = 0)^1 tr(A_(i_1) ... A_(i_N) X) ket(i_1 ... i_N) = sum_(j = 1)^N ket(0)_1 cdots ket(0)_(j - 1) ket(1)_j ket(0)_(j + 1) cdots ket(0)_N,
    $ which is the *$W$-state* $ket(W)$.
]
#example[
    Let $
        A_0 = mat(1, 0; 0, 0), quad A_1 = mat(0, 0; 0, 1).
    $ Then the MPS is the *Greenberger-Horne-Zeilinger (GHZ) state* $
        ket("GHZ") = ket(0)^(tp N) + ket(1)^(tp N).
    $ Equivalently, we can construct the GHZ state as a PEPS with $ket(phi) = ket(00) + ket(11)$ and $cal(P) = ket(0) bra(00) + ket(1) bra(11)$, so that $cal(P) ket(00) = ket(0)$, $cal(P) ket(01) = cal(P) ket(1) = 0$, $cal(P) ket(11) = ket(1)$. We can also construct the GHZ state on a 2D lattice as a PEPS with $ket(phi) = ket(00) + ket(11)$ and
    #figure(
        image("2d-ghz-projector.png", width: 40%)
    )
]
#definition[
    A SPT (symmetry-protected topological) phase is a phase of matter which is not symmetry-breaking (there is no order parameter), but cannot be deformed into a trivial phase without breaking a symmetry.
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
    $ Applying the circuit between each qubit pair (with first qubit odd and second even) transforms this Hamiltonian into the *cluster state Hamiltonian* $
        H & = -sum_j (Z_(2j - 1) X_(2j) Z_(2j + 1) + Z_(2j) X_(2j + 1) Z_(2j + 2)) \
        & = -sum_k Z_(k - 1) X_k Z_(k + 1)
    $ This Hamiltonian has symmetry group $ZZ_2 times ZZ_2$, realised by the symmetries $S_1 = product_j X_(2j - 1)$ and $S_2 = product_j Z_(2j)$. If we push this backwards through the above circuit, we see that these symmetries are equivalent to the symmetries on the virtual spins $S'_1 = product_j Z_(2j) Z_(2j + 1)$ and $S'_2 = product_j X_(2j) X_(2j + 1)$. This means that the cluster state possesses SPT (symmetry-protected topological) order.
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
    $ So the spin operators pull through $cal(P)$, and so since $ket(phi) = ket(01) - ket(10)$ is $"SO"(3)$-invariant, so is the AKLT state.

    The AKLT state can also be written as the MPS $ket(psi(A))$, where $A_i = sigma_i$ for each $i in [3]$ (and $sigma_i$ are the Pauli matrices).

    The AKLT state is in a *symmetry-protected topological (SPT)* phase.
]
#remark[
    In the cluster and AKLT state examples, we saw that the symmetries can be realised in a projective way: the initial (virtual state) possesses a symmetry, and the symmetries commute with the projector, meaning the projected PEPS state also possesses the symmetry.
]
#definition[
    The *bond dimension* $D$ of a PEPS is the dimension of either of the subsystems in which one of the qubits of the entangled pair lives.
]

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

    Equivalently, for $ket(psi(A))$ of bond-dimension $D$, $
        exists m in NN "s.t." {A^(i_1) ... A^(i_m)}
    $ spans the full matrix algebra (the vector space of $D times D$ matrices).
]
#remark[
    Symmetry-broken phases correspond to non-injective MPS. 
]
#example[
    The GHZ state ($A^0 = mat(1, 0; 0, 0)$, $A^1 = mat(0, 0; 0, 1)$) is not injective.
]
#definition[
    A *gauge transformation* is a transformtion on the tensors of an MPS that leaves the state invariant. They are given by basis changes on the virtual indices.
]
#theorem("Fundamental Theorem of MPS")[
    "Any two translationally invariant MPS represent the same quantum state iff their tensors are related by a gauge transformation."

    Let $ket(psi(A))$ and $ket(psi(B))$ be two injective MPS with the same bond dimension. Then for all system sizes $N$, $ket(psi(A)) = ket(psi(B))$ iff there exists a phase $phi$ and an invertible matrix $X$ such that for each index $i$, $
        B^i = e^(i phi) X A^i X^(-1).
    $ Note that $X$ need only have a left inverse, so may be rectangular and enlarge the bond dimension.
]
#proof[
    $<==$ direction is straightforward: if $B_j = M A_j M^(-1)$, then
    #figure(
        image("ft-mps-1.png")
    )
    since the $M^(-1) M$ cancel. The phase $e^(i phi)$ does not change the state, as quantum states that differ by a global phase are equivalent.

    For the $==>$ direction:
    #figure(
        image("ft-mps-2.jpeg")
    )
]

== Phases of matter

#remark[
    The different phases of matrix product states are indexed by the second group cohomology class $cal(H)^2 (G, U(1))$ of the symmetry group $G$, and can be determined using projective representations $R$ of $G$ (which satisfy $R(g h) = e^(i phi(g, h)) R(g) R(h)$ where $phi(g, h) in RR$). $cal(H)^2 (G, U(1))$ labels all projective representations of $G$.
]
#definition[
    The *Landau paradigm* says that given a many-body system for which the Hamiltonian has a certain global symmetry (given by a group $G$), the different phases of matter are characterised by the ways in which this symmetry can be broken. There is a subgroup $H$ of $G$ which characterises the unbroken symmetries.

    In particular, for 1D quantum spin systems, phases are completey characterised by subgroups and co-cycles of the subgroups.

    The Landau paradigm implies all information of system (and about which phase state is in) is encoded in entanglement features of the tensor network state describing that system.
]<def:landau-paradigm>
#definition[
    An *order parameter* is any observable which transforms non-trivially under the global symmetry operation, has zero expectation value in the symmetric phase, and a non-zero expectation value in the symmetry-broken phase.
]<def:order-parameter>
#remark[
    We can encode a Hamiltonian $H(x)$ into a tensor $A^i$ with three legs (in the 1D case) or 5 legs (in the 2D case).
]
#example[
    The Hamiltonian of a 1D Ising spin chain in a transverse magnetic field is $
        H = -sum_i Z_i Z_(i + 1) + lambda X_i.
    $ Here, the global symmetry is the group $ZZ_2$: all terms in the Hamiltonian commute with the operator $O_X = tp.big_i X_i$, hence $[H, O_X] = 0$, so $O_X$ is a symmetry of the Hamiltonian. $O_X^2 = I$, so $O_X$ forms a representation of $ZZ_2$. So in this case, there are only two phases of matter. For $abs(lambda) >> 1$, the unique ground state of $H$ is $
        ket(psi) = tp.big_i ket(+)_i,
    $ which as expected, is symmetric under the global symmetry $O_X$. This phase is called the *paramagnetic phase* or the *symmetric phase*. If $0 <= lambda << 1$, then there are two ground states in the limit as the number of spins $N -> oo$. The ground state eigenspace is approximately spanned by $
        ket(psi_0) = tp.big_i ket(1)_i, quad ket(psi_1) = tp.big_i ket(0)_i.
    $ Clearly, these two states are transformed into each other by the action of the symmetry operator $O_X$. Thus, this phase is called the *ferromagnetic phase* or the *symmetry-broken phase*. Any linear combination of these two states is also a ground state, so in particular the GHZ state $ket(psi_0) + ket(psi_1)$ is a ground state. The GHZ states are non-injective MPS with bond dimension $2$.

    Thus, the phase transition happens at $lambda = 1$, where the ground state changes from a unique symmetric state to a non-unique symmetry-broken state.

    For this example, the order parameter is $O_Z = tp.big_i Z_i$: we have $O_Z O_X = -O_X O_Z$ (anti-commutes); also, $braket(psi, O_Z, psi) = 0$, $braket(psi_0, O_Z, psi_0) = 1$, and $braket(psi_1, O_Z, psi_1) = -1$.
]
#example[
    Continuing from above, we can also construct an order parameter which has non-zero expectation value in the symmetric phase, but zero expectation value in the symmetry-broken phase: explicitly, such an order parameter is the *disorder operator*: $
        A = sum_i A_i,
    $ where $A_i = sum_(k = i - L)^i X_k$ is the *string operator*. $A$ has non-zero expectation value in the paramagnetic phase (including in the limit $L -> oo$), and in the limit $L -> oo$, $A$ has zero expectation value in the symmetry-broken phase. 

    
]
#definition[
    The above is an example of a *duality transformation*: for every symmetric phase, it is possible to associate to it a "dual" Hamiltonian with the same spectrum (same eigenvalues), but with different degeneracies (i.e. different eigenspaces) which is fully symmetry broken (meaning it has none of the symmetries of the group $G$ which characterised the symmetries of the symmetric phase).

    Under a duality transformation, symmetric local operators (terms in the Hamiltonian) are mapped to related symmetric local operators, but non-symmetric local operators (i.e. order parameters) are mapped to nonlocal "string" operators.

    Informally, two Hamiltonians $H(x)$ and $hat(H)(x)$ depending on the same parameters $x$ are dual if they have the same phase diagram. Dualities are given by *intertwiners* in MPO form and are independent of the ground state. These intertwiners preserve the spectrum (eigenvalues) of the Hamiltonians.
]
#example[
    The duality transformation in the case of the 1D Ising model is called *Kramers-Wannier (duality) transformation*. If the 1D Ising Hamiltonian is on a ring of $L$ qubits, then we can define the Kramers-Wannier transformation $U_"KW"^i$ in MPO form as
    #figure(
        image("kramers-wannier-mpo.png", width: 70%)
    )
    where
    #figure(
        image("kw-ghz.png", width: 70%)
    )
    This tensor network involves GHZ tensor in the $X$ and $Z$ basis: $
        ket("GHZ"_Z) & = ket(000) + ket(111), \
        ket("GHZ"_X) & = (H tp H tp H) ket("GHZ"_Z) = ket(+++) + ket(---).
    $ Explicitly, the dual of the 1D Ising Hamiltonian is $
        H_2 = -sum_i Z_(i + 1 \/ 2) + lambda X_(i - 1 \/ 2) X_(i + 1 \/ 2)
    $ The reason for the $plus.minus 1 \/ 2$ here is that the operators live on the dual lattice (so e.g. $X_(i + 1 \/ 2)$ lives between sites $i$ and $i + 1$).
]
#example[
    The Kramers-Wannier transformation can be generalised to two dimensions. Now, the Hamiltonian is $
        H_1 = -sum_(gen(i j)) X_i X_j + lambda Z_i,
    $ where $gen(i j)$ is the set of nearest-neighbour pairs of qubits. The dual Hamiltonian is $
        H_2 = -sum_(gen(i j)) X_gen(i j) + lambda_v product_(gen(i j) in v) Z_gen(i j)
    $ We can use PEPOs (projected entangled pair operators) to represent the Kramers-Wannier transformation in 2D:
    #figure(
        image("kw-2d.png", width: 70%)
    )
]
#definition[
    We say states which cannot be transformed into each by any constant depth local circuit are in distinct *topological phases*, or have distinct *topological order*.
]
#remark[
    All injective MPS are in the same (topological) phase as the product state, and therefore each other. Thus, there are no non-trivial topological phases in 1D.
]
#remark[
    We can distinguish between topological vs non-topological (i.e. symmetry-breaking) phases as they have very different entanglement features.
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
#definition[
    A *ground state (GS)* of a Hamiltonian $H$ is an eigenstate of $H$ corresponding to the smallest eigenvalue $E_0$ of $H$.

    An *excited state* of $H$ is an eigenstate corresponding to a non-minimal eigenvalue of $H$. The smallest energy of an excited state is called the *mass gap* $E_1$ of the Hamiltonian.

    When the number of qubits $N -> oo$, $H$ is *gapped* if there is $delta$ independent of $N$ such that $E_1 - E_0 > delta$.
]
#definition[
    A *symmetry* of a Hamiltonian $H$ is a unitary operator $U$ such that $[H, U] = 0$, i.e. $U H U^dagger = H$.
]
#example[
    A common symmetry is *translation-invariance*: a Hamiltonian $H$ is translation-invariant if $T H T^(-1) = H$ where $T ket(i_1 i_2 i_3 i_4 ...) = ket(i_2 i_3 i_4 ...)$. For local Hamiltonians $H$, this means each term of $H$ is the same operator acting on different qubits.
]
#proposition[
    If a Hamiltonian $H$ has a symmetry $U$ and $ket(psi_"GS")$ is the unique ground state of $H$, then $ket(psi_"GS")$ is invariant under $U$, i.e. $U ket(psi_"GS") = ket(psi_"GS")$ (up to a phase).

    More generally, if $H$ has a symmetry $U$, then some eigenspace of $H$ also has this symmetry (and this is the ground state eigenspace if the GS is unique).
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
#definition[
    *Adiabatic evolution* of a quantum system is the process of slowly changing the Hamiltonian of the system, such that the system remains in the ground state of the current Hamiltonian at each time step. For this to occur, the change in $H(t)$ must be slow, and the system must be gapped at all time steps.
]<def:adiabatic-evolution>
#remark[
    We can define phases of matter in terms of adiabatic evolution. Say the Hamiltonian is $H = sum_alpha x_alpha h_alpha$, where $[h_alpha, U(g)^(tp L)] = 0$ for all $g in G$, for some group $G$ and unitary representation $U$ of $G$. If the parameters $x_alpha$ are varied such that the gap of the Hamiltonian does not close, then the ground states of these Hamiltonians are in the same phase of matter.

    States within the same phase can be transformed into each other by quasi- (approximately) adiabatic evolution that does not change the area law of entanglement: this means a sub-linear (in the system size) depth quantum circuit connects the ground states to each other, and so the only thing that distinguishes ground states in the same phase is some change of local physics.

    To go to one phase from another, we must cross a phase transition, which means the entanglement structure of the state is reordered. Lieb-Robinson bounds show that states in different phases cannot be connected by a quasi-adiabatic evolution (so a quantum circuit of at least linear depth is needed to connected them). Hence, Lieb-Robinson bounds give a new way of defining what phases of matter are: we can define them in terms of ground states, instead of Hamiltonians, which are generally harder to diagonalise.
]
#remark[
    Lieb-Robinson bounds show that in 1D, the Kaihler manifold of physical states is spanned by the set of matrix product states; hence, we can completely characterise 1D quantum spin systems by MPS.
]