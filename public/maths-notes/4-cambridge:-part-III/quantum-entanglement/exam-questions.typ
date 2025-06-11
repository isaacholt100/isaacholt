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

// let the games begin


= The Quantum Entanglement in Many-body Physics Ultimate Cheatsheet

== The first exam question

*The first exam question is on mixed states and the Lindblad equation.*

Notes from the revision class:
- understand mixed states, the Lindblad equation (be able to write it down), what it means, what is the long time limit of applying it over and over again (what happens to the density matrix in long time limit, what is the unique density matrix that emerges in this limit). connection of purification of Lindblad equation to MPS. just use regular MPS (not continuous). so take MPS with an epsilon
- Lindblad equation is limit of a CP map, and can purify CP map as MPS (can argue this way)
- how to show Lindblad equation has unique fixed point (quantum Perron-Frobenius says if ergodic then unique fixed point)
- ergodic: $exists m$: $forall n >= m$, ${A^(i_1) A^(i_2) ... A^(i_n)}$ spans the full matrix algebra (corresponds to injective MPS)

Key points:
- *Schmidt Decomposition*: Let $ket(psi)$ be a pure state in a bipartite system $HH_(A B) = HH_A tp HH_B$, where $HH_A$ has dimension $N_A$ and $HH_B$ has dimension $N_B >= N_A$. Then there exist orthonormal states ${ket(e_i): i in [N_A]} subset.eq HH_A$ and ${ket(f_i): i in [N_A]} subset.eq HH_B$ such that $
    ket(psi) = sum_(i = 1)^(N_A) lambda_i ket(e_i) tp ket(f_i),
$ where $lambda_i >= 0$ and $sum_i lambda_i^2 = 1$. \ The $lambda_i$ are unique up to re-ordering. The $lambda_i$ are called the *entanglement spectrum*, *Schmidt coefficients*, *Schmidt weights* or *Schmidt numbers* of $ket(psi)$ and the number of $lambda_i > 0$ is the *Schmidt rank*, *Schmidt number* or *entanglement rank* of the state.
- The squared Schmidt coefficients of $ket(psi) in HH_A tp HH_B$ are the eigenvalues of the reduced density operators $rho_A = tr_B (ket(psi) bra(psi))$ and $rho_B = tr_A (ket(psi) bra(psi))$.
- Let $rho in S(HH)$ be a quantum state with spectral decomposition $rho = sum_(i = 1)^n p_i ket(e_i) bra(e_i)$. The *von-Neumann entropy* of $rho$ is $
    S(rho) = -sum_(i = 1)^n p_i log(p_i) = -tr(rho log(rho)).   
$ The von-Neumann entropy is a measure of how mixed the state $rho$ is: it is non-negative and is zero iff $rho$ is a pure state.
- Let $ket(psi) in S(HH_A tp HH_B)$ be a bipartite pure state. The *entanglement entropy* of $ket(psi)$ is the von-Neumann entropy of either of its reduced density operators. So the entanglement entropy is $
    S(rho_A) = S(rho_B) = -sum_(i = 1)^n lambda_i^2 log(lambda_i^2),
$ where $rho_A = tr_B (ket(psi) bra(psi))$, $rho_B = tr_A (ket(psi) bra(psi))$ and $lambda_1, ..., lambda_n$ are the Schmidt coefficients of $ket(psi)$.
- A *completely positive (CP)* map is a linear map $T: B(HH) -> B(HH)$ such that for all $n in NN$, $T tp II_n$ is positive (i.e. if $A >= 0$, then $(T tp id_n)(A) >= 0$).
- CP maps can be expressed in their *Kraus decomposition* as $
    T(rho) = sum_k A_k rho A_k^dagger,
$ where the ${A_k}$ are *Kraus operators*.
- A *completely positive trace preserving (CPTP)* map is a CP map $T$ such that $tr(T(A)) = tr(A)$ for all $A in B(HH)$. In particular, CPTP maps map density operators to density operators, and describe the most general evolution of a quantum system.
- If $A$ has Kraus decomposition $T(rho) = sum_k A_k rho A_k^dagger$, then the Kraus operators satisfy $sum_k A_k^dagger A_k = II$.
- The *transfer matrix* of a quantum channel with Kraus operators ${A_k}$ is $
    E = sum_k A_k tp overline(A_k),
$ where $overline(A_k)$ is the entry-wise complex conjugate of $A_k$.
- Given a set of *Lindblad operators* ${L_i: i in [M]}$ (which are arbitrary square matrices), define the Kraus operators $
    A_0 & = sqrt(I - dif t sum_(i = 1)^M L_i^dagger L_i), \
    A_i & = sqrt(dif t) L_i, quad i in [M],
$ where $dif t$ is infinitesimal. The CP map $T$ defined by these Kraus operators satisfies $T(rho) = rho + O(dif t)$, which gives $
    (dif rho)/(dif t) & = sum_i L_i rho L_i^dagger - 1/2 (sum_i L_i^dagger L_i rho + rho sum_i L_i^dagger L_i) \
    & = sum_i (L_i rho L_i^dagger - 1/2 {L_i^dagger L_i, rho})
$ Given that the system evolves according to a Hamiltonian $H$, we obtain the *Lindblad equation* $
    (dif rho)/(dif t) = -i [H, rho] + sum_i (L_i rho L_i^dagger - 1/2 {L_i^dagger L_i, rho}),
$ where $dif rho = T(rho) - rho$.
- Physically, evolution according to the Lindblad equation corresponds to when we couple the system of interest to an ancilla through an infinitesimal interaction / evolution with a Hamiltonian which couple both systems, then take the trace over the ancilla. This only makes sense when the ancillary system cannot interact with the system of interest anymore at later times.
- CPTP maps and the Lindblad equation are the two ways of describing the evolution of a quantum system: the Lindblad equation is the continuous version of a CPTP map. They are the most general evolution of a many-body quantum system coupled to a part (the environment) which we take the trace over.
- We can connect the purification of the Lindblad equation to MPS in the following way: the Lindblad equation is the limit of a CPTP map (quantum channel), as shown above. Let $T(rho) = sum_i A_i rho A_i^dagger$ be a quantum channel with Kraus operators $A_i$. Say we start with an initial state $rho_0 = ket(psi_0) bra(psi_0)$. Then a purification of the channel applied $N$ times to $rho_0$, $T^N (rho_0)$ is $
    ket(psi_N) = sum_(i_1, ..., i_N) A_(i_1) cdots A_(i_N) ket(psi_0) tp ket(i_1) ... ket(i_N).
$ The channel acts as $ket(psi_0) |-> sum_i A_i ket(psi_0) tp ket(i)_E$ followed by taking the partial trace over the environment $E$ (this is easy to check). $ket(psi_N)$ is the resulting state if we apply the channel $N$ times without taking the trace.
- $ket(psi_N)$ has the form of a matrix product state (MPS). This is called an *unravelling/purification* of the channel $T$. So CPTP maps/Lindblad equation give a dual description of MPS.
- The physical interpretation of unravelling is: consider an atom in a cavity/box coupled (interacting with) to some light modes. Every time a Kraus operator $A_i$ is applied, a photon (light mode) in the state $ket(i)$ escapes the cavity. Tracing out the light modes gives the Lindblad equation/CPTP maps. The purification is the dual description of MPS that tells us the wave function of the escaped light modes.
- Taking the limit means we purification of the Lindblad equation can be expressed as a continuous MPS. The purification of the Lindblad equation is $
    ket(psi(t)) = hat(T) exp(integral_0^t (Q tp I + sum_i L_i tp psi_i^dagger (x)) dif x) ket(psi_0) ket(Omega),
$ where $Q = i H - 1/2 sum_i L_i^dagger L_i$, $psi_i^dagger (x)$ is a creation operator of a particle/photon of type $i$ at time $x$ and $hat(T) exp$ is a time-ordered exponential.
- A quantum channel $T$ is called *ergodic* if for all $rho in S(HH)$, ${T^n (rho): n >= 0}$ spans the space of density matrices $S(HH)$. Equivalently, there is $m in NN$ such that $forall n >= m$, ${A^(i_1) A^(i_2) ... A^(i_n)}$ spans the full matrix algebra (this corresponds to injective MPS via the purification procedure above).
- The *quantum Perron-Frobenius theorem* states that if a quantum channel $T$ is ergodic, then there is a unique eigenvalue $lambda = 1$, and all other eigenvalues are roots of unity (these correspond to limit cycles), or satisfy $abs(lambda) < 1$. In particular, ergodic channels have a unique fixed point (called the *steady state*).
- If $T$ is ergodic with fixed point $rho^*$, then the long time limit of applying the channel to any state $rho in S(HH)$ is $
    lim_(n -> oo) T^n (rho) = rho^*.
$
- The above properties for quantum channels also hold for the Lindblad equation, since it is a limit of a quantum channel.

== The second exam question

*The second exam question is on monogamy of entanglement and the area law.*

Notes from the revision class:
- give an example of a monogamous system. explain why this frustration is relevant in context of many-body physics (it gives rise to interesting behaviour).
- if everything interacts with everything in infinite dimensional system, monogamy implies reduced density matrices are separable
- TODO: phase diagrams classified by symmetries and breaking of them
- TODO: permutation-invariant Hamiltonian, each qubit interacting with each other one, what is the (reduced density matrix of the) ground state
- in words, why is monogamy of entanglement related to the area law of entanglement, and why does area law of entanglement connect with tensor networks (don't need to write pages, just a few lines. don't need to prove things for this bit)

Key points:
- *Monogamy of entanglement* is the property that if two parties/systems are maximally entangled, then they cannot be entangled with another party/system. Conversely, if three parties/systems are pairwise entangled, then none of them are maximally entangled.
- We can more generally describe monogamy as: there is only a finite amount of entanglement that a system can share with other parties: the more parties the entanglement is shared between, the smaller the individual entanglement between the system and any of those other parties.
- The monogamy property of entanglement is extremely relevant for understanding the physics of many-body systems, as it tells us that ground states in high-dimensional systems will exhibit very low entanglement. Consequently, low-dimensional quantum many-body systems such as quantum spin chains or 2-D quantum spin systems will have the most interesting quantum properties, as the ones in higher dimensional systems are too close to seperable states for entanglement to play a central role.
- In the case of infinite-dimensional systems: if every qubit interacts with every other (neighbouring) qubit (so each (neighbouring) qubit pair is entangled), then monogamy implies that the reduced density matrices are separable, since the entanglement is shared between infinitely many parties, so in fact there is no entanglement between each qubit pair.
- Monogamy leads to *frustration* effects: certain local interactions cannot be satisfied simultaneously.
- Frustration is what leads to interesting physics (e.g. phases of matter, phase transitions) in many-body systems: it is due to the fact that the Hamiltonian is a sum of local terms, some of which do not commute. If they did commute, then the ground state would simply be an eigenstate of each term.
- Monogamy and frustration means that interactions between qubits are generally restricted to nearest neighbours (so correlations are localised). This imposes many constraints on the set of allowed wave functions, and so the manifold (called the *Kaihler manifold*) of physically relevant states, within the full $2^N$-dimensional Hilbert space of possible states, is low dimensional.
- This means that in a gapped phase of matter (meaning there is gap between leading and sub-leading eigenvalues in the limit as system size $-> oo$), we have an area law for entanglement: entanglement entropy of qubits in a region scales with the size of the boundary of the region.
- Moreover, the tensor network states (e.g. MPS, PEPS) parametrise (span) this Kaihler manifold.
- An *example of a monogamous system*: the system governed by a *Heisenberg Hamiltonian*, which is given by $
    H = sum_i X_i X_(i + 1) + Y_i Y_(i + 1) + Z_i Z_(i + 1).
$ (This is also an XXZ Hamiltonian with nearest neighbour interactions, up to a factor of $-1$.) If there are periodic boundary conditions, $H$ is translation-invariant, so its ground state is as well (assuming that it is unique). If the system size is two qubits (so $i$ ranges from $1$ to $2$), then the ground state is the singlet $1/sqrt(2) (ket(0) ket(1) - ket(1) ket(0))$. This is maximally entangled since its reduced density matrix is maximally mixed. Hence, if we now increase the system size to $3$ qubits, the system is now frustrated: the ground state of the $3$-qubit system wants to consist of singlets between each pair of the qubits (each pair has a Heisenberg interaction, so we want the reduced density matrix of each pair to be as close to the singlet $1/sqrt(2) (ket(0) ket(1) - ket(1) ket(0))$); however, monogamy prevents this. Here, the frustration in the system due to the fact that the Hamiltonian is a sum of local terms, some of which do not commute. (This is what causes frustration in the general case as well.)
- The diagram below shows the possible reduced density matrices of the ground state of an XXZ Hamiltonian. The big triangle is the set of all reduced density matrices. The diamond is the set of separable states. The blue line encloses the set of all translation-invariant reduced density matrices when the XXZ Hamiltonian acts on a 1D lattice. The red line encloses the set of all reduced density matrices when the XXZ Hamiltonian acts on a 2D lattice. As the dimension tends to infinity, there is more and more frustration of more neighbours, and the set of reduced density matrices approaches the separable states (the diamond). Note each of the sets are convex. The point $(-1, -1)$ corresponds to the singlet $1/sqrt(2) (ket(01) - ket(10))$. #figure(image("convex-set.png", width: 60%))

Monogamy of entanglement and the area law are related to Lieb-Robinson bounds. Here are some key points:

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

== The third exam question

*The third exam question is on classifying phases of matter.*

Notes from the revision class:
- stick to 1d quantum spin chains. start with symmetry which Hamiltonian commutes with, perturbing Hamiltonian results in phase transition corresponding to breaking a symmetry, also topological phases and projective representations of the symmetry group
- be able to reproduce the AKLT example: on physical and virtual levels, have SO(3) and SU(2) symmetries which pull through the projector

Key points:
- If we have a PEPS and on the physical level it transforms according to (linear) representations of a symmetry group $G$, then the virtual level must transform according to projective representations of $G$.
- The different phases of matrix product states are indexed by the second group cohomology class $cal(H)^2 (G, U(1))$ of the symmetry group $G$, and can be determined using projective representations $R$ of $G$ (which satisfy $R(g h) = e^(i phi(g, h)) R(g) R(h)$ where $phi(g, h) in RR$). $cal(H)^2 (G, U(1))$ labels all projective representations of $G$.
- The *Landau paradigm* says that given a many-body system for which the Hamiltonian has a certain global symmetry (given by a group $G$: $[U(g)^(tp L), H] = 0$ for all $g in G$), the different phases of matter are characterised by the ways in which this symmetry can be broken. There is a subgroup $H$ of $G$ which characterises the unbroken symmetries. The ground state $ket(psi_0)$ in a phase corresponding to a subgroup $H$ satisfies $U(g)^(tp L) ket(psi_0) = ket(psi_0)$.
- If we perturb the parameters of the system Hamiltonian, the ground state which shares the same symmetry as the Hamiltonian will remain in the same phase of matter, until a phase transition occurs, which corresponds to breaking a symmetry (i.e. the ground state no longer shares the same symmetry as before and there is a ground state degeneracy).
- In particular, for 1D quantum spin systems, phases are completely characterised by subgroups and co-cycles of the subgroups.
- The Landau paradigm implies all information of system (and about which phase state is in) is encoded in entanglement features of the tensor network state describing that system.
- The *AKLT state* is the 1D PEPS with entangled pair state $ket(phi) = ket(01) - ket(10)$ and projector $cal(P): CC^(2 times 2) -> CC^3$ given by $
    cal(P) = ket(tilde(1)) bra(00) + ket(tilde(0)) 1/sqrt(2) (bra(01) + bra(10)) + ket(-tilde(1)) bra(11)
$
- On periodic boundary conditions, the AKLT state is $"SO"(3)$ symmetric (but it is not symmetric on open boundary conditions): the spin vector on the spin-1 particle $(S_X, S_Y, S_Z)$ is given by $
    S_X & = 1/sqrt(2) (ket(tilde(0)) (bra(tilde(1)) + bra(-tilde(1))) + (ket(tilde(1)) + ket(-tilde(1))) bra(tilde(0))) = 1/sqrt(2) mat(0, 1, 0; 1, 0, 1; 0, 1, 0) \
    S_Y & = 1/sqrt(2) i (ket(tilde(0)) (bra(tilde(1)) - bra(-tilde(1))) + (ket(-tilde(1)) - ket(tilde(1))) bra(tilde(0))) = 1/sqrt(2) mat(0, -i, 0; i, 0, -i; 0, i, 0) \
    S_Z & = ket(tilde(1)) bra(tilde(1)) - ket(-tilde(1)) bra(-tilde(1)) = mat(1, 0, 0; 0, 0, 0; 0, 0, -1)
$ Then it is straightforward to show that $
    S_Z cal(P) & = cal(P) 1/2 (Z_1 + Z_2) \
    S_X cal(P) & = cal(P) 1/2 (X_1 + X_2) \
    S_Y cal(P) & = cal(P) 1/2 (Y_1 + Y_2)
$ So the spin operators pull through $cal(P)$, and so since $ket(phi) = ket(01) - ket(10)$ is $"SU"(2)$-invariant (meaning that $(U tp U) ket(phi) = ket(phi)$ for all $U in "SU"(2)$), the AKLT state is $"SO"(3)$-invariant (meaning $U^(tp L) ket(psi_"AKLT") = ket(psi_"AKLT")$ for all $U in "SO"(3)$), since $"SU"(2)$ is the double cover of $"SO"(3)$.
- The AKLT state can also be written as the MPS $ket(psi(A))$, where $A_i = sigma_i$ for each $i in [3]$ (and $sigma_i$ are the Pauli matrices).
- The AKLT state is the ground state of the spin 1 Hamiltonian $
    H_"AKLT" = sum_i (1/2 vd(S)_i dot vd(S)_(i + 1) + 1/6 (vd(S)_i dot vd(S)_(i + 1))^2 + 1/3),
$ where $vd(S) = (S_X, S_Y, S_Z)$.
- For the AKLT state example, the symmetries can be realised in a projective way: the initial (virtual state) possesses a symmetry (via projective representations of a group $G$), and the symmetries "pull through" (commute with) the projector, meaning the projected PEPS state also possesses the symmetry (via linear representations of the same group $G$).
- This means the AKLT state is in a *symmetry-protected topological (SPT)* phase.

You should be able to reproduce the FTMPS:
#definition[
    An MPS $ket(psi(A))$ is in *left-canonical form* if $
        sum_(j = 0)^(d - 1) A_j^dagger A_j = II_D
    $ In TNN, this is written as
    #figure(
        image("left-canonical-tnn.png", width: 20%)
    )
]<def:mps.left-canonical-form>
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
    Let $ket(psi(A))$ be an MPS in left-canonical form. $ket(psi(A))$ is *injective* if the identity matrix is the left eigenstate of the transfer matrix with eigenvalue $1$. Equivalently, the leading (largest in absolute value) eigenvalue of the transfer matrix is $1$, and all other eigenvalues have modulus $< 1$.

    Equivalently, for $ket(psi(A))$ of bond-dimension $D$, $
        exists m in NN "s.t." {A^(i_1) ... A^(i_m)}
    $ spans the full matrix algebra (the vector space of $D times D$ matrices).
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

    For the $==>$ direction (fixed point $rho$ is unique by quantum Perron-Frobenius since the MPS are injective)
    #figure(
        image("ft-mps-2.jpeg")
    )
]

== The fourth exam question

*The fourth exam question is on dualities*.

Notes from the revision class:
- Kramers-Wannier duality for the Ising model in transverse magnetic field. what does a duality transformation mean, how does it affect the symmetries
- what happens to the spectrum of the Hamiltonian
- phase is mapped to symmetry-broken phase
- be able to reproduce the Kramers-Wannier duality in terms of MPO
- gain extra marks for reproducing in 2D
- how Ising model is related to toric code (the Kramers-Wannier maps the Ising Hamiltonian to the toric code Hamiltonian)

#definition[
    An *order parameter* is any observable which transforms non-trivially under the global symmetry operation (i.e. doesn't commute with the symmetry), has zero expectation value in the symmetric phase, and a non-zero expectation value in the symmetry-broken phase.
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
        ket(psi_0) = tp.big_i ket(0)_i, quad ket(psi_1) = tp.big_i ket(1)_i.
    $ Clearly, these two states are transformed into each other by the action of the symmetry operator $O_X$. Thus, this phase is called the *ferromagnetic phase* or the *symmetry-broken phase*. Any linear combination of these two states is also a ground state, so in particular the GHZ state $ket(psi_0) + ket(psi_1)$ is a ground state. The GHZ states are non-injective MPS with bond dimension $2$.

    Thus, the phase transition happens at $lambda = 1$, where the ground state changes from a unique symmetric state to a non-unique symmetry-broken state.

    For this example, the order parameter is $O_Z = tp.big_i Z_i$: we have $O_Z O_X = -O_X O_Z$ (anti-commutes); also, $braket(psi, O_Z, psi) = 0$, $braket(psi_0, O_Z, psi_0) = 1$, and $braket(psi_1, O_Z, psi_1) = plus.minus 1$.
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
    where (the $plus.square$ and $square.filled$ should be swapped in the below and above)
    #figure(
        image("kw-ghz.png", width: 70%)
    )
    This tensor network involves GHZ tensor in the $X$ and $Z$ basis: $
        ket("GHZ"_Z) & = ket(000) + ket(111), \
        ket("GHZ"_X) & = (H tp H tp H) ket("GHZ"_Z) = ket(+++) + ket(---).
    $ Explicitly, the dual of the 1D Ising Hamiltonian under the Kramers-Wannier transformation is $
        H_2 = -sum_i Z_(i + 1 \/ 2) + lambda X_(i - 1 \/ 2) X_(i + 1 \/ 2),
    $ which also has a $ZZ_2$ symmetry (realised by a different representation of $ZZ_2$). The reason for the $plus.minus 1 \/ 2$ here is that the operators live on the dual lattice (so e.g. $X_(i + 1 \/ 2)$ lives between sites $i$ and $i + 1$).

    We can also add a boundary condition to the Kramers-Wannier transformation, by adding a Pauli matrix to the MPO (this results in twisted boundary conditions), as in the diagram below (again, the $plus.square$ and $square.filled$ should be swapped):
    #figure(
        image("kw-boundary-conditions.png", width: 70%)
    )
]
#example[
    The Kramers-Wannier transformation can be generalised to two dimensions. The dual model is $
        -sum_(gen(i j)) X_i X_j - lambda sum_i Z_i quad <-> -sum_(gen(i j)) X_gen(i j) - sum_(v "vertices") lambda_v product_(gen(i j) in v) Z_gen(i j)
    $ where $gen(i j)$ is the set of nearest-neighbour pairs of qubits. We can use PEPOs (projected entangled pair operators) to represent the Kramers-Wannier transformation in 2D (the first item in the diagram is the Kramers-Wannier transformation as a PEPO) - $circle$ represents a GHZ tensor in the $X$ basis with 5 qubits, $bot$ represents a GHZ tensor in the $Z$ basis with 3 qubits:
    #figure(
        image("kw-2d.png", width: 70%)
    )
]
#definition[
    We say states which cannot be transformed into each by any constant depth local circuit are in distinct *topological phases*, or have distinct *topological order*.
]
#remark[
    The 2D Kramers-Wannier transformation maps the 2D Ising Hamiltonian to the toric code Hamiltonian. For details of the toric code, see `kw-toric-code.pdf`.
]