#let ket(arg) = $lr(| #h(0.2pt) arg #h(0.2pt) angle.r, size: #0%)$
#let bra(arg) = $lr(angle.l #h(0.2pt) arg #h(0.2pt) |, size: #0%)$
#let braket(..args) = $angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r$
#let tp = sym.times.circle

= Entanglement theory

for exam:
- entanglement theory (first chapter):
    - Schmidt numbers/entanglement spectrum which are eigenvalues of $rho_A$. This is an entanglement monotones.
    - gives entanglement entropy S(rho), which gives measure of how mixed rho is.
    - mixed states and their evolutions, CP maps $sum_k A_k rho A_k^dagger$, A_k are Kraus operators. this is an evolution of a mixed state. it is the most general evolution of a many-body system coupled to a part, which we take the trace over.
    - continuous version of this evolution: $(d rho)/(d t) = -i [H, rho] + sum_i L_i rho L_i^dagger - 1/2 {L_i^dagger L_i, rho}_+$ (the Lindblad equation). these are the two ways of describing evolution of a system
    - CP maps and Lindblad equation give dual description of matrix product states (MPS): unravellings (also called purification) (physical meaning is we have $chi$-dimensional system sitting in a box. Lindblad equation/CP maps describes evolution if system is coupled (interacting) with light modes which escape from the box)
    - fixed points of CP maps and Lindblad equation (quantum version of stochastic matrix and master equation). fixed points are unique if there is quantum version of ergodicity - systems evolve to steady state

- monogamy of entanglement (second chapter):
    - monogamy: if two qubits are maximally entangled, then they cannot be entangled with another qubit; conversely, if three are pairwise entangled, then none of them are maximally entangled
    - example of monogamy: with Heisenberg Hamiltonian: $H = sum_i X_i X_(i + 1) + Y_i Y_(i + 1) + Z_i Z_(i + 1)$. if system is two qubits, ground state of this is $1/sqrt(2) (ket(0) ket(1) - ket(1) ket(0))$ which is maximally entangled since reduced density matrix is maximally mixed. Frustration is due to fact that Heis Hamiltonian is sum of terms which don't pairwise commute with each other. non-commuting terms lead to interesting physics (e.g. phase transitions)
    - monogamy leads to frustration
    - monogamy of entanglement means manifold (called the Kaihler manifold) of physical states (within full Hilbert space of dimension 2^n) is low dimensional. in a gapped phase of matter, we have an area law for entanglement entropy within this manifold. tensor networks (e.g. MPS, PEPS) parametrise this manifold, i.e. span this manifold (note the manifold is not a Hilbert space).
    - Hamiltonian is usually translation invariant, so there is eigenspace which also has this symmetry. (this is the ground state eigenspace if GS is unique)

- Lieb-Robinson bounds (third chapter)
    - there will be no (or at most very superficial) questions about the bounds themselves
    - bounds show that there is finite speed at which correlations can spread (this is hard to prove)
    - gives notion of locality: local effect takes time to affect points far away from it
    - locality: effect affects spins far away noticeably (not exponentially) after a time related to the speed of the correlations.
    - bounds allow you to prove that in gapped phase, all ground states satisfy an area law
    - e.g. in one dimensional spin chain, for reduced density matrix $A$ (where $A$ is 1D region of the qubits), then $S(rho_A) <= r partial A$, for $r$ a constant. In 1D, $partial A$ is bounded by constant independent of $A$.
    - Lieb Robinson bounds give new way of defining what phases of matter are
    - phase of matter defined in terms of adiabatic evolution. $H = sum_alpha x_alpha h_alpha, [h_a, U(g)^(tp L)] = 0$ for all $g in G$ a group. if you vary parameters $x_alpha$ and gap does not close (is non-zero), then these ground states are in the same phase
    - states within the same phase can be transformed into each other by quasi-adiabatic evolution that do not change the area law (sub linear (in system size) depth quantum circuit that connects the ground states to each other). s only thing that distinguishes ground states in same phase is some change of local physics.
    - can draw phase diagram.
    - to go to one phase from another, have to cross phase transition, which means entanglement is reordered. Lieb Robinson bounds show that to go one state in one phase to state in different phase, need quantum circuit that is at least linear (in system size) depth
    - so can think of phases of matter as GS instead of Hammiltonians
    - means we can consider states instead of Hamiltonians
    - Lieb Robinson bounds show in 1D, manifold is spanned by MPS, so can completely characterise 1D quantum spin chains by MPS

- tensor networks (fourth chapter)
    - can characterise states in terms of entangled pairs. o\~o o\~o o\~o ... o\~o. One of these o\~o states is $sum_(i = 1)^chi ket(i) ket(i)$. $sum_(i = 1)^chi ket(tau) ket(i)$ (MPS). 1D case
    - in 2D case, analogue is PEPS (projected entangled pair states)
    - motivation is for solving many-body schrodinger equation, classical complexity of doing this scales exponentially with system size.
    - TNs give angle to tackle this problem.
    - can encode Hamiltonian H(x) into tensor A^i with three legs (1D) or 5 legs (2D)
    - be able to give examples of MPS and PEPS
    - Landau paradigm: all about symmetries. all information of system (and about which phase state is in) is encoded in entanglement features of the tensor networks
    - fundamental theorem of MPS: for injective MPS $ket(psi(A))$, $ket(psi(A)) = ket(psi(B)) "iff" exists phi, X "s.t." X A X^(-1) = e^(i phi) B$.
    - symmetries can be realised in a projective way (symmetry protected topological phases of matter (SPT) - simplest example is cluster state, another example is AKLT state where $A^i = sigma_i$ are Paulis)
    - dualities: H(x) <-> hat(H)(x) (depending on same parameters x, may have different symmetries) are dual if they have same phase diagram. dualities given by intertwiners in matrix product operator form and are independent of the GS. matrix product operator preserves the spectrum of the Hamiltonians
    - can distinguish between topological vs non-topological phases as they have very different entanglement features
    - landau paradigm says there is global symmetry (group G), all possible phases of mmatter are characterised by ways of breaking that symmetry, there is subgroup H which characterises unbroken symmetries, so classifies phases of matter
    - so for 1D quantum spin systems, phases are completely characterised by the subgroups and co-cycles of the subgroups
    - projective representations, second homology $H^2 (H, U(1))$
    - should be able to reproduce Kramers-Wa... transformation : maps between Hamiltonians which have $G = ZZ_2$ symmetry. so in this case, only two phases of matter
    - in each phase, there is unique dual Hamiltonian where all symmetries are spontaneously broken.
    - how to generalise to 2 dimensions: building blocks: GHZ state: 4 legs: $sum_i ket(i i i i)$ (GHZ in Z basis). can also get GHZ in X basis by applying Hadamard transformation
    - you should be able to reproduce the construction of the intertwiners in 1 and 2 dimensions.

exam questions will be very simple. it's important that you get the ideas and able to reproduce toy examples (e.g. AKLT), construct intertwiners, reproducing FT of MPS, understand the symmetries of the AKLT state, understand the Lindblad equation, what is unravelling, how it's connected to MPS, understand what monogamy is and what it implies (frustration). these notes are based on exam questions