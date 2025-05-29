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

The first exam question is on mixed states and the Lindblad equation.

Notes from the revision class:
- understand mixed states, the Lindblad equation (be able to write it down), what it means, what is the long time limit of applying it over and over again (what happens to the density matrix in long time limit, what is the unique density matrix that emerges in this limit). connection of purification of Lindblad equation to MPS. just use regular MPS (not continuous). so take MPS with an epsilon
- Lindblad equation is limit of a CP map, and can purify CP map as MPS (can argue this way)
- how to show Lindblad equation has unique fixed point (quantum Perron-Frobenius says if ergodic then unique fixed point)
- ergodic: $exists m$: $forall n >= m$, ${A^(i_1) A^(i_2) ... A^(i_n)}$ spans the full matrix algebra (corresponds to injective MPS)


== The second exam question

The second exam question is on monogamy of entanglement and the area law.

- Notes from the revision class:
    - give an example of a monogamous system. explain why this frustration is relevant in context of many-body physics (it gives rise to interesting behaviour).
    - if everything interacts with everything in infinite dimensional system, monogamy implies reduced density matrices are separable
    - phase diagrams classified by symmetries and breaking of them
    - permutation-invariant Hamiltonian, each qubit interacting with each other one, what is the (reduced density matrix of the) ground state
    - in words, why is monogamy of entanglement related to the area law of entanglement, and why does area law of entanglement connect with tensor networks (don't need to write pages, just a few lines. don't need to prove things for this bit)

Key points:
- *Monogamy of entanglement* is the property that if two qubits are maximally entangled, then they cannot be entangled with another qubit. Conversely, if three qubits are pairwise entangled, then none of them are maximally entangled.
- We can also describe monogamy as: there is only a finite amount of entanglement that a spin/qudit can share with other parties: the more parties the entanglement is shared between, the smaller the individual entanglement between the spin and any of those other parties.
- The monogamy property of entanglement is extremely relevant for understanding the physics of many-body systems, as it tells us that ground states in high-dimensional systems will exhibit very low entanglement. Consequently, low-dimensional quantum many-body systems such as quantum spin chains or 2-D quantum spin
systems will have the most interesting quantum properties, as the ones in higher dimensional systems are too close to seperable states for entanglement to play a central role.
- In the case of infinite-dimensional systems: if every qubit interacts with every other qubit (so each qubit pair is entangled), then monogamy implies that the reduced density matrices are separable, since the entanglement is shared between infinitely many parties, so in fact there is no entanglement between each qubit pair.
- Monogamy leads to *frustration* effects: certain local interactions cannot be satisfied simultaneously.
- Frustration is what leads to interesting physics (e.g. phase transitions) in many-body systems.
- Monogamy and frustration means that interactions between qubits are generally restricted to nearest neighbours. This imposes many constraints on the set of allowed wave functions, and so the manifold (called the *Kaihler manifold*) of physically relevant states, within the full $2^N$-dimensional Hilbert space of possible states, is low dimensional.
- This means that in a gapped phase of matter (meaning there is gap between leading and sub-leading eigenvalues in the limit as system size $-> oo$), we have an area law for entanglement: entanglement entropy of qubits in a region scales with the size of the boundary of the region. Moreover, the tensor network states (e.g. MPS, PEPS) parametrise this manifold.
- An *example of a monogamous system*: the system governed by the *Heisenberg Hamiltonian*, which is given by $
    H = sum_i X_i X_(i + 1) + Y_i Y_(i + 1) + Z_i Z_(i + 1).
$ If the system size is two qubits (so $i$ ranges from $1$ to $2$), then the ground state is the singlet $1/sqrt(2) (ket(0) ket(1) - ket(1) ket(0))$. This is maximally entangled since its reduced density matrix is maximally mixed. Hence, if we now increase the system size to $3$ qubits, the system is now frustrated: the ground state of the $3$-qubit system wants to consist of singlets between each pair of the qubits (each pair has a Heisenberg interaction, so we want the reduced density matrix of each pair to be as close to the singlet $1/sqrt(2) (ket(0) ket(1) - ket(1) ket(0))$); however, monogamy prevents this. Here, the frustration in the system due to the fact that the Hamiltonian is a sum of local terms, some of which do not commute. (This is what causes frustration in the general case as well.)

- classifying phases of matter:
    - stick to 1d quantum spin chains. start with symmetry which Hamiltonian commutes with, perturbing Hamiltonian results in phase transition corresponding to breaking a symmetry, also topological phases and projective representations of the symmetry group
    - be able to reproduce the AKLT example: on physical and virtual levels, have SO(3) and SU(2) symmetries which pull through the projector
- dualities:
    - Kramers-Wannier duality for the Ising model in transverse magnetic field. what does a duality transformation mean, how does it affect the symmetries
    - what happens to the spectrum of the Hamiltonian
    - phase is mapped to symmetry-broken phase
    - be able to reproduce the Kramers-Wannier duality in terms of MPO
    - gain extra marks for reproducing in 2D
    - how Ising model is related to toric code (the Kramers-Wannier maps the Ising Hamiltonian to the toric code Hamiltonian)

uniqueness of the fixed point from the proof of FTMPS is from quantum Perron-Frobenius since the MPS are injective

more questions on tensor networks than last year. less about Lieb-Robinson bounds