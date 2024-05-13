== Observables

- Observables/measurements represented by Hermitian operators $hat(A)$.
- Hermitian conjugate is defined as $<A psi, chi> = <psi, A^dagger chi>$. Matrix representation is $(A^*)^t$.
- outcome of measurement is eigenvalue of $hat(A)$. Spectral representation is $hat(A) = sum_i alpha_i |i><i|$ for eigenvalues $alpha_i$ and eigenstates $|i>$.
- If $hat(B) = sum_j beta_j |j><j|$ and $[hat(A), hat(B)] != 0$ then measuring $hat(A)$ and $hat(B)$ will not result in state collapsing to simultaneous eigenstate.

== Mixed states vs pure states

- Pure state: definite quantum mechanical state.
- Mixed state is ensemble of pure states, each with associated classical probability of system being in that state.
- e.g. $|psi> = 1/sqrt(2) (|0> + |1>) = |+>$ is pure, mixed state is ${(1/2, |0>), (1/2, |1>)}$. If $hat(B)$ has eigenstates $|+>$ and $| - >$ with eigenvalues $1$, $-1$ (i.e. $sigma_1$), then measuring $hat(B)$ on $|+>$ then result will always be $1$. But measuring $hat(B)$ on mixed state will randomly yield $1$ or $-1$ with equal probability.
- Double slit experiment analog: mixed state is closing one slit in half of the cases, closing the other in the other half. Pure state: electron goes through both slits at the same time.
  
== Density matrix

- $hat(rho) = |psi><psi|$ for pure state $|psi>$.
- $hat(rho) = sum_i p_i |psi_i><psi_i|$ for mixed state ${(p_i, |psi_i>)}$.
- For any density matrix, $tr(hat(rho)) = 1$ but $tr(hat(rho)^2) = 1$ iff $hat(rho)$ is pure state.
- Spectral decomposition: $hat(A) = sum_i alpha_i |i><i| = sum_i alpha_i P_i$. Probability of measuring result $alpha_i$ is $tr(rho P_i)$.

*Bloch sphere not as important to revise.*

== Bipartite systems

- Entangled vs separable states.
- Separable states: $|psi> times.circle |phi>$.
- Entangled: sum of separable states which cannot be factorised into a separable state.
- If $|psi> = 1/sqrt(2) (|0> times.circle |1> + |1> times.circle |0>)$, it has density matrix $1/2 (|01><01| + |01><10| + |10><01| + |10><10|)$.
    - If Alice measures with operator $A = |0><0| - |1><1|$ then if her measurement is $1$ then state collapses to $|01>$. If her measurement is $-1$ then state collapses to $|10>$.
    - Density matrix afterwards is $1/2 |01><01| + 1/2 |10><10|$ if know Alice has measured but we don't know what she measured.
    - Reduced density matrix for Bob:
        - Before measurement: $tr_A (rho_"before") = 1/2 (|1><1| + |0><0|)$ (only states kept are those where A and B bits agree). This is the density matrix of a mixed state.
        - After measurement: $tr_B (rho_"after") = 1/2 (|1><1| + |0><0|)$ i.e. same as before measurement.
        - So Bob's reduced density matrix is not affected by Alice's measurement.

== Entanglement applications

- Don't learn QKD etc. by heart, learn the key ingredients. They are:
- 1. We can entangled information into an existing state: e.g. start with product state $|psi> times.circle |beta_00>$, then apply CNOT on first two qubits, this is used in teleportation.
- 2. Quantum systems do not have local realism: since it is possible to have measurement operators which do not commute.

Don't expect heavy computations about entropy chapter.