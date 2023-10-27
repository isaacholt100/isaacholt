#import "../../template.typ": template
#show: template

#let hbar = $planck.reduce$
#let ip(a, b) = $angle.l #a, #b angle.r$
#let ket(arg) = $lr(| arg angle.r)$
#let bra(arg) = $lr(angle.l arg |)$
#let braket(..args) = $lr(angle.l #args.pos().join("|") angle.r)$
#let conj(arg) = $arg^*$
#let expected(arg) = $angle.l arg angle.r$

= Quantum mechanics essentials

== States and wave functions

- A particle's position on the real line is given by a wave function $psi(x, t) -> CC$.
- Probability of finding particle in $(a, b)$ is $ P(a, b) = integral_a^b |psi(x, t)|^2 dif x $
- Time-evolution of wave function given by *Schrodinger equation*: $ i hbar (diff psi(x, t)) / (diff t) = -hbar^2 / (2m) diff^2 / (diff x^2) psi(x, t) + V(x) psi(x, t) = hat(H) psi(x, t) $ where $ hat(H) = hat(K) + hat(V) $ is the Hamiltonian operator.
- Schrodinger equation is *linear*, so any linear combination of solutions is another solution (*principle of superposition*).
- An inner product is defined on the space of solutions to the Schrodinger equation: $ ip(psi, phi) = integral_(-oo)^oo psi^*(x, t) phi(x, t) dif x $
- *Hilbert space*: vector space with inner product satisfying $ ip(psi, a phi_1 + b phi_2) = a ip(psi, phi_1) + b ip(psi, phi_2) " and " ip(psi, phi) = ip(phi, psi)^*$
- Write $ket(psi)$ (a *ket*) for vector in Hilbert space $cal(H)$ corresponding to wave function $psi$.
- Write $bra(phi)$ (a *bra*) for *dual* vector in $cal(H^*)$.
- *Dirac (bra-ket) notation*: $ braket(phi, psi) := ip(phi, psi) = integral_(-oo)^oo phi^* (x, t) psi(x, t) dif x $
- *Dual* of vector space $V$ is set of linear functionals from $V$ to $CC$: $ V^* := {Phi: V -> CC: forall (a, b) in CC^2, forall (z, w) in V^2, quad Phi(a underline(z) + b underline(w)) = a Phi(underline(z)) + b Phi(underline(w)) } $ We have $dim(V^*) = dim(V)$.
- If $V = CC^n$, can think of vectors in $V$ as $n times 1$ matrices and vectors in $V^*$ as $1 times n$ matrices.
- A quantum mechanical system is described by a ket $ket(psi)$ in Hilbert space $cal(H)$. For all $ket(psi), ket(phi) in cal(H)$:
    - $forall (a, b) in CC^2, a ket(psi) + b ket(phi) in cal(H)$
    - Inner product of $ket(psi)$ with $ket(phi)$ is a complex number written as $braket(psi, phi)$. It is Hermitian: $braket(psi, phi) = braket(phi, psi)^*$.
    - Inner product is *sesquilinear* (linear in the second factor, anti-linear in the first). For $ket(phi) = c_1 ket(phi_1) + c_2 ket(phi_2)$:
    $ braket(psi, phi) & = c_1 braket(psi, phi_1) + c_2 braket(psi, phi_2) \ braket(phi, psi) & = c_1^* braket(phi_1, psi) + c_2^* braket(phi_2, psi) $
    - $braket(psi, psi) >= 0$ and $braket(psi, psi) = 0 <==> ket(psi) = 0$.
    - States which differ by only a normalisation factor are physically equivalent: $ forall c in CC^*, quad ket(psi) tilde.op c ket(psi) $ So we normally assume that a state $ket(psi)$ has norm $1$: $norm(ket(psi)) = 1$.
- Note that the state labelled zero, $ket(0)$, is not equal to the zero state (the $0$ vector).
- If $hat(A)$ is linear opearator then $hat(A) (a ket(psi) + b ket(phi)) = a \(hat(A) ket(psi)\) + b \(hat(A) ket(phi)\)$
- Products and combinations of linear operators are also linear operators.
- *Adjoint (Hermitian conjugate)* of $hat(A)$, $hat(A)^dagger$ is defined by $ bra(psi) (hat(A)^dagger ket(phi)) = conj((bra(phi) (hat(A) ket(psi)))) $
- $hat(A)$ is *self-adjoint (Hermitian)* if $hat(H)^dagger = hat(H)$. Self-adjoint operators correspond to *observables* (measurable quantities) since they have real eigenvalues. Similarly, a *hermitian matrix* $H$ satisfies $H^dagger = (H^T)^* = H$.
- $hat(U)$ is *unitary* if $hat(U)^dagger hat(U) = hat(I)$. Unitary operators describe time-evolution in quantum mechanics. Similarly, a unitary matrix $U$ satisfies $U^dagger U = U U^dagger = I$.
- If we have $braket(n, m) = delta_(n m)$, the basis is orthonormal.
- *Qubit system*: Hilbert space $cal(H) = "span"(ket(0), ket(1))$. Any $ket(psi) in cal(H)$ can be written as $a_0 ket(0) + a_1 ket(1)$. If $ket(phi) = b_0 ket(0) + b_1 ket(1)$, $ braket(phi, psi) & = (b_0^* bra(0) + b_1^* ket(1))(a_0 ket(0) + a_1 ket(1)) \ & = conj(b_0) a_0 braket(0, 0) + conj(b_1) a_1 braket(1, 1) + conj(b_0) a_1 braket(0, 1) + conj(b_1) a_0 braket(1, 0) = conj(b_0) a_0 + conj(b_1) a_0 \ & = mat(conj(b_0), conj(b_1)) mat(1, 0; 0, 1) mat(a_0; a_1) $ If $ket(0), ket(1)$ is an energy eigenbasis, then $hat(H) ket(0) = E_0 ket(0)$ and $hat(H) ket(1) = E_1 ket(1)$ where $E_0, E_1$ are eigenvalues. $PP("measuring " E_0) = a_0^2 = |braket(0, psi)|^2, PP("measuring " E_1) = a_1^2 = |braket(1, psi)|^2$. If $a_0^2 + a_1^2 = 1$, then $braket(psi, psi) = 1$ so $psi$ is normalised. The expected energy measurement is $expected(E) = E_0 |a_0|^2 + E_1 |a_1|^2$.
- *Matrix form* of operator $hat(A)$: $ A_(n m) = braket(n, hat(A), m) $ For $hat(A)^dagger$, $braket(n, hat(A)^dagger, m) = conj(braket(m, hat(A), n))$.
- *Change of basis*: $B = S^(-1) A S$.
- *Schrodinger equation in braket notation*: $ i hbar diff / (diff t) ket(psi(t)) = hat(H) ket(psi(t)) $ If $hat(H)$ independent of $t$, then $ket(psi(t)) = e^(-i / hbar hat(H) t)$.
- *Exponential of operator*: $ exp(hat(A)) = sum_(n = 0)^oo hat(A)^n / n! $
- If $hat(A) = "diag"(a_1, ..., a_n)$ is diagonal, then $exp(hat(A)) = "diag"(e^(a_1), ..., e^(a_n))$.
- If $J^2 = -I$ ($I$ is identity matrix) then $ exp(J t) = cos(t) I + sin(t) J $
- $hat(A)$ *diagonalisable* if $hat(A) = hat(S) hat(D) hat(S)^(-1)$ where $hat(D)$ is diagonal and $hat(S)$ has columns corresponding to eigenvectors of $hat(A)$.
- For $hat(A)$ diagonalisable, $ exp(hat(A)) = sum_(n = 0)^oo (hat(S) hat(D) hat(S)^(-1))^n / (n!) = hat(S) (sum_(n = 0)^oo hat(D)^n / (n!)) hat(S)^(-1) = hat(S) exp(hat(D)) hat(S)^(-1) $
- For an orthonormal basis ${ket(n)}$, the identity operator is given by $ I = sum_n ket(n) bra(n) $
- *Spectral representation of operator*: $ hat(A) = sum_n lambda_n ket(n) bra(n) $ for orthonomal eigenvectors ${ket(n)}$. We can view a function $f$ acting on real numbers as acting on $hat(A)$ by $ f(hat(A)) = sum_n f(lambda_n) ket(n) bra(n) $

== Pure states and mixed states

- *Pure state*: linear combination of states $ket(psi) = ket(psi_1) + dots.h.c + ket(psi)n)$. Probability of being in this state is $1$.
- For a *density matrix* describing a *pure state* $hat(rho)_psi = ket(psi) bra(psi)$, $ tr(hat(rho)_psi) & = sum_n braket(n, hat(rho), n) = sum_n braket(n, psi) braket(psi, n) \ & = sum_n braket(psi, n) braket(n, psi) = bra(psi) (sum_n ket(n) bra(n)) ket(psi) = braket(psi, psi) = 1 $ Also $tr(hat(rho)_psi^2) = 1$.
- $ expected(E)_psi & = braket(psi, hat(H), I, psi) = sum_n braket(psi, hat(H), n) braket(n, psi) \ & = sum_n braket(n, psi) braket(psi, hat(H), n) = sum_n braket(n, hat(rho)_psi, hat(H), n) = tr(hat(rho)_psi hat(H)) $
- *Mixed state*: probability $p_i$ for each state $ket(psi_i)$. $hat(rho)_i = ket(psi_i) bra(psi_i)$ and $ hat(rho) = sum_i p_i hat(rho)_i $ For observable $hat(A)$ expressed in matrix form with basis as the states $ket(psi_i)$, then $expected(hat(A)) = tr(hat(rho) hat(A))$. For mixed state, we still have $tr(hat(rho)) = 1$ but $tr(hat(rho)^2) = sum_i p_i^2 <= 1$ with equality only when some $p_i = 1$ (i.e. a pure state). It conveys how "mixed" the state is.
- *Example*: for ensemble ${(3/4, ket(0)), (1/4, ket(1))}$, $ hat(rho) = 3/4 ket(0) bra(0) + 1/4 ket(1) bra(1) = mat(3\/4, 0; 0, 1\/4) $ This ensemble is *not* unique: $ {(1/2, sqrt(3/4) ket(0) + sqrt(1/4) ket(1)), (1/2, sqrt(3/4) ket(0) - sqrt(1/4) ket(1))} $ gives an equivalent density matrix: $ hat(rho)_1 & = (sqrt(3/4) ket(0) + sqrt(1/4) ket(1))(sqrt(3/4) bra(0) + sqrt(1/4) bra(1)) \ & = 3/4 ket(0) bra(0) + 1/4 ket(1) bra(1) + ..., hat(rho)_2 = ..., 1/2 hat(rho)_1 + 1/2 hat(rho)_2 = mat(3\/4, 0; 0, 1\/4) $
- *Definition*: *trace distance* between two density matrices: $ D(hat(rho)_1, hat(rho)_2) = 1/2 tr |hat(rho)_1 - hat(rho)_2| = sum_i |lambda_i| $ where $|hat(A)| = sqrt(hat(A)^dagger hat(A))$ and $lambda_i$ are the eigenvalues of $hat(rho)_1 - hat(rho)_2$.