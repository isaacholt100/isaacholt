#import "../../template.typ": *

#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Topological Quantum Matter Notes",
    author: "Isaac Holt",
    keywords: ("quantum", "error correction")
)

Themes:
- quantum matter
    - topological order (TO)
- quantum computing
    - quantum error correction (QEC)
    - topological quantum computing

Methods:
- mostly operator algebra (Pauli operators, Fermion operators)
- *some* field theory (second quantisation, path integrals)
- just a *little* band theory

#let ket(arg) = $lr(| #h(0.2pt) arg #h(0.2pt) angle.r, size: #0%)$
#let bra(arg) = $lr(angle.l #h(0.2pt) arg #h(0.2pt) |, size: #0%)$
#let braket(..args) = $angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r$
#let Ket(arg) = $lr(| #h(1pt) arg #h(1pt) angle.r)$
#let Bra(arg) = $lr(angle.l #h(1pt) arg #h(1pt) |)$
#let Braket(..args) = $lr(angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r)$
#let tp = sym.times.circle

= Background

== Notes on second quantisation

We can define an action of $S_n$ on an $n$ qudit state (a representation of the $n$-qudit Hilbert space by $S_n$) linearly by $
    sigma ket(i_1 ... i_n) = ket(i_sigma(1) ... i_sigma(n)).
$
#definition[
    A *boson* is a quantum state $ket(psi)$ that is invariant under the action of $S_n$ (symmetric under permutations), i.e. $
        forall sigma in S_n, quad sigma ket(psi) = ket(psi).
    $
]
#definition[
    A *fermion* is a quantum state $ket(phi)$ that is anti-symmetric under permutations, i.e. invariant under even permutations and is negated under odd permutations: $
        forall sigma in A_n, quad & sigma ket(phi) = ket(phi) \
        forall tau in S_n \\ A_n, quad & tau ket(phi) = -ket(phi)
    $
]
#definition[
    The symmetrisation of a state $ket(chi)$ is $
        S_(plus.minus) ket(chi) = 1/abs(S_n) sum_(sigma in S_n) (plus.minus 1)^("sgn"(sigma)) sigma ket(chi)
    $ where $"sgn"(sigma)$ denotes the sign of the permutation $sigma$. $S_+$ results in a boson, $S_-$ results in a fermion.
]
#notation[
    *Second quantisation* is a compact way of expressing bosons and fermions: $
        ket(n_1\, ...\, n_d)_plus.minus = S_(plus.minus) ket(i_1 ... i_n)
    $ where $n_j$ denotes the number of single qudit states that are in state $ket(j)$, in any basis state of $ket(n_1\, ...\, n_d)_plus.minus$. The number of qudits is $n = sum_(j = 1)^d n_j$.

    The states $ket(n_1\, ...\, n_d)_plus.minus$ are called *occupation (number) states*.
]
#proposition[
    Occupation states satisfy:
    + $braket(n_1\, ...\, n_d, m_1\, ...\, m_d) = delta_(n_1 m_1) cdots delta_(n_d m_d)$.
    + $sum_(n_1 + dots.c + n_d = n) ket(n_1\, ...\, n_d) bra(n_1\, ...\, n_d) = I$.
]
#definition[
    For a fixed number of qudits $n$, the space of all occupated number states is called *Fock space*.
]
Define the creation and annihilation operators $
    hat(a)_j^dagger ket(...\, n_j\, ...)_plus.minus & = sqrt(n_j + 1) ket(...\, n_j + 1\, ...)_plus.minus \
    hat(a)_j ket(...\, n_j + 1\, ...)_plus.minus & = sqrt(n_j + 1) ket(...\, n_j\, ...)_plus.minus \
$
This gives $
    [hat(a)_i, hat(a)_j] = [hat(a)_i^dagger, hat(a)_j^dagger] = 0, quad [hat(a)_i, hat(a)_j^dagger] = delta_(i j) quad "for bosons" \
    {hat(a)_i, hat(a)_j} = {hat(a)_i^dagger, hat(a)_j^dagger} = 0, quad {hat(a)_i, hat(a)_j^dagger} = delta_(i j) quad "for bosons"
$
A corollary of ${hat(a)_j^dagger, hat(a)_j^dagger} = 2 hat(a)_j^dagger hat(a)_j^dagger = 0$ is the Pauli principle that no single particle state can be occupied by more than one fermion.
#definition[
    The *occupation number operator* is $hat(n)_j = hat(a)_j^dagger hat(a)_j$. Note that $hat(n)_j ket(...\, n_j\, ...) = n_j ket(...\, n_j\, ...)$.
]
#example[
    The total particle number operator is $
        hat(n) = sum_j hat(n)_j
    $
]
For a single-qudit operator $hat(T) = sum_(i, j) t_(i j) ket(i) bra(j)$, we have $
    hat(T) = sum_(i j) t_(i j) hat(a)_i^dagger hat(a)_j
$ (since $ket(i) bra(j) ket(k) = hat(a)_i^dagger hat(a)_j ket(k)$)

Noting that $ket(phi) = sum_i braket(i, phi) ket(i)$, we define $
    hat(a)_phi^dagger = sum_i braket(i, lambda) hat(a)_i^dagger
$ (note this is analogous to a basis transformation)

=

#notation[
    When working with $N$ qubits (an $N$ site system), write $X_j, Y_j, Z_j$ for the Pauli $X, Y, Z$ on site $j$, e.g. $X_j = 1 tp cdots tp 1 tp X tp 1 tp cdots tp 1$.
]

= Quantum Ising model

TODO: familiarise with classical Ising model

*Quantum ising model*: $H = - J sum_(i, j, n n) Z_i Z_j - h sum_j Z_j$, $J > 0$. $n n$ denotes nearest neighbours. We have $H ket({z_j}) = E({z_j}) ket({z_j})$, $Z_i ket({z_j}) = z_i ket({z_j})$ where $z_i in {-1, 1}$.

*Transverse field Ising model*: $H = -J sum_(i, j: n n) Z_i Z_j - h sum_j X_j$, $J > 0$ (feromagn), $h > 0$. It has a $ZZ_2$ symmetry: $P = product_j X_j$, $H P = P H$, $P^2 = I$.

$P ket({z_j}) = ket({-z_j})$ (spin flip).

If $J = 0$: ground state is $ket("GS") = tp_(j = 1)^N ket(+)_j =: ket(underline(X))$. Denote $ket(0) = ket(arrow.t)$, $ket(1) = ket(arrow.b)$.

If $h = 0$: ground states are $ket(arrow.double.t) = tp.big_(j = 1)^N ket(0)_j$, $ket(arrow.double.b) = tp.big_(j = 1)^N ket(1)_j$, or any linear combination of these.

We have $P ket(underline(X)) = underline(X)$, and $braket(underline(X), Z_j, underline(X)) = 0$, since $Z_j ket(+)_j = ket(-)_j$. So order param ($z_j$) is $0$, can think of as paramagnet.

Also, $P ket(arrow.double.t) = ket(arrow.double.b)$, and $braket(arrow.double.t, Z_j, arrow.double.t) != 0$, so order param ($z_j$) is not $0$, so can think of as feromagnet.

Since $[H, P] = 0$, so there exists a basis $ket(psi_(E, P))$ such that $H ket(psi_(E, P)) = E_P ket(psi_(E, P))$, and $P ket(psi_(E, P)) = p ket(psi_(E, P))$, where $p in {-1, 1}$.

The ground states are $ket("GS"_(plus.minus)) = 1/sqrt(2) (ket(arrow.double.t) + ket(arrow.double.b))$. We have $P ket("GS"_(plus.minus)) = plus.minus ket("GS"_(plus.minus))$, and $braket("GS"_(plus.minus), Z_j, "GS"_(plus.minus)) = 0$.

\ \

Now consider $H = H_0 + delta H$, where $H_0 = -J sum_(i, j: n n) Z_i Z_j$, and $delta H = -h sum_j X_j$, where $abs(h) << J$. $delta H$ is the perturbation, with coupling $h$.

== Brilloin-Wigner perturbation theory

Write the eigenstates of $H_0$ as $H_0 ket(n) = E_n ket(n)$, and $H ket(tilde(n)) = E_(tilde(n)) ket(tilde(n))$. Write $P = sum_(n in S) ket(n) bra(n)$ and $Q = P^perp = I - P = sum_(n in S^perp) ket(n) bra(n)$. Denote perturbed ground state energies by $E_tilde(m)$. Let $ket(tilde(m)^((n)))$ denote unnormalised perturbed ground-space eigenstates, i.e. $H ket(tilde(m)^((n))) = E_tilde(m) ket(tilde(m)^((n)))$, and $ket(psi_tilde(m)) := P ket(tilde(m)^((n)))$ is normalised.

We have $(H_0 + delta H) ket(tilde(m)^((n))) = E_tilde(m) ket(tilde(m)^((n)))$, so $(E_tilde(m) - H_0) ket(tilde(m)^((n))) = delta H ket(tilde(m)^((n)))$. So $
    (E_tilde(m) - E_n) braket(n, tilde(m)^((n))) = braket(n, delta H, tilde(m)^((n)))
$. If $ket(n) in S^perp$, then $ket(n) braket(n, tilde(m)^((n))) = (ket(n) bra(n))/(E_tilde(m) - E_n) delta H ket(tilde(m)^((n)))$ and so $sum_(ket(n) in S^perp) ket(n) braket(n, tilde(m)^((n))) = sum_(ket(n) in S^perp) (ket(n) bra(n))/(E_tilde(m) - E_n) delta H ket(tilde(m)^((n)))$. We rewrite this as $Q ket(tilde(m)^((n))) = G delta H ket(tilde(m)^((n)))$. So $ket(tilde(m)^((n))) = ket(psi_tilde(m)) + G delta H ket(tilde(m)^((n)))$, and so we have $
    ket(tilde(m)^((n))) = (I - G delta H)^(-1) ket(psi_tilde(m))
$
Now for $ket(n) in S$, we have $(E_tilde(m) - E_0) braket(n, tilde(m)^((n))) = braket(n, underbrace(delta H (I - G delta H)^(-1), =: A^((tilde(m)))), psi_tilde(m)) = sum_(n' in S) underbrace(braket(n, A^((tilde(m))), n'), H_(n n')^("eff")) underbrace(braket(n', tilde(m)^((n))), delta_(n'))$. $H_(n n')^("eff"))$ is a $d_G times d_G$ "effective" Hamiltonian.