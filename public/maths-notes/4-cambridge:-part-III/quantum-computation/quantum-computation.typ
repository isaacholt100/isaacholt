#import "@preview/quill:0.2.0": *
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.1" as cetz: canvas, draw
#let name-abbrvs = (
    "Hidden Subgroup Problem (HSP)": "HSP",
    "Discrete Logarithm Problem (DLP)": "DLP",
    "Amplitude Amplification Theorem/2D-subspace Lemma": "Amplitude Amplification Theorem",
    "Lie-Trotter Product Formula": "Lie-Trotter"
)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)
#set document(
    title: "Quantum Computation Notes",
    author: "Isaac Holt",
    keywords: ("quantum computing", "quantum", "quantum computation", "algorithms", "complexity")
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

= Hidden subgroup problem

== Review of Shor's algorithm

#problem("Factoring")[
    / Input: a positive integer $N$.
    / Promise: $N$ is composite.
    / Task: Find a non-trivial factor of $N$ in $O(poly(n))$ time, where $n = log N$.
]<prb:factoring>
#definition[
    We say an *efficient problem* is one that can be solved in polynomial time.
]<def:efficient-problem>
#remark[
    Clasically, the best known factoring algorithm runs in $e^(O(n^(1\/3) (log n)^(2\/3)))$. Shor's algorithm runs in $O(n^3)$ by converting factoring into period finding:
    - Given input $N$, choose $a < N$ which is coprime to $N$.
    - Define $f: ZZ -> ZZ\/N$, $f(x) = a^x mod N$. $f$ is periodic with period $r$ (the order of $a mod N$), i.e. $f(x + r) = f(x)$ for all $x in ZZ$. Finding $r$ allows us to factor $N$.
]

== Period finding

#problem("Periodicity Determination Problem")[
    / Input: An oracle for a function $f: ZZ\/M -> ZZ\/N$.
    / Promise:
        - $f$ is periodic with period $r < M$ (i.e. $forall x in ZZ\/M$, $f(x + r) = f(x)$), and
        - $f$ is injective in each period (i.e. if $0 <= x < y < r$, then $f(x) != f(y)$).
    / Task: Determine the period $r$.
]<prb:periodicity-determination>
#remark[
    Solving the periodicity determination problem classically requires takes time $O\(sqrt(M)\)$.
]
#definition[
    Let $f: ZZ\/M -> ZZ\/N$. Let $H_M$ and $H_N$ be quantum state spaces with orthonormal state bases ${ket(i): i in ZZ\/N}$ and ${ket(j): j in ZZ\/M}$. Define the unitary *quantum oracle* for $f$ by $U_f$ by $
        U_f ket(x) ket(z) = ket(x) ket(z + f(x)).
    $ The first register $ket(x)$ is the *input register*, the last register $ket(z)$ is the *output register*.
]<def:quantum-oracle>
#definition[
    The *query complexity* of an algorithm is the number of times it queries $f$ (i.e. for the quantum case, the number of times it uses $U_f$).
]<def:quantum-query-complexity>
#definition[
    The *quantum Fourier transform* over $ZZ\/M$ is the unitary $QFT$ defined by its action on the computational basis: $
        QFT ket(x) = 1/sqrt(M) sum_(y = 0)^(M - 1) omega^(x y) ket(y),
    $ where $omega = e^(2pi i\/M)$ is an $M$-th root of unity. Note that $QFT$ requires only $O\((log M)^2\)$ gates to implement, whereas a general $M times M$ unitary requires $O(4^M \/ M)$ elementary gates.
]<def:quantum-fourier-transform>
#lemma[
    Let $alpha = e^(2pi i y\/M)$. Then $
        sum_(j = 0)^(k - 1) alpha^j = cases(
            (1 - alpha^k)/(1 - alpha) = 0 & "if" alpha != 1 "i.e." M divides.not y,
            k & "if" alpha = 1 "i.e." M divides y
        ).
    $
]
#proofhints[
    Trivial.
]
#proof[
    The sum is a geometric series with common ratio $alpha$.
]
#lemma("Boosting success probability")[
    If a process succeeds with probability $p$ on one trial, then $
        Pr("at least one success in" t "trials") = 1 - (1 - p)^t > 1 - delta
    $ for $t = log(1\/d)/p$.
]
#proofhints[
    Trivial.
]
#proof[
    Trivial.
]
#theorem("Co-primality Theorem")[
    The number of integers less than $r$ that are coprime to $r$ is $O(r\/log log r)$.
]
#algorithm("Quantum Period Finding")[
    The algorithm solves the @prb:periodicity-determination:
    Let $f: ZZ\/M -> ZZ\/N$ be periodic with period $r < M$ and one-to-one in each period. Let $A = M/r$ be the number of periods. We work over the state space $H_M tp H_N$.
    + Construct the state $1/sqrt(M) sum_(i = 0)^(M - 1) ket(i) ket(0)$ and query $U_f$ on it.
    + Measure second register in computational basis and discard the second register.
    + Apply the quantum Fourier transform to the input state.
    + Measure the input state, yielding outcome $c$.
    + Compute the denominator $r_0$ of the simplified fraction $c/M$.
    + Repeat the previous steps $O(log log r) = O(log log M) = O(log m)$ times, halting if at any iteration, $f(0) = f(r_0)$.
]
#theorem("Correctness of Quantum Period Finding Algorithm")[
    When repeated, $O(log log r) = O(log log M)$ times, the quantum period finding algorithm obtains the correct value of $r$ with high probability.
]
#proofhints[
    Straightforward.
]
#proof[
    After querying $U_f$, we have the state $1/sqrt(M) sum_(i = 0)^(M - 1) ket(i) ket(f(i))$. Upon measuring the second register in the computational basis, the input state collapses to $ket("per") = 1/sqrt(A) sum_(j = 0)^(A - 1) ket(x_0 + j r)$, where $f(x_0) = y$ and $0 <= x_0 < r$. Applying the quantum Fourier transform to $ket("per")$ then gives Quantum Fourier Transform to $ket("per")$: $
        QFT ket("per") & = 1/sqrt(M) sum_(y = 0)^(M - 1) 1/sqrt(A) sum_(j = 0)^(A - 1) omega^((x_0 + j r) y) ket(y) \
        & = 1/sqrt(M A) sum_(y = 0)^(M - 1) omega^(x_0 y) sum_(j = 0)^(A - 1) omega^(j r y) ket(y) \
        & = sqrt(A/M) sum_(k = 0)^(r - 1) omega^(x_0 k M\/r) ket(k M\/r)
    $ Importantly, now the outcomes and probabilities are independent of $x_0$, so carry useful information about $r$. TODO add diagram showing amplitudes for this state. The outcome after the measuring the input state is $c = k_0 M \/ r$ for some $0 <= k_0 < r$ (so $c \/ M = k_0 \/ r$). If $k_0$ is coprime to $r$, then the denominator $r_0$ of the simplified fraction $c/M$ is equal to $r$. By the coprimality theorem, the probability that $k_0$ is coprime to $r$ is $O(1\/log log r)$. Checking if $f(0) = f(r_0)$ tells us if $r_0 = r$, since $f$ is periodic and one-to-one in each period, and $r_0 <= r$.
]

== Analysis of QFT part of period finding algorithm

#notation[
    For $R = {0, r, ..., (A - 1)r} subset.eq ZZ\/M$ ($A r = M$), write $ket(R)$ for the uniform superposition of all computational basis states in $R$: $
        ket(R) = 1/sqrt(A) sum_(k = 0)^(A - 1) ket(k r).
    $
]
#definition[
    For each $x_0 in ZZ\/M$, define the lienar map by its action on the computational basis states: $
        U(x_0): H_M & -> H_M, \
        ket(k) & |-> ket(x_0 + k).
    $
]
#definition[
    Note that since $(ZZ\/M, +)$ is abelian, all $U(x_i)$ commute: $U(x_1) U(x_2) = U(x_1 + x_2) = U(x_2) U(x_1)$. Hence, they have a simultaneous basis of eigenvectors ${ket(chi_k): k in ZZ\/M}$, i.e. for all $k, x_0 in ZZ\/M$, $U(x_0) ket(chi_k) = w(x_0, k) ket(chi_k)$, where $abs(w(x_0, k)) = 1$. The $ket(chi_k)$ are called *shift-invariant states* and form an orthonormal basis for $H_M$. The $ket(chi_k)$ are given explicitly by $
        ket(chi_k) = 1/sqrt(M) sum_(ell = 0)^(M - 1) e^(-2pi i k ell\/M) ket(ell).
    $
]<def:quantum-fourier-characters>
#proposition[
    The explicit definition of the $ket(chi_k)$ indeed satisfies the property $forall k, x_0 in ZZ\/M$, $U(x_0) ket(chi_k) = w(x_0, k) ket(chi_k)$, and we have $w(x_0, k) = omega^(k x_0)$, where $omega = e^(2pi i\/M)$.
]
#proofhints[
    Straightforward.
]
#proof[
    We have that $
        U(x_0) ket(chi_k) & = 1/sqrt(M) sum_(ell = 0)^(M - 1) e^(-2pi i k ell\/M) ket(x_0 + ell) \
        & = 1/sqrt(M) sum_(tilde(l) = 0)^(M - 1) e^(-2pi i(tilde(l) - x_0) k\/M) ket(tilde(l)) \
        & = e^(2pi i k x_0 \/M) ket(chi_k) \
        & =: w(x_0, k) ket(chi_k)
    $
]
#remark[
    Let $U: H_M -> H_M$ be the unitary mapping the shift-invariant basis to the computational basis: $U: ket(chi_k) |-> ket(k)$. The matrix representation of $U^(-1)$ with respect to the computational basis has entries $
        (U^(-1))_(j k) = braket(j, U^(-1), k) = braket(j, chi_k) = 1/sqrt(M) e^(-2pi i j k\/M)
    $ So the matrix representation of $U$ with respect to the same basis has entries $U_(k j) = overline((U^(-1))_(j k)) = 1/sqrt(M) e^(2pi i j k\/M)$. Hence, we have $
        U ket(k) = 1/sqrt(M) sum_(j = 0)^(M - 1) e^(2pi i j k\/M) ket(j),
    $ and so $U$ is precisely the QFT $mod M$.
]

== The hidden subgroup problem (HSP)

#problem("Discrete Logarithm Problem (DLP)")[
    / Input: $g, x in G$ for an abelian group $G$.
    / Promise: $g$ is a generator of $G$.
    / Task: Find $log_g x$, i.e. find $L in ZZ\/abs(G)$ such that $x = g^L$.
]<prb:dlp>
#notation[
    Write $[n]$ for ${1, ..., n}$. Write e.g. $i j$ for the set ${i, j}$.
]
#definition[
    Let $Gamma_1 = ([n], E_1)$ and $Gamma_2 = ([n], E_2)$ be (undirected) graphs. $Gamma_1$ and $Gamma_2$ are *isomorphic* if there exists a permutation $pi in S_n$ such that for all $1 <= i, j < n$, $i j in E_1$ iff $pi(i) pi(j) in E_2$.
]<def:graph.isomorphic>
#definition[
    Let $Gamma = ([n], E)$ be a graph. The *automorphism group* of $Gamma$ is $
        Aut(Gamma) = {pi in S_n: i j in E "iff" pi(i) pi(j) in E quad forall i, j in [n]}.
    $ $Aut(Gamma)$ is a subgroup of $S_n$, and $pi in Aut(Gamma)$ iff $pi$ leaves $Gamma$ invariant as a labelled graph.
]<def:graph-automorphism-group>
#definition[
    The *adjacency matrix* of a graph $Gamma = (V, E)$ is the $n times n$ matrix $M_A$ defined by its entries: $
        (M_A)_(i j) := cases(
            1 quad & "if" i j in E,
            0 & "otherwise"
        ).
    $
]<def:adjacency-matrix>
#problem("Graph Isomorphism Problem")[
    / Input: Adjacency matrices $M_1$ and $M_2$ of graphs $Gamma_1 = ([n], E_1)$ and $Gamma_2 = ([n], E_2)$.
    / Task: Determine whether $Gamma_1$ and $Gamma_2$ are isomorphic.
]<prb:graph-isomorphism>
#remark[
    The best known classical algorithm for solving the graph isomorphism problem has quasi-polynomial time complexity $n^(O((log n)^2))$.
]
#problem("Hidden Subgroup Problem (HSP)")[
    Let $G$ be a finite group.
    / Input: An oracle for a function $f: G -> X$.
    / Promise: There is a subgroup $K < G$ such that:
        + $f$ is constant on the (left) cosets of $K$ in $G$.
        + $f$ takes a different value on each coset.
    / Task: Determine $K$.
]<prb:hsp>
#remark[
    - To find $K$, we either find a generating set for $K$, or sample uniformly random elements from $K$.
    - We want to determine $K$ with high probability in $O(poly log |G|)$ queries. Using $O(|G|)$ queries is easy, as we just query all values $f(g)$ and find the "level sets" (sets where $f$ is constant).
]
#example[
    The following problems are special cases of HSP:
    - The @prb:periodicity-determination: $G = ZZ\/M$, $K = gen(r) = {0, r, ..., (A - 1)r}$. The cosets are $x_0 + K = {x_0, x_0 + r, ..., x_0 + (A - 1) r}$ for each $0 <= x_0 < r$.
    - The @prb:dlp on $(ZZ\/p)^times$: let $f: ZZ\/(p - 1) times ZZ\/(p - 1) -> (ZZ\/p)^times$ be defined by $f(a, b) = g^a x^(-b) = g^(a - L b)$. $G = ZZ\/(p - 1) times ZZ\/(p - 1)$, the hidden subgroup is $K = {lambda (L, 1): lambda in ZZ\/(p - 1)}$. (Note that if we know $K$, we can pick any $(c, d) = (lambda L, lambda) in K$ and compute $L = c/d$ to find $L$.)
    - The @prb:graph-isomorphism: $G = S_n$, hidden subgroup is $K = Aut(G)$. Let $f_Gamma: S_n -> X$ where $X$ is set of adjacency matrices of labelled graphs on $[n]$, defined by $f_Gamma (pi) = pi(A)$. Note $abs(S_n) = abs(G) = n!$, so $log abs(G) approx n log n$, so $O(poly log abs(G)) = O(poly n)$.
]
#definition[
    An *irreducible representation (irrep)* of a finite abelian group $G$ is a homomorphism $chi: G -> CC^times$.
]<def:irrep>
#theorem[
    - Let $chi: G -> CC^times$ be an irrep. For all $g in G$, $chi(g)$ is a $abs(G)$-th root of unity.
    - There are always exactly $abs(G)$ distinct irreps. In particular, we can label each irrep uniquely by some $g in G$.
]
#theorem("Schur's Lemma")[
    Let $chi_i$ and $chi_j$ be irreps of $G$. Then $
        1/abs(G) sum_(g in G) chi_i (g) overline(chi_j (g)) = delta_(i j).
    $
]<thm:schurs-lemma>
#proof[
    Omitted.
]
#example[
    $chi_0: G -> CC^times$, $chi_0(g) = 1$ is the *trivial irrep*. Note that for any $chi_i != chi_0$, $sum_(g in G) chi_i (g) = 0$ by Schur's lemma.
]
#definition[
    For finite abelian $G$, we define the *shift operators* on $H_abs(G)$ for each $k in G$ by $
        U(k): H_abs(G) & -> H_abs(G), \
        ket(g) & |-> ket(k + g).
    $ Note that since $G$ is abelian, the $U(k)$ commute: $
        U(k) U(l) = U(k + l) = U(l) U(k) quad forall k, l in G.
    $ Hence, they have simultaneous eigenstates, which gives an orthonormal basis for $H_abs(G)$.
]
#proposition[
    For each $k in G$, consider the state $
        ket(chi_k) = 1/sqrt(abs(G)) sum_(g in G) overline(chi_k (g)) ket(g).
    $ The $ket(chi_k)$ are shift-invariant (invariant up to a phase under the action of all $U(g)$, $g in G$).
]
#proofhints[
    Straightforward.
]
#proof[
    Since $chi_k$ is a homomorphism, we have $overline(chi_k (g)) = chi_k (-g)$. Now $
        U(g_0) ket(chi_k) & = 1/sqrt(abs(G)) sum_(g in G) overline(chi_k (g)) ket(g_0 + g) \
        & = 1/sqrt(abs(G)) sum_(g' in G) overline(chi_k (g' - g_0)) ket(g') \
        & = 1/sqrt(abs(G)) sum_(g' in G) overline(chi_k (g')) chi_k (g_0) ket(g') \
        & = chi_k (g_0) ket(chi_k).
    $
]
#definition[
    The *quantum Fourier transform (QFT)* on $H_abs(G)$ is the unitary implementing the change of basis from the shift-invariant states ${ket(chi_g): g in G}$ to the computational basis ${ket(g): g in G}$.

    Note that $QFT^(-1) ket(g) = ket(chi_g)$. So $(QFT^(-1))_(k g) = braket(k, chi_g) = 1/sqrt(abs(G)) overline(chi_g (k))$, so $QFT_(k g) = 1/sqrt(abs(G)) chi_k (g)$. So the explicit form is $
        QFT ket(g) = 1/sqrt(abs(G)) sum_(k in G) chi_k (g) ket(k).
    $
]
#example[
    - For $G = ZZ\/M$, we can check that $chi_a (b) = e^(2pi i a b\/M)$ are irreps. So the irreps of $ZZ\/M$ are naturally labelled by $a in ZZ\/M$ and this gives the usual $QFT mod M$ as defined earlier.
    - Similarly, for $G = ZZ\/(M_1) times dots.c times ZZ\/(M_r)$, $chi_g (h) = e^(2pi i (g_1 h_1 \/M_1 + dots.c + g_r h_r \/M_r))$ are the irreps.
]
#algorithm([Quantum HSP solver for finite abelian $G$])[
    + Working in the state space $H_abs(G) tp H_abs(X)$, prepare the uniform superposition state $
        1/sqrt(abs(G)) sum_(g in G) ket(g) ket(0)
    $ and query $U_f$ on it.
    + Measure the output register, then discard this register.
    + Apply QFT $mod thick abs(G)$ to the input register, then measure this register.
    + Repeat the above steps $O(log abs(G))$ times.
]
#theorem("Correctness of Quantum HSP Solver")[
    The quantum HSP solver algorithm solves the @prb:hsp for finite abelian groups with high probability.
]
#proofhints[
    Use that irreps of $G$ restricted to $K$ are irreps of $K$, and that if $O(log abs(G))$ measurements are made, then with probability at least $2\/3$, we have enough equations to determine the generators of $K$.
]
#proof[
    Querying $U_f$ on the state gives $
        1/sqrt(abs(G)) sum_(g in G) ket(g) ket(f(g))
    $ Upon measurement of the output register, we obtain a uniformly random value $f(g_0)$ from $f(G)$, and the state collapses to a *coset state* $
        ket(g_0 + K) = 1/sqrt(abs(K)) sum_(k in K) ket(g_0 + k).
    $

    We have $ket(K) = sum_(g in G) a_g ket(chi_g)$, so $ket(g_0 + K) = U(g_0) ket(K) = sum_(g in G) a_g chi_g (g_0) ket(chi_g)$. So applying QFT to the input state gives $sum_(g in G) a_g chi_g (g_0) ket(g)$, so the probability of measuring outcome $k$ is $abs(a_k chi_k (g_0))^2 = abs(a_k)^2$. Now $
        QFT ket(K) & = 1/sqrt(abs(K)) sum_(k in K) QFT ket(k) \
        & = 1/sqrt(abs(G) abs(K)) sum_(g in G) (sum_(k in K) chi_g (k)) ket(g)
    $ Note that irreps of $G$ restricted to $K$ are irreps of $K$. The trivial irrep $chi_0: G -> CC$ remains the trivial irrep $chi_0$ for $K$. But there may be other irreps that become the trivial irrep on restriction to $K$. Hence $
        sum_(k in K) chi_g (k) = cases(
            abs(K) quad & "if" chi_g|_K = chi_0|_K,
            0 & "otherwise"
        )
    $ Hence $
        QFT ket(K) = sqrt(abs(K)/abs(G)) sum_(g in G \ chi_g|_K = chi_0|_K) ket(g)
    $ and measuring in the computational basis on this state yields random $g in G$ such that $forall k in K$, $chi_g (k) = 1$.

    If $K$ has generators $k_1, ..., k_m$ (note that for an arbitrary group, we have $m = O(log abs(G))$), then we have a set of equations $chi_g (k_i) = 1$ for all $i in [m]$. We can show that if $O(log abs(G))$ such $g$ are drawn uniformly at random, then with probability at least $2\/3$, we have enough equations to determine $k_1, ..., k_m$.
]
#example[
    Let $G = ZZ\/M_1 times dots.c times ZZ\/M_r$. The irreps are $
        chi_g (h) = e^(2pi i (g_1 h_1 \/ M_1 + dots.c + g_r h_r \/ M_r)).
    $ For $k in K$, $chi_g (k) = 1$ iff $(g_1 k_1)/M_1 + dots.c + (g_r k_r)/M_r = 0 mod 1$. This is a homogenous linear equation in $k$, and $O(log abs(G))$ independent such equations determine $K$ as the nullspace.
]
#remark[
    We can implement QFT over abelian groups (and some non-abelian groups, including $S_n$) using circuits with $O((log abs(G))^2)$ elementary gates.

    In the non-abelian case, we can still easily prepare coset states with one query to $f$. But the shift operators $U(g_0)$ no longer commute, so we don't have a (canonical) shift-invariant basis.
]
#definition[
    A *$d$-dimensional unitary representation* of a finite group $G$ is a homomorphism $
        chi: G -> U(d)
    $ where $U(d)$ is the group of $d times d$ unitary matrices.
]<def:unitary-representation>
#definition[
    A $d$-dimensional unitary representation $chi$ of $G$ is *irreducible* if no non-trivial subspace of $CC^d$ is invariant under the action of $\{chi(g_1), ..., chi\(g_(abs(G))\)\}$ (i.e. we cannot simultaneously block diagonalise all the $chi(g)$ matrices by a basis change).
]<def:unitary-representation.irreducible>
#definition[
    A set of irreps ${chi_1, ..., chi_m}$ is a *complete set of irreps* for every irrep $chi$ of $G$, there exists $1 <= i <= m$ such that $chi$ is unitarily equivalent to $chi_i$, i.e. for some $V in U(d)$, $forall g in G, chi(g) = V chi_i (g) V^dagger$.
]<def:complete-irreps>
#theorem[
    Let the dimensions of a complete set of irreps $chi_1, ..., chi_m$ be $d_1, ..., d_m$. Then $d_1^2 + dots.c + d_m^2 = abs(G)$.
]<thm:squares-of-dimensions-of-complete-set-of-irreps-sum-to-size-of-group>
#notation[
    Write $chi_(i, j k)(g)$ for the $(j, k)$-th entry of the matrix $chi_i (g)$.
]
#theorem("Schur Orthogonality")[
    Let $chi_1, ..., chi_m$ be a complete set of irreps for $G$ with respective dimensions $d_1, ..., d_m$, and let $i in [m]$, $j, k in [d_i]$. Then $
        sum_(g in G) chi_(i, j k)(g) overline(chi_(i', j' k')(g)) = abs(G) delta_(i i') delta_(j j') delta_(k k').
    $
]<thm:schur-orthogonality>
#definition[
    The *Fourier basis* for a group $G$ consists of $
        ket(chi_(i, j k)) = 1/sqrt(abs(G)) sum_(g in G) overline(chi_(i, j k)(g)) ket(g)
    $ for each $i in [n]$ and $j, k in [d_i]$. Note that by Schur orthogonality, this is an orthonormal basis.
]
#remark[
    Note that these states are not shift invariant for every $U(g_0): ket(g) |-> ket(g_0 g)$. So measurement of the coset state $ket(g_0 K)$ yields an output distribution that is not independent of $g_0$.
]
#definition[
    The *Quantum Fourier transform* over $H_abs(G)$ is the unitary mapping the Fourier basis to the computational basis: $
        QFT ket(chi_(i, j k)) = ket(i\, j k).
    $ $ket(i\, j k)$ is a relabelling of the states $ket(g)$ for $g in G$ (note this is valid by @thm:squares-of-dimensions-of-complete-set-of-irreps-sum-to-size-of-group).
]
#remark[
    - Measuring $QFT ket(g_0 K)$ does *not* give $g_0$-independent outcomes. A complete measurement in the computational basis gives an outcome $i, j, k$.
    - However, there is an incomplete measurement which projects into the $d_i^2$-dimensional subspaces $
        S_i = span{ket(chi_(i, j k)): j, k in [d_i]}.
    $ for each $i in [n]$. Call this measurement operator $M_"rep"$. Note that this distinguishes only between the irreps.
    - Measuring only the representation labels of $QFT ket(g_0 K)$ gives an outcome distribution of the $i$ values that i independent of the random shift $g_0$, since the $chi_i$ are homomorphisms.
    - Note this only gives partial information about $K$. If $K$ is a normal subgroup, then in fact we can then determine $K$ with $O(log abs(G))$ queries.
]


= Quantum phase estimation (QPE)

Quantum phase estimation is a unifying algorithmic primitive, e.g. there is an alternative factoring algorithm based on QPE, and has many important applications in physics.

#problem("Quantum Phase Estimation")[
    / Input: Unitary $U in U(d)$ acting on $CC^d$; state $ket(v_phi) in CC^d$; level of precision $n in NN$.
    / Promise: $ket(v_phi)$ is an eigenstate of $U$ with *phase* (eigenvalue) $e^(2pi i phi)$, $phi in [0, 1)$ (i.e. $U ket(v_phi) = e^(2pi i phi) ket(v_phi)$).
    / Task: Output an estimate $tilde(phi)$ of $phi$, accurate to $n$ binary bits of precision.
]
#remark[
    If $U$ is given as a circuit, we can implement the controlled-$U$ operation, $Ctrl(U)$, by controlling each elementary gate in the circuit of $U$.

    If $U$ is given as a black box, we need more information. Note that $U$ is equivalent to $U' = e^(i theta) U$ and $ket(psi)$ is equivalent to $e^(i theta) ket(psi)$, but $Ctrl(U)$ is not equivalent to $Ctrl(U')$. Given an eigenstate $ket(alpha)$ with known phase $e^(i alpha)$ (so $U ket(alpha) = e^(i alpha) ket(alpha)$), we have $U' ket(alpha) = e^(i(theta + alpha)) ket(alpha)$. so $U$ and $U'$ can be distinguished using this additional information. The following circuit implements $Ctrl(U)$ (the top two lines end in state $Ctrl(U) ket(a) ket(xi)$):

    #figure(quantum-circuit(
        lstick($"control" quad ket(a)$), 2, ctrl(1), 1, ctrl(1), $X$, $P(-alpha)$, $X$, rstick($ket(a)$), [\ ],
        lstick($ket(xi)$), 2, swap(1), 1, swap(1), 3, rstick($U^a ket(xi)$), [\ ],
        lstick($ket(alpha)$), 2, swap(0), $U$, swap(0), 3, rstick($ket(alpha)$)
    ))
    
    where $P(-alpha) = mat(1, 0; 0, e^(-i alpha))$, and $circle.small.filled dash #h(0em) times dash #h(0em) times$ denotes the controlled SWAP operation.
]
#definition[
    For a unitary $U$, the *generalised control* unitary $Ctrl(U)$ is defined linearly by $
        forall x in {0, 1}^n, quad Ctrl(U) ket(x) ket(xi) = ket(x) U^x ket(xi),
    $ where $U^x$ denotes $U$ applied $x$ times (e.g. $Ctrl(U) ket(11) ket(xi) = ket(11) U^3 ket(xi)$). Note that $Ctrl(U^k)$ = $(Ctrl(U))^k$.
    The following circuit implements $Ctrl(U)$:
    #figure(quantum-circuit(
        lstick($ket(x_(n - 1))$), 3, ctrl(4), 1, [\ ],
        lstick($dots.v$), 5, [\ ],
        lstick($ket(x_1)$), 1, ctrl(2), 3, [\ ],
        lstick($ket(x_0)$), ctrl(1), 4, [\ ],
        lstick($ket(xi)$), $U^(2^0)$, $U^(2^1)$, midstick($dots.c$), $U^(2^(n - 1))$, 1, rstick($U^x ket(xi)$) 
    ))
]<def:generalised-control>
#algorithm("Quantum Phase Estimation")[
    Work over the space $\(CC^2\)^(tp n) tp CC^d$, where $\(CC^2\)^(tp n)$ is the $n$-qubit register, $CC^d$ is the "qudit" register.
    + Apply the following circuit to $ket(0 ... 0) ket(v_phi)$: #figure(
        quantum-circuit(
            lstick($"line"(n - 1)$), $H$, 3, ctrl(4), mqgate($QFT_(2^n)^(-1)$, n: 4), 1, [\ ],
            // lstick($"line"(n - 2)$), $H$, 5, [\ ],/
            lstick($dots.v$), [\ ],
            lstick($"line"(1)$), $H$, 1, ctrl(2), 4, [\ ],
            lstick($"line"(0)$), $H$, ctrl(1), 5, [\ ],
            lstick($ket(v_phi)$), 1, $U^(2^0)$, $U^(2^1)$, midstick($dots.c$), $U^(2^(n - 1))$, 2,
        )
    ) We write $U_"PE"$ for this unitary part of the circuit.
    + Discard the qudit register holding $ket(v_phi)$, and measure the input qubits, yielding outcome $y_0 ... y_(n - 1)$ from lines $0, ..., n - 1$.
    + The estimate of $phi$ is $tilde(phi) = y \/ 2^n = y_0 \/ 2 + dots.c + y_(n - 1) \/ 2^n$.
]<alg:qpe>
#remark[
    After $Ctrl(U^(2^(n - 1)))$, the input qubits are in the state $
        1/sqrt(2^n) sum_(x in {0, 1}^n) e^(2pi i phi x) ket(x).
    $ If $phi$ had an exact $n$-bit expansion $0.i_1 i_2 ... i_n = (i_1 ... i_n) \/ 2^n =: phi_n \/ 2^n$, then this state is precisely $QFT_(2^n) ket(phi_n)$, in which case, after applying $QFT^(-1)$, we have $ket(phi_n)$, so measuring the input bits gives $phi_n$, and so $phi$, exactly.
]
#lemma[
    For all $alpha in RR$,
    + If $abs(alpha) <= pi$, then $abs(1 - e^(i alpha)) = 2 abs(sin(alpha\/2)) >= 2/pi abs(alpha)$.
    + If $alpha >= 0$, then $abs(1 - e^(i alpha)) <= alpha$.
]<lem:qpe-complex-modulus-inequalities>
#proofhints[
    For both, think graphically.
]
#proof[
    + The line $y = 2/pi alpha$ lies below $2 sin(alpha\/2)$ for $0 <= alpha <= pi$).
    + On the complex unit circle, the arc length $alpha$ from $1$ to $e^(i alpha)$ is at least the chord length from $1$ to $e^(i alpha)$.
]
#theorem("Phase Estimation Theorem")[
    Let $tilde(phi)$ be the estimate of $phi$ from the quantum phase estimation algorithm. Then
    + $Pr(tilde(phi) #[is closest $n$-bit approximation of $phi$]) >= 4/pi^2 approx 0.4$.
    + For all $epsilon > 0$, $Pr(abs(tilde(phi) - phi) > epsilon) = O(1/(2^n epsilon))$. So for any desired accuracy $epsilon$, the probability of failure decays exponentially with the number of bits of precision (lines in the circuit).
]<thm:phase-estimation>
#proofhints[
    Let $delta(y) = phi - y\/2^n + epsilon_y$, where $epsilon_y in {-1, 0, 1}$ is such that $delta(y) in [-1\/2, 1\/2]$. Show the probability of the measuring yielding outcome $y$ is $
        p_y = 1/2^(2n) abs((1 - e^(2^n 2 pi i delta(y)))/(1 - e^(2pi i delta(y))))^2.
    $
    + Find an upper bound on $delta(a)$ where $a$ is the closest $n$-bit approximation of $phi$.
    + Show that $
        p_y <= 1/2^(2n) (2/(4 delta(y)))^2 = 1 / (2^(2n + 2) delta(y)^2).
    $ Let $B = {y in {0, 1}^n: abs(delta(y)) > epsilon}$. Show that for each $y in B$, $abs(delta(y)) <= epsilon + k_y \/ 2^n$ for some $k_y in NN$, and that each $k_y$ occurs at most twice here. Conclude the upper bound using an integral.
]
#proof[
    Let $
        ket(A) = 1/sqrt(2^n) sum_(x = 0)^(2^n - 1) e^(2pi i phi x) ket(x).
    $ Let $delta(y) = phi - y\/2^n + epsilon_y$, where $epsilon_y in {-1, 0, 1}$ is such that $delta(y) in [-1\/2, 1\/2]$. $delta(y)$ can be thought of as the signed (positive if clockwise, negative if anticlockwise) arc distance between the points $y \/ 2^n$ and $phi$ on a circle of circumference $1$.
    #unmarked-fig(
        figure(
            canvas({
                import cetz.draw: *

                let r = 2
                circle((0, 0), radius: r)
                let n = 16
                for i in range(n) {
                    circle((r * calc.sin(2 * calc.pi * i / n), r * calc.cos(2 * calc.pi * i / n)), ..point-style, fill: black, name: "point-" + str(i))
                }
                content("point-0.north", box(inset: (bottom: 0.5em))[$y = 0$], anchor: "south")
                content("point-7.south-east", box(inset: (left: 0.25em))[$y = 7$], anchor: "north-west")
                content("point-13.west", box(inset: (right: 0.25em))[$y = 13$], anchor: "east")
                let phi-angle = 2rad * calc.pi * 1.5 / 16
                circle((r * calc.cos(phi-angle), r * calc.sin(phi-angle)), ..point-style, fill: diagram-colors.red, name: "phi")
                content("phi.north-east", box(inset: (left: 0.25em))[$phi$], anchor: "south-west")
                let y1-angle = 2rad * calc.pi * 7 / 16
                let y2-angle = 2rad * calc.pi * 13 / 16
                circle((r * calc.cos(y1-angle), r * calc.sin(y1-angle)), ..point-style, fill: diagram-colors.blue)
                circle((r * calc.cos(y2-angle), r * calc.sin(y2-angle)), ..point-style, fill: diagram-colors.blue)
                set-style(stroke: diagram-colors.red + 2pt, mark: (end: ">", fill: diagram-colors.red))
                c-arc((0, 0), r - 0.3, y1-angle, phi-angle + 0.01rad, name: "positive", mark: (end: ">"))
                content("positive.arc-center", box(inset: (top: 0.5em))[$+$], anchor: "north")
                c-arc((0, 0), r - 0.3, y2-angle - 2rad * calc.pi, phi-angle - 0.01rad, name: "negative")
                content("negative.arc-center", box(inset: (right: 0.5em))[$-$], anchor: "east")
            }),
            caption: [Example when $n = 4$: the $16$ possible values of $y$ are equally spaced around the circle. $delta(13)$ is positive, $delta(7)$ is negative.]
        )
    )
    Since $QFT^(-1) ket(x) = 1/sqrt(2^n) sum_(y = 0)^(2^n - 1) e^(-2pi i x y \/ 2^n) ket(y)$, we have $
        QFT^(-1) ket(A) = 1/2^n sum_(y = 0)^(2^n - 1) sum_(x = 0)^(2^n - 1) e^(2pi i x delta(y)) ket(y)
    $ so the probability of measuring outcome $y$ is $
        p_y = Pr(tilde(phi) = y/2^n) = 1/2^(2n) abs((1 - e^(2^n 2 pi i delta(y)))/(1 - e^(2pi i delta(y))))^2.
    $
    + Let $alpha = 2^n 2pi delta(a)$, where $a$ is the closest $n$-bit approximation of $phi$. Note we can imagine the possible values of $tilde(phi)$ as lying on the unit circle, spaced by angle $(2pi) / 2^n$. This gives a visual intuition to the fact that $abs(delta(a)) <= 1/(2^(n + 1))$. Hence $abs(alpha) <= pi$, and so by the above lemma, $
        p_a = Pr(tilde(phi) = a) >= 1/(2^(2n)) ((2^(n + 2) delta(a))/(2pi delta(a)))^2 = 4/pi^2.
    $
    + Note that $abs(1 - e^(2^n 2 pi i delta(y))) <= 2$ by the triangle inequality. Let $B = {y in {0, 1}^n: abs(delta(y)) > epsilon}$ denote the set of "bad" values of $y$. For all $y in {0, 1}^n$, we have $delta(y) in [-1 \/ 2, 1 \/ 2]$. So by @lem:qpe-complex-modulus-inequalities, we have $abs(1 - e^(2pi i delta(y))) >= 4 abs(delta(y))$, thus $
        p_y <= 1/2^(2n) (2/(4 delta(y)))^2 = 1 / (2^(2n + 2) delta(y)^2).
    $ Let $delta^+ = min{delta(y): y in B, delta(y) > 0}$ be the smallest $delta(y)$ such that $delta(y) > epsilon$, and $delta^- = max{delta(y): y in B: delta(y) < 0}$ be the largest $delta(y)$ such that $delta(y) < -epsilon$. For all $y in B$, we have $delta(y) = delta^+ + k_y \/ 2^n$ or $delta(y) = delta^- - k_y \/ 2^n$ for some $k_y in NN$, so $abs(delta(y)) > epsilon + k_y \/ 2^n$. Note that each $k in NN$, $k = k_y$ for at most $2$ values of $y in B$. Hence, $
        Pr(abs(delta(y)) > epsilon) & = Pr(y in B) = sum_(y in B) p_y \
        & <= sum_(y in B) 1/(2^(2n + 2) (epsilon + k_y\/2^n)^2) \
        & < 2 sum_(k = 0)^oo 1/2^(2n + 2) 1/(epsilon + k\/2^n)^2 \
        & <= 1/(2^(2n + 1) epsilon^2) + sum_(k = 1)^oo 1/2^(2n + 1) 1/(epsilon + k\/2^n)^2 \
        & = 1/(2^(2n + 1) epsilon^2) + integral_0^oo 1/2^(2n + 1) 1/(epsilon + x\/2^n)^2 dif x \
        & = 1/(2^(2n + 1) epsilon^2) + integral_(2^n epsilon)^oo 1/(2u^2) dif u = 1/(2^(2n + 1) epsilon^2) + 1/(2^(n + 1) epsilon).
    $
]
#remark[
    The QPE algorithm excluding the measurement is a unitary - call this unitary $U_"PE"$. If we apply $U_"PE"$ to an arbitrary state $ket(psi) = sum_j c_j ket(v_j)$ where $ket(v_j)$ are the eigenstates of $U$ with eigenvalue $e^(2pi i phi_j)$, then we have $
        U_"PE" ket(psi) = sum_(j) c_j ket(tilde(phi)_j) ket(v_j)
    $ If every $phi_j$ has an exact $n$-bit representation, then this is exact. Otherwise, we have $ket(tilde(phi)_j) = sqrt(1 - eta) ket(tilde(phi)_1) + sqrt(eta) ket(tilde(phi)_0)$, where $ket(tilde(phi)_1)$ is a superposition of all $n$-bit strings that are correct to the first $n$-bits of $phi$, and $ket(tilde(phi)_0)$ is a superposition of strings with the first $n$ bits not all correct.
]
#remark[
    Complexity of QPE: we use $Ctrl(U), ..., Ctrl(U^(2^(n - 1)))$, so the number of uses of $Ctrl(U)$ is $approx 2^n$. So this initially looks like exponential time, but there are special cases of $U$ where by repeated squaring, this can be implemented with $poly(n)$ gates.

    If we want to estimate $phi$ accurate to $m$ bits of precision with probability $1 - eta$, then by the phase estimation theorem with $epsilon = 1/2^m$, we need $n = O(m + log(1\/eta))$ lines. Note this is a modest, polynomial increase in the number of lines of the circuit for an exponential reduction in $eta$.
]


= Amplitude amplification

Amplitude amplification is an extension of the key insights in Grover's algorithm (TODO: read part II notes for Grover's).

#notation[
    Given $ket(alpha) in H_d$, write $L_ket(alpha) = span{ket(alpha)}$ for the one-dimensional subspace generated by $ket(alpha)$.
]
#notation[
    Given a subspace $A <= H_d$, denote the projector onto $A$ by $P_A$. Note that $
        P_A = sum_(i = 1)^k ket(a_i) bra(a_i)
    $ for any orthonormal basis ${ket(a_1), ..., ket(a_k)}$ of $A$.
]
#notation[
    Given a subspace $A <= H_d$, define the unitary $I_A = I - 2 P_A$, which is the reflection in the "mirror" $A^perp$: indeed, note that for all $ket(phi) in A$, $I_A = -ket(phi)$, and for all $ket(psi) in A^perp$, $I_A ket(psi) = ket(psi)$, since $P_A ket(psi) = 0$.

    In the case that $A$ is one-dimensional and spanned by $ket(alpha)$, we have $P_A = ket(alpha) bra(alpha)$, and write $I_ket(alpha) = I - 2 ket(alpha) bra(alpha)$.
]
#proposition[
    Let $ket(alpha) in H_d$. For any unitary $U in U(d)$, we have $
        U I_ket(alpha) U^dagger = I_(U ket(alpha)).
    $
]
#proofhints[
    Trivial.
]
#proof[
    $U I_ket(alpha) U^dagger = U U^dagger - 2 U ket(alpha) bra(alpha) U^dagger = I_(U ket(alpha))$.
]
#problem("Unstructured Search Problem")[
    / Input: An oracle for a function $f: {0, 1}^n -> {0, 1}$.
    / Promise: There is a unique $x_0 in {0, 1}^n$ such that $f(x_0) = 1$.
    / Task: Find $x_0$.
]<prb:unstructured-search>
#remark[
    The unstructured search problem is closely related to the complexity class NP and to Boolean satisfiability.
]
#definition[
    For fixed $ket(x_0) in H_2^(tp n)$, the *Grover iteration operator* $Q$ is defined as $
        Q := -H^(tp n) I_ket(0) H^(tp n) I_ket(x_0) = -I_(H^(tp n) ket(0)) I_ket(x_0).
    $
]
#remark[
    Note that for a function $f: {0, 1}^n -> {0, 1}$ fulfilling the promise of the @prb:unstructured-search, we can implement $I_ket(x_0)$ without knowing $x_0$: we have $U_f ket(x) 1/sqrt(2) (ket(0) - ket(1)) = (-1)^f(x) ket(x) 1/sqrt(2) (ket(0) - ket(1)) = I_ket(x_0) ket(x) 1/sqrt(2) (ket(0) - ket(1))$. Hence, implementing $Q$ requires only one query to $f$.
]
#theorem("Grover")[
    In the $2$-dimensional subspace spanned by $ket(psi) = H^(tp n) ket(0)$ and $ket(x_0)$, the action of $Q$ is a rotation by angle $2 alpha$, where $sin(alpha) = 1/sqrt(2^n) = braket(x_0, psi)$.
]
#algorithm("Grover's Algorithm")[
    Work in the state space $H_2^(tp n)$.
    + Prepare $ket(psi) = H^(tp n) ket(0)$.
    + Apply $Q^m$ to $ket(psi)$, where $m$ is closest integer to $arccos(1\/sqrt(N))/(2 arcsin(1\/sqrt(N))) = theta / (2 alpha)$ and $cos(theta) = sin(alpha) = braket(x_0, psi) = 1 \/ sqrt(2^n)$. This rotates $ket(psi)$ to be close to $ket(x_0)$ (within angle $plus.minus alpha$ of $ket(x_0)$).
    + Measure to get $x_0$ with probability $p = abs(braket(x_0, Q^m, psi))^2 = 1 - 1/N$. For large $N$, $arccos(1\/sqrt(N)) approx pi/2$, and $arcsin(1\/sqrt(N)) approx 1\/sqrt(N)$. The number of iterations is $m = pi/4 sqrt(N) = O(sqrt(N))$. So we need $O(sqrt(N))$ queries to $U_f$. In contrast, clasically we need $Omega(N)$ queries to $f$ to find $x_0$ with any desired constant probability. Note that $Omega(N)$ queries are both necessary and sufficient.
]<alg:grovers>
#notation[
    Write $G$ for the subspace of the state space $H$ whose associated amplitudes in a given state we wish to amplify. $G$ is called the "good" subspace. We call the subspace $G^perp$ the "bad" subspace. Note that $H = G xor G^perp$, and for any state $ket(phi) in H$, there is a unique decomposition with real, positive coefficients $ket(phi) = sin(theta) ket(g) + cos(theta) ket(b)$, where $ket(g) = P_G ket(phi)$ and $ket(b) = P_(G^perp) ket(phi)$.
]
#theorem("Amplitude Amplification Theorem/2D-subspace Lemma")[
    /*Let $ket(psi) = H^(tp n) ket(0)$.*/ Let $G <= H_2^(tp n)$ be a subspace and $ket(g) = P_G ket(psi)$, $ket(b) = P_(G^perp) ket(psi)$. In the $2$-dimensional subspace $span{ket(psi), ket(g)} = span{ket(b), ket(g)}$, the unitary $
        Q = -I_ket(psi) I_G
    $ is a rotation by angle $2 theta$, where $sin(theta) = norm(P_G ket(psi))_2$ is the length of the "good" projection of $ket(psi)$.
]<thm:amplitude-amplification>
#proofhints[
    Consider the matrix representation of $Q$ in the $span{ket(b), ket(g)}$ basis.
]
#proof[
    By definition, we have $I_G ket(g) = -ket(g)$, and $I_G ket(b) = ket(b)$. Hence $Q ket(g) = I_ket(psi) ket(g)$ and $Q ket(b) = -I_ket(psi) ket(b)$. The matrix representation of $I_ket(psi)$ in the ${ket(b), ket(g)}$ basis is $
        mat(1, 0; 0, 1) - 2 vec(cos(theta), sin(theta)) mat(cos(theta), sin(theta))
        & = mat(1 - 2 cos(theta)^2, -2 sin(theta) cos(theta); -2 sin(theta) cos(theta),  1 - 2 sin(theta)^2) \
        & = mat(-cos(2 theta), -sin(2 theta); -sin(2 theta), cos(2 theta)).
    $ So $Q ket(b) = cos(2theta) ket(b) + sin(2theta) ket(g)$, and $Q ket(g) = -sin(2theta) ket(b) + cos(2theta) ket(g)$. So the matrix representation of $Q$ in the ${ket(b), ket(g)}$ basis is $
        mat(cos(2 theta), -sin(2theta); sin(2theta), cos(2theta))
    $ which indeed is a rotation by angle $2theta$.
]
#corollary[
    We have $Q^m ket(psi) = cos((2m + 1) theta) ket(b) + sin((2m + 1) theta) ket(g)$.
]
#proofhints[
    Trivial.
]
#proof[
    Induction on $m$.
]
#notation[
    Denote by $m_"opt"$ the $m in ZZ$ which maximises the probability of measuring (in the ${ket(b), ket(g)}$ basis) an outcome in $G$ on the state $Q^m ket(psi)$. Note that this probability is equal to $sin((2m + 1) theta)^2$, which is maximised when $
        (2m + 1) theta = pi \/ 2 quad ==> m = pi \/ 4 theta - 1 \/ 2.
    $ So $m_"opt"$ is the nearest integer to $pi \/ 4 theta - 1 \/ 2$.
]
#example[
    Let $theta = pi \/ 6$, then $m_"opt" = 1$ and $Q ket(psi) = ket(g)$. So we obtain a good outcome with certainty on measurement.
]
#remark[
    Note that since $Q$ is a rotation by angle $2 theta$, $Q^(m_"opt") ket(psi)$ lies within angle $plus.minus theta$ of $ket(g)$, hence the $ket(g)$ component of $Q^(m_"opt") ket(psi)$ has amplitude $>= cos(theta)^2$. TODO: insert diagram. So for small $theta$, $
        Pr("measuring good outcome") >= cos(theta)^2 approx 1 - O(theta^2).
    $ Also, for small $theta$, $
        m_"opt" = O(1 \/ theta) approx O(1 \/ sin(theta)).
    $
]
#remark[
    $Q$ can be implemented (efficiently) if $I_ket(psi)$ and $I_G$ can be implemented (efficiently). For an efficient implementation of $I_G$, it suffices for $G$ to be spanned by some subset of computational basis states, and the indicator function $indicator(G)$ is efficiently computable. In this case, we have $
        U_(indicator(G)) ket(x) 1/sqrt(2) (ket(0) - ket(1)) & = (-1)^(indicator(G)(x)) 1/sqrt(2) (ket(0) - ket(1))
    $ Since $I_G$ is defined by its action $ket(g) |-> -ket(g)$ for $g in G$ and $ket(b) |-> ket(b)$ for $b in G^perp$, the first register holds the value $I_G ket(x)$.
    
    For an efficient implementation of $I_ket(psi)$,  we usually have $ket(psi) = H^(tp n) ket(0 ... 0)$, and then $I_ket(psi) = H^(tp n) I_ket(0) H^(tp n)$ can be implemented with $O(n)$ gates.
]
#remark[
    In the amplitude amplification process, the relative amplitudes of basis states inside $ket(g)$ and $ket(b)$ won't change. So amplitude amplification boosts the overall amplitude of $ket(g)$ at the expense of the amplitude of $ket(b)$.
]

== Applications of amplitude amplification

#example[
    // TODO: for this generalised Grover (including stuff before), does G have to be a subspace, or just a subset? looks like just a subset in this example
    We can generalise Grover search from $1$ marked item to $k$ marked items out of $N = 2^n$ items. In this case, $
        ket(psi) & = 1/sqrt(2^n) sum_(x in {0, 1}^n) ket(x) \
        & = sqrt(k/N) 1/sqrt(k) sum_(x in G) ket(x) + sqrt((N - k)/N) 1/sqrt(N - k) sum_(x in G^perp) ket(x) \
        & =: sqrt(k/N) ket(g) + sqrt((N - k)/N) ket(b)
    $ so $sin(theta) = sqrt(k \/ N)$. For $k << N$, $sin(theta) approx theta$, so $m_"opt" = O\(sqrt(N\/k)\)$ uses of $Q$ required. E.g. $N = 4 = 2^2$ items and $k = 1$ marked item, we have $sin(theta) = 1 \/ 2$, so $theta = pi \/ 6$, so Grover search is exact, and requires exactly one application of $Q$.
]

#example("Quadratic speedup of general quantum algorithms")[
    Let $U$ be a unitary representing a quantum algorithm/circuit, with $U ket(0...0) = alpha ket(g) + beta ket(b)$ where $ket(g)$ is a superposition of good/correct outcomes, and $ket(b)$ is a superposition of bad/incorrect outcomes. Note $ket(g) = sum_(x in {0, 1}^n) c_x ket(x)$ is generally a non-uniform superposition. We have $
        Pr("measuring" U ket(0...0) "yields good outcome") = abs(alpha)^2.
    $ Thus, we need to run $U$ about $O(1 \/ abs(alpha)^2)$ times to succeed with high probability.
    
    Now define $ket(psi) = U ket(0...0)$ and $Q = -I_ket(psi) I_G$. We can implement $Q$ if we have a method to verify the output of $U$; so in particular, we can use this method for any NP problem. This will mean we can efficiently implement the indicator function $indicator(G)$ of good labels and therefore also $I_G$. So by the @thm:amplitude-amplification, $Q$ performs a rotation of $2theta$ where $sin(theta) = abs(alpha)$. So after approximately $
        m_"opt" approx pi \/ 4theta = O(1 \/ theta) = O(1 \/ sin(theta)) = O(1 \/ abs(alpha))
    $ (for $theta$ small) uses of $Q$, we get a good outcome with high probability.
]<exm:quadratic-speed-up-of-general-quantum-algorithm>
#problem("Counting Problem")[
    / Input: $f: {0, 1}^n -> {0, 1}$.
    / Task: Estimate the number $k = abs(f^(-1)({1}))$ of inputs that evaluate to $1$.
]<prb:counting>
#example("Quantum Counting")[
    This combines amplitude amplification and quantum phase estimation. Let the "good" subspace $G$ be the subspace with basis $f^(-1)({1})$. As usual, let $
        ket(g) & := 1/sqrt(k) sum_(x in f^(-1)({1})) ket(x), quad ket(b) := 1/sqrt(2^n - k) sum_(x in f^(-1)({0})) ket(x), \
        ket(psi) & = 1/sqrt(2^n) sum_(x in {0, 1}^n) ket(x) = sqrt(k/N) 1/sqrt(k) sum_(x in f^(-1)({1})) ket(x) + sqrt((N - k)/N) 1/sqrt(N - k) sum_(x in f^(-1)({0})) ket(x).
    $ Recall that $Q$ has matrix representation $
        Q = mat(cos(2 theta), -sin(2theta); sin(2 theta), cos(2 theta))
    $ in the orthonormal basis ${ket(b), ket(g)}$ where $sin(theta) = norm(P_G ket(psi))$. The eigenvalues and eigenstates of $Q$ are $lambda_(plus.minus) = e^(plus.minus 2 i theta)$ and $ket(e_(plus.minus)) = 1/sqrt(2)(ket(b) minus.plus i ket(g))$. So we can write $ket(psi) = sin(theta) ket(g) + cos(theta) ket(b) = 1/sqrt(2) (e^(-i theta) ket(e_+) + e^(i theta) ket(e_-))$. So $ket(psi)$ is an equally-weighted superposition of eigenstates of $Q$. Write $e^(plus.minus 2 i theta) = e^(2pi i phi_(plus.minus))$ with $phi_(plus.minus) in (0, 1)$. We have $phi_+ = theta \/ pi$ and $phi_- = (-2 theta + 2pi) \/ 2pi = 1 - theta \/ pi$. When $k << N$, $sin(theta) = sqrt(k\/N) approx theta$, so using $U_"PE"$ with $m$ qubits of precision $
        U_"PE" ket(psi) = 1/sqrt(2) (e^(-i theta) ket(e_+) ket(tilde(phi)_+) + e^(i theta) ket(e_-) ket(tilde(phi)_-))
    $ Measuring the QPE output gives (with probability $1\/2$) an estimate of $phi_+ = theta \/ pi approx 1/pi sqrt(k \/ N)$ or (with probability $1\/2$) an estimate of $phi_- = 1 - theta \/ pi approx 1 - 1/pi sqrt(k \/ N)$. So in either case, we get an estimate of $sqrt(k\/N)$ (since we can tell when $k << N$ which case we are in). By the @thm:phase-estimation, with probability at least $4 \/ pi^2$, QPE with $m$ lines gives us an approximation of $sqrt(k \/ N)$ to precision $O(1\/2^m)$, using $O(2^m)$ $Ctrl(Q)$ operations, each of which requires one query to $f$. Write $delta \/ sqrt(2^n) = 1 \/ 2^m$ for some $delta > 0$. So we can estimate $sqrt(k)$ to precision $delta$, and since $Delta(x^2) = 2x Delta(x)$, we estimate $sqrt(k)$ to additive error (precision) $O(delta sqrt(k))$ using $O(2^m) = O(sqrt(N) \/ delta)$ queries to $f$.
]<exm:quantum-counting>
#remark[
    The quantum counting algorithm is quadratically faster than the best possible classical algorithm, which is:
    - Sample random $x$ from ${0, 1}^n$, then $Pr(f(x) = 1) = k\/N$.
    - Draw $m$ samples $x_1, ..., x_m$, then the estimate is $tilde(k) = ell N \/ m$, where $m = |{i in [m]: f(x_i) = 1}|$.
    We need $m = O(N\/delta^2)$ to estimate $k$ to high precision.
]

= Hamiltonian simulation

We want to use a quantum system to simulate the evolution/dynamics of another quantum system, given its Hamiltonian $H$. For an $n$-qubit system, in general this requires $O(2^n)$ time on a classical computer. For some physically interesting classes of $H$, we have quantum algorithms that run in $O(poly(n))$ time.

#definition[
    The *exponential* of a matrix $A in CC^(n times n)$ is defined as $
        exp(A) = e^A := sum_(k = 0)^oo A^k / k!.
    $ Note that if $[A, B] = 0$, then $exp(A) exp(B) = exp(A + B)$, but generally this does not hold when $[A, B] != 0$.
]<def:matrix-exponential>
#theorem[
    If $H$ is Hermitian, then $e^(-i H t)$ is unitary for all $t in RR$.
]<thm:evolution-operator-is-unitary-for-hermitian-matrices>
#proofhints[
    Straightforward.
]
#proof[
    We have $(e^(-i H t))^* = e^(i H t)$ since $H = H^*$, and since $[-i H t, i H t] = 0$, $e^(-i H t) e^(i H t) = e^0 = I$.
]
#proposition[
    If $A in CC^(n times n)$ has orthonormal spectrum ${(lambda_i, ket(e_i)): i in [n]}$, then $
        exp(A) = sum_(i = 1)^n exp(lambda_i) ket(e_i).
    $
]<prop:exponential-of-matrix-is-exponential-applied-to-spectrum>
#proofhints[
    Straightforward.
]
#proof[
    By orthonormality, we have $
        A^k = (sum_(i = 1)^n lambda_i ket(e_i))^k = sum_(i = 1)^n lambda_i^k ket(e_i).
    $ Hence, $
        exp(A) = sum_(k = 0)^oo A^k / k! = sum_(i = 1)^n sum_(k = 0)^oo lambda_i^k / k! ket(e_i).
    $
]
#definition[
    Given a Hamiltonian $H$, the unitary $U(t) = e^(-i H t)$ is called the *evolution operator* of $H$. Given $H$ and $t > 0$, we want to simulate $U(t)$ accurately.
]<def:evolution-operator>
#proposition[
    The Schrodinger equation which governs the time evolution of a physical state $ket(psi(t))$, given by (assuming $planck.reduce = 1$) $
        dif / (dif t) ket(psi(t)) = -i H ket(psi(t)),
    $ has solution $
        ket(psi(t)) = e^(-i H t) ket(psi(0))
    $ when $H$ is time-independent.
]<prop:solution-to-finite-dimensional-time-independent-schrodinger-equation>
#proofhints[
    Straightforward.
]
#proof[
    Let $H$ have orthonormal spectrum ${(lambda_j, ket(e_j)): j in [n]}$. By @prop:exponential-of-matrix-is-exponential-applied-to-spectrum, we have $
        ket(psi(t)) = e^(-i H t) ket(psi(0)) = sum_(j = 1)^n e^(-i lambda_j t) ket(e_j) braket(e_j, psi(0)).
    $ Hence, $
        dif / (dif t) ket(psi(t)) & = sum_(j = 1)^n -i lambda_j t e^(-i lambda_j t) ket(e_j) braket(e_j, psi(0)) \
        & = (sum_(j = 1)^n -i lambda_j ket(e_j) bra(e_j)) sum_(k = 1)^n e^(-i lambda_k t) ket(e_k) braket(e_k, psi(0))
    $ by orthonormality.
]
#definition[
    The *operator norm* (*spectral norm*) of an operator $A: H -> H$ acting on the space $H$ of states is $
        norm(A) & := max{norm(A ket(psi)): psi in H, thick norm(psi) = 1}.
    $
]<def:operator-norm>
#theorem[
    If $A$ is diagonalisable with eigenvalues $lambda_1, ..., lambda_n$, then $
        norm(A) = max{abs(lambda_1), ..., abs(lambda_n)}.
    $
]<thm:norm-of-matrix-is-max-abs-value-of-its-eigenvalues>
#proofhints[
    Straightforward.
]
#proof[
    Let ${(lambda_j, ket(e_j)): j in [n]}$ be the orthonormal spectrum of $A$. For $>=$, we have $
        norm(A) >= max{norm(A ket(e_1)), ... norm(A ket(e_n))} = max{norm(lambda_1 ket(e_1)), ..., norm(lambda_n ket(e_n))} = max{abs(lambda_1), ..., abs(lambda_n)}.
    $ For $<=$, let $ket(psi) in H$ with $norm(psi) = 1$. The $ket(e_j)$ form an orthonormal basis, so $ket(psi) = sum_(j = 1)^n a_j ket(e_j)$ for some coefficients $a_j in [-1, 1]$. Let $lambda' = max{abs(lambda_1), ..., abs(lambda_n)}$. Then $
        norm(A ket(psi))^2 & = norm(sum_(j = 1)^n a_j lambda_j ket(e_j))^2 \
        & = sum_(j = 1)^n abs(a_j)^2 abs(lambda_j)^2 quad & "by orthonormality" \
        & <= sum_(j = 1)^n abs(a_j)^2 lambda'^2 = lambda'^2.
    $
]
#proposition[
    The operator norm satisfies the following properties:
    + *Submultiplicative*: $norm(A B) <= norm(A) dot norm(B)$.
    + *Triangle inequality*: $norm(A + B) <= norm(A) + norm(B)$.
]<prop:operator-norm-is-submultiplicative-and-subadditive>
#proofhints[
    Straightforward.
]
#proof[
    + Let $ket(psi_0)$ achieve the maximum in $norm(A B) = max{norm(A B ket(psi)): ket(psi) in H, norm(ket(psi)) = 1}$. Let $b = norm(B ket(psi_0))$. We have $
        1/b norm(A B) = 1/b norm(A B ket(psi_0)) = norm(A (B ket(psi_0))/b) <= norm(A),
    $ hence $norm(A B) <= norm(A) dot b$, but also $b <= norm(B)$.
    + We have $
        norm(A + B) & = max{norm(A ket(psi) + B ket(psi)): ket(psi) in H, norm(psi) = 1} \
        & <= max{norm(A ket(psi)) + norm(B ket(psi)): ket(psi) in H, norm(psi) = 1} \
        & <= max{norm(A ket(psi)): ket(psi) in H, norm(psi) = 1} + max{norm(B ket(psi)): ket(psi) in H, norm(psi) = 1}.
    $
]
#definition[
    Let $U, tilde(U): H -> H$ be operators. $tilde(U)$ *$epsilon$-approximates* $U$ if $
    norm(U - tilde(U)) <= epsilon,
$ i.e. for all normalised states $ket(psi)$, $norm(U ket(psi) - tilde(U) ket(psi)) <= epsilon$.
]<def:epsilon-approximation>
#lemma[
    Let $U_1, ..., U_m, tilde(U)_1, ..., tilde(U)_m$ be unitaries. Suppose $tilde(U)_i$ $epsilon$-approximates $U_i$ for each $1 <= i <= m$. Then $
        norm(U_m med dots.c med U_1 - tilde(U)_m med dots.c med tilde(U)_1) <= m epsilon.
    $ So the error increases at most linearly.
]<lem:approximation-of-unitary-product-grows-linearly>
#proofhints[
    Straightforward.
]
#proof[
    By induction on $m$. The case $m = 1$ is true by assumption. Assume it is true for $m = k$. We have $
        & norm(U_(k + 1) thick cdots thick U_1 - tilde(U)_(k + 1) thick cdots thick tilde(U)_1) \
        = & norm(U_(k + 1) U_k thick cdots thick U_1 - tilde(U)_(k + 1) U_k thick cdots thick U_1 + tilde(U)_(k + 1) U_k thick cdots thick U_1 - tilde(U)_(k + 1) tilde(U)_k thick cdots thick tilde(U)_1) \
        <= & norm((U_(k + 1) - tilde(U)_(k + 1)) U_k thick cdots thick U_1) + norm(tilde(U)_(k + 1) (U_k thick cdots thick U_1 - tilde(U)_k thick cdots thick tilde(U)_1)) \
        <= & epsilon dot 1 + 1 dot k epsilon = (k + 1) epsilon
    $ by assumption, @prop:operator-norm-is-submultiplicative-and-subadditive and the inductive hypothesis.
]
#definition[
    $H$ is a *$k$-local Hamiltonian on $n$ qubits* if we can write $
        H = sum_(j = 1)^m H_j
    $ where each $H_j$ acts non-trivially on at most $k$ qubits, in which case we write $H_j = tilde(H)_j tp I$ (note these qubits need not be adjacent).

    Note that $m <= binom(n, k) = O(n^k)$, and we usually take $k$ to be a constant.
]
#notation[
    Write $U_((i))$ for the unitary $
        I tp dots.c tp I tp U tp I tp dots.c tp I
    $ where $U$ is in the $i$-th position, i.e. $U_((i))$ is the unitary acting on the $i$-th qubit on $n$-qubits.
]
#example[
    - $H = X tp I tp I - 5 Z tp Y tp I$ is $2$-local on $3$ qubits.
    - For the *Ising model* on an $n times n$ grid, where each qubit acts non-trivially only with its neighbours, the Hamiltonian is $
        H = J sum_(i, j = 1)^n (Z_((i, j)) Z_((i, j + 1)) + Z_((i, j)) Z_((i + 1, j)))
    $ where $J in RR$ is a coupling constant.
    - For the *Heisenberg model* on a line, the Hamiltonain is $
        H = sum_(i = 1)^(n - 1) (J_X X_((i)) X_((i + 1)) + J_Y Y_((i)) Y_((i + 1)) + J_Z Z_((i)) Z_((i + 1))),
    $ where $J_X, J_Y, J_Z in RR$ are constants.
]
#theorem("Solovay-Kitaev")[
    Let $U$ be a unitary on $k$-qubits, and $S$ be a universal set of elementary gates. Then $U$ can be $epsilon$-approximated using $O((log (1 \/ epsilon))^c)$ gates from $S$, where $c < 4$ is a constant.
]<thm:solovay-kitaev>
#proof[
    Omitted.
]
#proposition[
    Let $H = sum_(j = 1)^m H_j$ be a $k$-local Hamiltonian where all the local terms $H_j$ commute. Then for all $t > 0$ and $epsilon > 0$, the evolution operator $U(t) = e^(-i H t)$ can be $epsilon$-approximated by a circuit with $O(m polylog(m \/ epsilon))$ gates from any universal gate set.
    
    Note that $m = O(n^k)$, so the time-complexity is polynomial in $n$.
]<prop:simulation-for-k-local-hamiltonian-with-commuting-local-terms>
#proofhints[
    Straightforward.
]
#proof[
    Fix $t > 0$ and $epsilon > 0$. We have $
        U(t) = e^(-i H t) = e^(-i sum_(j = 1)^m H_j) t = product_(j = 1)^m e^(-i H_j t).
    $ Each $e^(-i H_j t)$ is a unitary that acts non-trivially on at most $k$ qubits. So we have a circuit for $e^(-i H t)$ in terms of some set of $k$-qubit gates. By @thm:solovay-kitaev, each $e^(-i H_j t)$ can be $delta$-approximated by a unitary $tilde(U)_j (t)$ circuit with $O(polylog(1 \/ delta))$ gates. By @lem:approximation-of-unitary-product-grows-linearly, we have $
        norm(U(t) - product_(i = 1)^m tilde(U)_j (t)) < m delta.
    $ So choosing $delta = epsilon \/ m$, we obtain a circuit of size $O(m polylog(m \/ epsilon))$ which $epsilon$-approximates $U(t)$.
]
#notation[
    For $N times N$ matrices $X$ and $Y$, write $X = Y + O(epsilon)$ to mean $X = Y + E$ where $norm(E) <= epsilon$.
]
#lemma("Lie-Trotter Product Formula")[
    Let $A$ and $B$ be $N times N$ matrices with $norm(A), norm(B) <= delta < 1$. Then $
        e^(-i A) e^(-i B) = e^(-i (A + B)) + O(delta^2).
    $
]<lem:lie-trotter-product-formula>
#proofhints[
    Write $e^(-i A) = I - i A + E_A$ and show that $norm(E_A) = O(delta^2)$, do the same for two other matrices.
]
#proof[
    We have $
        e^(-i A) & = I - i A + sum_(j = 2)^oo (-i A)^j / j! =: I - i A + E_A.
    $ Now $
        norm(E_A) & = norm((-i A)^2 sum_(j = 0)^oo (-i A)^j / (j + 2)!) \
        & <= norm((-i A)^2) dot norm(sum_(j = 0)^oo (-i A)^j / (j + 2)!) quad & "by submultiplicativity" \
        & <= norm((-i A)^2) dot sum_(j = 0)^oo norm((-i A)^j) / (j + 2)! quad & "by triangle inequality and continuity" \
        & <= norm(A)^2 sum_(j = 0)^oo norm((-i A))^j / j! quad & "by submultiplicativity" \
        & = delta^2 e^(delta) <= delta^2.
    $ So $e^(-i A) = I - i A + O(delta^2)$. By the same argument, we have $
        e^(-i B) & = I - i B + O(delta^2), \
        e^(-i(A + B)) & = I - i(A + B) + O(2 delta^2) = I - i(A + B) + O(delta^2)
    $ since $norm(A + B) <= norm(A) + norm(B) = 2 delta$. Hence, $
        e^(-i A) e^(-i B) & = (I - i A + O(delta^2))(I - i B + O(delta^2)) \
        & = I - i(A + B) + O(delta^2) \
        & = e^(-i (A + B)) + O(delta^2),
    $ since $norm(A B) <= delta^2$ by submultiplicativity.
]
#proposition[
    There is a $poly(n, 1 \/ epsilon, t)$-time quantum algorithm for simulating the evolution operators of $k$-local Hamiltonians.
]<prop:simulation-for-general-k-local-hamiltonian>
#proofhints[
    - Let $tilde(H)_j = H_j t \/ M$ for some constant $M$ to be determined later. Show that $
        e^(-i tilde(H)_1) med dots.c med e^(-i tilde(H)_m) = e^(-i (tilde(H)_1 + dots.c + tilde(H)_m)) + O(m^3 tilde(delta)^2),
    $ assuming a bound on $norm(tilde(H)_j)$, which you should determine.
    - Using that $
        U(t) = e^(-i(H_1 + dots.c + H_m)t) = (e^(-i (H_1 + dots.c + H_m) t \/ M))^M
    $ and the above, find an $O(...)$ lower bound for $M$.
]
#proof[
    Let $H = sum_(j = 1)^m H_j$ be a $k$-local Hamiltonian and $U(t) = e^(-i H t)$ be its evolution operator. If all the $H_j$ commute, then we are done by @prop:simulation-for-k-local-hamiltonian-with-commuting-local-terms. Otherwise, define $tilde(H)_j = H_j t \/ M$ for each $j in [m]$, for some fixed constant $M$ to be determined later. We want each $norm(tilde(H)_j) <= tilde(delta)$ with $tilde(delta) <= 1 \/ m$, since then $norm(tilde(H)_1 + dots.c + tilde(H)_ell) <= ell tilde(delta)$, and we need the @lem:lie-trotter-product-formula approximation to hold for all $ell in [m]$. We have $
        & (e^(-i tilde(H)_1) e^(-i tilde(H)_2)) med dots.c med e^(-i tilde(H)_m) \
        = & (e^(-i (tilde(H)_1 + tilde(H)_2)) + O(tilde(delta)^2)) e^(-i tilde(H)_3) dots.c e^(-i tilde(H)_m) quad & #[by @lem:lie-trotter-product-formula] \
        = & e^(-i (tilde(H)_1 + tilde(H)_2)) e^(-i tilde(H)_3) dots.c e^(-i tilde(H)_m) + O(tilde(delta)^2) quad & #[by submultiplicativity] \
        = & (e^(-i(tilde(H)_1 + tilde(H)_2 + tilde(H)_3)) + O((2 tilde(delta))^2)) e^(-i tilde(H)_4) med dots.c med e^(-i tilde(H)_m) + O(tilde(delta)^2).
    $ since each $e^(-i tilde(H)_j)$ is unitary, so has unit norm. Repeatedly applying @lem:lie-trotter-product-formula, we obtain $
        e^(-i tilde(H)_1) med dots.c med e^(-i tilde(H)_m) & = e^(-i (tilde(H)_1 + dots.c + tilde(H)_m)) + O(tilde(delta)^2) + dots.c + O(((m - 1) tilde(delta))^2) \
        & = e^(-i (tilde(H)_1 + dots.c + tilde(H)_m)) + O(m^3 tilde(delta)^2).
    $ Let the $O(m^3 tilde(delta)^2)$ error be $E m^3 tilde(delta)^2$. Now $
        U(t) = e^(-i(H_1 + dots.c + H_m)t) = (e^(-i (H_1 + dots.c + H_m) t \/ M))^M = (e^(-i (tilde(H)_1 + dots.c + tilde(H)_m)))^M.
    $ So we need the error in approximating $e^(-i H t \/ M)$ to be at most $epsilon \/ M$, so we require $E m^3 tilde(delta)^2 < epsilon \/ M$. Let $delta = tilde(delta) M \/ t$ (so that $norm(H_j) <= delta$ for each $j$): we want $norm(H_j) <= delta = tilde(delta) M \/ t <= M \/ (m t)$, i.e. $M >= m t norm(H_j)$ for all $j$. So any $
        M > max{E m^3 (delta t)^2 \/ epsilon, m t norm(H_1), ... m t norm(H_m)} = O(m^3 (delta t)^2 \/ epsilon)
    $ suffices. We have $
        norm(e^(-i H_1 t \/ M) med dots.c med e^(-i H_m t \/ M) - e^(-i(H_1 + dots.c + H_m) t \/ M)) <= epsilon \/ M.
    $ and so by @lem:approximation-of-unitary-product-grows-linearly, $
        norm(e^(-i H_1 t) med dots.c med e^(-i H_m t) - e^(-i(H_1 + dots.c + H_m) t)) <= epsilon.
    $ The circuit is composed of $M m$ gates of the form $e^(-i H_j t \/ M)$, so the entire circuit consists of $O(m^4 (delta t)^2 \/ epsilon)$ of these gates. Recall that if $H$ is $k$-local, then $m <= binom(n, k) = O(n^k)$. So we have a circuit with $C = O(n^(4k) (delta t)^2 \/ epsilon)$ gates of the form $e^(-i H_j t \/ M)$ approximating $e^(-i H t)$ to precision $epsilon$. By @thm:solovay-kitaev, each of these gates can be $(epsilon \/ C)$-approximated by $O(log^4 (C \/ epsilon))$ gates from an elementary universal gate set. So the final complexity is $tilde(O)(n^(4k) (delta t)^2 \/ epsilon)$ which is $poly(n, 1 \/ epsilon, t)$.
]
#remark[
    - The time dependence is quadratic, but there are improved product formulae that allow the dependence of the circuit size on $t$ to be $O(t^(1 + alpha))$ for any $alpha > 0$.
    - The $epsilon$-dependence is $poly(1 \/ epsilon)$ whereas in the commuting case it was $polylog(1 \/ epsilon)$. However, there are methods that decrease this to $(1 \/ epsilon)^(1 \/ 2k)$.
]


= The Harrow-Hassidim-Lloyd (HHL) algorithm

#definition[
    The *condition number* of a square matrix $A in CC^(N times N)$ is defined as $
        kappa(A) := cases(
            norm(A^(-1)) dot norm(A) quad & "if" A "is invertible",
            oo & "otherwise"
        ).
    $ We say $A$ is *well-conditioned* if $kappa(A)$ is small, i.e. if $kappa(A) = O(polylog(N))$.
]<def:condition-number>
#remark[
    $kappa(A)$ can be thought of a measure of "how invertible" $A$ is. As $kappa(A)$ increases, numerically computing $A^(-1)$ becomes more unstable.
]
#proposition[
    If $A in CC^(N times N)$ is Hermitian with non-zero eigenvalues $lambda_1, ..., lambda_N$, then $
        kappa(A) = max{abs(lambda_i): i in [N]} / min{abs(lambda_i): i in [N]}.
    $
]<prop:condition-number-of-hermitian-matrix-is-ratio-of-max-abs-eigenvalue-and-min-abs-eigenvalue>
#proofhints[
    Straightforward.
]
#proof[
    We have $
        A = sum_(i = 1)^N lambda_i ket(v_i) bra(v_i)
    $ where $ket(v_1), ..., ket(v_n)$ are the eigenvalues of $A$. Hence, $
        A^(-1) = sum_(i = 1)^N lambda_i^(-1) ket(v_i) bra(v_i),
    $ so $A^(-1)$ has eigenvalues $lambda_1^(-1), ..., lambda_N^(-1)$. So by @thm:norm-of-matrix-is-max-abs-value-of-its-eigenvalues, we have $
        kappa(A) = norm(A^(-1)) dot norm(A) & = max{abs(lambda_i^(-1)): i in [N]} dot max{abs(lambda_i): i in [N]} \
        & = max{abs(lambda_i): i in [N]} / min{abs(lambda_i): i in [N]}.
    $
]
#problem("Linear System Solution Problem")[
    / Input: matrix $A in CC^(N times N)$, vector $b in CC^N$.
    / Task: find a vector $x in CC^N$ such that $A x = b$.
]
#remark[
    The best known classical algorithms for solving linear systems require $O(poly(N) dot log(1 \/ epsilon))$ time. Note that even just reading the inputs $A$ and $b$, or writing the solution $x$ requires $O(poly(N))$ time.
    
    Instead of computing the full solution $x$, the HHL algorithm estimates properties of $x$ of the form $mu = x^T M x$ (i.e. quadratic forms), where $M$ is Hermitian, e.g. the total weight assigned by $x$ to a subset of indices/components.
]
#algorithm("HHL")[
    We are given $ket(b) = 1/norm(b)_2 sum_(i = 0)^(N - 1) b_i ket(i)$.
    + Apply the unitary part $U_"PE"$ of @alg:qpe for the unitary $e^(-i A)$ with $m$ bits of precision to the state $ket(b) ket(0)^(tp m)$.
    + Append an ancillary qubit (in state $ket(0)$) to the state, then apply a controlled rotation (acting on the last $m$ qubits plus the ancillary qubit) to it.
    + Perform a *post-selection* step: measure the last qubit, and if the outcome is $0$, reject and go back to step 1, otherwise accept.
    + Apply $U_"PE"^(-1)$ (the inverse of phase estimation) to the resulting state.
    + Perform a measurement in the $M$ basis on the first $n$ qubits of the resulting state.
    + Repeat all of the above $O(log(1/eta) \/ delta^2)$ times and compute the empirical mean of the measurements, where $eta$ controls the probability of success and $delta$ controls the approximation error.
]<alg:hhl>
#remark[
    - We can also use HHL for non-Hermitian $A$: double the system size and set $
        tilde(A) = mat(0, A^dagger; A, 0), quad tilde(b) = vec(0, b).
    $ Then run HHL on $tilde(A)$ and $tilde(b)$: if $A x = b$, then $tilde(A) tilde(x) = tilde(b)$ where $tilde(x) = vec(x, 0)$.
    - We can also use HHL for non-Hermitian $M$: run HHL on $M_1 = 1/2 \(M + M^dagger\)$ and $M_2 = 1/(2i) \(M - M^dagger\)$ (which are Hermitian) to give estimates $hat(mu)_1$ and $hat(mu)_2$, then combine to give $hat(mu) := hat(mu)_1 + i hat(mu)_2$.
]
#theorem("Chernoff-Hoeffding")[
    Let $X_1, ..., X_k$ be IID RVs on $[a, b]$ with mean $mu$, and let $overline(X) = 1/k (X_1 + dots.c + X_k)$. Then $
        Pr\(abs(overline(X) - mu\) > delta) <= e^(-2k delta^2 \/ (b - a)^2).
    $
]<thm:chernoff-hoeffding>
#proof[
    Omitted.
]
#theorem[
    If Hamiltonian simulation and phase estimation are exact, then the @alg:hhl algorithm computes a estimate $hat(mu)$ of $mu = x^T M x$ to accuracy $delta$, with probability at least $1 - eta$.
]
#proofsketch[
    Let $
        A = sum_(i = 1)^N lambda_i ket(v_i) bra(v_i)
    $ be the spectral decomposition of $A$. For simplicity, we assume that Hamiltonian simulation and phase estimation are exact; in particular, for each $i in [N]$, $lambda_i = ell_i \/ 2^n$ for some $ell_i in {0, ... N - 1}$. Assume that $max{abs(lambda_1), ..., abs(lambda_n)} = 1$ and that $kappa(A)$ is known or bounded above by some value $kappa_max$. Writing $kappa = kappa(A)$, we have by @prop:condition-number-of-hermitian-matrix-is-ratio-of-max-abs-eigenvalue-and-min-abs-eigenvalue that $abs(lambda_i) in [1\/kappa, 1]$ for each $i in [N]$. Work in the $n$-qubit Hilbert space spanned by ${ket(1), ..., ket(N)}$. Write $
        ket(b) = sum_(i = 1)^N b_i ket(i) = sum_(j = 1)^N beta_j ket(v_j)
    $ Due to the bounds on the $abs(lambda_i)$, $A^(-1)$ exists and is equal to $sum_(i = 1)^N 1/lambda_j ket(v_j) bra(v_j)$. Thus, the (unnormalised) solution to $A ket(x) = ket(b)$ is  $
        ket(x) = A^(-1) ket(b) = sum_(j = 1)^N beta_j dot 1/lambda_j ket(v_j).
    $
    + Applying $U_"PE"$ on the state $ket(psi) := ket(b) ket(0)^(tp m)$ gives the state $
        U_"PE" ket(psi) = sum_(i = 1)^N beta_i ket(v_i) ket(ell_i)
    $ (assuming $e^(-i A)$ and $U_"PE"$ are exact and error-free). Consider the controlled rotation $Ctrl("Rot")$ acting on $n + 1$ qubits, defined by the following action: for all $j in [N]$, $
        Ctrl("Rot") ket(ell_j) ket(0) = ket(ell_j) (cos\(theta_j\) ket(0) + sin\(theta_j\) ket(1)) = ket(ell_j) (sqrt(1 - c^2 / lambda_j^2) ket(0) + c / lambda_j ket(1)),
    $ where $theta = arcsin(c \/ lambda)$ and $c <= min{abs(lambda_j): j in [N]}$, and e.g. $Ctrl("Rot") ket(y) ket(0) = ket(y) ket(0)$ for all other $y$ (this part is not important and could be chosen to be something else which is consistent with $Ctrl("Rot")$ being unitary). By unitarity, this fully determines $Ctrl("Rot")$. \ By the above bounds on the $abs(lambda_j)$, we can choose $c = 1 \/ kappa$. So in $Ctrl("Rot")$, the angle depends on the first register but not on $A$ or $b$ (so we're not sneaking extra info in here). $Ctrl("Rot")$ can be implemented efficiently using $O(poly(n))$ one and two-qubit gates (by e.g. @thm:solovay-kitaev).
    + Applying $Ctrl("Rot")$ to the state $U_"PE" ket(psi) tp ket(0)$ produces the state $
        sum_(j = 1)^N beta_j sqrt(1 - c^2 \/ lambda_j^2) ket(v_j) ket(ell_j) ket(0) + beta_j c/lambda_j ket(v_j) ket(ell_j) ket(1)
    $
    + At the post-selection step, the probability of success (i.e. measuring outcome $1$) is (Probability of successfully preparing state $ket(x)$ is $
        p & = norm(sum_(j = 1)^N beta_j c/lambda_j ket(v_j) ket(ell_j))^2 = sum_(j = 1)^N abs(beta_j c \/ lambda_j)^2 >= c^2 sum_(j = 1)^N abs(beta_j)^2 = c^2 = 1/kappa^2
    $ In this case, the post-measurement state has collapsed to (ignoring the ancillary qubit) $
        ket(phi) = 1/sqrt(p) sum_(j = 1)^N beta_j c/lambda_j ket(v_j) ket(ell_j)
    $ To boost the success probability to at least $1 - eta$, we can either repeat the post-selection step $O(log(1 \/ eta) / p) = O(log(1\/ eta) kappa^2)$ times.
    + Applying $U_"PE"^(-1)$ to $ket(phi)$ "uncomputes" the register holding the $ket(ell_j)$, resetting it to $ket(0)$, so gives $
        ket(tilde(x)) = c/sqrt(p) sum_(j = 1)^N beta_j / lambda_j ket(v_j) = c/sqrt(p) ket(x).
    $
    + Performing a measurement on $ket(tilde(x))$ in the $M$ basis on the first $n$ qubits (i.e. measuring in the $M tp I_m$ basis on the entire state, where $I_m$ is the identity operator on $m$ qubits) yields an eigenvalue of $M$.
    + We have $mu = braket(x, M, x) = p/c^2 braket(tilde(x), M tp I, tilde(x))$. Computing the empirical average of the measurements gives us an estimate of $tilde(mu) = braket(tilde(x), M tp I_m, tilde(x))$. By the @thm:chernoff-hoeffding bound, to estimate $tilde(mu)$ with probability at least $1 - eta$ to accuracy $delta$, we need $O(log(1 \/ eta) / delta^2)$ of the measurements in the $M$ basis. Since $c$ is known, we just need an estimate of $p$ to be able to estimate $mu$. \ To estimate $p$: the post-selection step is a Bernoulli trial, with probability of outcome $1$ being $p$. So the mean is $0 dot (1 - p) + 1 dot p = p$. This can also be estimated by the empirical average of the proportion of post-selection steps performed that succeed, and we again use the @thm:chernoff-hoeffding bound.
]
#remark[
    Note that in reality @alg:hhl outputs a state $ket(tilde(x)')$ that is $epsilon$-close to $ket(tilde(x))$, rather than $ket(tilde(x))$ itself.
    // Using $ket(tilde(x)')$ a further $O(poly(n) kappa^2 \/ epsilon)$ times, we can estimate any $mu = x^T M x$.
]
#remark[
    Instead of repeating the post-selection step (step 3 of @alg:hhl) until we succeed, we can use amplitude amplification to the state before we measure, i.e. to the state $
        U_"HHL" ket(b) = sqrt(1 - p) ket("junk") ket(0) + sqrt(p) ket(tilde(x)) ket(1),
    $ which gives a quadratic improvement on the $O(kappa^2)$ measurements needed for success in the post-selection step.

    Similarly, instead of estimating the probability $p$ using the @thm:chernoff-hoeffding bound, we could use amplitude amplification in the form of @exm:quantum-counting.
]
#remark[
    In @alg:hhl, we want to be able to apply the transformation $ket(b) |-> A^(-1) ket(b) = ket(x)$. However, this is generally non-unitary so cannot be directly implemented. Instead, we implemented it probabilistically using @alg:qpe, performed on the unitary $U = e^(-i A)$, which in turn is implemented by Hamiltonian simulation. At the end, the measurement in $M$ basis re-introduces the non-unitarity.
]
#definition[
    We say a matrix $A in CC^(N times N)$ is *row sparse* if each row of $A$ contains $O(polylog(N))$ non-zero entries.

    More generally, $A$ is *row $s$-sparse* if each row contains at most $s$ non-zero entries.
]<def:matrix.row-sparse>
#definition[
    We say an $s$-sparse matrix $A$ is *row-computable* if the entries of $A$ can be efficiently computed in the following sense: there is a (classical) $O(s)$-time algorithm $C$ which, given a row index $1 <= i <= N$ and an integer $k$, outputs the $k$-th non-zero entry  $A_(i j)$ of row $i$ and its column index $j$: $
        C(i, k) = (j, A_(i j)).
    $
]
#theorem[
    Under the following assumptions, for row $s$-sparse $A$, HHL runs in time $O((log N) kappa^2 s^2 dot 1/epsilon)$:
    - $norm(b)_2$ is $1$ (or is efficiently computable), and the state $ket(b)$ can be prepared exactly and efficiently.
    - The unitary $Ctrl(Rot)$ can be implemented exactly and efficiently.
    - Measurements in the $M$ basis can be performed efficiently.
]
#proof[
    Non-examinable.
]
// Runtime of HHL:
    // - The precision dependence in Hamiltonian simulation can be made $O(log(1 \/ epsilon))$, so we neglect it.
    // - Most of the complexity of HHL comes from QPE. Suppose we do QPE with $m$ qubits of precision $alpha = 1\/2^m$. We need to figure out how to choose $m$ and $t$ to get $epsilon$-precision at the end of HHL, i.e. $epsilon$-precision for estimating $mu$.
    // - QPE uses $Ctrl(U)$, ..., $Ctrl(U^(2^(m - 1)))$. Can implemented $Ctrl(U) = mat(I, 0; 0, U)$ on $tilde(A) = mat(0, 0; 0, A)$. So we need to implement $e^(-i A t)$ for $t = 1, 2, 4, ..., 2^(m - 1)$. Since $(Ctrl(U))^(2^j) = e^(-i A dot 2^j)$, the total time of evolution is $t_0 = 1 + 2 + dots.c + 2^(m - 1) = O(2^m) = O(1 \/ alpha)$. After controlled rotation and post selection, we get $
    //     ket(tilde(x)') = 1/(D') sum_(j = 1)^N beta_j c / (lambda'_j) ket(v_j) ket(lambda_j')
    // $ where $D'^2 = p = sum_(j = 1)^N abs(beta_j)^2 abs(c \/ lambda'_j)$. We want $ket(tilde(x)')$ to be within $epsilon$ of $ket(tilde(x))$. To establish dependence of $t_0$ on $epsilon$, we use two facts about relative errors:
    //     + $dif (1 \/ lambda) approx 1/lambda^2 dif lambda$, so $(dif (1 \/ lambda))/(1 \/ lambda) = (dif lambda) / lambda$
    //     + If $A'$ and $B'$ approximate $A$ and $B$ to relative error $delta$, then $A' / B'$ approximates $A / B$ to relative error $delta$: $A' / B' = (A(1 + delta))/(B(1 + delta)) = A/B (1 + O(delta))$.
    // So $1/(lambda'_j)$ approximates $1/lambda_j$ to relative error $O(eta / lambda_j) = O(kappa eta)$ since $abs(1 \/ lambda_j) <= kappa$. $D'$ approximates $D$ to relative error $O(kappa eta)$ as well, because $D$ is homogenous in $1/lambda_j$. Using (2) with $A' = beta_j c \/ lambda'_j$ and $B' = D'$, the amplitudes of $ket(tilde(x)')$ approximate those of $ket(tilde(x))$ to $O(kappa eta)$. Hence, $
    //     norm(ket(tilde(x)') - ket(tilde(x))) = norm((1 + O(kappa eta)) ket(tilde(x)) - ket(tilde(x))) = O(kappa eta).
    // $ So we want $O(kappa eta) = epsilon$ so take $eta = epsilon / kappa$, so $t_0 = kappa / epsilon$.

    // So the overall complexity is $O(poly(n) dot t) = O(poly(n) dot kappa dot 1/epsilon)$ (we would get $kappa^2$ without using amplitude amplification).
#remark[
    The condition that there is an efficient Hamiltonian simulation algorithm for $A$ holds for local Hamiltonians and for row-computable matrices.

    Since reading $A$ and $b$ would take $poly(N)$ time if they were stored as their components, there needs to be a more efficient presentation of $A$ (e.g. row-computable matrices) and $b$ (stored as a quantum state). The only time the presentation of $A$ features in HHL is in the Hamiltonian simulation step, so requiring this to run in $poly(n, t)$ time is sufficient.
]
#remark[
    Given $s$-sparse $A$, the best known classical algorithm for computing an $epsilon$-approximation of $mu = x^T M x$ runs in $O(N s sqrt(kappa) dot log(1/epsilon))$ time, even with assumptions comparable to our assumptions for HHL. Classically, there is no known method of estimating the quadratic forms $mu = x^T M x$ which is faster than computing $x$ first. Thus, when $epsilon$ is constant (or even $epsilon = O(1/poly(n))$) and $A$ is well-conditioned and row-sparse, the HHL runtime is an exponential speedup over the classical algorithm runtime.
]


= Clifford computations and classical simulation of quantum computation

== Classical simulation of quantum computation

We want to know whether there is a "key quantum effect or resource" that gives quantum computing its (potential) benefits over classical computing.

To formalise this comparison of quantum vs classical computing, we will define a precise mathematical framework of classical simulation of quantum computation.

#problem("Classical Simulation")[
    / Input:
        - Description of a quantum circuit $C$ as a list of $1$- and $2$- qubit gates acting on $n$ qubit lines.
        - Description of an input product state $ket(alpha_1) tp cdots tp ket(alpha_n)$ (note this also has a $poly(n)$-sized classical description).
        - Description of the designated output qubit(s) line(s).
    / Promise:
        - $C$ has size $N = abs(C) = poly(n)$.
        - We only measure one qubit, for a decision answer.
    / Task: By (randomised) classical means only, perform in $poly(n)$ time one of the following:
        - *Weak simulation*: sample a bit from the output distribution of $C ket(alpha_1) ... ket(alpha_n)$ with the output qubit measured in the computational basis.
        - *Strong simulation*: calculate the output probabilities $Pr("output is" 0) = p$. 
]
#remark[
    Note that the ability to perform strong simulation implies the ability to perform weak simulation.
]
#definition[
    If $C$ is classical simulable (in $poly(n)$ time), then we say there is no *quantum advantage* (up to polynomial overheads).
]
#remark[
    - Any quantum process performs a weak simulation of itself, i.e. the final measurement gives a sample from the output distribution.
    - Strong simulability is a much stronger property.
    - "Direct" strong simulation is always possible, but generally not in polynomial time: the action of successive gates is simply matrix-vector multiplication in a $2^n$-dimensional space, and so we can compute all amplitudes of the output state in $O(2^n)$ time. Although this direct simulation isn't efficient, it shows that any quantum-computable function is also classically computable.
]
#theorem[
    If the state (including the input state) at each stage of a $poly(n)$-sized circuit $C$ is a product of (single-qubit) states, then direct strong simulation can be efficiently performed for $C$ with that input state.
]
#proofhints[
    Express a state at a given stage as a product state and as a sum of computational basis states, assume that the gate acting on it acts non-trivially on the first two qubits (why can we assume this?), then express the state in the next stage as a sum of computational basis states and as a product state.
]
#proof[
    We can assume that each gate of the circuit acts two qubits (by extending the $1$-qubit gates to act trivially on another qubit). Say at a given stage of the circuit, the state is $
        ket(psi) = sum_(i_1, ..., i_n in {0, 1}) c_(i_1 ... i_n) ket(i_1 ... i_n),
    $ and is transformed by a gate $U$. Suppose for simplicity that $U$ acts on the first two qubits (the same argument works for any qubit indices pair). Let $U_i^j$ denote the $(i, j)$-th entry of the matrix representation of $U$ in the computational basis. The action of $U$ on $ket(psi)$ produces the state $
        U ket(psi) & = sum_(i_1, ..., i_n in {0, 1}) d_(i_1 ... i_n) ket(i_1 ... i_n), \
        "where" quad d_(i_1 ... i_n) & = sum_(k_1, k_2 in {0, 1}) U_(i_1 i_2)^(k_1 k_2) c_(k_1 k_2 i_3 ... i_n).
    $ But now since $ket(psi)$ is a product state, it can be expressed as $
        ket(psi) = times.circle.big_(j = 1)^n (alpha_j^((0)) ket(0) + alpha_j^((1)) ket(1)),
    $ where $c_(i_1 ... i_n) = product_(j = 1)^n alpha_j^((i_j))$. Hence, $
        d_(i_1 ... i_n) = underbrace(sum_(k_1, k_2 in {0, 1}) U_(i_1 i_2)^(k_1 k_2) alpha_1^((k_1)) alpha_2^((k_2)), =: med gamma_(i_1 i_2)) dot product_(j = 3)^n alpha_j^((i_j)).
    $ The first term in the product is simply an inner product of two $4$-dimensional vectors, so can be computed in $O(1)$ time. Finally, since by assumption $U ket(psi)$ is a product state, it can be expressed as $
        U ket(psi) = times.circle.big_(j = 1)^n (beta_j^((0)) ket(0) + beta_j^((1)) ket(1)),
    $ where $d_(i_1 ... i_n) = product_(j = 1)^n beta_j^((i_j))$. We have $beta_j^((k)) = alpha_j^((k))$ for all $k in {0, 1}$ and $j >= 3$ since $U$ acts non-trivially only on the first two qubits. $beta_0^((0)), beta_0^((1)), beta_1^((0)), beta_1^((1))$ can be determined from $gamma_00, gamma_01, gamma_10, gamma_11$ in $O(1)$ time.

    So, inductively, the amplitudes of each single-qubit state which appears in each product state in the circuit can be computed, given those of the previous product state, in constant time, so the final state's amplitudes can be computed in $O(abs(C))$ time from the initial state's amplitudes.
]
#remark[
    Recall that a state is a product state iff it has no entanglement. So it is sometimes claimed that entanglement is the source of quantum speedups. However, the converse is not true, i.e. entanglement is necessary but not sufficient.
]

== Clifford computations

#definition[
    The $1$-qubit Pauli group $cal(P)_1$ is ${plus.minus i, plus.minus 1} dot {I, X, Y, Z}$ with the usual rules $X Y = i Z$, etc. The $n$-qubit Pauli group is $cal(P)_n = cal(P)_1 tp dots.c tp cal(P)_1$.
]<def:pauli-group>
#definition[
    A *Clifford operation* on $n$-qubits is a unitary $C in U(2^n)$ which preserves the Pauli group under conjugation, i.e. $
        forall P in cal(P)_n, quad C^dagger P C in cal(P)_n.
    $ The *Clifford group* is the set of all Clifford operations - it is the normaliser of the subgroup $cal(P)_n$.
]
#remark[
    Clifford groups are important in applications:
    - Quantum error correction (e.g. stabiliser codes) and fault-tolerance.
    - They give insights into the power of quantum vs classical computing.
]
#example[
    - All Pauli matrices are Clifford operations.
    - $1$-qubit Clifford operations include $H$ (e.g. $H Z H = X$) and $S = mat(1, 0; 0, i)$.
    - $2$-qubit Clifford operations include $Ctrl(X)$ and SWAP, e.g. $Ctrl(X_(1 2)) Z_1 Ctrl(X_(1 2)) = Z_1 Z_2$, and $Ctrl(X_(1 2)) Ctrl(X_(2 1)) Ctrl(X_(1 2)) = "SWAP"_(1 2)$.
]
#theorem[
    $C in U(2^n)$ is Clifford iff it can be decomposed into a circuit of $H$, $S$ and $Ctrl(X)$ gates.
]<thm:clifford-iff-decomposable-into-hadamard-s-and-c-not-gates>
#proof[
    Omitted.
]
#definition[
    A *Clifford computation/circuit* is a circuit consisting only of Clifford gates, with a measurement in the computational basis at the end, and possibly with intermediate (for our purposes, $1$-qubit) measurements in the $Z$ basis.
    
    We treat each intermediate measurement as an extra elementary computational step (called a "measurement gate"). Note we can apply unitary gates to the post-intermediate-measurement states.
]<def:clifford-circuit>
#example[
    $
        ket(0) ket(0) -->^H ket(+) ket(0) -->^(Ctrl(X)) 1/sqrt(2) (ket(00) + ket(11))
    $ is a Clifford circuit. More generally, the family of *Cat/GHZ* circuits are Clifford circuits: $
        ket(0)^(tp n) -->^H ket(plus)^(tp n) -->^Ctrl(X_(1 2)) dots.c -->^Ctrl(X_(1 n)) 1/sqrt(2) (ket(0)^(tp n) + ket(1)^(tp n)).
    $
]
#theorem("Gottesman-Knill")[
    Let $C$ be any $M = poly(n)$-size Clifford circuit on $n$ qubits with no intermediate measurements, let any product state $ket(alpha_1) ... ket(alpha_n)$ be the input state and let the output be a measurement on the (WLOG, by applying SWAP gates) first qubit line. Then the output can always be classically strongly (and so also weakly) simulated efficiently.
]<thm:gottesman-knill>
#proofhints[
    Denote by $p_i$ the probability of the measurement yielding outcome $i$ for $i = 0, 1$. Express $p_0 - p_1$ in bra-ket notation, the rest is straightforward.
]
#proof[
    Idea: instead of evolving the input state $ket(psi_"in")$ to $C ket(psi_"in") =: ket(psi_"end")$, we "backpropagate" the final measurement to $ket(psi_"in")$.

    Noting that $Z = ket(0) bra(0) - ket(1) bra(1)$, write $Z_1 = Pi_0 - Pi_1$, where $Pi_0$ and $Pi_1$ are projectors onto the subspaces $span{ket(00...0)}$ and $span{ket(10...0)}$ respectively. Let the unitary part of $C$ be $C_M dots.c C_1$. Denoting by $p_i$ the probability of the measurement yielding outcome $i$ for $i = 0, 1$, we have $
        p_0 - p_1 & = braket(psi_"end", Z_1, psi_"end") = braket(psi_"in", C^dagger Z_1 C, psi_"in") \
        & = braket(psi_"in", C_1^dagger dots.c C_M^dagger Z_1 C_M dots.c C_1, psi_"in")
    $ $C_1^dagger dots.c C_M^dagger Z_1 C_M dots.c C_1$ is a successive conjugation of $Z_1$ by Clifford operations (and each is a $1$- or $2$- qubit conjugation, hence each conjugation is a constant size computation).

    By the definition of Clifford operations, we obtain $
        p_0 - p_1 = braket(psi_"in", tilde(P)_1 tp dots.c tp tilde(P)_n, psi_"in")
    $ where each $tilde(P)_i$ is in the Pauli group. Hence, since $ket(psi_"in") = ket(alpha_1) ... ket(alpha_n)$, the above factorises: $
        p_0 - p_1 = product_(i = 1)^n braket(alpha_i, tilde(P)_i, alpha_i).
    $ Each $braket(alpha_i, tilde(P)_i, alpha_i)$ is a $2 times 2$ matrix computation. So computing $p_0 - p_1$ takes $O(n)$ time classically. We also need $O(M)$ time for computing $tilde(P)_1 tp dots.c tp tilde(P)_n = C^dagger Z_1 C$. Since we also know $p_0 + p_1 = 1$, we can obtain $p_0$ and $p_1$.
]
#definition[
    A Clifford circuit with intermediate measurements is *non-adaptive* if it does not depend on the intermediate measurement outcomes, and *adaptive* otherwise.
]<def:clifford-circuit.adaptive>
#theorem[
    The set of Clifford gates together with the gate $T = mat(1, 0; 0, e^(i pi \/ 4))$ are a universal gate set for quantum computation.
]<thm:cliffords-and-t-are-universal-gate-set>
#proof[
    Omitted.
]
#theorem[
    Let $C$ be any $poly(n)$-sized Clifford circuit consisting of intermediate measurements, let $ket(psi_"in") = ket(alpha_1) ... ket(alpha_n)$ be the input state, and say we measure on the (WLOG) first qubit.
    + If $C$ is non-adaptive, then the output is classically strongly simulable efficiently.
    + Adaptive Clifford circuits are sufficient for fully universal quantum computation.
]<thm:adaptivity-determines-classical-strong-simulation-or-universal-quantum-computation>
#proofhints[
    See proof sketch.
]
#proof("sketch")[
    + Non-adaptive Clifford circuits are reducible to fully unitary Clifford circuits, using ancillary qubits and $Ctrl(X)$ gates (then done by @thm:gottesman-knill).
    + Use the Brayvi-Kitaev idea of "magic states" and @thm:cliffords-and-t-are-universal-gate-set. Let $ket(A) = 1/sqrt(2) (ket(0) + e^(i pi \/ 4) ket(1))$ denote the $1$-qubit "magic state". We'll implement the $T$ gate using the following "$T$-gadget":
    #figure(quantum-circuit(
        lstick($ket(psi)$), 1, ctrl(1), 2, gate($S^m$), 1, rstick($T ket(psi)$), nl,
        lstick($ket(A)$), 1, targ(), meter(), setwire(2), 1, ctrl(-1, wire-count: 2, label: ((content: [Measurement: \ $m in {0, 1}$], pos: bottom))), 1, rstick("discard")
    ))
]
#remark[
    @thm:cliffords-and-t-are-universal-gate-set and @thm:adaptivity-determines-classical-strong-simulation-or-universal-quantum-computation show we can achieve an increase in power from classically simulable to quantum universal by either:
    - Allowing Clifford circuits to use non-Clifford gates, e.g. $T$, or
    - Allowing only Clifford operations and intermediate measurements, but also the exotic resource "magic" states.
]
#remark[
    If $C$ is a $poly(n)$-sized adaptive Clifford circuit whose only inputs are computational basis states, then the output of $C$ is classically _weakly_ simulable efficiently.
]