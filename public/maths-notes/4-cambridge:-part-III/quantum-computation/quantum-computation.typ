#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let poly = math.op("poly")
#let ip(a, b) = $angle.l #a, #b angle.r$
#let ket(arg) = $#h(0.2pt) | #h(0.2pt) arg #h(0.2pt) angle.r$
#let bra(arg) = $angle.l #h(0.2pt) arg #h(0.2pt) | #h(0.2pt)$
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

= Hidden subgroup problem

== Review of Shor's algorithm

#definition[
    The *factoring problem* is: given a positive integer $N$, find a non-trivial factor ($!= 1, N$) in time polynomial in $n$ (i.e. $O(poly(n))$), where $n = O(log N)$ is the length of the description of the problem input (memory/space used to store it).
]<def:factoring-problem>
#definition[
    An *efficient problem* is one that can be solved in polynomial time.
]<def:efficient-problem>
#remark[
    Clasically, the best known factoring algorithm runs in $e^(O(n^(1\/3) (log n)^(2\/3)))$. Shor's algorithm (quantum) runs in $O(n^3)$ by converting factoring into period finding:
    - Given input $N$, choose $a < N$ which is coprime to $N$.
    - Define $f: ZZ -> ZZ\/N$, $f(x) = a^x mod N$. $f$ is periodic with period $r$ (the order of $a mod N$), i.e. $f(x + r) = f(x)$ for all $x in ZZ$. Finding $r$ allows us to factor $N$.
]

== Period finding

#problem(name: "Periodicity Determination")[
    Given an oracle for $f: ZZ\/M -> ZZ\/N$ with promises:
    - $f$ is periodic with period $r < M$ (i.e. $forall x in ZZ\/M$, $f(x + r) = f(x)$),
    - $f$ is one-to-one in each period (i.e. $forall 0 <= x < y < r$, $f(x) != f(y)$),
    find $r$ in time $O(poly(m))$, where $m = O(log M)$.

    Clasically, this requires takes time $O\(sqrt(M)\)$.
]<prb:periodicity-determination>
#definition[
    Let $f: ZZ\/M -> ZZ\/N$. Let $H_M$ and $H_N$ be quantum state spaces with orthonormal state bases ${ket(i): i in ZZ\/N}$ and ${ket(j): j in ZZ\/M}$. Define the unitary *quantum oracle* for $f$ by $U_f$ by $
        U_f ket(x) ket(z) = ket(x) ket(z + f(x)).
    $ The first register $ket(x)$ is the *input register*, the last register $ket(z)$ is the *output register*.
]<def:quantum-oracle>
#definition[
    The *quantum query complexity* of an algorithm is the number of times it queries $f$ (i.e. uses $U_f$).
]<def:quantum-query-complexity>
#definition[
    The *quantum Fourier transform* over $ZZ\/M$ is the unitary defined by its action on the computational basis: $
        U_"QFT" ket(x) = 1/sqrt(M) sum_(y = 0)^(M - 1) omega^(x y) ket(y),
    $ where $omega = e^(2pi i\/M)$. Note that $U_"QFT"$ requires only $O\((log M)^2\)$ gates to implement, whereas a general unitary requires $O(4^n \/ n)$ elementary gates.
]<def:quantum-fourier-transform>
#lemma[
    Let $alpha = e^(2pi i y\/M)$. Then $
        sum_(j = 0)^(k - 1) alpha^j = cases(
            (1 - alpha^k)/(1 - alpha) = 0 & "if" alpha != 1 "i.e." M divides.not y,
            k & "if" alpha = 1 "i.e." M divides y
        ).
    $
]
#lemma(name: "Boosting success probability")[
    If a process succeeds with probability $p$ on one trial, then $
        Pr("at least one success in" t "trials") = 1 - (1 - p)^t > 1 - delta
    $ for $t = log(1\/d)/p$.
]
#theorem(name: "Co-primality Theorem")[
    The number of integers less than $r$ that are coprime to $r$ is $O(r\/log log r)$ for large $r$.
]
#algorithm(name: "Quantum Period Finding")[
    Let $f: ZZ\/M -> ZZ\/N$ be periodic with period $r < M$ and one-to-one in each period. Let $A = M/r$ be the number of periods. We work over the state space $H_M tp H_N$.
    + Construct the state $1/sqrt(M) sum_(i = 0)^(M - 1) ket(i) ket(0)$.
    + Query $U_f$ on the state, giving $1/sqrt(M) sum_(i = 0)^(M - 1) ket(i) ket(f(i))$.
    + Measure second register in computational basis, giving outcome $y in ZZ\/N$, and input state collapses to $ket("per") = 1/sqrt(A) sum_(j = 0)^(A - 1) ket(x_0 + j r)$, where $f(x_0) = y$ and $0 <= x_0 < r$. TODO: add diagram showing amplitudes for this state.
    + Apply the Quantum Fourier Transform to $ket("per")$: $
        QFT ket("per") & = 1/sqrt(M) sum_(y = 0)^(M - 1) 1/sqrt(A) sum_(j = 0)^(A - 1) omega^((x_0 + j r) y) ket(y) \
        & = 1/sqrt(M A) sum_(y = 0)^(M - 1) omega^(x_0 y) sum_(j = 0)^(A - 1) omega^(j r y) ket(y) \
        & = sqrt(A/M) sum_(k = 0)^(r - 1) omega^(x_0 k M\/r) ket(k M\/r)
    $ Note now the outcomes and probabilities are independent of $x_0$, so carry useful information about $r$. TODO add diagram showing amplitudes for this state.
    + Measure $QFT ket("per")$, yielding outcome $c = k_0 M\/r$ for some $0 <= k_0 < r$. So $c/M = k_0/r$. If $k_0$ is corpime to $r$, then the denominator $r_0$ of the simplified fraction $c/M$ is equal to $r$.
    + By the coprimality theorem, the probability that $k_0$ is coprime to $r$ is $O(1\/log log r)$.
    + To check if the computed value $r_0$ of $r$ is correct, compute/query $U_f$ to check if $f(0) = f(r_0)$ (this works since $f$ is periodic and one-to-one in each period, and $r_0 <= r$).
    + Repeat the previous steps $O(log log r) = O(log log M) = O(log m)$ times. This obtains the correct value of $r$ with high probability.
]
#remark[
    Why is QFT helpful for period finding?
    
    Let $R = {0, r, ..., (A - 1)r} in ZZ\/M$, so $
        ket(R) & = 1/sqrt(A) sum_(k = 0)^(A - 1) ket(k r) \
        ket("per") = ket(x_0 + R) & = 1/sqrt(A) sum_(k = 0)^(A - 1) ket(x_0 + k r).
    $ For each $x_0 in ZZ\/M$, define the shift operator $k -> x_0 + k$ and the associated linear map $U(x_0): H_M -> H_M$, $ket(k) |-> ket(x_0 + k)$. Since $(ZZ\/M, +)$ is abelian, all $U(x_i)$ commute: $U(x_1) U(x_2) = U(x_1 + x_2) = U(x_2) U(x_1)$. Hence, they have a simultaneous basis of eigenvectors ${ket(chi_k): k in ZZ\/M}$, i.e. for all $k, x_0 in ZZ\/M$, $U(x_0) ket(chi_k) = w(x_0, k) ket(chi_k)$, where $abs(w(x_0, k)) = 1$. The $ket(chi_k)$ are called *shift-invariant states* and form an orthonormal basis for $H_M$.

    Now $
        ket(R) & = sum_(k = 0)^(M - 1) a_k ket(chi_k), quad a_k "depend only on" r \
        ket("per") & = U(x_0) ket(R) = sum_(k = 0)^(M - 1) a_k w(x_0, k) ket(chi_k)
    $ So measurement in the $ket(chi_k)$ basis gives outcome $k$ with $Pr(k) = |a_k w(x_0, k)|^2 = |a_k|^2$. Suppose the unitary $U$ maps from the shift-invariant basis to the computational basis: $U: ket(chi_k) |-> ket(k)$.
]