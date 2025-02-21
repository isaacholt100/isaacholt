#import "@preview/quill:0.2.0": *
#import "../../template.typ": *
#import "../../diagram-style.typ": *
#import "@preview/cetz:0.3.1" as cetz: canvas, draw
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