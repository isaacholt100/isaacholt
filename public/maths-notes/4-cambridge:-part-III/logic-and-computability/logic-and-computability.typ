#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge
#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Logic and Computability Notes",
    author: "Isaac Holt",
    keywords: ("logic", "computability")
)

#let proves = sym.tack.r
#let satisfies = sym.tack.r.double
#let False = sym.perp

= Non-classical logic

== Intuitionistic logic

Idea: a statement is true if there is a proof of it. A proof of $phi => psi$ is a "procedure" that can convert a proof of $phi$ to a proof of $psi$. A proof of $not phi$ is a proof that there is no proof of $phi$.

In particular, $not not phi$ is not always the same as $phi$.

#fact[
    The Law of Excluded Middle (LEM) ($phi or not phi$) is not (generally) intuitionistically valid.
]

Moreover, the Axiom of Choice is incompatible with intuitionistic set theory.

In intuitionistic logic, $exists$ means an explicit element can be found.

Why bother with intuitionistic logic?
- Intuitionistic mathematics is more general, as we assume less (no LEM or AC).
- Several notions that are conflated in classical mathematics are genuinely different constructively.
- Intuitionistic proofs have a computable content that may be absent in classical proofs.
- Intuitionistic logic is the internal logic of an arbitrary topos.

We will inductively define a provability relation by enforcing rules that implement the BHK-interpretation.

#let Proof(..content) = figure(table(
  columns: (auto,),
  inset: 8pt,
  align: horizon,
  stroke: (x, y) => if y == 0 { none } else {(top: 1pt + black, right: none, left: none, bottom: none)},
  ..content
))

#definition[
    A set is *inhabited* if there is a proof that it is non-empty.
]<def:set.inhabited>
#axiom("Choice - Intutionistic Version")[
    Any family of inhabited sets admits a choice function.
]<axm:choice>
#theorem("Diaconescu")[
    The Law of Excluded Middle can be intutionistically deduced from the Axiom of Choice.
]<thm:diaconescu>
#proofhints[
    - Proof should use Axioms of Separation, Extensionality and Choice.
    - For proposition $phi$, consider $A = {x in {0, 1}: phi or (x = 0)}$ and $B = {x in {0, 1}: phi or (x = 1)}$.
    - Show that we have a proof of $f(A) = 0 or f(A) = 1$, similarly for $f(B)$.
    - Consider the possibilities that arise from above, show that they lead to either a proof of $phi$ or a proof of $not phi$.
]
#proof[
    - Let $phi$ be a proposition. By the Axiom of Separation, the following are sets: $
        A & = {x in {0, 1}: phi or (x = 0)}, \
        B & = {x in {0, 1}: phi or (x = 1)}.
    $
    - Since $0 in A$ and $1 in B$, we have a proof that ${A, B}$ is a family of inhabited sets, thus admits a choice function $f: {A, B} -> A union B$ by the Axiom of Choice.
    - $f$ satisfies $f(A) in A$ and $f(B) in B$ by definition.
    - So we have $f(A) = 0$ or $phi$ is true, and $f(B) = 1$ or $phi$ is true. Also, $f(A), f(B) in {0, 1}$.
    - Now $f(A) in {0, 1}$ means we have a proof of $f(A) = 0 or f(A) = 1$ and similarly for $f(B)$.
    - There are the following possibilities:
        + We have a proof that $f(A) = 1$, so $phi or (1 = 0)$ has a proof, so we must have a proof of $phi$.
        + We have a proof that $f(B) = 0$, so $phi or (0 = 1)$ has a proof, so we must have a proof of $phi$.
        + We have a proof that $f(A) = 0 and f(B) = 1$, in which case we can prove $not phi$: assume there is a proof of $phi$, we can prove that $A = B$ (by the Axiom of Extensionality), in which case $0 = f(A) = f(B) = 1$: contradiction.
    - So we can always specify a proof of $phi$ or a proof of $not phi$.
]
#notation[
    We write $Gamma proves phi$ to mean that $phi$ is a consequence of the formulae in the set $Gamma$. $Gamma$ is called the *set of hypotheses or open assumptions*.
]
#notation[
    Notation for assumptions and deduction.
]
#definition[
    The rules of the *intuitionistic propositional calculus (IPC)* are:
    - conjunction introduction,
    - conjunction elimination,
    - disjunction introduction,
    - disjunction elimination,
    - implication introduction,
    - implication elimination,
    - assumption,
    - weakening,
    - construction,
    - and for any $A$, $ (Gamma proves False)/(Gamma proves A). $
    as defined below.
]<def:rules-of-ipc>
#definition[
    The *conjunction introduction ($and$-I)* rule: $
        (Gamma proves A quad Gamma proves B)/(Gamma proves A and B).
    $
]<def:conjunction-introduction>
#definition[
    The *conjunction elimination ($and$-E)* rule: $
        (Gamma proves A)/(Gamma proves A or B), quad (Gamma proves B)/(Gamma proves A or B).
    $
]<def:conjunction-elimination>
#definition[
    The *disjunction introduction ($or$-I)* rule: $
        (Gamma proves A)/(Gamma proves A or B), quad (Gamma proves B)/(Gamma proves A or B).
    $
]<def:disjunction-introduction>
#definition[
    The *disjunction elimination (proof by cases) ($or$-E)* rule: $
        (Gamma, A proves C quad Gamma, B proves C quad Gamma proves A or B)/(Gamma proves C).
    $
]<def:disjunction-elimination>
#definition[
    The *implication/arrow introduction ($->$-I)* rule (note the similarity to the deduction theorem): $
        (Gamma, A proves B)/(Gamma proves A -> B).
    $
]<def:implication-introduction>
#definition[
    The *implication/arrow elimination ($->$-E)* rule (note the similarity to modus ponens): $
        (Gamma proves A -> B quad Gamma proves A)/(Gamma proves B).
    $
]<def:implication-elimination>
#definition[
    The *assumption ($A x$)* rule: for any $A$, $
        ()/(Gamma, A proves A)
    $
]<def:assumption>
#definition[
    The *weakening* rule: $
        (Gamma proves B)/(Gamma, A proves B).
    $
]<def:weakening>
#definition[
    The *construction* rule: $
        (Gamma, A, A proves B)/(Gamma, A proves B).
    $
]<def:construction>
#remark[
    We obtain classical propositional logic (CPC) from IPC by adding either:
    - $Gamma proves A or not A$: $ ()/(Gamma proves A or not A), $ or
    - If $Gamma, not A proves False$, then $Gamma proves A$: $ (Gamma, not A proves False)/(Gamma proves A). $
]
#notation[
    see scan
]
#definition[
    We obtain *intuitionistic first-order logic (IQC)* by adding the following rules to IPC for quantification:
    - existental inclusion,
    - existential elimination,
    - universal inclusion,
    - universal elimination
    as defined below.
]<def:rules-of-iqc>
#definition[
    The *existential inclusion ($exists$-I)* rule: for any term $t$, $
        (Gamma proves phi[t\/x])/(Gamma proves exists x . phi(x)).
    $
]<def:existential-inclusion>
#definition[
    The *existential elimination ($exists$-I)* rule: $
        (Gamma proves exists x . phi quad Gamma, phi proves psi)/(Gamma proves psi),
    $ where $x$ is not free in $Gamma$ or $psi$.
]<def:existentail-elimination>
#definition[
    The *universal inclusion ($forall$-I)* rule: $
        (Gamma proves phi)/(Gamma proves forall x . phi),
    $ where $x$ is not free in $Gamma$.
]<def:universal-inclusion>
#definition[
    The *universal exclusion ($forall$-E)* rule: $
        (Gamma proves forall x . phi(x))/(Gamma proves phi[t\/x]),
    $ where $t$ is a term.
]<def:universal-exclusion>
#definition[
    We define the notion of *discharging/closing* open assumptions, which informally means that we remove them as open assumptions, and append them to the consequence by adding implications. We enclose discharged assumptions in square brackets $[]$ to indicate this, and add discharged assumptions in parentheses to the right of the proof. For example, $->$-I is written as $
        (Gamma, & [A] \ & dots.v \ & B )/(Gamma proves A -> B) (A)
    $
]
#example[
    A natural deduction proof that $A and B -> B and A$ is given below: $
        (([A and B])/A quad ([A and B])/B)/((B and A)/(A and B -> B and A) (A and B))
    $
]
#example[
    A natural deduction proof of $phi -> (psi -> phi)$ is given below (note clearly we must use $->$-I): 
    #Proof(
        $[phi] quad [psi]$,
        $psi -> phi$,
        $phi -> (psi -> phi)$
    )
]
#example[
    A natural deduction proof of $(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))$ (note clearly we must use $->$-I):
    #Proof(
        $[phi -> (psi -> chi)] quad [phi -> psi] quad [phi]$,
        $psi -> chi quad quad psi$,
        $chi$,
        $phi -> chi$,
        $(phi -> psi) -> (phi -> chi)$,
        $(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))$
    )
]
#notation[
    If $Gamma$ is a set of propositions, $phi$ is a proposition and $L in {"IPC", "IQC", "CPC", "CQC"}$, write $Gamma proves_L phi$ if there is a proof of $phi$ from $Gamma$ in the logic $L$.
]
#lemma[
    If $Gamma proves_"IPC" phi$, then $Gamma, psi proves_"IPC" phi$ for any proposition $psi$. If $p$ is a primitive proposition (doesn't contain any logical connectives or quantifiers) and $psi$ is any proposition, then $Gamma[psi\/p] proves_"IPC" phi[psi\/p]$.
]
#proof[
    Induction on number of lines of proof (exercise).
]

== The simply typed $lambda$-calculus

#definition[
    The set $Pi$ of *simple types* is generated by the grammar $
        Pi := U | Pi -> Pi
    $ where $U$ is a countable set of *type variables (primitive types)* together with an infinite set of $V$ of *variables*. So $Pi$ consists of $U$ and is closed under $->$: for any $a, b in Pi$, $a -> b in Pi$.
]<def:simple-types>
#definition[
    The set $Lambda_Pi$ of *simply typed $lambda$-terms* is defined by the grammar $
        Lambda_Pi := V | lambda  V: Pi thin . thin Lambda_Pi | Lambda_Pi med Lambda_Pi
    $ In the term $lambda x: tau . M$, $x$ is a variable, $tau$ is type and $M$ is a $lambda$-term. Forming terms of this form is called *$lambda$-abstraction*. Forming terms of the form $Lambda_Pi Lambda_Pi$ is called *$lambda$-application*.
]<def:simply-typed-lambda-term>
#example[
    The $lambda$-term $lambda x: ZZ . x^2$ should represent the function $x |-> x^2$ on $ZZ$.
]
#definition[
    A *context* is a set of pairs $Gamma = {x_1: tau_1, ..., x_n: tau_n}$ where the $x_i$ are distinct variables and each $tau_i$ is a type. So a context is an assignment of a type to each variable in a given set. Write $C$ for the set of all possible contexts. Given a context $Gamma in C$, write $Gamma, x: tau$ for the context $Gamma union {x: tau}$ (if $x$ does not appear in $Gamma$).

    The *domain* of $Gamma$ is the set of variables ${x_1, ..., x_n}$ that occur in it, and its *range*, $abs(Gamma)$, is the set of types ${tau_1, ..., tau_n}$ that it manifests.
]<def:context>
#definition[
    Recursively define the *typability relation* $forces subset.eq C times Lambda_Pi times Pi$ via:
    + For every context $Gamma$, variable $x$ not occurring in $Gamma$ and type $tau$, we have $Gamma, x: tau forces x: tau$.
    + For every context $Gamma$, variable $x$ not occurring in $Gamma$, types $sigma, tau in Pi$, and $lambda$-term $M$, if $Gamma, x: sigma forces M: tau$, then $Gamma forces (lambda x: sigma . M): (sigma -> t)$.
    + For all contexts $Gamma$, types $sigma, tau in Pi$, and terms $M, N in Lambda_Pi$, if $Gamma forces M: (sigma -> t)$ and $Gamma forces N: sigma$, then $Gamma forces (M N): tau$.
]<def:typability-relation>
#definition[
    For $Gamma in C$, we say a $lambda$-term $M in Lambda_Pi$ is *typable* if for some type $tau in Pi$, $Gamma forces M: tau$.
]
#notation[
    We will refer to the $lambda$-calculus of $Lambda_Pi$ with this typability relation as $lambda(->)$.
]
#definition[
    A variable $x$ occurring in a $lambda$-abstraction $lambda x: sigma . M$ is *bound* and is *free* otherwise. A term with no free variables is called *closed*.
]<def:variable.bound-and-free>
#definition[
    Terms $M$ and $N$ are *$alpha$-equivalent* if they differ only in the names of their bound variables.
]<def:alpha-equivalence>
#definition[
    If $M$ and $N$ are $lambda$-terms and $x$ is a variable, then we define the *substitution of $N$ for $x$ in $M$* by the following rules:
    - $x[x := N] = N$.
    - $y[x := N] = y$ for $y != x$.
    - $(P Q)[x := N] = P[x := N] Q[x := N]$ for $lambda$-terms $P, Q$.
    - $(lambda y: sigma . P)[x := N] = lambda y: sigma . (P[x := N])$ for $x != y$ and $y$ not free in $N$.
]<def:substitution>
#definition[
    The *$beta$-reduction* relation is the smallest relation $-->_beta$ on $Lambda_Pi$ closed under the following rules:
    - $(lambda x: sigma . P) Q -->_beta P[x := Q]$. The term being reduced is called a *$beta$-redex*, and the result is called its *$beta$-contraction*.
    - If $P -->_beta P'$, then for all variables $x$ and types $sigma in Pi$, we have $lambda x: sigma . P -->_beta lambda x: sigma . P'$.
    - If $P -->_beta P'$ and $Z$ is a $lambda$-term, then $P Z -->_beta P' Z$ and $Z P -->_beta Z P'$.
]<def:beta-reduction>
#definition[
    We define *$beta$-equivalence*, $equiv_beta$, as the smallest equivalence relation containing $-->_beta$.
]<def:beta-equivalence>
#example[
    We have $(lambda x: ZZ . (lambda y: tau . x)) 2 -->_beta (lambda y: tau . 2)$.
]
#lemma("Free Variables Lemma")[
    Let $Gamma forces M: sigma$. Then
    - If $Gamma subset.eq Gamma'$, then $Gamma' forces M: sigma$.
    - The free variables of $M$ occur in $Gamma$.
    - There is a context $Gamma^* subset.eq Gamma$ whose variables are exactly the free variables in $M$, with $Gamma^* forces M: sigma$.
]<lem:free-variables>
#proof[
    By induction on the grammar (exercise).
]
#lemma("Generation Lemma")[
    + For every variable $x in V$, context $Gamma$ and type $sigma in Pi$: if $Gamma forces x: sigma$, then $x: sigma in Gamma$.
    + If $Gamma forces (M N): sigma$, then there is a type $tau in Pi$ such that $Gamma forces M: tau -> sigma$ and $Gamma forces N: tau$.
    + If $Gamma forces (lambda x . M): sigma$, then there are types $tau, rho in Pi$ such that $Gamma, x: tau forces M: rho$ and $sigma = (tau -> rho)$.
]<lem:generation>
#proof[
    By induction on the grammar (exercise).
]
#lemma("Substitution Lemma")[
    + If $Gamma forces M: sigma$ and $alpha in U$ is a type variable, then $Gamma[alpha := tau] forces M: sigma[alpha := tau]$.
    + If $Gamma, x: tau forces M: sigma$ and $Gamma forces N: tau$, then $Gamma forces M[x := N]: sigma$.
]<lem:substitution>
#proof[
    By induction on the grammar (exercise).
]
#proposition("Subject Reduction")[
    If $Gamma forces M: sigma$ and $M -->_beta N$, then $Gamma forces N: sigma$.
]<prop:subject-reduction>
#proof[
    - By induction on the derivation of $M -->_beta N$, using Generation and Substitution Lemmas (exercise).
]
#definition[
    A $lambda$-term $M in Lambda_Pi$ is an *$beta$-normal form ($beta$-NF)* if there is no term $N != M$ such that $M -->_beta N$.
]<def:lambda-term.beta-normal-form>
#notation[
    Write $M ->>_beta N$ if $M$ reduces to $N$ after (potentially) multiple $beta$-reductions.
]
#theorem([Church-Rosser for $lambda(->)$])[
    Suppose that $Gamma forces M: sigma$. If $M ->>_beta N_1$ and $M ->>_beta N_2$, then there is a $lambda$-term $L$ such that $N_1 ->>_beta L$ and $N_2 ->>_beta L$, and $Gamma forces L: sigma$.
]<thm:church-rosser>
#remark[
    In Church-Rosser, the fact that $M ->>_beta N_1$ and $M ->>_beta N_2$ implies that $N_1, N_2 ->>_beta L$ is called *confluence*, and can be represented diagramatically as
    #figure(diagram(cell-size: 5mm, $
        & M edge("ld", ->>) edge("rd", ->>) & \
        N_1 edge("rd", ->>) & & N_2 edge("ld", ->>) \
        & L &
    $))
]
#corollary("Uniqueness of normal form")[
    If a simply-typed $lambda$-term admits a $beta$-NF, then this form is unique.
]<cor:uniqueness-of-beta-normal-form>
#proposition("Uniqueness of types")[
    + If $Gamma forces M: sigma$ and $Gamma forces M: tau$, then $sigma = tau$.
    + If $Gamma forces M: sigma$, $Gamma forces N: tau$, and $M equiv_beta N$, then $sigma = tau$.
]<prop:uniqueness-of-types>
#proof[
    + Induction (exercise).
    + By Church-Rosser, there is a $lambda$-term $L$ which both $M$ and $N$ reduce to (since $beta$-equivalence means there is a finite sequence of alternating up and down $->>_beta$ relations). By Subject Reduction, we have $Gamma forces L: sigma$ and $Gamma forces L: tau$, so $sigma = tau$ by 1.
]
#example[
    There is no way to assign a type to $lambda x . x x$: let $x$ be of type $tau$, then by the Generation Lemma, in order to apply $x$ to $x$, $x$ must be of type $tau -> sigma$ for some type $sigma$. But $tau != tau -> sigma$, which contradicts Uniqueness of Types.
]
#definition[
    The *height function* is the recursively defined map $h: Pi -> NN$ that maps all type variables $u in U$ to $0$, and a function type $sigma -> tau$ to $1 + max{h(sigma), h(tau)}$: $
        h: Pi & -> NN, \
        h(alpha) & = 0 quad forall alpha in U, \
        h(sigma -> tau) & = 1 + max{h(sigma), h(tau)} quad forall sigma, tau in Pi.
    $ The *height* of a redex is defined as the height of the type of its $lambda$-abstraction: $
        h((lambda x: sigma . P^tau)^(sigma -> tau) Q) = h(sigma -> tau).
    $
]<def:height-function>
#notation[
    $(lambda x: sigma . P^tau)^(sigma -> tau)$ denotes that $P$ has type $tau$ and the $lambda$-abstraction has type $sigma -> tau$.
]
#theorem([Weak normalisation for $lambda(->)$])[
    Let $Gamma forces M: sigma$. Then there is a finite reduction path $M := M_0 -->_beta M_1 -->_beta ... -->_beta M_n$, where $M_n$ is in $beta$-normal form.
]
#proof("\"Taming the Hydra\"")[
    - Idea is to apply induction on the complexity of $M$.
    - Define a function $m: Lambda_Pi -> NN times NN$ by $
        m(M) := cases(
            (0, 0) & "if" M "is in" beta"-NF",
            (h(M), "redex"(M)) & "otherwise"
        )
    $ where $h(M)$ is the maximal height of a redex in $M$, and $"redex"(M)$ is the number of redexes in $M$ of that height.
    - We use induction over $omega times omega$ to show that if $M$ is typable, then it admits a reduction to $beta$-NF.
    - The problem is that reductions can copy redexes or create new ones, so our strategy is to always reduce the right-most redex of maximal height.
    - We will argue that, by following this strategy, any new redexes that we generate have a strictly lower height than the height of the redex we chose to reduce.
    - If $Gamma forces M: sigma$ and $M$ is already in $beta$-NF, then we are done.
    - So assume $M$ is not in $beta$-NF. Let $Delta$ be the rightmost redex of maximal height $h$.
    - By reducing $Delta$, we may introduce copies of existing redexes or create new ones.
    - Creation of new redexes by $beta$-reduction of $Delta$ in one of the following ways:
        + If $Delta$ is of the form $(lambda x: (rho -> mu) ... x P^rho ...) (lambda y: rho . Q^mu)^(rho -> mu)$, then it reduces to $... (lambda y: rho . Q^mu)^(rho -> mu) P^rho ...$, in which case there is a new redex of height $h(rho -> mu) < h$.
        + We have $Delta = (lambda x: tau . (lambda y: rho . R^mu)) P^tau$ occurring in $M$ in the scenario $Delta^(rho -> mu) Q^rho$. Say $Delta$ reduces to $lambda y: rho . R_1^mu$. Then we create a new redex $(lambda y: rho . R_1^mu) Q^rho$ of height $h(rho -> mu) < h(tau -> (rho -> mu)) = h$.
        + $Delta = (lambda x: (rho -> mu) . x)(lambda y: rho . P^mu)$, which occurs in $M$ as $Delta^(rho -> mu) Q^rho$. Reduction then gives the redex $(lambda y: rho . P^mu) Q^rho$ of height $h(rho -> mu) < h$.
    - Now $Delta$ itself no longer appears in $M$, (lowering the count of redexes of maximal height by $1$), and any newly created redexes have height $< h$.
    - If we have $Delta = (lambda x: tau . P^rho) Q^tau$ and $P$ contains multiple free occurrences of $x$, then all the redexes in $Q$ are multiplied when performing $beta$-reduction.
    - However, our choice of $Delta$ ensures that the height of any such redex in $Q$ has height $< h$ (since these redexes are to the right of $Delta$ in $M$).
    - Thus, it is always the case that for the new term $M'$, $m(M') < m(M)$ in the lexicographic order. So by the induction hypothesis, since $M'$ can be reduced to $beta$-NF, so can $M$.
]
#theorem([Strong Normalisation for $lambda(->)$])[
    Let $Gamma forces M: sigma$. Then there is no infinite reduction sequence $M -->_beta M_1 -->beta ...$.
]
#proof[
    Exercise (sheet 1).
]

== The Curry-Howard correspondence

#remark[
    We can think of a proposition $phi$ as the "type of its proofs". The properties of simply-typed $lambda(->)$ match the rules of IPC rather precisely. We first show a correspondence between $lambda(->)$ and the implicational fragment $"IPC"(->)$ of IPC that includes only the $->$ connective, the axiom scheme, and the ($->$-I) and ($->$-E) rules. We later extend this to all of IPC by introducing more complex types to $lambda(->)$.

    Start with $"IPC"(->)$ and build a simply-typed $lambda$-calculus out of it whose set of type variables $U$ is precisely the set of primitive propositions of the logic. Clearly, the set of types $Pi$ then matches the set of propositions in the logic.
]
#proposition([Curry-Howard correspondence for IPC$(->)$])[
    Let $Gamma$ be a context for $lambda(->)$ and $phi$ be a proposition. Then:
    + If $Gamma forces M: phi$, then $abs(Gamma) = {tau in Pi: (x: tau) in Gamma "for some" x} proves_("IPC"(->)) phi$.
    + If $Gamma proves_("IPC"(->)) phi$, then there is a simply-typed $lambda$-term $M in lambda(->)$ such that $\{(x_phi: phi): phi in Gamma\} forces M: phi$.
]
#proof[
    + 
        - Use induction on the derivation of $Gamma forces M: phi$.
        - Let $x$ be a variable not occurring in $Gamma'$ and the derivation is of the form $Gamma', x: phi forces x: phi$, then we have that $abs(Gamma'\, x: phi) proves_("IPC"(->)) phi$ since $phi proves_("IPC"(->)) phi$ (as $abs(Gamma'\, x: phi) = abs(Gamma') union {phi}$).
        - If the derivation has $M$ of the form $lambda x: sigma . N$ and $phi = (sigma -> tau)$, then we must have $Gamma, x: sigma forces N: tau$. By the induction hypothesis, we have that $abs(Gamma\, x: sigma) proves tau$, i.e. $abs(Gamma), sigma proves tau$. But then $abs(Gamma) proves sigma -> tau$ by ($->$-I).
        - If the derivation is of the form $Gamma forces (P Q): phi$, then we must have $Gamma forces P: (sigma -> phi)$ and $Gamma forces Q: sigma$. By the induction hypothesis, we have $abs(Gamma) proves (sigma -> phi)$ and $abs(Gamma) proves sigma$, so $abs(Gamma) proves phi$ by ($->$-E).
    +
        - Use induction on the derivation of $Gamma proves phi$.
        - Write $Delta = {(x_psi: psi): psi in Gamma}$. Then we only have a few ways to construct a proof at a given stage. Say the derivation is of the form $Gamma, phi proves phi$. If $phi in Gamma$, then clearly $Delta forces x_phi: phi$. If $phi in.not Gamma$, then $Delta, x_phi: phi forces x_phi: phi$.
        - Suppose the derivation is at a stage of the form $ (Gamma proves phi -> psi, quad Gamma proves phi)/(Gamma proves psi) $
        - Then by the induction hypothesis there are $lambda$-terms $M$ and $N$ such that $Delta forces M: (phi -> psi)$ and $Delta forces N: phi$, from which $Delta forces (M N): psi$.
        - If the stage is given by $
            (Gamma, phi proves psi)/(Gamma proves phi -> psi),
        $ then there are two subcases:
            - If $phi in Gamma$, then the induction hypothesis gives $Delta forces M: psi$ for some term $M$. By the weakening rule, we have $Delta, x: phi forces M: M: psi$, where $x$ is a variable not occurring in $Delta$. But then $Delta forces (lambda x: phi . M): (phi -> psi)$.
            - If $phi in.not Gamma$, then the induction hypothesis gives $Delta, x_phi: phi forces M: psi$ for some $lambda$-term $M$, thus $Delta forces (lambda x_phi: phi . M): (phi -> psi)$.
]
#example[
    Let $phi, psi$ be primitive propositions. The $lambda$-term $
        lambda f: (phi -> psi) -> phi . lambda g: phi -> psi . g(f g)
    $ has type $((phi -> psi) -> phi) -> ((phi -> psi) -> psi)$, and therefore encodes a proof of that proposition in IPC($->$).
    #Proof(
        $g: [phi -> psi] quad f: (phi -> psi) -> phi$,
        $f g: phi quad g: [phi -> psi] quad & (->"-E")$,
        $g(f g): psi quad & (->"-E")$,
        $lambda g . g(f g): (phi -> psi) -> psi quad & (->"-I", phi -> psi)$,
        $lambda f . lambda g . g(f g): ((phi -> psi) -> phi) -> ((phi -> psi) -> psi) quad & (->"-I", (phi -> psi) -> phi)$
    )
]
#definition[
    The *full simply-typed $lambda$-calculus* consists of:
    - A set of types $Pi$ generated by the grammar $
        Pi := U | Pi -> Pi | Pi times Pi | Pi + Pi | 0 | 1
    $ Types of the form $Pi times Pi$ are *product types*, those of the form $Pi + Pi$ are *coproduct types*, $0$ is the *initial type*, and $1$ is the *terminal type*. Again, $U$ is a set of type variables.
    - A set of terms $Lambda_Pi$ generated by the grammar $
        Lambda_Pi := & V | lambda V: Pi . Lambda_Pi | Lambda_Pi Lambda_Pi | pi_1 (Lambda_Pi) | pi_2 (Lambda_Pi) | i_1 (Lambda_Pi) | i_2 (Lambda_Pi) \ | & "case"(Lambda_Pi; V . Lambda_Pi; V . Lambda_Pi) | * | !_Pi Lambda_Pi
    $ where $V$ is a set of variables and $*$ is a constant.

    We have the new typing rules: #Proof(
        $Gamma forces M: psi times phi$,
        $Gamma forces pi_1 (M): psi$
    ) #Proof(
        $Gamma forces M: psi times phi$,
        $Gamma forces pi_2 (M): phi$
    ) #Proof(
        $Gamma forces M: psi quad Gamma forces N: phi$,
        $Gamma forces gen(M, N): psi times phi$
    ) #Proof(
        $Gamma forces M: psi$,
        $Gamma forces iota_1 (M): psi + phi$
    ) #Proof(
        $Gamma forces N: phi$,
        $Gamma forces iota_2 (N): psi + phi$
    ) #Proof(
        $Gamma forces L: psi + phi quad Gamma, x: psi forces M: rho quad Gamma, y: phi forces N: rho$,
        $Gamma forces "case"(L; x^psi . M; y^phi . N): rho$
    ) #Proof(
        $quad$,
        $Gamma forces *: 1$
    ) #Proof(
        $Gamma forces M: 0$,
        $Gamma forces !_phi M: phi$
    )
    We also have the new reduction rules:
    - Projections: $pi_1 gen(M, N) -->_beta M$ and $pi_2 gen(M, N) -->_beta N$.
    - Pairs: $gen(pi_1 M, pi_2 M) -->_eta M$.
    - Definition by cases: $"case"(iota_1 (M); x . M; y . L) -->_beta K[x := M]$ and $"case"(iota_2 (M); x . K; y . L) -->_beta L[y := M]$
    - Unit: if $Gamma forces M: 1$, then $M -->_eta *$.
]
#remark[
    We can extend the Curry-Howard correspondence with these new types, letting
    - $0 <--> False$.
    - $times <--> and$.
    - $+ <--> or$.
    - $-> thick <--> thick ->$.
]
#example[
    Consider the following proof of $(phi and chi) -> (psi -> phi)$:
    #Proof(
        $[phi and chi]: p quad [psi]: b$,
        $phi: pi_1 (p)$,
        $(psi -> phi): lambda b: psi . pi_1 (p)$,
        $((phi and chi) -> (psi -> phi)): lambda p: phi times chi . lambda b: psi . pi_1 (p)$
    )
    We decorate this proof by turning the assumptions into variables.
]
#remark[
    We have the following correspondence:
    #figure(table(
        columns: 2,
        [Simply-typed $lambda$-calculus], "IPC",
        [(Primitive) types], [(Primitive) propositions],
        [Variable], [Hypothesis],
        [Simply-typed $lambda$-term], [Proof],
        [Type construction], [Logical connective],
        [Term inhabitation], [Provability],
        [Term reduction], [Proof normalisation]
    ))
]

== Semantics for IPC

#definition[
    A *lattice* is a set $L$ equipped with binary operations $and$ and $or$ which are commutative and associative and satisfy the *absorption laws*: for all $a, b in L$,
    - $a or (a and b) = a$,
    - $a and (a or b) = a$.
]<def:lattice>
#definition[
    A lattice $L$ is *distributive* if for all $a, b, c in L$, $a or (b and c) = (and b) or (a and c)$.
]<def:lattice.distributive>
#definition[
    A lattice $L$ is *bounded* if there are elements $False, top in L$ such that $a or False = a$ and $a and top = a$ for all $a in L$.
]<def:lattice.bounded>
#definition[
    A lattice $L$ is *complemented* if it is bounded and for every $a in L$, there is $a^* in L$ such that $a and a^* = False$ and $a or a^* = top$.
]<def:lattice.complemented>
#definition[
    A *Boolean algebra* is a complemented distributive lattice.
]<def:boolean-algebra>
#remark[
    In any lattice, $and$ and $or$ are idempotent. Moreover, we can define an ordering by setting $a <= b$ if $a and b = a$.
]
#example[
    - For every set $I$, the powerset $powset(I)$ of $I$ with $and = sect$ and $or = union$ is the prototypical Boolean algebra.
    - More generally, the clopen subsets of a topological space form a Boolean algebra with $and = sect$ and $or = union$.
    - In particular, the set of finite and cofinite subsets of $ZZ$ is a Boolean algebra.
]
#proposition[
    Let $L$ be a bounded lattice and $<=$ be the order induced by the operations in $L$ ($a <= b <==> a and b = a$). Then $<=$ is a partial order with least element $bot$ and greatest element $top$, and for all $a, b in L$, $a and b = inf{a, b}$ and $a or b = sup{a, b}$. Conversely, every partial order with all finite $inf$'s and $sup$'s is a bounded lattice.
]
#proof[
    Exercise.
]
Classically, we say that $Gamma satisfies t$ if for every valuation $v: L -> {0, 1}$ such that $v(p) = 1$ for all $p in Gamma$, we have $v(t) = 1$. We might want to replace ${0, 1}$ with some other Boolean algebra to get semantics for IPC, with an accompanying completeness theorem. But Boolean algebras believe in the LEM!

#definition[
    A *Heyting algebra* $H$ is a bounded lattice equipped with a binary operation $=>$ such that for all $a, b, c in H$, $ a and b <= c "iff" a <= (b => c). $ This can be thought of as an algebraic version of the deduction theorem. A *Heyting homomorphism* (morphism of Heyting algebras) is a function that preserves all finite meets ($and$), finite joins ($or$), and $=>$.
]
#example[
    + Every Boolean algebra is a Heyting algebra: define $a => b := a^* or b$ ($a^*$ should be thought of as $not a$). Note that we must have $a^* = (a => bot)$.
    + Every topology on a set $X$ is a Heyting algebra, where $(U => V) := "int"((X - U) union V)$.
    + A finite distributive lattice is a Heyting algebra.
]
#definition[
    Let $H$ be a Heyting algebra and $L$ be a propositional language with a set of primitive propositions $P$. An *$H$-valuation* is a function $v: P -> H$, extended recursively to $L$, by setting:
    - $v(bot) = bot$.
    - $v(A and B) = v(A) and v(B)$.
    - $v(A or B) = v(A) or v(B)$.
    - $v(P -> Q) = v(A) => v(B)$.
]<def:heyting-algebra>
#definition[
    A proposition $A in L$ is $H$-valid if $v(A) = top$ for all $H$-valuations $v$, and is an *$H$-consequence* of a (finite) set of propositions $Gamma$ if $v(and.big Gamma) <= v(A)$ (we write $Gamma satisfies_H P$).
]
#lemma("Soundness of Heyting Semantics")[
    Let $H$ be a Heyting algebra and $v: L -> H$ be an $H$-valuation. If $Gamma proves_"IPC" A$, then $Gamma satisfies_H A$.
]
#proof[
    By induction on the structure of the proof $Gamma proves A$.
    - $(A x)$: $v(and.big Gamma and A) = v(and.big Gamma) and v(A) <= v(A)$.
    - ($and$-I): $A = B and C$ and we have derivations $Gamma_1 proves B$ and $Gamma_2 proves C$, with $Gamma_1, Gamma_2 subset.eq Gamma$. By the indutive hypothesis, we have $v(and.big Gamma) <= v(and.big Gamma_1) and v(and.big Gamma_2) <= v(B) and v(C) = v(B and C)$, i.e. $Gamma satisfies_H A$.
    - ($->$-I): $A = B -> C$, so we must have $Gamma union {B} proves C$. By the inductive hypothesis, we have $v(and.big Gamma) and v(B) = v(and.big Gamma and B) <= v(C)$. By the definition of $=>$, this implies $v(and.big Gamma) <= (v(B) => v(C)) = v(B -> C) = v(A)$, i.e. $Gamma satisfies_H A$.
    - ($or$-I): $A = B or C$ and WLOG we have a derivation $Gamma proves B$. By the inductive hypothesis, we have $v(and.big Gamma) <= v(B)$, but $v(B or C) = v(B) or v(C) = sup{v(B), v(C)}$, and so $v(B) <= v(B or C)$.
    - ($and$-E): by the induction hypothesis, we have $v(and.big Gamma) <= v(B and C) = v(B) and v(C) <= v(B), v(C)$.
    - ($->$-E): we know that $v(A -> B) = (v(A) => v(B))$. From $v(A -> B) <= (v(A) => v(B))$, we derive $v(A) and v(A -> B) <= v(B)$ by definition of $=>$. So if $v(and.big Gamma) <= v(A -> B)$ and $v(and.big Gamma) <= v(A)$, then $v(and.big Gamma) <= v(B)$ as required.
    - ($or$-E): by the inductive hypothesis, $v(A and and.big Gamma) <= v(C)$, $v(B and and.big Gamma) <= v(C)$ and $v(and.big Gamma) <= v(A or B) = v(A) or v(B)$. This last fact means that $v(and.big Gamma) and (v(A) or v(B)) = v(and.big Gamma)$. Since Heyting algebras are distributive lattices, this is the same as $(v(and.big Gamma) and v(A)) or (v(and.big Gamma) and v(B))$, and this is $<= v(C)$.
    - ($bot$-E): if $v(and.big Gamma) <= v(bot) = bot$, then $v(and.big Gamma) = bot$, in which case $v(and.big Gamma) <= v(A)$ for any $A$ by minimality of $bot$ in $H$.
]
#example[
    The LEM is not intuitionistically valid: let $p$ be a primitive proposition and consider the Heyting algebra given by the topology ${emptyset, {1}, {1, 2}}$ on $X = {1, 2}$. Define a valuation $v$ with $v(p) = {1}$, in which case $v(not p) = not {1} = "int"(X \\ {1}) = emptyset$. So $v(p or not p) = {1} or emptyset = {1} != top$. So by Soundness, $proves.not_"IPC" p or not p$.
]
#example[
    Pierce's law $((p -> q) -> p) -> p$ is not intuitionistically valid: take the valuation on the standard topology on $RR^2$ that maps $p$ to $RR^2 \\ {(0, 0)}$ and $q$ to $emptyset$.
]
Classical completeness states that $Gamma proves_"CPC" A$ iff $Gamma satisfies_2 A$. For intuitionistic completeness, there is no single finite replacement for $2$.

#definition[
    Let $Q$ be a logical doctrine (e.g. CPC, IPC, etc.), $L$ be a propositional language, and $T$ be an $L$-theory. The *Lindenbaum-Tarski* algebra $F^Q (T)$ is built in the following way:
    - The underlying set of $F^Q (T)$ is the set of equivalence classes $[phi]$ of propositions $phi$, where $phi tilde psi$ when $T, phi proves_Q psi$ and $T, psi proves_Q phi$.
    - If $star$ is a logical connective in the fragment $Q$, we set $[phi] star [psi] := [phi star psi]$.
    We are interested in the cases $Q = "CPC"$, $Q = "IPC"$ and $Q = "IPC" \\ {->}$.
]
#proposition[
    The Lindenbaum-Tarski algebra of any theory in $"IPC" \\ {->}$ is a distributive lattice.
]
#proof[
    Clearly, $and$ and $or$ inherit associativity and commutativity, so in order for $F^("IPC" \\ {->})(T)$ to be a lattice, we only need to check the absorption laws: $[phi] or [phi and psi] = [phi]$, and $[phi] and [phi or psi] = [phi]$. The first is true, since $T, phi proves_("IPC" \\ {->}) phi or (phi and psi)$ by ($or$-I), and also $T, phi or (phi and psi) proves_("IPC" \\ {->}) phi$ by ($or$-E). The second is true by a similar argument.

    For distributivity, $T, phi and (psi or chi) proves (phi and psi) or (phi and chi)$ by ($and$-E) followed by ($or$-E):
    #Proof(
        $phi and (psi or chi)$,
        $phi quad psi or chi quad ("by" (and"-E"))$,
        $(phi and psi) or (phi and chi) quad ("by" (or"-E"))$
    )
    Similarly, $T, (phi and psi) or (phi and chi) proves phi and (psi or chi)$ by ($or$-E) followed by ($and$-I).
]
#lemma[
    The Lindenbaum-Tarski algebra of any theory relative to IPC is a Heyting algebra.
]
#proof[
    We already know that $F^"IPC" (T)$ is a distributive lattice, so it is enough to show that $[phi] => [psi] := [phi -> psi]$ gives a Heyting implication, and that $F^"IPC" (T)$ is bounded. Suppose that $[phi] and [psi] <= [chi]$, i.e. $T, phi and psi proves_"IPC" chi$. We want to show that $[phi] <= [psi -> chi]$, i.e. $T, phi proves (psi -> chi)$. But this is clear:
    #Proof(
        $phi quad [psi]$,
        $phi and psi$,
        $chi quad ("by hypothesis")$,
        $psi -> chi quad (->"-I", psi)$
    )
    Conversely, if $T, phi proves (psi -> chi)$, then we can prove $T, phi and psi proves chi$:
    #Proof(
        $phi and psi$,
        $phi quad psi$,
        $psi -> chi quad ("by hypothesis")$,
        $psi -> chi quad psi$,
        $chi quad (->"-E")$
    )
    So defining $[phi] => [psi] := [phi -> psi]$ provides a Heyting $=>$. The bottom element of $F^"IPC" (T)$ is just $[bot]$: if $[phi]$ is any element, then $T, bot proves phi$ by ($bot$-E). The top element is $top := [bot -> bot]$: if $phi$ is any proposition, then $[phi] <= [bot -> bot]$ via
    #Proof(
        $phi quad [bot]$,
        $bot quad (bot"-E")$,
        $bot -> bot$
    )
]
#theorem("Completeness of Heyting Semantics")[
    A proposition is provable in IPC iff it is $H$-valid for every Heyting algebra $H$.
]<thm:completeness-of-heyting-semantics>
#proof[
    One direction is easy: if $proves_"IPC" phi$, then there is a derivation in IPC, thus $top <= v(phi)$ for any Heyting algebra $H$ and valuation $v$ by soundness. But then $v(phi) = top$ and $phi$ is $H$-valid.

    For the other direction, consider the Lindenbaum-Tarski algebra $F(L)$ of the empty theory relative to IPC, which is a Heyting algebra by the above lemma. We can define a valuation $v$ by extending $P -> F(L)$, $p |-> [p]$, to all propositions. Since $v$ is a valuation, it follows by induction (and the construction of $F(L)$) that $v(phi) = [phi]$ for all propositions $phi$. Now $phi$ is valid in every Heyting algebra, and so in $F(L)$ in particular. So $v(phi) = top = [phi]$, hence $proves_"IPC" phi$.
]
#definition[
    Given a poset $S$, the set $a arrow.t := {s in S: a <= s}$ is a *principal up-set*. $U subset.eq S$ is a *terminal segment* if $a arrow.t subset.eq U$ for each $a in U$.
]
#proposition[
    For any poset $S$, the set $T(S) = {U subset.eq S: U "is a terminal segment of" S}$ can be made into a Heyting algebra, and the way this is done is unique.
]
#proof[
    Order the terminal segments by $subset.eq$. Meets and joins are $sect$ and $union$, so we just need to define $=>$. For $U, V in T(S)$, define $(U => V) := {s in S: (s arrow.t) sect U subset.eq V}$. To show this is a valid definition, let $U, V, W in T(S)$. We have $
        W subset.eq (U => V) & "iff" (w arrow.t) sect U subset.eq V "for all" w in W
    $ which happens if for every $w in W$ and $u in U$, we have if $w <= u$, then $u in V$. But $W$ is a terminal segment, so this is the same as saying that $W sect U subset.eq V$.
]
#definition[
    Let $P$ be a set of primitive propositions. A *Kripke model* is a teriple $(S, <=, forces)$ where $(S, <=)$ is a poset (whose elements are called "worlds" or "states" and whose ordering is called the "accessibility relation"), and $forces subset.eq S times P$ is a binary relation called "forcing" satisfying the *persistence property*: if $p in P$ is such that $s forces p$ and $s <= s'$, then $s' forces p$.
]
Every valuation $v$ on $T(S)$ induces a Kripke model by setting $s forces p$ if $s in v(p)$.