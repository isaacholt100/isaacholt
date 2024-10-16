#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

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
#axiom(name: "Choice - Intutionistic Version")[
    Any family of inhabited sets admits a choice function.
]<axm:choice>
#theorem(name: "Diaconescu")[
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
        Lambda_Pi := V | lambda  V: pi thin . thin Lambda_Pi | Lambda_Pi med Lambda_Pi
    $ In the term $lambda x: tau . M$, $x$ is a variable, $tau$ is type and $M$ is a $lambda$-term. Forming terms of this form is called *$lambda$-abstraction*. Forming terms of the form $Lambda_Pi Lambda_Pi$ is called *$lambda$-application*.
]<def:simply-typed-lambda-term>
#definition[
    A *context* is a set of pairs $Gamma = {x_1: tau_1, ..., x_n: tau_n}$ where the $x_i$ are distinct variables and each $tau_i$ is a type. So a context is an assignment of a type to each variable in a given set. Write $C$ for the set of all possible contexts. Given a context $Gamma in C$, write $Gamma, x: tau$ for the context $Gamma union {x: tau}$ (if $x$ does not appear in $Gamma$).

    The *domain* of $Gamma$ is the set of variables ${x_1, ..., x_n}$ that occur in it, and its *range*, $abs(Gamma)$, is the set of types ${tau_1, ..., tau_n}$ that it manifests.
]<def:context>
#definition[
    Recursively define the *typability relation* $| proves subset.eq C times Lambda_Pi times Pi$ via:
    + For every context $Gamma$, variable $x$ not occurring in $Gamma$ and type $tau$, we have $Gamma, x: tau | proves x: tau$.
    + For a context $Gamma$, variable $x$ not occurring in $Gamma$, types $sigma, tau in Pi$, and $lambda$-term. If $Gamma, x: sigma | proves M: tau$, then $Gamma | proves (lambda x: sigma . M): (sigma -> t)$.
    + Let $Gamma$ be a context, $sigma, tau in Pi$ be types, and $M, N in Lambda_Pi$ be terms. If $Gamma | proves M: (sigma -> t)$ and $Gamma | proves N: sigma$, then $Gamma | proves (M N): tau$.

]<def:typability-relation>
#notation[
    We will refer to the $lambda$-calculus of $Lambda_Pi$ with this typability relation as $lambda(->)$.
]
#definition[
    A variable $x$ occurring in a $lambda$-abstraction $lambda x: sigma . M$ is *bound* and is *free* otherwise. A term with no free variables is called *closed*.
]<def:variable.bound-and-free>
#definition[
    Terms $M$ and $N$ are *$alpha$-equivalent* if they differ only in the names of teh bound variables.
]<def:alpha-equivalence>
#definition[
    If $M$ and $N$ are $lambda$-terms and $x$ is a variable, then we define the *substitution of $N$ for $x$ in $M$* by the following rules:
    - $x[x := N] = N$.
    - $y[x := N] = N$.
    - $(P Q)[x := N] = P[x := N] Q[x := N]$ for $lambda$-terms $P, Q$.
    - $(lambda y: sigma . P)[x := N] = lambda y: sigma . (P[x := N])$ for $x != y$ and $y$ not free in $N$.
]<def:substitution>
#definition[
    The *$beta$-reduction* relation is the smallest relation $-->_beta$ on $Lambda_Pi$ closed under the following rules:
    - $(lambda x: sigma . P) Q -->_beta P[x := Q]$. The term being reduced is called a *$beta$-redex*, and the result is called its *$beta$-contraction*.
    - If $P -->_beta P'$, then for all variables $x$ and types $sigma in Pi$, we have $lambda x: sigma . P -->_beta lambda x: sigma . P'$.
    - If $P -->_beta P'$ and $Z$ is a $lambda$-term, then $P Z -->_beta P' Z$ and $Z p -->_beta Z P'$.
]<def:beta-reduction>
#definition[
    We define *$beta$-equivalence*, $equiv_beta$, as the smallest equivalence relation containing $-->_beta$.
]<def:beta-equivalence>
#example[
    We have $(lambda x: ZZ . (lambda y: tau . x)) 2 -->_beta (lambda y: tau . 2)$.
]
#lemma(name: "Free Variables Lemma")[
    Let $Gamma | proves M: sigma$. Then
    - If $Gamma subset.eq Gamma'$, then $Gamma' | proves M: sigma$.
    - The free variables of $M$ occur in $Gamma$.
    - There is a context $Gamma^* subset.eq Gamma$ comprising exactly the free variables in $M$, with $Gamma^* | proves M: sigma$.
]<lem:free-variables>