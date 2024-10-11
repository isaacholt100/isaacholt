#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let ob = math.op("ob")
#let mor = math.op("mor")
#let cod = math.op("cod")
#let Set = [*Set*]
#let Gp = [*Gp*]
#let Rng = [*Rng*]
#let Vect(K) = $bold("Vect")_#K$
#let Top = [*Top*]
#let Met = [*Met*]
#let Mfd = [*Mfd*]
#let TopGp = [*TopGp*]
#let Htpy = [*Htpy*]
#let Rel = [*Rel*]
#let Part = [*Part*]
#let Mat(K) = $bold("Mat")_#K$


= Definitions and examples

#definition[
    A *category* $cal(C)$ consists of:
    + a collection $ob(cal(C))$ of objects $A, B, C, ...$,
    + a collection $mor(cal(C))$ of morphisms $f, g, h, ...$,
    + two operations $dom$ and $cod$ from $mor(cal(C))$ to $ob(cal(C))$. We write $f: A -> B$ to mean $f$ is a morphism and $dom(f) = A$ and $cod(f) = B$.
    + an operation from $ob(cal(C))$ to $mor(cal(C))$ sending $A$ to $indicator(A): A -> A$.
    + a partial binary operation $(f, g) |-> f g$ on $mor(C)$, such that $f g$ is defined iff $dom(f) = cod(g)$, and in this case $dom(f g) = dom(g)$ and $cod(f g) = cod(f)$.
    and satisfies the following:
    + $f indicator(A) = f$ and $indicator(A) g = g$ when the composites are defined.
    + $f(g h) = (f g) h$ whenever $f g$ and $g h$ are defined.
]<def:category>
#remark[
    - $ob(cal(C))$ and $mor(cal(C))$ are not necessarily sets. If they are, then $cal(C)$ is called a *small* category.
    - An equivalent definition exists without using objects.
    - $f g$ means first apply $g$, then $f$.
]
#example[
    + #Set = the category of all sets and functions between them. (Formally, a morphism of #Set is a pair $(f, B)$ where $f$ is a set-theoretic function and $B$ is its codomain).
    + Algebraic categories:
        - #Gp is the category of groups and group homomorphisms.
        - #Rng is the category of rings and ring homomorphisms.
        - #Vect($K$) is the category of vector spaces over a field $K$ with linear maps.
    + Topological categories:
        - #Top is the category of topological spaces and continuous maps.
        - #Met is the category of metric spaces and non-expansive maps (i.e. $d(f(x), f(y)) <= d(x, y)$).
        - #Mfd is the category of smooth manifolds and smooth ($C^oo$) maps.
        - #TopGp is the category of topological groups and continuous homomorphisms.
    + Quotient categories:
        - #Htpy is the category with same objects as #Top but morphisms are homotopy classes of continuous maps.
        - In general, given a category $cal(C)$ and an equivalence relation $tilde$ on $mor(cal(C))$ such that $f tilde g => (dom(f) = dom(g) and cod(f) = cod(g))$, and $f tilde g => f h tilde g h$ when the composites $f h$ and $g h$ are defined, we can form a *quotient* category $cal(C)\/tilde$.
    + #Rel is the category with the same objects as *Set* but with morphisms that are relations $R subset.eq A times B$, with composition defined by $R compose S = {(a, c): exists b: (a, b) in S and (b, c) in R}$.
    + #Part is the category of sets and partial functions.
]
#definition[
    For every category $cal(C)$, the *opposite category* $cal(C)^"op"$ has the same objects and morphisms as $cal(C)$, but $dom$ and $cod$ are interchanged and composition is reversed. This yields a *duality principle*: if $P$ is a true statement about categories, then so is $P^*$ (which is obtained by reversing arrows in $P$).
]<def:opposite-category>
#definition[
    A *monoid* is a small category with one object $*$ (a semigroup with an identity element). In particular, a group is a $1$-object where all morphisms are isomorphisms.
]<def:monoid>
#definition[
    A *groupoid* is a category where every morphism is an isomorphism.
]<def:groupoid>
#example[
    The *fundamental groupoid* of a space $X$, $pi_1 (X)$, is the category where objects are the points of $X$, and morphisms $x -> y$ are homotopy classes of path from $x$ to $y$. (Note this depends only on $X$, whereas the fundamental group depends on $X$ and a point $x in X$).
]<exa:fundamental-groupoid>
#definition[
    A category is *discrete* if the only morphisms are identities.
]<def:category.discrete>
#definition[
    A category $cal(C)$ is a *preorder* if for every pair of objects $(A, B)$, there exists at most $1$ morphism $A -> B$, then $mor(C)$ becomes a reflexive and transitive relation on $ob(C)$.

    In particular, a poset is a small preorder where the only isomorphisms are identities.
]<def:category.preorder>
#example[
    For a field $K$, the category $Mat(K)$ has natural numbers as objects, morphisms $n -> m$ are $m times n$ matrices with entries from $K$, and composition is matrix multiplication.
]<exa:matrix-category>