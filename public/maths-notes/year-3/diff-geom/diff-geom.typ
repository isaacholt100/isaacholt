#import "../../template.typ": template
#show: template

= Motivation

== Plane curves

- Curves mainly parametrised: $alpha: I -> RR^2$, $I subset RR$ interval, with a direction.
- *Four vertex theorem*: every closed plane curve has at least $4$ vertices.

== Surfaces

- Surfaces are $2$-dimensional subsets of $RR^3$.

= Regular curves in $RR^n$

== Regular curves, length and tangent vectors

- Let $I$ be open interval, then $underline(alpha): I -> RR^n$ is *parametrised curve*.
    - $underline(alpha)$ is *smooth* if $underline(alpha)(u) = (alpha_1 (u), ..., alpha_n (u))$ where all $alpha_i: I -> RR$ are smooth maps.
    - Image $underline(alpha)(I) subset RR^n$ is the *trace*.
    - *Tangent vector of $alpha$ at $u$* is $ underline(alpha)'(u) = (alpha'_1 (u), ..., alpha'_n (u)) $
    - $underline(alpha)$ is *regular* if $forall u in I, underline(alpha)' (u) != 0$. $underline(alpha)$ is *singular at $u$* if $underline(alpha)'(u) = 0$.
    - If $underline(alpha)$ is regular, *unit tangent vector of $alpha$ at $u$* is $ underline(t)(u) = underline(alpha)'(u) / norm(underline(alpha)'(u)) $
    - If $forall u in I, norm(underline(alpha)'(u)) = 1$ then $underline(alpha)$ is a *unit speed curve*. If $forall u in I, norm(underline(alpha)'(u)) = c$, $underline(alpha)$ is *constant speed curve*.