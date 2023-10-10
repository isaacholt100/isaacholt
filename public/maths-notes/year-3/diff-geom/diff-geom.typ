#import "../../template.typ": template
#show: template

#let vd(arg) = $underline(arg)$

= Motivation

== Plane curves

- Curves mainly parametrised: $alpha: I -> RR^2$, $I subset RR$ interval, with a direction.
- *Four vertex theorem*: every closed plane curve has at least $4$ vertices.

== Surfaces

- Surfaces are $2$-dimensional subsets of $RR^3$.

= Regular curves in $RR^n$

== Regular curves, length and tangent vectors

- Let $I$ be open interval, then $vd(alpha): I -> RR^n$ is *parametrised curve*.
- $vd(alpha)$ is *smooth* if $vd(alpha)(u) = (alpha_1 (u), ..., alpha_n (u))$ where all $alpha_i: I -> RR$ are smooth maps.
- Image $vd(alpha)(I) subset RR^n$ is the *trace*.
- *Tangent vector of $alpha$ at $u$* is $ vd(alpha)'(u) = (alpha'_1 (u), ..., alpha'_n (u)) $
- $vd(alpha)$ is *regular* if $forall u in I, vd(alpha)' (u) != 0$. $vd(alpha)$ is *singular at $u$* if $vd(alpha)'(u) = 0$.
- If $vd(alpha)$ is regular, *unit tangent vector of $alpha$ at $u$* is $ vd(t)(u) = vd(alpha)'(u) / norm(vd(alpha)'(u)) $
- If $forall u in I, norm(vd(alpha)'(u)) = 1$ then $vd(alpha)$ is a *unit speed curve*. If $forall u in I, norm(vd(alpha)'(u)) = c$, $vd(alpha)$ is *constant speed curve*.
- *Example*: unit circle $vd(alpha)(u) = (cos u, sin u)$ is regular: $alpha'(u) = (-sin u, cos u) != 0$. It is unit speed as $norm(alpha'(u)) = 1$.
- *Example*: helix $vd(alpha)(u) = (cos u, sin u, u)$, $vd(alpha)'(u) = (-sin u, cos u, 1)$, $norm(vd(alpha)'(u)) = sqrt(2)$ so constant speed.
- *Example*: *cusp* $vd(alpha)(u) = (u^3, u^2)$, $vd(alpha)'(u) = (3u^2, 2u)$ so $vd(alpha)'(u) = 0 <==> u = 0$ so $vd(alpha)$ singular at $0$.
- *Example*: *node* $vd(alpha)(u) = (u^3 - u, u^2 - 1)$. So $vd(alpha)(-1) = vd(alpha)(1) = (0, 0)$ so it has a self-intersection at the origin. $vd(alpha)'(u) = (3u^2 - 1, 2u)$ so is regular.
- *Definition*: let $vd(alpha): I -> RR^n$, $[a, b] subset I$. $vd(alpha)$ is *rectifiable* on $[a, b]$ if $ L(vd(alpha) |_([a, b])) := sup{sum_(i = 0)^(n - 1) med norm(vd(alpha)(u_(i + 1)) - vd(alpha)(u_i)): n in NN, a = u_0 < dots.h.c < u_m = b} $ is finite. Then $ L(vd(alpha) |_([a, b]))$ is the *(arc) length* of $vd(alpha): [a, b] -> RR^n$.
- *Proposition*: let $vd(alpha): I -> RR^n$ smooth, $[a, b] subset I$. Then $ L(vd(alpha) |_([a, b])) = integral_a^b norm(vd(alpha)'(u)) dif u $

== Reparametrisation

- *Definition*: let $vd(alpha): I -> RR^n$ be smooth regular curve. A *parameter change* for $alpha$ is a smooth map $h: J -> I$, $J subset RR$ is open interval, where
    - $forall t in J, h'(t) != 0$
    - $h(J) = I$.
$tilde(vd(alpha)) = vd(alpha) compose h: J -> RR^n$ is a *reparametrisation* of $vd(alpha)$. If $h' > 0$, $h$ is *orientation preserving*, otherwise it is *orientation reversing*.
- *Proposition*: let $vd(alpha): I -> RR^n$ be smoooth, regular curve, $u_0 in I$, $ell: I -> RR$ defined by $ ell(u) = integral_(u_0)^u norm(vd(alpha)'(t)) dif t $ Let $J = ell(I)$. Then $ell$ is strictly monotone increasing and $tilde(vd(alpha)) = vd(alpha) compose ell^(-1): J -> RR^n$ is unit speed.
- *Proposition*: let $vd(alpha): I -> RR^n$ be smooth regular curve and $tilde(vd(alpha)) := vd(alpha) compose h: J -> RR^n$ be reparametrisation of $vd(alpha)$ with parameter change $h: J -> I$. Let $[a, b] subset I$ and $[c, d] = h^(-1) ([a, b])$. Then $ L(vd(alpha)|_([a, b])) = L(tilde(vd(alpha))|_([c, d])) $ i.e. length is independent of parametrisation.

= Plane curves

== Unit normal vectors and curvature

- *Definition*: let $alpha: I -> RR^2$ be smooth regular plane curve. The *unit normal vector* of $alpha$ at $u$ is $ vd(n)_(alpha) (u) = vd(t)(u) mat(cos(pi \/ 2), sin(pi \/ 2); -sin(pi \/ 2), cos(pi \/ 2)) = (-t_2(u), t_1(u)) $
- *Lemma*: let $alpha: I -> RR^2$ be smooth unit speed plane curve. Then $vd(t)'(s) = alpha''(s)$ is parallel to $vd(n)(s)$.
- *Definition*: *(signed) curvature* $kappa(s)$ of unit speed plane curve $alpha: I -> RR^2$ at $s in I$ is defined by $ vd(t)'(s) = kappa(s) vd(n)(s) $ Note that we can compute $kappa(s)$ by $ vd(t)'(s) dot.op vd(n)(s) = kappa(s) vd(n)(s) dot.op vd(n)(s) = kappa(s) norm(vd(n)(s))^2 = kappa(s) $
- *Rule for sign of curvature*: if curve turns clockwise, curvature is negative, if curve turns anti-clockwise, its curvature is positive.
- *Proposition*: let $alpha: I -> RR^2$ be any smooth regular plane curve, $alpha(u) = (x(u), y(u))$. Then its curvative is $ kappa(u) = (x'(u) y''(u) - x''(u) y'(u)) / ((x'(u))^2 + (y'(u))^2)^(3\/2) $