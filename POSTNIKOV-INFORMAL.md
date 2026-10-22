# Postnikov convergence: informal argument

Date: 2026-10-22.

This records the argument for the convergence theorem in
`notes/postnikov.tex`. The comparison, natural inverse map, and first inverse
homotopy have been checked in `core`. The second inverse homotopy below is now
also checked in `core` (2026-10-22): CPostBox, CPostRead, CPostInvIn,
CPostCube, CPostInv, CPostInvAsm, CPostInvNat; the result is
`CPostInvNat.LeftInverse.homotopy`, a term of the model's Path type from
psi . phi to the identity on DA. The fibration structure on the internal limit
(CPostFib.PostFib.fib) is also checked.

The crucial correction to the last paragraph of the notes is that it needs
**nonconstant boundary faces**. A constant path in $D_NA$, when read in $A$ by
Eilenberg–Zilber extension, need not be constant. The higher simplices of
$u\in DA$ provide the replacement faces.

## The limit, comparison, and first homotopy

Write $C=i^*A$. The internal limit is

$$
L=\sum_{(u_N):\prod_N D_NA}
       \prod_N\operatorname{Path}_{D_NA}(r_Nu_{N+1},u_N).
$$

The comparison $\varphi:DA\to L$ sends $u$ to its restrictions, with constant
coherence paths. Products, paths, and sums give the fibration structure on $L$.

For $\ell=(u_N,p_N)$, the existing recursion constructs $\psi(\ell)\in DA$.
Its prisms $H^N$ and squares $\Theta_N$ assemble into a path

$$
\varphi\psi(\ell)\simeq\ell.
$$

The square boundaries give exactly the coherence needed for a path in the
displayed sum. Naturality in $X$ follows by comparing the recursive
constructions before and after restriction: they have equal input data, hence
use the same fillers. This comparison includes the auxiliary stage recursion
and the final step in $K_mA$. These naturality proofs and the assembled internal
homotopy now check.

It remains to construct $\psi\varphi\simeq\mathrm{id}$.

## Boundary data supplied by a full element of $DA$

Fix $u\in DA(X)$, and run the recursion on $\varphi(u)$. For $f:[m]\to X$, put

$$
U_f=u_m(f)\in C_m.
$$

First we need two pieces of boundary data supplied by $u$.

For any $k$, read $u$ on $[m]\times[k]$, along $f\pi_1$: on a strict chain

$$
c:[r]\hookrightarrow[m]\times[k]
$$

use $u_r(f\pi_1c)$, and extend by Eilenberg–Zilber. Denote the resulting
simplicial map by $R_f^{[k]}$. This requires no truncation bound, since $u$ has
components in every dimension.

For $k=0$, this reading is the simplex $U_f$. Consequently

$$
R_f:=R_f^{[1]}
$$

is a prism with both ends $U_f$. It need not be the constant prism. These
readings commute with the simplex face inclusions.

For $N\ge m+1$, the high-stage data of the existing recursion satisfy

$$
H^N_f:\psi\varphi(u)(f)\longrightarrow U_f,
$$

and, using the orientation of the checked squares,

$$
\begin{aligned}
\Theta_N|_{s=0}&=H^{N+1}_f,&
\Theta_N|_{s=1}&=H^N_f,\\
\Theta_N|_{t=0}&=\psi\varphi(u)(f),&
\Theta_N|_{t=1}&=R_f(s).
\end{aligned}
$$

The last edge is $R_f$, rather than a constant edge: reading the constant
$D_NA$-path gives precisely this prism.

We also need a square $Q_f(s,v)$ whose edges are

$$
\begin{aligned}
Q_f(s,0)&=R_f(s),& Q_f(1,v)&=R_f(v),\\
Q_f(0,v)&=R_f(v),& Q_f(s,1)&=U_f.
\end{aligned}
$$

Construct it from $R_f^{[2]}$ by precomposition with the monotone map
$\mathrm{id}_{[m]}\times\beta$, where

$$
\beta:[1]\times[1]\longrightarrow[2],
\qquad
\begin{array}{c|cc}
 &s=0&s=1\\ \hline
v=0&0&1\\
v=1&2&2
\end{array}
$$

The three noncollapsed edges of $\beta$ are the three strict edge inclusions
into $[2]$, so their readings are all $R_f$. The fourth edge is constant at $2$,
so its value is the constant prism at $U_f$. Here we precompose an **already
extended simplicial map**; we do not assume that the original reading operation
commutes with projections. This distinction resolves the boundary issue.

## The second inverse homotopy

Proceed by induction on $m$. Construct a prism $G_f$ and, for every $N\ge m+1$,
squares $\Xi_f^N(t,v)$ with boundaries

$$
\begin{aligned}
\Xi_f^N(t,0)&=H_f^N(t),& \Xi_f^N(t,1)&=G_f(t),\\
\Xi_f^N(0,v)&=\psi\varphi(u)(f),& \Xi_f^N(1,v)&=R_f(v).
\end{aligned}
$$

Require their restrictions to every simplex face to be the corresponding data
already constructed there.

### Initial square

Construct $G_f$ and $\Xi_f^{m+1}$ by filling the open square with lid
$H_f^{m+1}$ at $v=0$, the constant face at $t=0$, the face $R_f(v)$ at $t=1$,
and the previously constructed squares $\Xi_{fd_i}^{m+1}$ on the simplex
boundary. The missing face at $v=1$ is $G_f$.

Its endpoints are $\psi\varphi(u)(f)$ and $U_f$, and its simplex faces are the
previously constructed $G_{fd_i}$.

### Successor cube

Construct $\Xi_f^{N+1}$ from $\Xi_f^N$ by filling a cube with coordinates
$(t,s,v)$, prescribing the following faces.

| Face | Prescribed value |
|---|---|
| $v=0$ | $\Theta_N(t,s)$ |
| $s=1$ | $\Xi_f^N(t,v)$ |
| $v=1$ | $G_f(t)$, independent of $s$ |
| $t=0$ | $\psi\varphi(u)(f)$ |
| $t=1$ | $Q_f(s,v)$ |

On each simplex face prescribe the cube already constructed in dimension
$m-1$. The missing face $s=0$ is $\Xi_f^{N+1}$.

All intersections agree. In particular, the three nonconstant edges of $Q_f$
match the $R_f$-edges of $\Theta_N$, $\Xi_f^N$, and the new square; its constant
edge matches the endpoint of $G_f$.

These boxes can all be filled in $C$ itself. The high-stage $H^N,\Theta_N$
already live there, and $R_f,Q_f$ come from the full element $u$. Thus this
construction does not require an additional truncation bound for the cubes.

### Assembly and naturality

Retaining the filled cubes as auxiliary data ensures agreement on intersections
of simplex faces. The resulting $G_f$ are therefore face-compatible. As in the
existing assembly lemma, evaluate $G_f$ at $(\mathrm{id},h)$ for each

$$
(f,h):[m]\longrightarrow X\times[1].
$$

This produces an element of $DA(X\times[1])$, with endpoints

$$
\psi\varphi(u)\quad\text{and}\quad u.
$$

Finally, $R_f$, $Q_f$, and every filling problem depend only on the restricted
input along $f$. Induction on dimension and stage, comparing equal filling
problems, gives naturality under $X$-restriction. Hence these cylinders define
the second internal homotopy.

Together with the first inverse homotopy, this establishes that
$\varphi:DA\to L$ is a homotopy equivalence (both homotopies checked:
`CPostConvergence.RightInverse.homotopy`, `CPostInvNat.LeftInverse.homotopy`).
