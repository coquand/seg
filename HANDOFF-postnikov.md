# Handoff: Theorem 5.1 of seg/notes/postnikov.tex (convergence) in seg/core

Status 2026-10-21 (end of session 3). Nothing committed (user rule: never commit). Check with
`./segc core changed`.

## Done (all check)

| file | content |
|---|---|
| CBoxEZ | image factorisation of a simplex of a graded poset (EZX), along k (EZXK), along a strict iota (EZXI); heights of [n] and of products; strict-le, strict-inj |
| CFacesGen | faces suffice for any presheaf on Delta; CLocD.FacesGen is now its instance |
| CBoxFill | Lemma box: prisms over a poset X relative to a sieve Q, from CDFill's face-uniform fillers, extended by EZ |
| CBoxSq | test: open boxes of squares (X = [m] * [1], boundary sieve) |
| CFaceTwo | two-faces arithmetic, shared with CLocHorn (refactored to use it) |
| CPostMap | DR: reading a D_N-element along phi : P -> Y into i*A (B <= N); DRI (strict reindexing), DRZ (agree on chains), zc-mu |
| CPostBdry | BG geometry of [m] * Y, BS: side on (faces x Y) u ([m] x QY) from face data F and end data Ev; product/strictness lemmas |
| CPostStep1 | P1 (lid u_{m+1} along f, outputs H0v, psi, ...), S1: step 1 at f : [m'+1] -> X |
| CPostStep3 | E3 (end data psi / p_N, lid H, ends of p_N, outputs H' via HT), S3: step 3 at (f, N) with faces |
| CPostStep0 | S1z, S3z: steps 1 and 3 at a point (no faces) |
| CPostRec | the recursion: records Rec (data at f), HSt/NPk, SRec (stages, bcase), R0 (dim 0), ST (dim m -> m+1, face relations psi-face, H-face, T-face), FF0/FFS (faces agree), Drec, **psi : DA(X)** |
| CPostSq | (session 3) the open box of a square over [m] * [1]_t, line s, for ANY type B with face-uniform fillers at e: SqE (lid L at s = e, psi at t = 0, Pl at t = 1, corners L0/L1; HT: the prism at s = e'), SqS (m = m'+1, sides Th y), SqZ (m = 0). Step 3 (S3, S3z) is now an instance (B = A, e = e1) |
| CCosk | (session 3) KT now also has etaE/etaE-act (eta on total presheaves), ev/ev-pt/ev-nat/rd-ev (value at the identity, moved from CCoskHorn.HK, which keeps aliases), eta-ev, ev-eta, ev-irr |
| CPostK | DRK: reading of z in D_N A along phi into i*K_N (no bound); DRKI (strict reindexing); DRKE (DRK = eta o DR' when chains agree, height <= N, N'); SgS (sgm strict for strict g); DRS / DRKS (reading along a strict chain = z at that chain) |
| CPostMap | + DRId (reading on [n] at the identity = zc) |
| CPostStep2 | step 2: E2 (DPK = DRK of p_m along f*1, lid eta Hs(m+1), End0K/End1K: p_m at s = 0/1 is eta of u_{m+1}/u_m, HT: Hm, Hm-0, Hm-1 (= eta DU)), S2 (m = m'+1, sides eta Th y, FaceK), S2z; both instances of CPostSq for B = K_m A, e = e0, fillers CDFill.FT of CCoskHorn.HK |
| CFacesGen | SGB: faces suffice for a family given only where Ok n holds (Ok down-closed, prop); SG = SGB at Top (callers unchanged) |
| CPostLine | PL: St2S/St2Z (step 2 at every simplex from the recursion's data), HmT/HmTp/HmT0/HmT1 (split on the dimension), val N n F = vlow (Hs N, n < N) or vtop (ev of step-2 Hm, n = N), TF/LF/WF (face naturality), FG (SGB), DCN[N].line : D_N A at X*[1] (CLocDNC.from), to-inj, end-rd; **end0: line at 0 = r_N psi, end1: line at 1 = u_N** |
| CPostSquare | PS: ThmT (+ p, n, s1, s0, t0, t1 by split), val2 (Ts N for n < N, ev of step-2 Thm for n = N), WF, FG, DCS[N].sq : D_N A at (X*[1]_t)*[1]_s; **edges sq-s0 = r l_{N+1}, sq-s1 = l_N, sq-t0 = constant line at r_N psi, sq-t1 = p_N** |

## Representation (keep it)

Everything in the recursion lives in i*A (A fibrant), never in C_N:
- psi(f) : element of A([m]) over f.
- H(f, N), N >= m+1 : family (W, g : [W] -> [m], j : [W] -> [1]) -> EI, natural (BF-output form).
  H(f, m+1) from step 1; H(f, N+1) = Theta(f, N+1) at s = 0.
- Theta(f, N+1), N >= m+1 : family (W, g : [W] -> [m] * [1]_t, j = s), the square of step 3
  (the C_{N+1} square Theta'; Theta_N of the note is its image).
- Step 2 (in C_m = i*K_m) is NOT part of the recursion: Theta_m(f), H^m(f) are only needed for
  the final homotopy phi psi ~ id. Do it afterwards per f with CBoxFill on i*K_m (horn filling
  CCoskHorn.HK), sides Theta(f d_y, m+1) pushed by eta_m, ends psi / p_m.

Invariants of the data at f (stage-conditional: leb (suc m) N):
H0 (H at t = 0 is psi), H1 (H at t = 1 is DR[u_N] along f), Ts1 (Theta at s = 1 is H),
Tt0 (Theta at t = 0 is psi), Tt1 (Theta at t = 1 is DR[p_N] along f * 1), Ts0 (Theta at s = 0 is
H(f, N+1)). Face relations (step outputs): psi-face, H0-face / H'-face, Thf-face.

## Done: the recursion (CPostRec) and psi(u , p) in DA(X)

L[G, A, c, X, x, u, p, pe0, pe1].psi. The stage recursion uses bcaseL/bcaseD with bcase-t/-f;
data below the stage m+1 are copies (junk) and all invariants there are conditional.
CLocD-style: proof-irrelevance of the bound proofs of the readings is DRP.

## Done: phi psi ~ id, componentwise (session 3)

For (u , p) at (X , x): the lines DCN[N].line (CPostLine) and squares DCS[N].sq (CPostSquare) with all
their edges are the components of a path phi psi (u , p) ~ (u , p) in the internal limit L. Step 2
is not part of the recursion: it is run per simplex in CPostLine.St2S/St2Z on the recursion's data.
Full check: 227 modules, 0 failed, 39.9 s; `./segc core changed` after edits.

## Done: n = -1 (session 3, end)

postnikov.tex §"The propositional truncation" (Theorem prop). CTruncProp: IsPropE (B a proposition,
total-presheaf form), pth-eq, D0P.isProp (D_0 A is a proposition), D0M (fibrant, modal: CLocUniv.dModalH,
CLocEq.FibD = Fib without the fibration of A). CTruncFill: SF (face-uniform sphere filling in a fibrant
proposition: lid = horn filler CLocHorn.FaceFill.K0, box CBoxFill with sides the prop paths via
CPostBdry.BS over [k+1]*[0]; indexed by elements of D_0 B over [k], so faces = presheaf action), sN :
D_0 B -> D B, KMap, UP0.k : D_0 A -> B. Core: 229 modules, 38 s.
Not done for n >= 0 (see the note: needs the iterated-path / sphere comparison).

## Next

1. The internal limit L as a type of the model (Pi over N of D_N A, Sigma, Path), and phi; then the
   components above assemble into a path in L. Decide first whether L is needed as a type or the
   componentwise statement suffices (ask the user).
2. Naturality in X of psi and of the homotopy: the data at k f for (u , p) and at f for the restriction
   of (u , p) along k agree (induction on m over Rec; St2S/St2Z data are functions of Rec data).
3. psi phi ~ id (note, end of the proof of Thm conv): G(f), Xi^N(f) by the same recursion one dimension
   higher; the generic CPostSq box will need a cube version.

## Gotchas met

- seg identifies compH (compH f g) h with compH f (compH g h) in expected types; an explicit
  comp-assoc step can then be rejected (CPostStep3 End0/End1): drop it.
- app (idH X) s does not reduce to s: use app-idH1.
- Arith eliminators into U l need `module AL = Arith[l]` (AL.eqN-dec, AL.ltb-dec).
- `apH suc` fails (constructor arity): use `apH (\ z -> suc z)`.
- `idJ` is a keyword with exactly six arguments: write `idJ A a P d b e`, never a partial application
  (the parser reports "an identifier expected" at the next declaration).
- A file only sees modules of files listed BEFORE it in All.seg (CPostMap cannot use CPostBdry).
- Facts about step-2 data at a variable dimension n need a split on n (HmT, ThmT and their lemmas):
  St2Z and St2S are different modules, so nothing reduces for variable n.

## Done: psi phi ~ id (session 4, 2026-10-22; POSTNIKOV-INFORMAL.md, checked, uncommitted)

| file | content |
|---|---|
| CPostBox | generic open box over [m] * Y for any poset Y with heights and sieve QY (BoxS: m = m'+1 with sides via CPostBdry.BS; BoxZ: m = 0); outputs Thf, Thf-e (lid), Thf-E (end data), Thf-face. CPostSq is NOT yet refactored as its instance (methodology ruling: candidate) |
| CPostRead | readings of a full u in DA through the stages (Rd = CPostMap.DR of v_N u): zcU, RdZ, RdI, RdS (on [n] along f: the simplex U_f); beta : [1]*[1] -> [2] with its four edges; Sq m f: R (on [m]*[1]), R2 (on [m]*[2]), Q = R2 . (id * beta), Q-v0/Q-s1/Q-s0 (= R), Q-v1 (= U_f), Rend; Face: Uf-face, R-face, Q-face |
| CPostInvIn | the CPostRec recursion run on phi(u): DUv (end H at t = 1 is U_f), zcP, DP.val (Theta at t = 1 is R) |
| CPostCube | the square boundary sieve QY on [1]_t * [1]_v (Geo: cut, landings, pt3); E4: end data from four pieces T0/T1/V0/V1 (Pc records) with corner agreements: Ev, Evp, Evn, Ev-T0.., Lid; E4Cmp: equal pieces give equal end data |
| CPostInv | the recursion: GRec m f = (Cy = G_f, Xi k = Xi^(k+m+1), Cu k = the cubes, with edges); stages indexed from m+1 (St m k = k + m + 1, no junk); SR (stage recursion), Com/SqOut (initial square via CPostSq), CubeAt/Out (cube end data, lid, next square), D0, DS (dimension m+1, sides from faces, FEC/aF), FFY (two faces agree, generic in Y), Drec |
| CPostInvAsm | Cyl: the cylinder in DA(X * [1]) (value G_f at (id , t)), face compatibility, ends end0 = psi phi u, end1 = u (p, p0, p1) |
| CPostInvNat | naturality: CPostNat transported along phi's naturality, readings via rd-dtact, fillers compared with CBoxFill.Compare / CPostSqNat (recG over dimension, xiR over stage); Nat.nat; **LeftInverse.homotopy : Path from psi . phi to id on DA** |

Checked: core all 245 modules, CPostFib fixed later the same day (see Next); the seven files take 9.9 s
(CPostInv 5.0 s, CPostInvNat 2.8 s). Sanity: the swapped statement (be , al) is rejected.

Next: CPostSq as an instance of CPostBox (and SqZCmp/SqSCmp via a generic box compare); lock with
lemmas to bring CPostInv / CPostInvNat under 1 s; CPostFib now checks: L is fibrant (PostFib.fib; ProductFib, HTFib, TowerFib).
