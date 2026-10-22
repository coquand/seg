# Handoff: separate modules from records in Unit (`seg/defenv`)

This handoff was written on 18 October 2026, for the next session. All work is in the parallel checker `seg/defenv`: executable `segd`, copy of `core/` in `defenv/core`. Nothing is committed, and `seg/src` and the shared `seg/core` are untouched.

Read `seg/defenv/CHANGES.md` first. It covers the design reached on 18 October: definitions kept as units, `⟨f ; η⟩`, lock strategy only in head computation, code identities, the `split`/`data` restriction, quotation, and the conversion rules.

## 1. Where things stand

Before the record work started, everything passed:

- All 199 files of `core` checked one at a time, each under 3 s.
- The examples passed except `byDeps`.
- All reviewer counterexamples were rejected.

Then three record changes were made. Each is decided and implemented in `defenv/src`:

1. **Record types are nominal.** Two `sig`/named Σ types are equal only for the same occurrence with equal dynamic parts. Contents are never compared.
2. **`new` is the constructor of its segment.** `new M[args]` is the canonical element, and two constructions with convertible arguments are convertible wherever they are written. `struct` is treated the same way. The earlier occurrence rule for `new` is dropped, because a dependent eliminator needs a single constructor: subject reduction.
3. **No η for records.**
   - The conversion rules `(VInst m r, w)` and `(VStruct fs, w)` are removed.
   - A λ-bound variable of segment type is `VVar` (itself, with the fields its type fixes) instead of an η-expanded instance.
   - η holds in `Id`, proved by the eliminator `split { M x1 … xn -> b }` on a segment type, or on a `sig` type.
     - It binds all declared fields (parameters) of the segment, the fixed ones included, which get their fixed values.
     - It computes on an element built by `new` or `struct` (`recordFields`), and is stuck on a variable.
     - Code: `recordBranch` in `Seg.hs`, plus the β case in `app` and `whnfP`.

The examples are updated and pass, except `byDeps`:

- `basic.seg` `etaRec` and `segtypes.seg` `etaE` are now proved with the eliminator, and definitional η is `#fails`.
- `records.seg`, `segtypes.seg` and `hidden.seg` now state that equal constructions are equal.

**`core` migration (stopped).** Modules where definitional η was used are being rewritten with η lemmas proved by the eliminator, with the old proof stated for the reconstructed elements:

- **Done:**
  - `Presheaf`: `pty-eta`, `psub-eta` and `pel-eta`, used by `sub-ext`, `el-ext` and `ty-ext2`, and in `isSet-PSub/PTy/PEl` (the retraction).
  - `CPartial`: `side-eta` and `rc-eta`, used by `side-ext` and `rc-ext`.
- **Stopped at:** `COp.OpExt.core` (file 26). It needs `B packOf = A` for `A : PTy[G]`, which is η again; use `pty-eta`.
- **Not yet checked:** files 27 to 199.
- The snapshot of `Presheaf.seg` before the η work is in the scratchpad (`Presheaf.pre-eta`); it may be gone in a new session. The original files are in `seg/core`.

## 2. The decision for the next session: separate modules from records

The confusion: Unit uses one construct, the segment, both as a module (a list of declarations and definitions with parameters, instantiated) and as a record type (fields, constructor, eliminator). The η and eliminator questions concern only the record role.

**Agreed design.** These are Thierry's answers on 18 October, with the reviewer's qualifications:

- **Records.** `record R (params) { fields ; definitions }`.

      record Box (A : U a) {
        value : A ;
        get : A = value ;
      }

  - `Box[N]` is a type: the parameters are given, the fields are not.
  - `new Box[N, zero]` is an element.
  - `b.get` computes from the element's fields.
  - Defined members are derived from the fields. They are not constructor arguments.
  - Record types are nominal.
  - Elements use constructor equality, with no definitional η. η is propositional, by elimination.
- **Modules.** `module M (params) { … }` is a list of declarations and definitions with parameters, used through `M[args].f` and aliases. A module is never a type: no `new M`, and no variable of type `M[…]`.
- **Answers:**
  1. A record's defined members are reached only through an element, `b.get`. If `Box[N, zero].get` is allowed later, it is explicit shorthand for `(new Box[N, zero]).get`, not a second, module reading of records.
  2. Modules may contain records, including records that depend on the module's parameters.
- **Reviewer's qualification: implementation.** This is more than a resolver restriction. Sharing the declaration-list representation is fine, but the checker must distinguish module instantiation from record formation, construction and elimination.
- **Reviewer's qualification: still to specify before migrating.** Partially fixed record types, `R[field := value]`, are used in `core`. Give their constructor and eliminator a clear account, so that the feature does not quietly reintroduce the module/record confusion.

## 3. Plan

1. **Specify, in a short note,** before any code:
   - records versus modules;
   - formation, construction, projection, elimination and β;
   - derived members;
   - partially fixed record types and their constructor and eliminator;
   - subtyping between `R[x := e]` and `R`.
2. **Implement it in `defenv` on small examples first:**
   - the `record` declaration;
   - the resolver checks, rejecting `new`/`M[…]`-as-type for modules with a message pointing to `record`;
   - the separate checker rules.
3. **List `core`'s segments used as records,** using the new error messages. Likely: `PCtx`, `PTy`, `PSub`, `PEl`, `Side`, `RC`, `SmallCat`, `DConj`, `CwF`, ….
4. **Migrate `core`,** declaring those as `record`. Rewrite each use of definitional η with the η lemmas, continuing from `COp`.

## 4. Working rules (Thierry)

- **Time limits.** Each file under 5 s. Stop as soon as one file takes longer and analyse why. No shell command over 1 minute.
- **Small checks first.** Check small examples first; for `core`, check files one at a time in dependency order. The script used was `runfrom.sh START` in the scratchpad; the order is `All.seg`'s imports, with `CBase` replaced by its own imports.
- **No artificial optimisation.** Optimise only when a measurement shows a need. The simplest, uniform design comes first.
- **Never commit** without Thierry's request.
- **Write concisely.** Answers of about one sentence when asked; no jargon in notes.
