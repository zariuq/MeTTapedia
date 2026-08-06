import Mettapedia.Languages.Metamath.SourceGSLTState
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
import Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
import Mettapedia.Languages.Metamath.InferenceSupportedProvableBoundary
import Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport

/-!
# Specification grounding for the Metamath GSLT semantics

Every semantic component of the GSLT-native Metamath vertical is anchored
here to the precise clause of the Metamath book that governs it, and to
the corresponding implementation site in the two reference verifiers.

## Citation key

* `[MM §x.y.z]` — Megill & Wheeler, *Metamath: A Computer Language for
  Mathematical Proofs*, chapter 4 *The Metamath Language*.  Section
  numbers verified directly against the book source: §4.1 *Specification
  of the Metamath Language* (4.1.1 Preliminaries, 4.1.2 Preprocessing,
  4.1.3 Basic Syntax, 4.1.4 Proof Verification), §4.2 *The Basic
  Keywords* (4.2.1 user-defined tokens, 4.2.2 constants and variables,
  4.2.3 `$c`/`$v`, 4.2.4 `$d`, 4.2.5 `$f`/`$e`, 4.2.6 assertions,
  4.2.7 frames, 4.2.8 scoping), §4.3 *The Anatomy of a Proof*,
  §4.4 *Extensions* (4.4.1 comments, 4.4.4 file inclusion,
  4.4.5 compressed proofs).
* `[mm-lean4 …]` — the verified Lean verifier; anchors below are
  compile-checked references, so a broken link fails this module's build.
* `[knife …]` — metamath-knife (`metamath-rs`, commit `76fc9f7`); Rust
  anchors are cited by file and item and were read at that commit.

The anchors are `example := @name` bindings: they carry no proof content,
but they make every claimed correspondence a compile-time obligation.

## Citation drift found and corrected in mm-lean4

Verified against the book source and corrected in-tree (comment-only
edits; definitions were always right):

* `Metamath/Spec/Core.lean` used a systematically shifted §4.2.x scheme
  (e.g. §4.2.4 for `$f`/`$e`/frames, §4.2.5 for `$d`); remapped to the
  book's numbering (`$d` = §4.2.4, `$f`/`$e` = §4.2.5, assertions =
  §4.2.6, frames = §4.2.7, active scope = §4.2.8).
* `Metamath/DeclarativeSpec.lean` cited "§4.2.3 Expressions"; the book
  defines expressions in §4.2.2 ("An expression is any sequence of math
  symbols, possibly empty") — §4.2.3 is the `$c`/`$v` declarations.  Its
  §4.2.2 quotes are verbatim book text and were left untouched.
* `Metamath/Verify.lean`: label-token syntax is §4.1.1, the comment
  content rule is §4.1.2, `$f`/`$e` interleaving order is §4.2.7, and
  the `?`-step sentence is §4.1.4.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding

open Metamath.Spec.Equivalence
open Metamath.Spec.Bridge (MarioVR MarioFormula MarioExpr)

/-! ## [MM §4.1.1 Preliminaries] — tokens and white space

"A Metamath database consists of a sequence of three kinds of tokens
separated by white space."  The lexical GSLT owns exactly this clause:
total tokenization by white-space separation, with byte-exact spans.

* Ours: the authored separator definition compiled to the incremental
  scanner, its chunk-independence law, and its equality with the unique
  relational tokenization.
* [mm-lean4 `Metamath.Verify`] the one-shot byte loop; the fusion theorem
  proves its token-call trace equals ours on every successful input.
* [knife `parser.rs`] `parse_segments` / the segment tokenizer over
  `Token` spans. -/

example := @SourceGSLTRawByteLexical.tokenize
example := @SourceGSLTRawByteLexical.Tokenizes
example := @SourceGSLTRawByteLexical.scanRun_append
example := @SourceGSLTRawByteLexical.tokenizeIncrementally_eq_tokenize
example := @SourceGSLTRawByteLexical.checkBytesCoreLogged_eq_incrementalGSLTScanner

/-! ## [MM §4.1.2 Preprocessing] — comments and file inclusion

Comments and `$[ … $]` file inclusion are preprocessing; comments count
as white space for parsing.  Comment delimiters are themselves tokens
(§4.4.1), which is why the lexical GSLT needs no comment mode.  Include resolution with
`(fileId, offset)` provenance is the open structural seam
([MM §4.4.4]). -/

example := @SourceGSLTRawByteLexical.LocatedByteSpan

/-! ## [MM §4.1.3 Basic Syntax] + [MM §4.2.8 Scoping] — the active-scope
database

"A block is a sequence of statements enclosed between `${` and `$}`" and
a statement is *active* from its occurrence to the end of its enclosing
block — except assertions, which "remain active forever."  This is the
world/context split the source state implements: a monotone
assertion/label ledger next to a scoped hypothesis environment.

* Ours: the scoped source state with its active floating hypotheses and
  the caller frame it presents to proofs.
* [mm-lean4 `Metamath.Verify`] `DB.frame` and the scope stack.
* [knife `scopeck.rs`] scope checking; `nameck.rs` `Nameset`/`Atom` for
  the global name ledger (interned `u32` atoms — the representation the
  generated C should adopt). -/

example := @SourceGSLTState.SourceState
example := @SourceGSLTState.SourceState.activeFloatingVariables
example := @SourceGSLTState.SourceState.callerFrame
example := @SourceGSLTState.SourceState.toSourcePrefix

/-! ## [MM §4.2.2–4.2.3] — constants, variables, declarations

"The basic Metamath language has two kinds of math symbols: constants
and variables"; `$c`/`$v` declare them.

* [mm-lean4] `Metamath.Spec.Variable`, `Metamath.Spec.Constant`,
  `Metamath.Sym` (const/var split), with `ConstSet` as the global
  constant predicate. -/

example := @Metamath.Spec.Variable
example := @Metamath.Spec.Constant
example := @Metamath.Sym
example := @Metamath.Spec.ConstSet

/-! ## [MM §4.2.4] — the `$d` statement

"…if any substitution is made to its two variables, the two expressions
that result from the substitution must have no variables in common"; the
per-pair verification procedure is [MM §4.1.4, *Verifying Disjoint
Variable Restrictions*].

* [mm-lean4] `Metamath.DJ`, `Metamath.DJ.subst`, `Metamath.Expr.disjoint`.
* [knife `scopeck.rs`] `Frame.mandatory_dv` / `Frame.optional_dv`. -/

example := @Metamath.DJ
example := @Metamath.DJ.subst
example := @Metamath.Expr.disjoint

/-! ## [MM §4.2.5] — `$f` and `$e` statements

"A variable must have its type specified in a `$f` statement before it
may be used in a `$e`, `$a`, or `$p` statement."

* [mm-lean4] `Metamath.Spec.Hyp` (floating/essential), `Metamath.VR.vhyp`
  (the floating formula `(typecode, [var])`). -/

example := @Metamath.Spec.Hyp
example := @Metamath.VR.vhyp

/-! ## [MM §4.2.6] — assertions -/

example := @Metamath.Statement
example := @Metamath.Spec.Database

/-! ## [MM §4.2.7] — frames, mandatory hypotheses, extended frames

"A frame groups together those hypotheses (and `$d` statements) relevant
to an assertion"; its `$f`/`$e` statements in order are the **mandatory
hypotheses** (RPN order).  For proofs, the book defines an **extended
frame**: "a frame together with zero or more `$d` and `$f` statements
that reference variables not among the mandatory variables"; those are
the **optional variables** and **optional hypotheses** for "temporary or
dummy variables", and "any proof referencing an assertion will ignore any
extensions to its frame."

* [mm-lean4] `Metamath.Spec.Frame` ("When stored in Database: mandatory
  hypotheses; when converted from scope frame: all active hypotheses" —
  the frame/extended-frame duality in one type).
* [knife `scopeck.rs`] `Frame` with `mandatory_count`,
  `mandatory_vars()`, `mandatory_hyps()`, and the pseudo-frames "required
  by the verifier for optional" variables — the extended frame,
  implemented.

The support boundary module proves this distinction is *load-bearing*:
provability over a bare frame and over its extension differ
(`InferenceSupportedProvableBoundary`), and the extension theorem below
implements the proof-site reconciliation direction.  The source-state
projection theorems separately prove that optional `$f` and `$d` operations
are absent from the stored assertion. -/

example := @Metamath.Spec.Frame
example := @Metamath.Spec.Frame.vars
example := @Metamath.Spec.Equivalence.varMapOfFrame
noncomputable example := @Metamath.Spec.Equivalence.frameToContext
example := @SourceGSLTState.declareFloating?_sourceAssertion_eq_of_optional
example := @SourceGSLTState.declareDisjoint?_sourceAssertion_eq_of_optional

/-! ## [MM §4.1.4] + [MM §4.3] — proof verification

"If the label refers to an active hypothesis, the expression … is pushed
onto a stack.  If the label refers to an assertion, a (unique)
substitution must exist that, when made to the mandatory hypotheses of
the referenced assertion, causes them to match the topmost entries of the
stack … The same substitution is made to the referenced assertion, and
the result is pushed onto the stack."

* Ours: the proof-occurrence machine (`MachineState`, `HeaderBuild`,
  `Execute`) and the compressed occurrence step; the supported
  declarative relation is the per-derivation semantic reading of the same
  algorithm.
* [mm-lean4 `Metamath.Verify`] the `ProofState` stack machine;
  `SupportedProvable` is the frame-supported declarative counterpart.
* [knife `verify.rs`] "a stack of known results; each step … pops zero or
  more results off the stack, does local checks, and pushes a new
  result." -/

example := @SourceGSLTCompressedTheorem.MachineState
example := @SourceGSLTCompressedTheorem.HeaderBuild
example := @SourceGSLTCompressedTheorem.Execute
example := @Metamath.Spec.Equivalence.SupportedProvable
example := @Metamath.Provable
example :=
  @InferenceSemanticFiniteSupport.Provable.exists_finiteSupport

/-! ## [MM §4.4.5] — compressed proofs

"A compressed proof … is a Metamath language extension which a complete
proof verifier should be able to parse and verify."

* Ours: `CompressedTheoremStep` and its preservation/reflection against
  the shipped mm-lean4 compressed fold. -/

example := @SourceGSLTCompressedTheorem.CompressedTheoremStep

/-!
## The active-frame anchor, implemented

[MM §4.2.7] read operationally — the "shadow specification" of what a
verifier must actually do — dictates the semantic anchor:

1. proof obligations are checked against the **active** (extended)
   frame, whose optional hypotheses supply typed dummy variables;
2. stored assertions expose only their **mandatory** frame to later
   proofs.

`SupportedProvable` is that anchor on the mm-lean4 side.  The boundary
module proved the unrestricted declarative `var` rule is *not*
conservative over it at a fixed frame; the book's own mechanism is the
extended frame.  The theorem below proves the proof-site half of that
mechanism: supported provability is preserved under extending the active
frame with a fresh optional floating hypothesis, so dummy supply is
monotone.  The distinct source-state theorems above prove the storage half:
trimming an extension back to an assertion's mandatory frame ignores every
optional `$f` and every optional pair generated by a `$d` declaration.

The remaining bridge to the unrestricted declarative relation is not a
fixed-frame conservativity theorem (the boundary module refutes that).
`InferenceSemanticFiniteSupport` now proves that each declarative derivation
has a finite list of variable leaves sufficient after a type-preserving
renaming.  The downstream `InferenceDummyAllocation` module constructs the
corresponding finite semantic frame extension and renaming.  Realizing such
an extension through a fixed source prefix remains a separate source-state
obligation: its typecodes and variables must be declared and its `$f` labels
must be globally fresh.
-/

/-- [MM §4.2.7] One step of frame extension: append an optional floating
hypothesis (`$f c v`).  Disjointness conditions are unchanged. -/
def extendFloat (fr : Metamath.Spec.Frame)
    (c : Metamath.Spec.Constant) (v : Metamath.Spec.Variable) :
    Metamath.Spec.Frame :=
  ⟨fr.hyps ++ [.floating c v], fr.dv⟩

/-- The source-valid freshness requirement for adjoining one optional
floating hypothesis.  The variable has no active floating hypothesis already
(the basic syntax forbids two active `$f` statements for one variable), and
its token does not already occur as a constant in an essential hypothesis.

The book phrases the first condition as a variable "not among the mandatory
variables" and separately requires the ordinary frame laws to continue to
hold for an extended frame.  Since `fr` is the full active frame at this
one-step boundary, absence from `fr.vars` states both obligations directly. -/
def OptionalFresh (fr : Metamath.Spec.Frame)
    (v : Metamath.Spec.Variable) : Prop :=
  v ∉ fr.vars ∧
    ∀ e, Metamath.Spec.Hyp.essential e ∈ fr.hyps → v.v ∉ e.syms

/-! ### Transport lemmas -/

theorem find?_append_of_some {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    {a : α} (h : l₁.find? p = some a) :
    (l₁ ++ l₂).find? p = some a := by
  induction l₁ with
  | nil => exact nomatch h
  | cons x xs ih =>
      simp only [List.cons_append, List.find?] at h ⊢
      cases hpx : p x with
      | true => rw [hpx] at h; exact h
      | false => rw [hpx] at h; exact ih h

theorem find?_append_of_none {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    (h : l₁.find? p = none) :
    (l₁ ++ l₂).find? p = l₂.find? p := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, List.find?] at h ⊢
      cases hpx : p x with
      | true => rw [hpx] at h; exact nomatch h
      | false => rw [hpx] at h; exact ih h

theorem findVR_append_of_some {vm tail : VarMap}
    {w : Metamath.Spec.Variable} {vr : MarioVR}
    (h : findVR vm w = some vr) :
    findVR (vm ++ tail) w = some vr := by
  unfold findVR at h ⊢
  cases hfind : vm.find? (fun p => p.1 = w) with
  | none => rw [hfind] at h; exact nomatch h
  | some q => rw [hfind] at h; rw [find?_append_of_some hfind]; exact h

theorem findVar_append_of_some {vm tail : VarMap} {vr : MarioVR}
    {w : Metamath.Spec.Variable}
    (h : findVar vm vr = some w) :
    findVar (vm ++ tail) vr = some w := by
  unfold findVar at h ⊢
  cases hfind : vm.find? (fun p => p.2 = vr) with
  | none => rw [hfind] at h; exact nomatch h
  | some q => rw [hfind] at h; rw [find?_append_of_some hfind]; exact h

theorem findVR_extend_of_ne {vm : VarMap} {v : Metamath.Spec.Variable}
    {vrN : MarioVR} {w : Metamath.Spec.Variable}
    (hnone : findVR vm w = none) (hne : w ≠ v) :
    findVR (vm ++ [(v, vrN)]) w = none := by
  unfold findVR at hnone ⊢
  cases hfind : vm.find? (fun p => p.1 = w) with
  | some q => rw [hfind] at hnone; exact nomatch hnone
  | none =>
      rw [find?_append_of_none hfind]
      have hdec : (decide (v = w)) = false :=
        decide_eq_false fun he => hne he.symm
      simp [List.find?, hdec]

theorem floatList_extendFloat (fr : Metamath.Spec.Frame)
    (c : Metamath.Spec.Constant) (v : Metamath.Spec.Variable) :
    floatList (extendFloat fr c v) = floatList fr ++ [(c, v)] := by
  unfold extendFloat floatList
  rw [List.filterMap_append]
  rfl

theorem frameVars_extendFloat (fr : Metamath.Spec.Frame)
    (c : Metamath.Spec.Constant) (v : Metamath.Spec.Variable) :
    (extendFloat fr c v).vars = fr.vars ++ [v] := by
  unfold extendFloat Metamath.Spec.Frame.vars
  rw [List.filterMap_append]
  rfl

theorem floatList_variables (fr : Metamath.Spec.Frame) :
    (floatList fr).map Prod.snd = fr.vars := by
  have aux : ∀ hyps : List Metamath.Spec.Hyp,
      (hyps.filterMap fun h =>
        match h with
        | .floating c v => some (c, v)
        | .essential _ => none).map Prod.snd =
      hyps.filterMap fun h =>
        match h with
        | .floating _ v => some v
        | .essential _ => none := by
    intro hyps
    induction hyps with
    | nil => rfl
    | cons hyp hyps ih => cases hyp <;> simp [ih]
  exact aux fr.hyps

theorem variable_mem_of_floating {fr : Metamath.Spec.Frame}
    {c : Metamath.Spec.Constant} {v : Metamath.Spec.Variable}
    (h : Metamath.Spec.Hyp.floating c v ∈ fr.hyps) :
    v ∈ fr.vars := by
  unfold Metamath.Spec.Frame.vars
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- A fresh optional float preserves both source-level floating-hypothesis
well-formedness laws.  This closes the edge that a merely semantic append
could otherwise introduce a second active `$f` for the same variable. -/
theorem frameWellFormed_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    (hframe : FrameWellFormed fr) (hfresh : OptionalFresh fr v₀) :
    FrameWellFormed (extendFloat fr c₀ v₀) := by
  constructor
  · intro c c' v hc hc'
    simp only [extendFloat, List.mem_append, List.mem_singleton] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · exact hframe.1 c c' v hc hc'
    · have hv : v = v₀ := by injection hc'
      subst v
      exact (hfresh.1 (variable_mem_of_floating hc)).elim
    · have hv : v = v₀ := by injection hc
      subst v
      exact (hfresh.1 (variable_mem_of_floating hc')).elim
    · injection hc with hcEq _
      injection hc' with hcEq' _
      exact hcEq.trans hcEq'.symm
  · have hnodup := hframe.2
    unfold FloatVarNoDup at hnodup ⊢
    rw [floatList_extendFloat, List.map_append, List.nodup_append]
    refine ⟨hnodup, by simp, ?_⟩
    intro v hv v' hv'
    have hvEq : v' = v₀ := by simpa using hv'
    subst v'
    rw [floatList_variables] at hv
    intro heq
    subst v
    exact hfresh.1 hv

/-- Adding a fresh optional float leaves all existing `$d` pairs valid and
cannot create a self-pair because the pair list itself is unchanged. -/
theorem dvWellFormed_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    (hdv : DVWellFormed fr) :
    DVWellFormed (extendFloat fr c₀ v₀) := by
  constructor
  · intro v w hvw
    obtain ⟨hv, hw⟩ := hdv.1 v w hvw
    constructor
    · simpa only [frameVars_extendFloat] using
        List.mem_append_left [v₀] hv
    · simpa only [frameVars_extendFloat] using
        List.mem_append_left [v₀] hw
  · exact hdv.2

/-- Negative calibration: an already-active variable is never fresh for a
second optional floating hypothesis. -/
theorem not_optionalFresh_of_mem {fr : Metamath.Spec.Frame}
    {v : Metamath.Spec.Variable} (hmem : v ∈ fr.vars) :
    ¬ OptionalFresh fr v :=
  fun hfresh => hfresh.1 hmem

theorem varMapOfFrameAux_append
    (l₁ l₂ : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (n : Nat) :
    varMapOfFrameAux n (l₁ ++ l₂) =
      varMapOfFrameAux n l₁ ++ varMapOfFrameAux (n + l₁.length) l₂ := by
  induction l₁ generalizing n with
  | nil => simp [varMapOfFrameAux]
  | cons head rest ih =>
      obtain ⟨c₁, v₁⟩ := head
      have harith : n + 1 + rest.length = n + (rest.length + 1) := by omega
      simp [varMapOfFrameAux, ih, harith, List.cons_append, List.length_cons]

theorem varMapOfFrame_extendFloat (fr : Metamath.Spec.Frame)
    (c : Metamath.Spec.Constant) (v : Metamath.Spec.Variable) :
    varMapOfFrame (extendFloat fr c v) =
      varMapOfFrame fr ++ [(v, ⟨c.c, (floatList fr).length⟩)] := by
  unfold varMapOfFrame
  rw [floatList_extendFloat, varMapOfFrameAux_append]
  simp [varMapOfFrameAux]

theorem exists_float_of_mem_vars {fr : Metamath.Spec.Frame}
    {w : Metamath.Spec.Variable} (hmem : w ∈ fr.vars) :
    ∃ c, (c, w) ∈ floatList fr := by
  unfold Metamath.Spec.Frame.vars at hmem
  rcases List.mem_filterMap.mp hmem with ⟨h, hh, hmatch⟩
  cases h with
  | floating c v =>
      have hv : v = w := Option.some.inj hmatch
      subst hv
      exact ⟨c, List.mem_filterMap.mpr ⟨_, hh, rfl⟩⟩
  | essential e => exact nomatch hmatch

theorem findVR_isSome_of_mem_aux {w : Metamath.Spec.Variable}
    {l : List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (hmem : ∃ c, (c, w) ∈ l) (n : Nat) :
    ∃ vr, findVR (varMapOfFrameAux n l) w = some vr := by
  induction l generalizing n with
  | nil => obtain ⟨c, hc⟩ := hmem; exact nomatch hc
  | cons head rest ih =>
      obtain ⟨c₁, v₁⟩ := head
      by_cases hw : v₁ = w
      · subst hw
        refine ⟨⟨c₁.c, n⟩, ?_⟩
        simp [findVR, varMapOfFrameAux]
      · obtain ⟨c, hc⟩ := hmem
        rcases List.mem_cons.mp hc with heq | htail
        · exact absurd (congrArg Prod.snd heq).symm hw
        · obtain ⟨vr, hvr⟩ := ih ⟨c, htail⟩ (n + 1)
          refine ⟨vr, ?_⟩
          unfold findVR at hvr ⊢
          simp only [varMapOfFrameAux, List.find?]
          have hdec : (decide (v₁ = w)) = false := decide_eq_false hw
          rw [hdec]
          exact hvr

theorem map_congr_mem {α β : Type _} {f g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.map_cons]
      rw [h a (List.Mem.head _),
        map_congr_mem (fun b hb => h b (List.Mem.tail _ hb))]

theorem frameToContext_hyps (fr : Metamath.Spec.Frame) :
    (frameToContext fr).hyps =
      fr.hyps.map (hypToMarioFormula (varMapOfFrame fr)) := rfl

theorem frameToContext_dj (fr : Metamath.Spec.Frame) :
    (frameToContext fr).dj =
      dvListToMarioDJ (varMapOfFrame fr) fr.dv := rfl

/-- The variable map of an extended frame agrees with the base frame's on
every variable that is either declared in the base frame or distinct from
the optional variable. -/
theorem findVR_extendFloat_stable {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    {w : Metamath.Spec.Variable}
    (hs : w ∈ fr.vars ∨ w ≠ v₀) :
    findVR (varMapOfFrame (extendFloat fr c₀ v₀)) w =
      findVR (varMapOfFrame fr) w := by
  rw [varMapOfFrame_extendFloat]
  cases hfind : findVR (varMapOfFrame fr) w with
  | some vr => exact findVR_append_of_some hfind
  | none =>
      rcases hs with hmem | hne
      · obtain ⟨c, hc⟩ := exists_float_of_mem_vars hmem
        obtain ⟨vr, hvr⟩ := findVR_isSome_of_mem_aux ⟨c, hc⟩ 0
        rw [show varMapOfFrame fr = varMapOfFrameAux 0 (floatList fr)
          from rfl] at hfind
        rw [hfind] at hvr
        exact nomatch hvr
      · exact findVR_extend_of_ne hfind hne

theorem toMarioSym_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    {s : String}
    (hs : Metamath.Spec.Variable.mk s ∈ fr.vars ∨ s ≠ v₀.v) :
    toMarioSym (varMapOfFrame (extendFloat fr c₀ v₀)) s =
      toMarioSym (varMapOfFrame fr) s := by
  have hs' : (⟨s⟩ : Metamath.Spec.Variable) ∈ fr.vars ∨
      (⟨s⟩ : Metamath.Spec.Variable) ≠ v₀ :=
    hs.imp_right fun hne he =>
      hne (congrArg Metamath.Spec.Variable.v he)
  simp only [toMarioSym]
  rw [findVR_extendFloat_stable hs']

theorem exprToMarioExpr_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    {e : Metamath.Spec.Expr}
    (h : ∀ s ∈ e.syms, Metamath.Spec.Variable.mk s ∈ fr.vars ∨ s ≠ v₀.v) :
    exprToMarioExpr (varMapOfFrame (extendFloat fr c₀ v₀)) e =
      exprToMarioExpr (varMapOfFrame fr) e := by
  unfold exprToMarioExpr
  exact map_congr_mem fun s hs => toMarioSym_extendFloat (h s hs)

theorem hypToMarioFormula_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    {h : Metamath.Spec.Hyp} (hmem : h ∈ fr.hyps)
    (hfresh : OptionalFresh fr v₀) :
    hypToMarioFormula (varMapOfFrame (extendFloat fr c₀ v₀)) h =
      hypToMarioFormula (varMapOfFrame fr) h := by
  cases h with
  | floating c w =>
      have hw : w ∈ fr.vars := by
        unfold Metamath.Spec.Frame.vars
        exact List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
      simp only [hypToMarioFormula]
      rw [findVR_extendFloat_stable (Or.inl hw)]
  | essential e =>
      simp only [hypToMarioFormula, exprToFormula]
      rw [exprToMarioExpr_extendFloat (by
        intro s hs
        exact Or.inr fun heq => hfresh.2 e hmem (heq ▸ hs))]

theorem frameToContext_hyps_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    {g : MarioFormula} (hfresh : OptionalFresh fr v₀)
    (hmem : g ∈ (frameToContext fr).hyps) :
    g ∈ (frameToContext (extendFloat fr c₀ v₀)).hyps := by
  rw [frameToContext_hyps] at hmem
  rw [frameToContext_hyps]
  rcases List.mem_map.mp hmem with ⟨h₀, hh₀, himg⟩
  refine List.mem_map.mpr ⟨h₀, List.mem_append_left _ hh₀, ?_⟩
  rw [hypToMarioFormula_extendFloat hh₀ hfresh]
  exact himg

theorem frameToContext_dj_le (fr : Metamath.Spec.Frame)
    (c₀ : Metamath.Spec.Constant) (v₀ : Metamath.Spec.Variable) :
    (frameToContext fr).dj ≤ (frameToContext (extendFloat fr c₀ v₀)).dj := by
  have transport : ∀ {q : MarioVR × MarioVR},
      q ∈ (fr.dv.filterMap fun p =>
        match findVR (varMapOfFrame fr) p.1,
              findVR (varMapOfFrame fr) p.2 with
        | some a, some b => some (a, b)
        | _, _ => none) →
      q ∈ (fr.dv.filterMap fun p =>
        match findVR (varMapOfFrame (extendFloat fr c₀ v₀)) p.1,
              findVR (varMapOfFrame (extendFloat fr c₀ v₀)) p.2 with
        | some a, some b => some (a, b)
        | _, _ => none) := by
    intro q hq
    rcases List.mem_filterMap.mp hq with ⟨p, hp, hmatch⟩
    refine List.mem_filterMap.mpr ⟨p, hp, ?_⟩
    cases h1 : findVR (varMapOfFrame fr) p.1 with
    | none => rw [h1] at hmatch; exact nomatch hmatch
    | some a' =>
        cases h2 : findVR (varMapOfFrame fr) p.2 with
        | none => rw [h1, h2] at hmatch; exact nomatch hmatch
        | some b' =>
            rw [h1, h2] at hmatch
            rw [varMapOfFrame_extendFloat,
              findVR_append_of_some h1, findVR_append_of_some h2]
            exact hmatch
  intro a b hab
  obtain ⟨hne, hor⟩ := hab
  refine ⟨hne, ?_⟩
  rcases hor with hp | hp
  · exact Or.inl (transport hp)
  · exact Or.inr (transport hp)

theorem marioExprWellFormed_extendFloat {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    {me : MarioExpr} (h : MarioExprWellFormed fr me) :
    MarioExprWellFormed (extendFloat fr c₀ v₀) me := by
  intro vr hvr
  obtain ⟨w, hw⟩ := h vr hvr
  refine ⟨w, ?_⟩
  rw [varMapOfFrame_extendFloat]
  exact findVar_append_of_some hw

/-! ### The extension theorem -/

/-- [MM §4.2.7] **Proof-site optional support is monotone**: supported
provability is preserved when the active frame is extended by an optional
floating hypothesis over a fresh variable.  This is the dummy-supply engine:
adding typed support does not disturb an existing derivation.  It is not, by
itself, the separate mandatory-frame projection theorem governing subsequent
proofs that reference the stored assertion. -/
theorem SupportedProvable.extendFloat
    {Γ : Metamath.Spec.Database} {fr : Metamath.Spec.Frame}
    {c₀ : Metamath.Spec.Constant} {v₀ : Metamath.Spec.Variable}
    (hfresh : OptionalFresh fr v₀)
    {fmla : MarioFormula}
    (h : SupportedProvable Γ fr fmla) :
    SupportedProvable Γ (SourceGSLTSpecGrounding.extendFloat fr c₀ v₀)
      fmla := by
  induction h with
  | hyp g hmem =>
      exact SupportedProvable.hyp g
        (frameToContext_hyps_extendFloat hfresh hmem)
  | var v hw =>
      obtain ⟨w, hw'⟩ := hw
      refine SupportedProvable.var v ⟨w, ?_⟩
      rw [varMapOfFrame_extendFloat]
      exact findVar_append_of_some hw'
  | ax σ hax hdj hhyps hvars hwf ih_hyps ih_vars =>
      exact SupportedProvable.ax σ hax
        (Metamath.DJ.subst.mono (Metamath.DJ.refl _)
          (frameToContext_dj_le fr c₀ v₀) hdj)
        ih_hyps ih_vars
        (fun v hv => marioExprWellFormed_extendFloat (hwf v hv))

/-! ### Finite optional-frame extensions

The book permits zero or more optional floating hypotheses.  The one-step
theorem above is the local law; the definitions below package a finite,
ordered sequence without hiding the freshness obligation at any step.  The
order is semantically relevant because `varMapOfFrame` assigns variable
indices in floating-hypothesis order. -/

/-- Append an ordered list of optional floating hypotheses to a frame. -/
def extendFloats : Metamath.Spec.Frame →
    List (Metamath.Spec.Constant × Metamath.Spec.Variable) →
    Metamath.Spec.Frame
  | fr, [] => fr
  | fr, (c, v) :: rest => extendFloats (extendFloat fr c v) rest

/-- Each optional variable must be fresh at the exact prefix where its `$f`
statement is appended.  This is stronger than merely requiring the supplied
names to be distinct from the initial frame. -/
inductive OptionalFloatSequence :
    (fr : Metamath.Spec.Frame) →
    List (Metamath.Spec.Constant × Metamath.Spec.Variable) → Prop
  | nil (fr) : OptionalFloatSequence fr []
  | cons {fr c v rest} :
      OptionalFresh fr v →
      OptionalFloatSequence (extendFloat fr c v) rest →
      OptionalFloatSequence fr ((c, v) :: rest)

/-- The executable batch extension is exactly a hypothesis-list append; its
disjoint-variable list is unchanged. -/
theorem extendFloats_eq (fr : Metamath.Spec.Frame)
    (declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)) :
    extendFloats fr declarations =
      { hyps := fr.hyps ++ declarations.map (fun pair =>
          Metamath.Spec.Hyp.floating pair.1 pair.2)
        dv := fr.dv } := by
  induction declarations generalizing fr with
  | nil => simp [extendFloats]
  | cons declaration rest ih =>
      obtain ⟨c, v⟩ := declaration
      rw [extendFloats, ih]
      simp [extendFloat, List.append_assoc]

/-- The corresponding variable map is the old map followed by the new
typed indices, starting at the old floating-hypothesis count. -/
theorem varMapOfFrame_extendFloats (fr : Metamath.Spec.Frame)
    (declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)) :
    varMapOfFrame (extendFloats fr declarations) =
      varMapOfFrame fr ++
        varMapOfFrameAux (floatList fr).length declarations := by
  have hfloat :
      floatList (extendFloats fr declarations) =
        floatList fr ++ declarations := by
    induction declarations generalizing fr with
    | nil => simp [extendFloats]
    | cons declaration rest ih =>
        obtain ⟨c, v⟩ := declaration
        rw [extendFloats, ih, floatList_extendFloat]
        simp [List.append_assoc]
  unfold varMapOfFrame
  rw [hfloat, varMapOfFrameAux_append]
  simp

/-- Finite optional extension preserves source frame well-formedness. -/
theorem frameWellFormed_extendFloats
    {fr : Metamath.Spec.Frame}
    {declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (hframe : FrameWellFormed fr)
    (hsequence : OptionalFloatSequence fr declarations) :
    FrameWellFormed (extendFloats fr declarations) := by
  induction hsequence with
  | nil => exact hframe
  | @cons fr c v rest hfresh htail ih =>
      exact ih (frameWellFormed_extendFloat hframe hfresh)

/-- Finite optional extension preserves well-formed disjoint-variable data. -/
theorem dvWellFormed_extendFloats
    {fr : Metamath.Spec.Frame}
    {declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (hdv : DVWellFormed fr) :
    DVWellFormed (extendFloats fr declarations) := by
  induction declarations generalizing fr with
  | nil => exact hdv
  | cons declaration rest ih =>
      obtain ⟨c, v⟩ := declaration
      exact ih (dvWellFormed_extendFloat hdv)

/-- [MM §4.2.7] A supported proof remains valid after any finite, ordered,
source-fresh optional floating extension. -/
theorem SupportedProvable.extendFloats
    {Γ : Metamath.Spec.Database} {fr : Metamath.Spec.Frame}
    {declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (hsequence : OptionalFloatSequence fr declarations)
    {fmla : MarioFormula}
    (h : SupportedProvable Γ fr fmla) :
    SupportedProvable Γ (extendFloats fr declarations) fmla := by
  induction hsequence with
  | nil => exact h
  | @cons fr c v rest hfresh htail ih =>
      exact ih (SupportedProvable.extendFloat hfresh h)

/-! ### Calibration against the support boundary

The boundary module's repair witness is literally one application of
[MM §4.2.7] frame extension to the closed-scope theorem site. -/

/-- Positive: the dummy frame of the boundary counterexample is exactly
the empty frame extended by one optional floating hypothesis. -/
example :
    SourceGSLTSpecGrounding.extendFloat
      InferenceSupportedProvableBoundary.emptyFrame
      InferenceSupportedProvableBoundary.wffConstant
      InferenceSupportedProvableBoundary.dummyVariable =
    InferenceSupportedProvableBoundary.dummyFrame := rfl

/-- Positive: the extension theorem transports any supported derivation
over the empty frame into the extended frame (the freshness condition is
vacuous there). -/
example {fmla : MarioFormula}
    (h : SupportedProvable
      InferenceSupportedProvableBoundary.counterexampleDatabase
      InferenceSupportedProvableBoundary.emptyFrame fmla) :
    SupportedProvable
      InferenceSupportedProvableBoundary.counterexampleDatabase
      InferenceSupportedProvableBoundary.dummyFrame fmla := by
  exact SupportedProvable.extendFloat
    (c₀ := InferenceSupportedProvableBoundary.wffConstant)
    (v₀ := InferenceSupportedProvableBoundary.dummyVariable)
    (by
      constructor
      · simp [InferenceSupportedProvableBoundary.emptyFrame,
          Metamath.Spec.Frame.vars]
      · intro e hmem
        simp [InferenceSupportedProvableBoundary.emptyFrame] at hmem)
    h

/-- Negative: the converse direction is refuted by the boundary module —
`|- c` is supported over the extended (dummy) frame but not over the bare
frame, so frame extension is strictly monotone. -/
example :
    ¬ (SupportedProvable
        InferenceSupportedProvableBoundary.counterexampleDatabase
        InferenceSupportedProvableBoundary.emptyFrame
        InferenceSupportedProvableBoundary.target) ∧
    SupportedProvable
      InferenceSupportedProvableBoundary.counterexampleDatabase
      InferenceSupportedProvableBoundary.dummyFrame
      InferenceSupportedProvableBoundary.target :=
  ⟨InferenceSupportedProvableBoundary.not_supportedProvable_target,
   InferenceSupportedProvableBoundary.supportedProvable_target_with_dummy⟩

end Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding
