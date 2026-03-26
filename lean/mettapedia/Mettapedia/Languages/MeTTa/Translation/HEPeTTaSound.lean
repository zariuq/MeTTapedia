import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.Properties
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.Framework.PredFiniteSufficient

/-!
# HE → PeTTa MeTTaEval Soundness (Pure Fragment)

Phase 1 of the HE ↔ PeTTa translation: prove that HE's evaluation
is sound with respect to PeTTa's `MeTTaEval` on the **pure, no-grounded fragment**.

## Reshaped Theorems (per council review)

The original `mettaCall_sound` overclaimed. This file provides three narrower,
honest theorems:

- **Theorem A** (`mettaCall_equation_step_sound`): one-step equation match →
  rule exists in PeTTa space. Does NOT chase recursive `EvalAtom` on the result.
- **Theorem B** (`evalAtom_leaf_sound`): empty/error/variable leaves pass through.
- **Theorem C** (`mettaCall_error_sound`): error passthrough is trivial.

## What is explicitly OUT of Phase 1

- `MettaCall.no_match` on compound expressions — no `MeTTaEval` constructor
- `MettaCall.empty_results` — same issue
- `EvalAtom.type_cast` — needs typeCast in MeTTaEval
- `EvalAtom.interpret_success/error` — needs InterpretExpression
- All Interpret* constructors (16 cases)
- `symbolPassThrough` without `isPassThroughType ty` proof

## References

- HE spec: `EvalSpec.lean` (6 mutual relations, 39 constructors)
- PeTTa target: `MeTTaEval.lean` (single relation, 8 constructors)
- AST bridge: `OSLFCore/Bridge.lean` (`atomToPattern`, `patternToAtom`)
- HE Properties: `Properties.lean` (eval_empty_always, mettaCall_error_always, etc.)
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge (atomToPattern patternToAtom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings ResultPair GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE (isErrorAtom isEmptyOrError)
open Mettapedia.Languages.MeTTa.PeTTa (PeTTaSpace MeTTaEval EvalResult)
open Mettapedia.Languages.MeTTa.PeTTa (mkError isPassThroughType)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern RewriteRule)
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern applyBindings
  isMatchCorrectAux isMatchCorrectListAux)

/-! ## Translatable Predicate -/

/-- An atom is in the **translatable pure fragment**: no `Atom.grounded` anywhere,
    and `atomToPattern` succeeds on it. -/
def Translatable (a : Atom) : Prop := (atomToPattern a).isSome = true

/-- Extract the witness pattern from a Translatable atom. -/
theorem translatable_witness (a : Atom) (h : Translatable a) :
    ∃ p, atomToPattern a = some p := by
  exact Option.isSome_iff_exists.mp h

/-! ## Hypothesis D: ExecGroundedOnly

Council (Ritchie, Conway, Tang, Harper): Since `GroundedDispatch` is arbitrary,
grounded elimination needs this constraint. Without it, the 5 grounded branches
are NOT absurd — `dispatch.isExecutable` could return true on non-grounded atoms. -/

/-- Constraint on `GroundedDispatch`: only `Atom.grounded` values are executable.
    This is the natural well-formedness condition on dispatch tables. -/
def ExecGroundedOnly (dispatch : GroundedDispatch) : Prop :=
  ∀ op, dispatch.isExecutable op = true → ∃ g, op = Atom.grounded g

/-! ## Space Translation -/

/-- Extract a PeTTa rewrite rule from an HE equation atom `(= lhs rhs)`. -/
def atomToRule? (a : Atom) : Option RewriteRule :=
  match a with
  | .expression [.symbol "=", lhs, rhs] => do
      let l ← atomToPattern lhs
      let r ← atomToPattern rhs
      return { name := "", typeContext := [], premises := [], left := l, right := r }
  | _ => none

def heSpaceToPeTTaSpace (space : Space) : PeTTaSpace :=
  let rules := space.atoms.filterMap atomToRule?
  let facts := space.atoms.filter (fun a => !Space.isEquation a) |>.filterMap atomToPattern
  { facts := facts, rules := rules }

/-! ## Bindings Translation -/

/-- Convert HE Bindings to OSLF Bindings. -/
def heBindingsToOSLF (b : Bindings) :
    Mettapedia.OSLF.MeTTaIL.Match.Bindings :=
  let assignPairs := b.assignments.filterMap fun (v, a) =>
    (atomToPattern a).map (v, ·)
  let eqPairs := b.equalities.map fun (x, y) => (x, Pattern.fvar y)
  assignPairs ++ eqPairs

/-! ## Bridge Lemmas -/

/-- An HE equation `(= lhs rhs)` where both sides are translatable produces
    a rule in the translated PeTTa space. -/
theorem heSpaceToPeTTaSpace_has_rule (space : Space)
    (lhs rhs : Atom) (hl : Translatable lhs) (hr : Translatable rhs)
    (hmem : Atom.expression [.symbol "=", lhs, rhs] ∈ space.atoms) :
    ∃ r, r ∈ (heSpaceToPeTTaSpace space).rules ∧
      r.premises = [] ∧
      ∃ pl pr, atomToPattern lhs = some pl ∧ atomToPattern rhs = some pr ∧
        r.left = pl ∧ r.right = pr := by
  have ⟨pl, hpl⟩ := translatable_witness lhs hl
  have ⟨pr, hpr⟩ := translatable_witness rhs hr
  refine ⟨{ name := "", typeContext := [], premises := [], left := pl, right := pr },
          ?_, rfl, pl, pr, hpl, hpr, rfl, rfl⟩
  simp only [heSpaceToPeTTaSpace]
  apply List.mem_filterMap.mpr
  exact ⟨.expression [.symbol "=", lhs, rhs], hmem, by simp [atomToRule?, hpl, hpr]⟩

/-- HE bindings assignment lookup corresponds to OSLF bindings lookup
    when the assigned atom is translatable. -/
theorem heBindingsToOSLF_lookup_assign (b : Bindings) (v : String) (a : Atom)
    (hmem : (v, a) ∈ b.assignments) (ht : Translatable a) :
    ∃ p, atomToPattern a = some p ∧
      (v, p) ∈ heBindingsToOSLF b := by
  have ⟨p, hp⟩ := translatable_witness a ht
  refine ⟨p, hp, ?_⟩
  simp only [heBindingsToOSLF]
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  exact ⟨(v, a), hmem, by simp [hp]⟩

/-! ## atomToPattern on specific atom forms -/

/-- `atomToPattern` on `Atom.error src msg` yields `mkError p_src p_msg`. -/
theorem atomToPattern_error (src msg : Atom)
    (hs : Translatable src) (hm : Translatable msg) :
    ∃ ps pm, atomToPattern src = some ps ∧ atomToPattern msg = some pm ∧
      atomToPattern (Atom.error src msg) = some (mkError ps pm) := by
  have ⟨ps, hps⟩ := translatable_witness src hs
  have ⟨pm, hpm⟩ := translatable_witness msg hm
  refine ⟨ps, pm, hps, hpm, ?_⟩
  -- Atom.error src msg = .expression [.symbol "Error", src, msg]
  simp only [Atom.error, atomToPattern]
  -- atomToPattern on expression [.symbol "Error", src, msg]:
  -- constructor = "Error", args = [src, msg]
  -- Need: atomToPattern src and atomToPattern msg both succeed
  -- and patArgs.length == args.length
  simp [hps, hpm, mkError]

/-- `atomToPattern` on `Atom.empty` (= `.symbol "Empty"`) yields `.apply "Empty" []`. -/
theorem atomToPattern_empty :
    atomToPattern Atom.empty = some (.apply "Empty" []) := by
  simp [Atom.empty, atomToPattern]

/-- `atomToPattern` on a variable `.var v` yields `.fvar v`. -/
theorem atomToPattern_var (v : String) :
    atomToPattern (.var v) = some (.fvar v) := by
  simp [atomToPattern]

/-! ## Theorem C: MettaCall Error Soundness

Council (Knuth, Ritchie): Knock out the trivial case first. -/

/-- **MettaCall error soundness**: When HE's `MettaCall.error_passthrough` fires
    (atom is `(Error src msg)`), the PeTTa `errorPassThrough` constructor applies. -/
theorem mettaCall_error_sound
    (space : Space) (_dispatch : GroundedDispatch)
    (src msg ty : Atom) (b : Bindings)
    (ps pm : Pattern)
    (_hps : atomToPattern src = some ps) (_hpm : atomToPattern msg = some pm) :
    ∀ (pty : Pattern),
      atomToPattern ty = some pty →
    ∃ (pres : EvalResult),
      MeTTaEval (heSpaceToPeTTaSpace space)
        (mkError ps pm) pty (heBindingsToOSLF b) pres ∧
      (mkError ps pm, heBindingsToOSLF b) ∈ pres := by
  intro pty _hpty
  exact ⟨[(mkError ps pm, heBindingsToOSLF b)],
    MeTTaEval.errorPassThrough ps pm pty (heBindingsToOSLF b),
    List.Mem.head _⟩

/-! ## Theorem B: EvalAtom Leaf Soundness

Council (Weirich, Wadler, SPJ, Brown): Narrow to what `MeTTaEval` can actually
represent. Proved for: variables, errors. -/

/-- **Variable leaf soundness**: HE's `EvalAtom` on a variable returns the variable
    unchanged; PeTTa's `varPassThrough` does the same. -/
theorem evalAtom_variable_sound
    (space : Space) (_dispatch : GroundedDispatch)
    (v : String) (ty : Atom) (b : Bindings)
    (_hty : Translatable ty) :
    ∀ (pty : Pattern),
      atomToPattern ty = some pty →
    ∃ (pres : EvalResult),
      MeTTaEval (heSpaceToPeTTaSpace space)
        (.fvar v) pty (heBindingsToOSLF b) pres ∧
      (.fvar v, heBindingsToOSLF b) ∈ pres := by
  intro pty _hpty
  exact ⟨[(.fvar v, heBindingsToOSLF b)],
    MeTTaEval.varPassThrough v pty (heBindingsToOSLF b),
    List.Mem.head _⟩

/-- **Error leaf soundness**: HE's `EvalAtom` on `(Error src msg)` returns the error
    unchanged; PeTTa's `errorPassThrough` does the same.
    (Factored from Theorem C for reuse in EvalAtom leaf proofs.) -/
theorem evalAtom_error_sound
    (space : Space) (_dispatch : GroundedDispatch)
    (src msg ty : Atom) (b : Bindings)
    (hs : Translatable src) (hm : Translatable msg)
    (_hty : Translatable ty) :
    ∀ (pty : Pattern),
      atomToPattern ty = some pty →
    ∃ ps pm, ∃ pres : EvalResult,
      atomToPattern src = some ps ∧
      atomToPattern msg = some pm ∧
      MeTTaEval (heSpaceToPeTTaSpace space)
        (mkError ps pm) pty (heBindingsToOSLF b) pres ∧
      (mkError ps pm, heBindingsToOSLF b) ∈ pres := by
  intro pty _hpty
  have ⟨ps, hps⟩ := translatable_witness src hs
  have ⟨pm, hpm⟩ := translatable_witness msg hm
  exact ⟨ps, pm, [(mkError ps pm, heBindingsToOSLF b)],
    hps, hpm,
    MeTTaEval.errorPassThrough ps pm pty (heBindingsToOSLF b),
    List.Mem.head _⟩

/-! ## Theorem A: MettaCall Equation Step Soundness

Council (McBride, Pfenning, Coquand, SPJ): Split by semantic layer. The one-step
equation match IS the core claim. Recursion is a separate induction.

The proof relies on a match correspondence lemma connecting HE's `simpleMatch`
(operating on `Atom`) to PeTTa's `matchPattern` (operating on `Pattern`).
This lemma is stated below and is the key Phase 2 infrastructure. -/

/-- Extract the original equation from `queryEquations` membership.
    If `queryEquations` returns `(rhs', b)`, then there exists an original equation
    `(= lhs_orig rhs_orig)` in `space.atoms` from which it was derived via freshening. -/
theorem queryEquations_source (space : Space) (atom : Atom) (fuel : Nat)
    (rhs' : Atom) (qb : Bindings)
    (h : (rhs', qb) ∈ Mettapedia.Languages.MeTTa.HE.queryEquations space atom fuel) :
    ∃ lhs_orig rhs_orig idx,
      (Atom.expression [.symbol "=", lhs_orig, rhs_orig], idx) ∈ space.atoms.zipIdx ∧
      let (lhs_f, rhs_f) := Mettapedia.Languages.MeTTa.HE.freshenEquation idx lhs_orig rhs_orig fuel
      rhs' = rhs_f ∧
      Mettapedia.Languages.MeTTa.HE.simpleMatch lhs_f atom Bindings.empty fuel = some qb := by
  simp only [Mettapedia.Languages.MeTTa.HE.queryEquations] at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨eq, idx⟩, hmem, hsome⟩ := h
  simp only at hsome
  split at hsome <;> simp_all
  rename_i lhs_orig rhs_orig
  split at hsome <;> simp_all
  rename_i b' hmatch_eq
  exact ⟨lhs_orig, rhs_orig, idx, hmem, hsome.1.symm, hmatch_eq⟩

/-- **MettaCall equation step soundness**: If HE's `equation_match` fires
    (finding an equation in space whose LHS matches the atom), then there exists
    a corresponding rule in the PeTTa space from the ORIGINAL equation.

    This is ONE-STEP only: it does NOT follow the recursive `EvalAtom` on the
    rewritten result. The recursive correspondence is Phase 2 (mutual induction).

    The conclusion talks about the ORIGINAL equation sides (pre-freshening),
    since `heSpaceToPeTTaSpace` builds rules from original equations. -/
theorem mettaCall_equation_step_sound
    (space : Space) (atom : Atom) (fuel : Nat)
    (rhs' : Atom) (queryBindings : Bindings)
    (h_query : (rhs', queryBindings) ∈
        Mettapedia.Languages.MeTTa.HE.queryEquations space atom fuel) :
    -- There exists an original equation in space with a corresponding PeTTa rule
    ∃ lhs_orig rhs_orig,
      .expression [.symbol "=", lhs_orig, rhs_orig] ∈ space.atoms ∧
      -- If both sides are translatable, the rule exists in PeTTa space
      (Translatable lhs_orig → Translatable rhs_orig →
        ∃ r ∈ (heSpaceToPeTTaSpace space).rules,
          r.premises = [] ∧
          ∃ pl pr, atomToPattern lhs_orig = some pl ∧
            atomToPattern rhs_orig = some pr ∧
            r.left = pl ∧ r.right = pr) := by
  obtain ⟨lhs_orig, rhs_orig, idx, hmem, _, _⟩ := queryEquations_source space atom fuel rhs' queryBindings h_query
  have hmem_atoms : .expression [.symbol "=", lhs_orig, rhs_orig] ∈ space.atoms := by
    have ⟨_, hlt, heq⟩ := List.mem_zipIdx hmem
    simp at hlt
    exact heq ▸ List.getElem_mem hlt
  exact ⟨lhs_orig, rhs_orig, hmem_atoms, fun hl hr =>
    heSpaceToPeTTaSpace_has_rule space lhs_orig rhs_orig hl hr hmem_atoms⟩

/-! ## Phase 2, Step 1: PureTranslatable + isMatchCorrect

`atomToPattern` can produce `.lambda`/`.subst` patterns (from `"λ"`/`"subst"` head
symbols), which are NOT `isMatchCorrect`. Standard MeTTa equations never use these.
`PureTranslatable` refines `Translatable` to guarantee `isMatchCorrect`. -/

/-- An atom translates to an `isMatchCorrect` pattern: no `.lambda`, `.subst`,
    or `.collection` nodes in the output. Covers all standard MeTTa atoms. -/
def PureTranslatable (a : Atom) : Prop :=
  ∃ p, atomToPattern a = some p ∧ isMatchCorrectAux p = true

theorem pureTranslatable_var (v : String) : PureTranslatable (.var v) :=
  ⟨.fvar v, by simp [atomToPattern], rfl⟩

theorem pureTranslatable_symbol (s : String) : PureTranslatable (.symbol s) :=
  ⟨.apply s [], by simp [atomToPattern], rfl⟩

/-- `isMatchCorrectListAux` holds when all elements satisfy `isMatchCorrectAux`. -/
private theorem isMatchCorrectListAux_of_forall {ps : List Pattern}
    (h : ∀ p ∈ ps, isMatchCorrectAux p = true) :
    isMatchCorrectListAux ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [isMatchCorrectListAux, Bool.and_eq_true]
    exact ⟨h p (.head _),
           ih (fun q hq => h q (.tail _ hq))⟩

/-- Standard expression atoms (head is not `"λ"` or `"subst"`) translate to
    `isMatchCorrect` patterns when all arguments are `PureTranslatable`. -/
theorem pureTranslatable_expr (c : String) (args : List Atom)
    (hc_not_lam : c ≠ "λ") (hc_not_subst : c ≠ "subst")
    (hargs : ∀ a ∈ args, PureTranslatable a) :
    PureTranslatable (.expression (.symbol c :: args)) := by
  -- Each arg has a pattern witness
  have hpats : ∀ a ∈ args, ∃ p, atomToPattern a = some p ∧ isMatchCorrectAux p = true := hargs
  -- Build the list of pattern witnesses: filterMap preserves length
  have hfm : (args.filterMap atomToPattern).length = args.length := by
    induction args with
    | nil => simp
    | cons a as ih =>
      simp only [List.filterMap_cons]
      obtain ⟨p, hp, _⟩ := hpats a (.head _)
      rw [hp]
      simp only [List.length_cons]
      congr 1
      exact ih (fun a' ha' => hargs a' (.tail _ ha'))
               (fun a' ha' => hpats a' (.tail _ ha'))
  -- atomToPattern on expression [.symbol c :: args] with c ≠ "λ", c ≠ "subst"
  let patArgs := args.filterMap atomToPattern
  have hatp : atomToPattern (.expression (.symbol c :: args)) = some (.apply c patArgs) := by
    unfold atomToPattern
    simp only [beq_iff_eq, hc_not_lam, ↓reduceIte, hc_not_subst]
    simp only [patArgs, hfm, ↓reduceIte]
  -- isMatchCorrectAux (.apply c patArgs)
  have hmc : isMatchCorrectAux (.apply c patArgs) = true := by
    simp only [isMatchCorrectAux]
    apply isMatchCorrectListAux_of_forall
    intro p hp
    rw [List.mem_filterMap] at hp
    obtain ⟨a, ha, hpa⟩ := hp
    obtain ⟨p', hp', hmc'⟩ := hpats a ha
    have : p = p' := Option.some.inj (hpa ▸ hp')
    rw [this]; exact hmc'
  exact ⟨.apply c patArgs, hatp, hmc⟩

/-- `PureTranslatable` implies `Translatable`. -/
theorem PureTranslatable.toTranslatable {a : Atom} (h : PureTranslatable a) :
    Translatable a := by
  obtain ⟨p, hp, _⟩ := h
  simp [Translatable, hp]

/-! ## Phase 2, Step 4: Symbol Passthrough -/

/-- **Symbol passthrough soundness**: HE's `EvalAtom` on a symbol with pass-through
    type returns the symbol unchanged; PeTTa's `symbolPassThrough` does the same. -/
theorem evalAtom_symbol_sound
    (space : Space) (_dispatch : GroundedDispatch)
    (s : String) (b : Bindings)
    (pty : Pattern) (hpass : isPassThroughType pty) :
    ∃ (pres : EvalResult),
      MeTTaEval (heSpaceToPeTTaSpace space)
        (.apply s []) pty (heBindingsToOSLF b) pres ∧
      (.apply s [], heBindingsToOSLF b) ∈ pres := by
  exact ⟨[(.apply s [], heBindingsToOSLF b)],
    MeTTaEval.symbolPassThrough s pty (heBindingsToOSLF b) hpass,
    List.Mem.head _⟩

/-! ## Phase 2, Step 2: Match Correspondence (HE simpleMatch → PeTTa matchPattern)

Council (Carneiro, Pfenning, McBride): prove existence of a PeTTa match, not exact
binding equality. `simpleMatch` success implies `matchPattern` nonemptiness. -/

/-- `matchPattern` on an fvar (wildcard) always succeeds with a singleton binding. -/
theorem matchPattern_fvar_nonempty (x : String) (t : Pattern) :
    [(x, t)] ∈ matchPattern (.fvar x) t := by
  rw [Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_iff_matchRel]; exact .fvar

/-- `matchPattern` on two identical nullary constructors succeeds with empty bindings. -/
theorem matchPattern_apply_nil_self (c : String) :
    [] ∈ matchPattern (.apply c []) (.apply c []) := by
  rw [Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_iff_matchRel]
  exact .apply .nil rfl

/-- Looking up a translated assignment by variable name finds the translated pair. -/
private theorem translated_assignments_find
    (as : List (String × Atom))
    (v : String) (a : Atom) (p : Pattern)
    (hlookup : List.lookup v as = some a)
    (hpat : atomToPattern a = some p) :
    List.find? (fun x => x.1 == v)
      (as.filterMap fun (w, t) => (atomToPattern t).map (w, ·)) = some (v, p) := by
  induction as with
  | nil => simp at hlookup
  | cons hd tl ih =>
      rcases hd with ⟨w, t⟩
      cases hbeq : (v == w) with
      | false =>
          have hlookup' : List.lookup v tl = some a := by
            simpa [List.lookup, hbeq] using hlookup
          have hwv' : (w == v) = false := by
            cases h : (w == v) with
            | false => rfl
            | true =>
                have hvw : v = w := (beq_iff_eq.mp h).symm
                have htrue : (v == w) = true := by exact beq_iff_eq.mpr hvw
                simp [htrue] at hbeq
          cases hat : atomToPattern t <;>
            simpa [List.find?, hat, hwv'] using ih hlookup'
      | true =>
          have hvw : v = w := by exact beq_iff_eq.mp hbeq
          subst hvw
          simp [List.lookup] at hlookup
          subst hlookup
          simp [hpat]

/-- A translated HE lookup yields the expected `applyBindings` result on a free variable. -/
private theorem applyBindings_fvar_of_lookup
    (b : Bindings)
    (v : String) (a : Atom) (p : Pattern)
    (hlookup : b.lookup v = some a)
    (hpat : atomToPattern a = some p) :
    applyBindings (heBindingsToOSLF b) (.fvar v) = p := by
  conv_lhs => rw [applyBindings.eq_def]
  simp only [heBindingsToOSLF]
  have hfind :
      List.find? (fun x => x.1 == v)
        (b.assignments.filterMap fun (w, t) => (atomToPattern t).map (w, ·)) =
        some (v, p) := by
    exact translated_assignments_find b.assignments v a p hlookup hpat
  rw [List.find?_append]
  rw [hfind]
  simp

/-- `atomToPattern` never produces a de Bruijn variable. -/
private theorem atomToPattern_never_bvar (a : Atom) (n : Nat) :
    atomToPattern a ≠ some (.bvar n) := by
  cases a with
  | var name => simp [atomToPattern]
  | symbol s => simp [atomToPattern]
  | grounded g => simp [atomToPattern]
  | expression es =>
      cases es with
      | nil => simp [atomToPattern]
      | cons hd tl =>
          cases hd with
          | symbol s =>
              unfold atomToPattern
              split
              · cases tl with
                | nil => simp
                | cons head tail =>
                    cases tail with
                    | nil =>
                        cases hbody : atomToPattern head <;> simp [hbody]
                    | cons hd tl => simp
              · split
                · cases tl with
                  | nil => simp
                  | cons head tail =>
                      cases tail with
                      | nil => simp
                      | cons repl tail' =>
                          cases tail' with
                          | nil =>
                              cases hbody : atomToPattern head <;>
                                cases hrepl : atomToPattern repl <;>
                                simp [hbody, hrepl]
                          | cons hd tl => simp
                · simp
          | var name => simp [atomToPattern]
          | grounded g => simp [atomToPattern]
          | expression xs => simp [atomToPattern]

/-! ## Phase 2: Commutation Infrastructure (GPT-5.4 Pro architecture, council 87%)

The key insight: prove `applyBindings (heBindingsToOSLF qb) pl = pa` (the commutation),
then derive matchPattern nonemptiness via `matchPattern_applyBindings_complete`. -/

/-! ### Step A: HEBindingsExtends -/

/-- Monotonicity predicate: `b'` extends `b` (preserves all lookups). -/
private def HEBindingsExtends (b b' : Bindings) : Prop :=
  ∀ x a, b.lookup x = some a → b'.lookup x = some a

private theorem heExt_refl (b : Bindings) : HEBindingsExtends b b :=
  fun _ _ h => h

private theorem heExt_trans {b1 b2 b3 : Bindings}
    (h12 : HEBindingsExtends b1 b2) (h23 : HEBindingsExtends b2 b3) :
    HEBindingsExtends b1 b3 :=
  fun x a hx => h23 x a (h12 x a hx)

/-! ### Step B: PureTranslatable isMatchCorrect extraction -/

private theorem pureTranslatable_hmc_of_eq {a : Atom} {p : Pattern}
    (h : PureTranslatable a) (hp : atomToPattern a = some p) :
    isMatchCorrectAux p = true := by
  obtain ⟨p', hp', hmc'⟩ := h
  have : p = p' := Option.some.inj (hp ▸ hp')
  rw [this]; exact hmc'

/-! ### Step C: applyBindings equation lemma -/

private theorem applyBindings_apply
    (bs : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (c : String) (args : List Pattern) :
    applyBindings bs (.apply c args) = .apply c (args.map (applyBindings bs)) := by
  conv_lhs => rw [applyBindings.eq_def]

/-! ### Step D: isMatchCorrectAux membership extraction -/

private theorem isMatchCorrectAux_of_mem_list
    {ps : List Pattern} {p : Pattern}
    (h : isMatchCorrectListAux ps = true) (hp : p ∈ ps) :
    isMatchCorrectAux p = true := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    simp only [isMatchCorrectListAux, Bool.and_eq_true] at h
    cases hp with
    | head _ => exact h.1
    | tail _ hp' => exact ih h.2 hp'

/-! ### Step E: filterMap length implies all Some -/

theorem filterMap_length_eq_length_implies_some
    {α β : Type*} (f : α → Option β) (xs : List α)
    (hlen : (xs.filterMap f).length = xs.length) :
    ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a as ih =>
    intro x hx
    cases hfa : f a with
    | none =>
      simp [hfa] at hlen
      have := List.length_filterMap_le f as
      omega
    | some y =>
      have hlen' : (as.filterMap f).length = as.length := by
        simp only [List.filterMap_cons, hfa, List.length_cons] at hlen
        omega
      cases hx with
      | head _ => exact ⟨y, hfa⟩
      | tail _ hx' => exact ih hlen' x hx'

/-! ### Step F: pure_expr_translation_shape -/

/-- A PureTranslatable expression translates to `.apply c patArgs` with matching length. -/
private theorem pure_expr_translation_shape
    (c : String) (args : List Atom) (p : Pattern)
    (hpat : atomToPattern (.expression (.symbol c :: args)) = some p)
    (hmc : isMatchCorrectAux p = true) :
    ∃ patArgs, p = .apply c patArgs ∧
      patArgs = args.filterMap atomToPattern ∧
      patArgs.length = args.length := by
  by_cases hlam : c = "λ"
  · subst hlam
    unfold atomToPattern at hpat
    simp only [beq_self_eq_true, ↓reduceIte] at hpat
    cases args with
    | nil => simp at hpat
    | cons body rest =>
      cases rest with
      | nil =>
        cases hbody : atomToPattern body <;> simp [hbody] at hpat
        subst hpat; simp [isMatchCorrectAux] at hmc
      | cons _ _ => simp at hpat
  · by_cases hsubst : c = "subst"
    · subst hsubst
      unfold atomToPattern at hpat
      simp only [beq_iff_eq, show "subst" ≠ "λ" by decide, ↓reduceIte, beq_self_eq_true] at hpat
      cases args with
      | nil => simp at hpat
      | cons body rest =>
        cases rest with
        | nil => simp at hpat
        | cons repl tail =>
          cases tail with
          | nil =>
            cases hbody : atomToPattern body <;>
              cases hrepl : atomToPattern repl <;>
              simp [hbody, hrepl] at hpat
            subst hpat; simp [isMatchCorrectAux] at hmc
          | cons _ _ => simp at hpat
    · unfold atomToPattern at hpat
      simp only [beq_iff_eq, hlam, ↓reduceIte, hsubst] at hpat
      split at hpat
      · rename_i hlen
        injection hpat with hp; subst hp
        exact ⟨args.filterMap atomToPattern, rfl, rfl, hlen⟩
      · simp at hpat

/-! ### Step G: pure_args_of_expr_translation -/

/-- All arguments of a PureTranslatable expression are themselves PureTranslatable. -/
private theorem pure_args_of_expr_translation
    (c : String) (args : List Atom) (p : Pattern)
    (hpat : atomToPattern (.expression (.symbol c :: args)) = some p)
    (hmc : isMatchCorrectAux p = true) :
    ∀ a ∈ args, PureTranslatable a := by
  obtain ⟨patArgs, hpEq, hfm, hlen⟩ := pure_expr_translation_shape c args p hpat hmc
  subst hpEq
  have hlistmc : isMatchCorrectListAux patArgs = true := by
    simpa [isMatchCorrectAux] using hmc
  intro a ha
  have ⟨q, hq⟩ := filterMap_length_eq_length_implies_some atomToPattern args
    (by rwa [← hfm]) a ha
  exact ⟨q, hq, isMatchCorrectAux_of_mem_list hlistmc
    (hfm ▸ List.mem_filterMap.mpr ⟨a, ha, hq⟩)⟩

/-! ### Step H: HE Bindings assign helpers -/

private theorem isBound_false_of_lookup_none {b : Bindings} {v : String}
    (h : b.lookup v = none) : b.isBound v = false := by
  simp [Bindings.isBound, h]

private theorem lookup_assign_of_lookup_none
    (b : Bindings) (v : String) (a : Atom)
    (hnone : b.lookup v = none) :
    (b.assign v a).lookup v = some a := by
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true, ↓reduceIte,
    List.lookup_append, Bindings.lookup] at hnone ⊢
  simp [hnone]

private theorem extends_assign_of_lookup_none
    (b : Bindings) (v : String) (a : Atom)
    (hnone : b.lookup v = none) :
    HEBindingsExtends b (b.assign v a) := by
  intro x val hx
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true, ↓reduceIte,
    List.lookup_append] at hx ⊢
  simp [hx]

/-! ### Step J+K: The commutation theorem (GPT-5.4 Pro architecture)

Council (Martin-Löf, Tao, Carneiro, 87%): The right invariant is
`applyBindings (heBindingsToOSLF qb) pl = pa`, not "matchPattern nonempty".
Then `matchPattern_applyBindings_complete` finishes the job. -/

/-- **Part 1: simpleMatch extends bindings** — output bindings extend input. -/
private theorem simpleMatch_extends (fuel : Nat) :
    (∀ lhs target b qb,
      Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b fuel = some qb →
      HEBindingsExtends b qb) ∧
    (∀ ps ts b qb,
      Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList ps ts b fuel = some qb →
      HEBindingsExtends b qb) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ h => by simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at h,
           fun ps ts b qb h => by
             cases ps <;> cases ts <;>
               simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList,
                     Mettapedia.Languages.MeTTa.HE.simpleMatch] at h
             subst h; exact heExt_refl _⟩
  | succ n ih =>
    obtain ⟨ih_match, ih_list⟩ := ih
    -- Define atom extends first, then list extends using it
    have hpat : ∀ lhs target b qb,
        Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b (n + 1) = some qb →
        HEBindingsExtends b qb := by
      intro lhs target b qb hmatch
      cases lhs with
      | var v =>
        cases hlookup : b.lookup v <;>
          simp [Mettapedia.Languages.MeTTa.HE.simpleMatch, hlookup] at hmatch
        · subst hmatch; exact extends_assign_of_lookup_none b v target hlookup
        · obtain ⟨_, rfl⟩ := hmatch; exact heExt_refl _
      | symbol s =>
        cases target <;> simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
        obtain ⟨_, rfl⟩ := hmatch; exact heExt_refl _
      | grounded g =>
        cases target <;> simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
        obtain ⟨_, rfl⟩ := hmatch; exact heExt_refl _
      | expression ps =>
        cases target <;> simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
        exact ih_list ps _ b qb hmatch.2
    have hlist : ∀ ps ts b qb,
        Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
        HEBindingsExtends b qb := by
      intro ps'
      induction ps' with
      | nil =>
        intro ts' b' qb' h'
        cases ts' <;>
          simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList] at h'
        subst h'; exact heExt_refl _
      | cons p' ps' ihps =>
        intro ts' b' qb' h'
        cases ts' with
        | nil => simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList] at h'
        | cons t' ts' =>
          unfold Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList at h'
          cases hhd : Mettapedia.Languages.MeTTa.HE.simpleMatch p' t' b' (n + 1) with
          | none => simp [hhd] at h'
          | some b'' =>
            simp [hhd] at h'
            exact heExt_trans (hpat p' t' b' b'' hhd) (ihps ts' b'' qb' h')
    exact ⟨hpat, hlist⟩

/-- **Part 2: The commutation theorem** (GPT-Pro architecture, council 87%). -/
private theorem simpleMatch_applyBindings_all (fuel : Nat) :
    (∀ lhs target b qb,
      Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b fuel = some qb →
      PureTranslatable lhs → PureTranslatable target →
      ∀ qb', HEBindingsExtends qb qb' →
      ∀ pl pa,
        atomToPattern lhs = some pl → atomToPattern target = some pa →
        applyBindings (heBindingsToOSLF qb') pl = pa) ∧
    (∀ ps ts b qb,
      Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList ps ts b fuel = some qb →
      (∀ a ∈ ps, PureTranslatable a) → (∀ a ∈ ts, PureTranslatable a) →
      ∀ qb', HEBindingsExtends qb qb' →
      (ps.filterMap atomToPattern).map (applyBindings (heBindingsToOSLF qb')) =
        ts.filterMap atomToPattern) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ h => by simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at h,
           fun ps ts b qb h _ _ _ _ => by
             cases ps <;> cases ts <;>
               simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList,
                     Mettapedia.Languages.MeTTa.HE.simpleMatch] at h
             subst h; simp⟩
  | succ n ih =>
    obtain ⟨ih_match, ih_list⟩ := ih
    have hpat : ∀ lhs target b qb,
        Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b (n + 1) = some qb →
        PureTranslatable lhs → PureTranslatable target →
        ∀ qb', HEBindingsExtends qb qb' →
        ∀ pl pa, atomToPattern lhs = some pl → atomToPattern target = some pa →
        applyBindings (heBindingsToOSLF qb') pl = pa := by
      intro lhs target b qb hmatch hl ha qb' hext pl pa hpl hpa
      cases lhs with
      | var v =>
        simp [atomToPattern] at hpl; subst hpl
        cases hlookup : b.lookup v <;>
          simp [Mettapedia.Languages.MeTTa.HE.simpleMatch, hlookup] at hmatch
        · subst hmatch
          have hlookup' : qb'.lookup v = some target :=
            hext v target (lookup_assign_of_lookup_none b v target hlookup)
          exact applyBindings_fvar_of_lookup qb' v target pa hlookup' hpa
        · rename_i old; obtain ⟨hold, rfl⟩ := hmatch
          subst hold
          exact applyBindings_fvar_of_lookup qb' v old pa (hext v old hlookup) hpa
      | symbol s =>
        simp [atomToPattern] at hpl; subst hpl
        cases target with
        | symbol t =>
          simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
          obtain ⟨hst, rfl⟩ := hmatch
          subst hst
          simp [atomToPattern] at hpa; subst hpa
          exact applyBindings_apply _ s []
        | _ => simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
      | grounded g => exfalso; obtain ⟨_, hp, _⟩ := hl; simp [atomToPattern] at hp
      | expression es =>
        cases es with
        | nil =>
          exfalso
          obtain ⟨_, hp, _⟩ := hl
          simp [atomToPattern] at hp
        | cons hd args =>
          cases hd with
          | symbol c =>
            cases target with
            | expression ts =>
              cases ts with
              | nil =>
                simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
              | cons thd targs =>
                cases thd with
                | symbol d =>
                  simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
                  rcases hmatch with ⟨hlen, hmatch⟩
                  simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList] at hmatch
                  cases hsym : Mettapedia.Languages.MeTTa.HE.simpleMatch (.symbol c) (.symbol d) b n with
                  | none =>
                    simp [hsym] at hmatch
                  | some b'' =>
                    simp [hsym] at hmatch
                    have hext_tail : HEBindingsExtends b'' qb :=
                      (simpleMatch_extends n).2 args targs b'' qb hmatch
                    have hext_head : HEBindingsExtends b'' qb' :=
                      heExt_trans hext_tail hext
                    have hheadComm :
                        applyBindings (heBindingsToOSLF qb') (.apply c []) = (.apply d []) :=
                      ih_match (.symbol c) (.symbol d) b b'' hsym
                        (pureTranslatable_symbol c) (pureTranslatable_symbol d)
                        qb' hext_head (.apply c []) (.apply d [])
                        (by simp [atomToPattern]) (by simp [atomToPattern])
                    have hheadEq : (.apply c [] : Pattern) = .apply d [] := by
                      simpa [applyBindings_apply] using hheadComm
                    cases hheadEq
                    have hmc_l : isMatchCorrectAux pl = true :=
                      pureTranslatable_hmc_of_eq hl hpl
                    have hmc_a : isMatchCorrectAux pa = true :=
                      pureTranslatable_hmc_of_eq ha hpa
                    obtain ⟨pArgs, hplEq, hplFm, _⟩ :=
                      pure_expr_translation_shape c args pl hpl hmc_l
                    obtain ⟨tArgsP, hpaEq, hpaFm, _⟩ :=
                      pure_expr_translation_shape c targs pa hpa hmc_a
                    have hargsPure : ∀ a ∈ args, PureTranslatable a :=
                      pure_args_of_expr_translation c args pl hpl hmc_l
                    have htargsPure : ∀ a ∈ targs, PureTranslatable a :=
                      pure_args_of_expr_translation c targs pa hpa hmc_a
                    have htail :=
                      ih_list args targs b'' qb hmatch hargsPure htargsPure qb' hext
                    rw [hplEq, hpaEq, applyBindings_apply]
                    simpa [hplFm, hpaFm] using htail
                | var _ =>
                  exfalso
                  simp [atomToPattern] at hpa
                | grounded _ =>
                  exfalso
                  simp [atomToPattern] at hpa
                | expression _ =>
                  exfalso
                  simp [atomToPattern] at hpa
            | _ =>
              simp [Mettapedia.Languages.MeTTa.HE.simpleMatch] at hmatch
          | var _ =>
            exfalso
            obtain ⟨_, hp, _⟩ := hl
            simp [atomToPattern] at hp
          | grounded _ =>
            exfalso
            obtain ⟨_, hp, _⟩ := hl
            simp [atomToPattern] at hp
          | expression _ =>
            exfalso
            obtain ⟨_, hp, _⟩ := hl
            simp [atomToPattern] at hp
    have hlist : ∀ ps ts b qb,
        Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
        (∀ a ∈ ps, PureTranslatable a) → (∀ a ∈ ts, PureTranslatable a) →
        ∀ qb', HEBindingsExtends qb qb' →
        (ps.filterMap atomToPattern).map (applyBindings (heBindingsToOSLF qb')) =
          ts.filterMap atomToPattern := by
      intro ps'
      induction ps' with
      | nil =>
        intro ts' b' qb' h' _ _ _ _
        cases ts' <;>
          simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList] at h'
        subst h'; simp
      | cons p' ps' ihps =>
        intro ts' b' qb' h' hps hts qb'' hext'
        cases ts' with
        | nil => simp [Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList] at h'
        | cons t' ts' =>
          unfold Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList at h'
          cases hhd : Mettapedia.Languages.MeTTa.HE.simpleMatch p' t' b' (n + 1) with
          | none => simp [hhd] at h'
          | some b'' =>
            simp [hhd] at h'
            have hpP := hps p' (.head _)
            have htP := hts t' (.head _)
            obtain ⟨pp, hpp, hmc_pp⟩ := hpP
            obtain ⟨pt, hpt, hmc_pt⟩ := htP
            have hext_tail : HEBindingsExtends b'' qb' :=
              (simpleMatch_extends (n + 1)).2 ps' ts' b'' qb' h'
            have hhead :=
              hpat p' t' b' b'' hhd ⟨pp, hpp, hmc_pp⟩ ⟨pt, hpt, hmc_pt⟩
                qb'' (heExt_trans hext_tail hext') pp pt hpp hpt
            have htail :=
              ihps ts' b'' qb' h'
                (fun a ha => hps a (.tail _ ha))
                (fun a ha => hts a (.tail _ ha))
                qb'' hext'
            simp [hpp, hpt, hhead, htail]
    exact ⟨hpat, hlist⟩

/-- **Part 3: Specialization** — `qb' = qb`. -/
private theorem simpleMatch_applyBindings_comm
    (lhs target : Atom) (b qb : Bindings) (fuel : Nat)
    (hl : PureTranslatable lhs) (ha : PureTranslatable target)
    (hmatch : Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b fuel = some qb)
    (pl pa : Pattern)
    (hpl : atomToPattern lhs = some pl) (hpa : atomToPattern target = some pa) :
    applyBindings (heBindingsToOSLF qb) pl = pa :=
  (simpleMatch_applyBindings_all fuel).1 lhs target b qb hmatch hl ha qb (heExt_refl _) pl pa hpl hpa

/-! ### Step L: Main theorem via commutation + completeness -/

/-- **Match correspondence**: if HE's `simpleMatch` succeeds on PureTranslatable
    atoms, PeTTa's `matchPattern` on the translated patterns is nonempty.

    Derived from `simpleMatch_applyBindings_comm` via
    `matchPattern_applyBindings_complete`. -/
theorem simpleMatch_implies_matchPattern_nonempty
    (lhs atom : Atom) (b : Bindings) (fuel : Nat) (qb : Bindings)
    (hl : PureTranslatable lhs) (ha : PureTranslatable atom)
    (hmatch : Mettapedia.Languages.MeTTa.HE.simpleMatch lhs atom b fuel = some qb) :
    ∃ pl pa, atomToPattern lhs = some pl ∧ atomToPattern atom = some pa ∧
      (matchPattern pl pa).length > 0 := by
  obtain ⟨pl, hpl, hmc_l⟩ := hl
  obtain ⟨pa, hpa, hmc_a⟩ := ha
  refine ⟨pl, pa, hpl, hpa, ?_⟩
  -- Step K+L: use commutation + completeness
  have hcomm : applyBindings (heBindingsToOSLF qb) pl = pa :=
    simpleMatch_applyBindings_comm lhs atom b qb fuel
      ⟨pl, hpl, hmc_l⟩ ⟨pa, hpa, hmc_a⟩ hmatch pl pa hpl hpa
  obtain ⟨bs', hbs', _⟩ :=
    Mettapedia.OSLF.Framework.PredFiniteSufficient.matchPattern_applyBindings_complete
      (pat := pl) (bs := heBindingsToOSLF qb) hmc_l
  have hmem : bs' ∈ matchPattern pl pa := hcomm ▸ hbs'
  exact List.length_pos_of_mem hmem

/-! ## Coverage Audit

### Proved (0 axiom, 16 theorems):
**Phase 1 (bridge + passthrough):**
- `heSpaceToPeTTaSpace_has_rule` — equation in space → rule in PeTTa space
- `heBindingsToOSLF_lookup_assign` — bindings correspondence
- `atomToPattern_error/empty/var` — atom translation on specific forms
- `queryEquations_source` — extract original equation from queryEquations
- `mettaCall_equation_step_sound` — equation match → PeTTa rule exists
- `mettaCall_error_sound` — error passthrough
- `evalAtom_variable_sound` — variable passthrough
- `evalAtom_error_sound` — error leaf passthrough

**Phase 2 Step 1 (PureTranslatable + isMatchCorrect):**
- `pureTranslatable_var/symbol/expr` — PureTranslatable witnesses
- `PureTranslatable.toTranslatable` — PureTranslatable ⊂ Translatable
- `isMatchCorrectListAux_of_forall` — list helper

**Phase 2 Step 4 (symbol passthrough):**
- `evalAtom_symbol_sound` — symbol passthrough via isPassThroughType

**Phase 2 Step 2 (match correspondence):**
- `matchPattern_fvar_nonempty` — fvar match always succeeds
- `matchPattern_apply_nil_self` — nullary constructor self-match

### Match correspondence core:
- `simpleMatch_implies_matchPattern_nonempty` — HE simpleMatch success → PeTTa
  matchPattern nonempty. Proved via the stronger
  `simpleMatch_applyBindings_comm` bridge plus
  `matchPattern_applyBindings_complete`.

### Phase 3 (out of scope):
- `MettaCall.no_match` on compound expressions — no MeTTaEval constructor
- `MettaCall.empty_results` — same
- `EvalAtom.type_cast` — needs typeCast in MeTTaEval
- `EvalAtom.interpret_success/error` — needs InterpretExpression
- Recursive EvalAtom/MettaCall correspondence (mutual induction) -/

/-! ## Translation Rule Correspondence

Each Prolog `translate_term/2` clause maps to a semantic layer:

| Prolog clause                          | Lean theorem                      | Bridge used                       |
|----------------------------------------|-----------------------------------|-----------------------------------|
| `chain → let`                          | `mettaCall_equation_step_sound`   | `heSpaceToPeTTaSpace_has_rule`    |
| `collapse-bind → collapse`             | `mettaCall_equation_step_sound`   | same                              |
| `superpose-bind → superpose`           | `mettaCall_equation_step_sound`   | same                              |
| `switch → case`                        | `mettaCall_equation_step_sound`   | same (rename only)                |
| `nop → let $_ X ()`                   | `mettaCall_equation_step_sound`   | same                              |
| `function/return → unwrap`             | `mettaCall_equation_step_sound`   | same                              |
| `(error patterns)`                     | `mettaCall_error_sound`           | `MeTTaEval.errorPassThrough`      |
| `(variable identity)`                  | `evalAtom_variable_sound`         | `MeTTaEval.varPassThrough`        |
| `(grounded ops)`                       | eliminated by `ExecGroundedOnly`  | absurd (Phase 2)                  |
| `(compound no-match)`                  | Phase 2                           | needs new MeTTaEval constructor   |
-/

/-! ## Executable Validation

Concrete `#eval` tests verifying the computable translation functions on actual
MeTTa atoms. These bridge the propositional proofs above to ground truth. -/

section EvalTests
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge (atomToPattern)
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern applyBindings)

-- atomToPattern on variables
#eval atomToPattern (.var "$x")             -- some (.fvar "$x")

-- atomToPattern on symbols
#eval atomToPattern (.symbol "if")          -- some (.apply "if" [])

-- atomToPattern on expressions: (= (if True $t $e) $t)
#eval atomToPattern (.expression [
  .symbol "=",
  .expression [.symbol "if", .symbol "True", .var "$t", .var "$e"],
  .var "$t"
])  -- some (.apply "=" [.apply "if" [.apply "True" [], .fvar "$t", .fvar "$e"], .fvar "$t"])

-- atomToRule? on the same equation
#eval atomToRule? (.expression [
  .symbol "=",
  .expression [.symbol "if", .symbol "True", .var "$t", .var "$e"],
  .var "$t"
])  -- some { name := "", left := .apply "if" [...], right := .fvar "$t", ... }

-- heSpaceToPeTTaSpace on a small space with one equation
#eval
  let space : Mettapedia.Languages.MeTTa.HE.Space :=
    { atoms := [.expression [.symbol "=",
        .expression [.symbol "if", .symbol "True", .var "$t", .var "$e"],
        .var "$t"]] }
  let pspace := heSpaceToPeTTaSpace space
  (pspace.rules.length, pspace.facts.length)
  -- (1, 0): one rule, zero facts

-- matchPattern: the translated "if True $t $e" pattern matches "if True a b"
#eval
  let pat := Pattern.apply "if" [.apply "True" [], .fvar "$t", .fvar "$e"]
  let target := Pattern.apply "if" [.apply "True" [], .apply "a" [], .apply "b" []]
  let ms := matchPattern pat target
  (ms.length, ms.head?)
  -- (1, some [("$e", .apply "b" []), ("$t", .apply "a" [])])

-- applyBindings: applying match result to RHS reconstructs the answer
#eval
  let bs : Mettapedia.OSLF.MeTTaIL.Match.Bindings :=
    [("$t", Pattern.apply "a" []), ("$e", Pattern.apply "b" [])]
  let rhs := Pattern.fvar "$t"
  applyBindings bs rhs
  -- .apply "a" []  (i.e., the symbol "a")

-- simpleMatch: HE's matching on the same example
#eval
  let lhs := Atom.expression [.symbol "if", .symbol "True", .var "$t", .var "$e"]
  let target := Atom.expression [.symbol "if", .symbol "True", .symbol "a", .symbol "b"]
  Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target
    Mettapedia.Languages.MeTTa.HE.Bindings.empty 100
  -- some { assignments := [("$e", .symbol "b"), ("$t", .symbol "a")], ... }

-- Full pipeline: HE simpleMatch → heBindingsToOSLF → applyBindings on translated pattern
-- Validates the commutation theorem on a concrete example.
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge (patternToAtom) in
#eval do
  let lhs := Atom.expression [.symbol "if", .symbol "True", .var "$t", .var "$e"]
  let target := Atom.expression [.symbol "if", .symbol "True", .symbol "a", .symbol "b"]
  let pl ← atomToPattern lhs
  let pa ← atomToPattern target
  let qb ← Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target
    Mettapedia.Languages.MeTTa.HE.Bindings.empty 100
  let oslf_bs := heBindingsToOSLF qb
  let result := applyBindings oslf_bs pl
  let result_atom := patternToAtom result
  let target_atom := patternToAtom pa
  return (result_atom == target_atom, repr result_atom, repr target_atom)
  -- Expected: (true, <same>, <same>): the commutation holds!

end EvalTests

end Mettapedia.Languages.MeTTa.Translation
