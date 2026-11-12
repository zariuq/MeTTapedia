import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaNativeLoweringContracts
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance
import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.Properties
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.Framework.PredFiniteSufficient

/-!
# HE and PeTTa source comparisons

`PureConstructor` proves the completed recursive comparison on its explicitly
admitted pure constructor/equation fragment. Its `CodeRel program []` boundary
requires closed materialized child syntax: fixed caller substitutions are not
an authority for arbitrary open sibling evaluation. Defined-call misses,
marker/error propagation, typing, effects and search policies retain their
separate source-level admissions and discriminators.

`OpenContinuation` transports successful tuple and typed-argument spines using
independent HE child derivations and actual retained PeTTa source paths. One
joint packet contains the evaluated prefix, unevaluated siblings and pending
caller observations; every completed prefix is interpreted in the final tail
frame. Per-occurrence continuation manifests preserve the supplied HE occurrences.
Their local child certificates do not assert complete recursive PeTTa search
coverage, so this transport is not whole-program open-query equivalence.

The shared E1/E2 comparison is a first-order Atom fragment. Its open recursive
admission requires a passive environment so variable lookup cannot introduce
an active call. It neither defines MeTTa nor bounds HO MeTTa Prime.

The earlier matcher-level section remains historical: equation membership,
leaf delivery and error passthrough are intentionally narrower than completed
recursive evaluation. `MeTTaEval` there is not substituted for either dialect's
independent recursive source judgment.
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

An unrestricted host dispatch may classify a symbolic head as executable.
The no-grounded fragment therefore needs this explicit dispatch condition. -/

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

/-! ## MettaCall error soundness -/

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

/-! ## EvalAtom leaf soundness

The historical relation below represents variable and error leaves. -/

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

/-! ## MettaCall equation-step soundness

Equation matching and recursive body evaluation are separate semantic claims.

The proof relies on a match correspondence lemma connecting HE's `simpleMatch`
(operating on `Atom`) to PeTTa's `matchPattern` (operating on `Pattern`).
The structural matching correspondence is proved below. -/

/-- Extract the original equation from `queryEquations` membership.
    If `queryEquations` returns `(rhs', b)`, then there exists an indexed raw
    equation `(= lhs_orig rhs_orig)` in `space.atoms` from which it was derived. -/
theorem queryEquations_source (space : Space) (atom : Atom) (fuel : Nat)
    (rhs' : Atom) (qb : Bindings)
    (h : (rhs', qb) ∈ Mettapedia.Languages.MeTTa.HE.queryEquations space atom fuel) :
    ∃ lhs_orig rhs_orig idx,
      (Atom.expression [.symbol "=", lhs_orig, rhs_orig], idx) ∈ space.atoms.zipIdx := by
  cases fuel with
  | zero =>
      simp [Mettapedia.Languages.MeTTa.HE.queryEquations] at h
  | succ n =>
      rcases List.mem_flatMap.mp h with ⟨eqidx, heqidx, hout⟩
      rcases eqidx with ⟨eq, idx⟩
      cases eq with
      | symbol s =>
          simp at hout
      | var v =>
          simp at hout
      | grounded g =>
          simp at hout
      | expression es =>
          cases es with
          | nil =>
              simp at hout
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hout
                    | cons lhs_orig tl1 =>
                        cases tl1 with
                        | nil =>
                            simp at hout
                        | cons rhs_orig tl2 =>
                            cases tl2 with
                            | nil =>
                                exact ⟨lhs_orig, rhs_orig, idx, by simpa using heqidx⟩
                            | cons extra tl3 =>
                                simp at hout
                  · simp [hs] at hout
              | var v =>
                  simp at hout
              | grounded g =>
                  simp at hout
              | expression es' =>
                  simp at hout

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
  obtain ⟨lhs_orig, rhs_orig, idx, hmem⟩ := queryEquations_source space atom fuel rhs' queryBindings h_query
  have hmem_atoms : .expression [.symbol "=", lhs_orig, rhs_orig] ∈ space.atoms := by
    have ⟨_, hlt, heq⟩ := List.mem_zipIdx hmem
    simp at hlt
    exact heq ▸ List.getElem_mem hlt
  exact ⟨lhs_orig, rhs_orig, hmem_atoms, fun hl hr =>
    heSpaceToPeTTaSpace_has_rule space lhs_orig rhs_orig hl hr hmem_atoms⟩

/-! ## Phase 2, Step 1: TwoSortTranslatable + isMatchCorrect

`atomToPattern` can produce `.lambda`/`.subst` patterns (from `"λ"`/`"subst"` head
symbols), which are NOT `isMatchCorrect`. Standard MeTTa equations never use these.
`TwoSortTranslatable` refines `Translatable` to guarantee `isMatchCorrect`. -/

/-- An atom translates to an `isMatchCorrect` pattern: no `.lambda`, `.subst`,
    or `.collection` nodes in the output. Covers all standard MeTTa atoms. -/
def TwoSortTranslatable (a : Atom) : Prop :=
  ∃ p, atomToPattern a = some p ∧ isMatchCorrectAux p = true

theorem pureTranslatable_var (v : String) : TwoSortTranslatable (.var v) :=
  ⟨.fvar v, by simp [atomToPattern], rfl⟩

theorem pureTranslatable_symbol (s : String) : TwoSortTranslatable (.symbol s) :=
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
    `isMatchCorrect` patterns when all arguments are `TwoSortTranslatable`. -/
theorem pureTranslatable_expr (c : String) (args : List Atom)
    (hc_not_lam : c ≠ "λ") (hc_not_subst : c ≠ "subst")
    (hargs : ∀ a ∈ args, TwoSortTranslatable a) :
    TwoSortTranslatable (.expression (.symbol c :: args)) := by
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

/-- `TwoSortTranslatable` implies `Translatable`. -/
theorem TwoSortTranslatable.toTranslatable {a : Atom} (h : TwoSortTranslatable a) :
    Translatable a := by
  obtain ⟨p, hp, _⟩ := h
  simp [Translatable, hp]

/-! ## Append-suffix head-pattern extension boundary

This mirrors the narrow operational translator extension used for successful
append-suffix function-head lowering.  The key architectural fact is:

- the base recovered-tail helper application stays in the current
  `TwoSortTranslatable` fragment
- the recursive structural `case` step does not, because the branch pattern is
  encoded as a raw non-symbol-headed atom rather than an OSLF `Pattern`
-/

/-- Proof-oriented builder for the append-suffix head-pattern extension.

Positive example: when `prefixElems = []`, this produces the recovered-tail
base case `let tailVar actual (__tr-raw-apply1 tailVar applyArg)`.

Negative example: when `prefixElems` is nonempty, the generated `case` branch
used to leave the bridge. The current shape instead binds the deconstruction
result to a fresh variable and peels it through symbol-headed helper interfaces
(`first-from-pair`, `second-from-pair`). -/
def appendSuffixHeadBinder : Atom → Atom
  | .var v => .var (v ++ "_head")
  | _ => .var "$__tr_head_elem"

def buildAppendSuffixHeadExtension
    (prefixElems : List Atom) (actual : Atom)
    (binders : List (Atom × Atom)) (tailVar applyArg : Atom) : Atom :=
  match prefixElems with
  | List.nil =>
      Atom.expression
        [Atom.symbol "let",
         tailVar,
         actual,
         Atom.expression [Atom.symbol "__tr-raw-apply1", tailVar, applyArg]]
  | List.cons prefixAtom rest =>
      match binders with
      | List.cons binder binders' =>
          let pairVar := binder.1
          let tailExpr := binder.2
          let headVar := appendSuffixHeadBinder pairVar
          let tailBind := Atom.var (match tailExpr with | .var v => v | _ => "$__tr_head_tail")
          Atom.expression
            [Atom.symbol "chain",
             Atom.expression [Atom.symbol "decons-atom", actual],
             pairVar,
             Atom.expression
               [Atom.symbol "let",
                headVar,
                Atom.expression [Atom.symbol "first-from-pair", pairVar],
                Atom.expression
                  [Atom.symbol "let",
                   tailBind,
                   Atom.expression [Atom.symbol "second-from-pair", pairVar],
                   Atom.expression
                     [Atom.symbol "unify",
                      headVar,
                      prefixAtom,
                      buildAppendSuffixHeadExtension rest tailBind binders' tailVar applyArg,
                      Atom.symbol "Empty"]]]]
      | List.nil => Atom.symbol "Empty"

/-- The recovered-tail base case stays in the current pure bridge fragment. -/
theorem buildAppendSuffixHeadExtension_nil_pureTranslatable
    (actual tailVar applyArg : Atom)
    (hactual : TwoSortTranslatable actual)
    (htail : TwoSortTranslatable tailVar)
    (harg : TwoSortTranslatable applyArg) :
    TwoSortTranslatable (buildAppendSuffixHeadExtension [] actual [] tailVar applyArg) := by
  simp [buildAppendSuffixHeadExtension]
  have happ : TwoSortTranslatable
      (.expression [.symbol "__tr-raw-apply1", tailVar, applyArg]) := by
    exact pureTranslatable_expr "__tr-raw-apply1" [tailVar, applyArg]
      (by simp) (by simp)
      (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl
        · exact htail
        · exact harg)
  exact pureTranslatable_expr "let"
    [tailVar, actual, .expression [.symbol "__tr-raw-apply1", tailVar, applyArg]]
    (by simp) (by simp)
    (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · exact htail
      · exact hactual
      · exact happ)

/-- A structural append-suffix cons step stays in the pure bridge fragment as
long as its prefix atom and recursive tail stay there. This removes the old
raw-pair obstruction from the extension itself. -/
theorem buildAppendSuffixHeadExtension_cons_pureTranslatable
    (prefixAtom : Atom) (rest : List Atom) (actual : Atom)
    (pairName tailName : String) (binders : List (Atom × Atom))
    (tailVar applyArg : Atom)
    (hprefix : TwoSortTranslatable prefixAtom)
    (hactual : TwoSortTranslatable actual)
    (_htailVar : TwoSortTranslatable tailVar)
    (_harg : TwoSortTranslatable applyArg)
    (hinner : TwoSortTranslatable
      (buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg)) :
    TwoSortTranslatable
      (buildAppendSuffixHeadExtension (List.cons prefixAtom rest) actual
        (List.cons (.var pairName, .var tailName) binders) tailVar applyArg) := by
  simp [buildAppendSuffixHeadExtension, appendSuffixHeadBinder]
  have hpair : TwoSortTranslatable (.var pairName) := pureTranslatable_var pairName
  have hhead : TwoSortTranslatable (appendSuffixHeadBinder (.var pairName)) := by
    simp [appendSuffixHeadBinder, pureTranslatable_var]
  have htail : TwoSortTranslatable (.var tailName) := pureTranslatable_var tailName
  have hdecons : TwoSortTranslatable (.expression [.symbol "decons-atom", actual]) := by
    exact pureTranslatable_expr "decons-atom" [actual]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact hactual)
  have hfirst : TwoSortTranslatable (.expression [.symbol "first-from-pair", .var pairName]) := by
    exact pureTranslatable_expr "first-from-pair" [.var pairName]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact hpair)
  have hsecond : TwoSortTranslatable (.expression [.symbol "second-from-pair", .var pairName]) := by
    exact pureTranslatable_expr "second-from-pair" [.var pairName]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact hpair)
  have hempty : TwoSortTranslatable (.symbol "Empty") := pureTranslatable_symbol "Empty"
  have hunify : TwoSortTranslatable
      (.expression
        [.symbol "unify",
          appendSuffixHeadBinder (.var pairName),
          prefixAtom,
          buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
          .symbol "Empty"]) := by
    exact pureTranslatable_expr "unify"
      [appendSuffixHeadBinder (.var pairName),
        prefixAtom,
        buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
        .symbol "Empty"]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hhead
        · exact hprefix
        · exact hinner
        · exact hempty)
  have hletTail : TwoSortTranslatable
      (.expression
        [.symbol "let",
          .var tailName,
          .expression [.symbol "second-from-pair", .var pairName],
          .expression
            [.symbol "unify",
              appendSuffixHeadBinder (.var pairName),
              prefixAtom,
              buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
              .symbol "Empty"]]) := by
    exact pureTranslatable_expr "let"
      [.var tailName,
        .expression [.symbol "second-from-pair", .var pairName],
        .expression
          [.symbol "unify",
            appendSuffixHeadBinder (.var pairName),
            prefixAtom,
            buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
            .symbol "Empty"]]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl | rfl
        · exact htail
        · exact hsecond
        · exact hunify)
  have hletHead : TwoSortTranslatable
      (.expression
        [.symbol "let",
          appendSuffixHeadBinder (.var pairName),
          .expression [.symbol "first-from-pair", .var pairName],
          .expression
            [.symbol "let",
              .var tailName,
              .expression [.symbol "second-from-pair", .var pairName],
              .expression
                [.symbol "unify",
                  appendSuffixHeadBinder (.var pairName),
                  prefixAtom,
                  buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
                  .symbol "Empty"]]]) := by
    exact pureTranslatable_expr "let"
      [appendSuffixHeadBinder (.var pairName),
        .expression [.symbol "first-from-pair", .var pairName],
        .expression
          [.symbol "let",
            .var tailName,
            .expression [.symbol "second-from-pair", .var pairName],
            .expression
              [.symbol "unify",
                appendSuffixHeadBinder (.var pairName),
                prefixAtom,
                buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
                .symbol "Empty"]]]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl | rfl
        · exact hhead
        · exact hfirst
        · exact hletTail)
  exact pureTranslatable_expr "chain"
    [.expression [.symbol "decons-atom", actual],
      .var pairName,
      .expression
        [.symbol "let",
          appendSuffixHeadBinder (.var pairName),
          .expression [.symbol "first-from-pair", .var pairName],
          .expression
            [.symbol "let",
              .var tailName,
              .expression [.symbol "second-from-pair", .var pairName],
              .expression
                [.symbol "unify",
                  appendSuffixHeadBinder (.var pairName),
                  prefixAtom,
                  buildAppendSuffixHeadExtension rest (.var tailName) binders tailVar applyArg,
                  .symbol "Empty"]]]]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · exact hdecons
      · exact hpair
      · exact hletHead)

/-! ## Append-suffix let-pattern extension boundary

This mirrors the narrow operational translator extension used for structural
function-call inversion under PeTTa `let`-patterns once the body has already been
rawified into explicit HE helper interfaces.
-/

/-- Proof-oriented builder for the append-suffix `let`-pattern extension. -/
def buildAppendSuffixLetExtension
    (prefixElems : List Atom) (actual : Atom)
    (binders : List (Atom × Atom)) (tailVar translatedBody : Atom) : Atom :=
  match prefixElems with
  | List.nil =>
      Atom.expression
        [Atom.symbol "let",
         tailVar,
         actual,
         translatedBody]
  | List.cons prefixAtom rest =>
      match binders with
      | List.cons binder binders' =>
          let pairVar := binder.1
          let tailExpr := binder.2
          let headVar := appendSuffixHeadBinder pairVar
          let tailBind := Atom.var (match tailExpr with | .var v => v | _ => "$__tr_head_tail")
          Atom.expression
            [Atom.symbol "chain",
             Atom.expression [Atom.symbol "decons-atom", actual],
             pairVar,
             Atom.expression
               [Atom.symbol "let",
                headVar,
                Atom.expression [Atom.symbol "first-from-pair", pairVar],
                Atom.expression
                  [Atom.symbol "let",
                   tailBind,
                   Atom.expression [Atom.symbol "second-from-pair", pairVar],
                   Atom.expression
                     [Atom.symbol "unify",
                      headVar,
                      prefixAtom,
                      buildAppendSuffixLetExtension rest tailBind binders' tailVar translatedBody,
                      Atom.symbol "Empty"]]]]
      | List.nil => Atom.symbol "Empty"

/-- The recovered-tail base case for structural `let`-pattern inversion stays
in the current pure bridge fragment when the translated body does. -/
theorem buildAppendSuffixLetExtension_nil_pureTranslatable
    (actual tailVar translatedBody : Atom)
    (hactual : TwoSortTranslatable actual)
    (htail : TwoSortTranslatable tailVar)
    (hbody : TwoSortTranslatable translatedBody) :
    TwoSortTranslatable (buildAppendSuffixLetExtension [] actual [] tailVar translatedBody) := by
  simp [buildAppendSuffixLetExtension]
  exact pureTranslatable_expr "let"
    [tailVar, actual, translatedBody]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · exact htail
      · exact hactual
      · exact hbody)

/-- A structural append-suffix `let`-pattern cons step stays in the pure bridge
fragment as long as its prefix atom and recursive tail stay there. -/
theorem buildAppendSuffixLetExtension_cons_pureTranslatable
    (prefixAtom : Atom) (rest : List Atom) (actual : Atom)
    (pairName tailName : String) (binders : List (Atom × Atom))
    (tailVar translatedBody : Atom)
    (hprefix : TwoSortTranslatable prefixAtom)
    (hactual : TwoSortTranslatable actual)
    (_htailVar : TwoSortTranslatable tailVar)
    (_hbody : TwoSortTranslatable translatedBody)
    (hinner : TwoSortTranslatable
      (buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody)) :
    TwoSortTranslatable
      (buildAppendSuffixLetExtension (List.cons prefixAtom rest) actual
        (List.cons (.var pairName, .var tailName) binders) tailVar translatedBody) := by
  simp [buildAppendSuffixLetExtension, appendSuffixHeadBinder]
  have hpair : TwoSortTranslatable (.var pairName) := pureTranslatable_var pairName
  have hhead : TwoSortTranslatable (appendSuffixHeadBinder (.var pairName)) := by
    simp [appendSuffixHeadBinder, pureTranslatable_var]
  have htail : TwoSortTranslatable (.var tailName) := pureTranslatable_var tailName
  have hdecons : TwoSortTranslatable (.expression [.symbol "decons-atom", actual]) := by
    exact pureTranslatable_expr "decons-atom" [actual]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact hactual)
  have hfirst : TwoSortTranslatable (.expression [.symbol "first-from-pair", .var pairName]) := by
    exact pureTranslatable_expr "first-from-pair" [.var pairName]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact hpair)
  have hsecond : TwoSortTranslatable (.expression [.symbol "second-from-pair", .var pairName]) := by
    exact pureTranslatable_expr "second-from-pair" [.var pairName]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact hpair)
  have hempty : TwoSortTranslatable (.symbol "Empty") := pureTranslatable_symbol "Empty"
  have hunify : TwoSortTranslatable
      (.expression
        [.symbol "unify",
          appendSuffixHeadBinder (.var pairName),
          prefixAtom,
          buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
          .symbol "Empty"]) := by
    exact pureTranslatable_expr "unify"
      [appendSuffixHeadBinder (.var pairName),
        prefixAtom,
        buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
        .symbol "Empty"]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hhead
        · exact hprefix
        · exact hinner
        · exact hempty)
  have hletTail : TwoSortTranslatable
      (.expression
        [.symbol "let",
          .var tailName,
          .expression [.symbol "second-from-pair", .var pairName],
          .expression
            [.symbol "unify",
              appendSuffixHeadBinder (.var pairName),
              prefixAtom,
              buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
              .symbol "Empty"]]) := by
    exact pureTranslatable_expr "let"
      [.var tailName,
        .expression [.symbol "second-from-pair", .var pairName],
        .expression
          [.symbol "unify",
            appendSuffixHeadBinder (.var pairName),
            prefixAtom,
            buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
            .symbol "Empty"]]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl | rfl
        · exact htail
        · exact hsecond
        · exact hunify)
  have hletHead : TwoSortTranslatable
      (.expression
        [.symbol "let",
          appendSuffixHeadBinder (.var pairName),
          .expression [.symbol "first-from-pair", .var pairName],
          .expression
            [.symbol "let",
              .var tailName,
              .expression [.symbol "second-from-pair", .var pairName],
              .expression
                [.symbol "unify",
                  appendSuffixHeadBinder (.var pairName),
                  prefixAtom,
                  buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
                  .symbol "Empty"]]]) := by
    exact pureTranslatable_expr "let"
      [appendSuffixHeadBinder (.var pairName),
        .expression [.symbol "first-from-pair", .var pairName],
        .expression
          [.symbol "let",
            .var tailName,
            .expression [.symbol "second-from-pair", .var pairName],
            .expression
              [.symbol "unify",
                appendSuffixHeadBinder (.var pairName),
                prefixAtom,
                buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
                .symbol "Empty"]]]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl | rfl | rfl
        · exact hhead
        · exact hfirst
        · exact hletTail)
  exact pureTranslatable_expr "chain"
    [.expression [.symbol "decons-atom", actual],
      .var pairName,
      .expression
        [.symbol "let",
          appendSuffixHeadBinder (.var pairName),
          .expression [.symbol "first-from-pair", .var pairName],
          .expression
            [.symbol "let",
              .var tailName,
              .expression [.symbol "second-from-pair", .var pairName],
              .expression
                [.symbol "unify",
                  appendSuffixHeadBinder (.var pairName),
                  prefixAtom,
                  buildAppendSuffixLetExtension rest (.var tailName) binders tailVar translatedBody,
                  .symbol "Empty"]]]]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · exact hdecons
      · exact hpair
      · exact hletHead)

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

/-! ## Structural matcher correspondence

The result asserts existence of a PeTTa match, rather than literal equality
of binding records: `simpleMatch` success implies `matchPattern` nonemptiness. -/

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

/-! ## Substitution commutation

The key insight: prove `applyBindings (heBindingsToOSLF qb) pl = pa` (the commutation),
then derive matchPattern nonemptiness via `matchPattern_applyBindings_complete`. -/

/-! ### Step A: HEBindingsExtends — now in BindingComposition.lean

`Bindings.Extends`, `Bindings.extends_refl`, `Bindings.extends_trans`,
`extends_assign_of_lookup_none`, and `simpleMatch_extends` are all
imported from `Mettapedia.Languages.MeTTa.HE.BindingComposition`. -/

private abbrev HEBindingsExtends := Bindings.Extends
private abbrev heExt_refl := Bindings.extends_refl
private abbrev heExt_trans := @Bindings.extends_trans

/-! ### Step B: TwoSortTranslatable isMatchCorrect extraction -/

private theorem pureTranslatable_hmc_of_eq {a : Atom} {p : Pattern}
    (h : TwoSortTranslatable a) (hp : atomToPattern a = some p) :
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

/-- A TwoSortTranslatable expression translates to `.apply c patArgs` with matching length. -/
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

/-- All arguments of a TwoSortTranslatable expression are themselves TwoSortTranslatable. -/
private theorem pure_args_of_expr_translation
    (c : String) (args : List Atom) (p : Pattern)
    (hpat : atomToPattern (.expression (.symbol c :: args)) = some p)
    (hmc : isMatchCorrectAux p = true) :
    ∀ a ∈ args, TwoSortTranslatable a := by
  obtain ⟨patArgs, hpEq, hfm, hlen⟩ := pure_expr_translation_shape c args p hpat hmc
  subst hpEq
  have hlistmc : isMatchCorrectListAux patArgs = true := by
    simpa [isMatchCorrectAux] using hmc
  intro a ha
  have ⟨q, hq⟩ := filterMap_length_eq_length_implies_some atomToPattern args
    (by rwa [← hfm]) a ha
  exact ⟨q, hq, isMatchCorrectAux_of_mem_list hlistmc
    (hfm ▸ List.mem_filterMap.mpr ⟨a, ha, hq⟩)⟩

/-! ### Step H + simpleMatch_extends — now in BindingComposition.lean

All imported: `isBound_false_of_lookup_none`, `lookup_assign_of_lookup_none`,
`extends_assign_of_lookup_none`, `simpleMatch_extends`. -/

/-! ### The commutation theorem

The invariant `applyBindings (heBindingsToOSLF qb) pl = pa` supplies the
premise of `matchPattern_applyBindings_complete`. -/

/-- Substitution commutes with the structural pattern translation. -/
private theorem simpleMatch_applyBindings_all (fuel : Nat) :
    (∀ lhs target b qb,
      Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b fuel = some qb →
      TwoSortTranslatable lhs → TwoSortTranslatable target →
      ∀ qb', HEBindingsExtends qb qb' →
      ∀ pl pa,
        atomToPattern lhs = some pl → atomToPattern target = some pa →
        applyBindings (heBindingsToOSLF qb') pl = pa) ∧
    (∀ ps ts b qb,
      Mettapedia.Languages.MeTTa.HE.simpleMatch.simpleMatchList ps ts b fuel = some qb →
      (∀ a ∈ ps, TwoSortTranslatable a) → (∀ a ∈ ts, TwoSortTranslatable a) →
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
        TwoSortTranslatable lhs → TwoSortTranslatable target →
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
            hext v target (Mettapedia.Languages.MeTTa.HE.lookup_assign_of_lookup_none b v target hlookup)
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
                      (Mettapedia.Languages.MeTTa.HE.simpleMatch_extends n).2 args targs b'' qb hmatch
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
                    have hargsPure : ∀ a ∈ args, TwoSortTranslatable a :=
                      pure_args_of_expr_translation c args pl hpl hmc_l
                    have htargsPure : ∀ a ∈ targs, TwoSortTranslatable a :=
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
        (∀ a ∈ ps, TwoSortTranslatable a) → (∀ a ∈ ts, TwoSortTranslatable a) →
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
              (Mettapedia.Languages.MeTTa.HE.simpleMatch_extends (n + 1)).2 ps' ts' b'' qb' h'
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
    (hl : TwoSortTranslatable lhs) (ha : TwoSortTranslatable target)
    (hmatch : Mettapedia.Languages.MeTTa.HE.simpleMatch lhs target b fuel = some qb)
    (pl pa : Pattern)
    (hpl : atomToPattern lhs = some pl) (hpa : atomToPattern target = some pa) :
    applyBindings (heBindingsToOSLF qb) pl = pa :=
  (simpleMatch_applyBindings_all fuel).1 lhs target b qb hmatch hl ha qb (heExt_refl _) pl pa hpl hpa

/-! ### Step L: Main theorem via commutation + completeness -/

/-- **Match correspondence**: if HE's `simpleMatch` succeeds on TwoSortTranslatable
    atoms, PeTTa's `matchPattern` on the translated patterns is nonempty.

    Derived from `simpleMatch_applyBindings_comm` via
    `matchPattern_applyBindings_complete`. -/
theorem simpleMatch_implies_matchPattern_nonempty
    (lhs atom : Atom) (b : Bindings) (fuel : Nat) (qb : Bindings)
    (hl : TwoSortTranslatable lhs) (ha : TwoSortTranslatable atom)
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

**Phase 2 Step 1 (TwoSortTranslatable + isMatchCorrect):**
- `pureTranslatable_var/symbol/expr` — TwoSortTranslatable witnesses
- `TwoSortTranslatable.toTranslatable` — TwoSortTranslatable ⊂ Translatable
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


/-! ## Complete pure constructor/eager source derivations

The source tree accounts for each argument alternative and every stored clause
position before continuing into its body. It is an inductive finite-completion
judgment, independent of either machine step or runner. The named fragment
excludes primitive/control heads, typed demand, list-view patterns and missing
defined calls. It retains ordinary variables, recursive bodies, duplicate
clauses and arbitrary nesting; no source termination claim follows merely
from the grammar. The dialect connections below must be proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Translation.PureConstructor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi
open PeTTa.SpaceSemantics (Equation Program)

/-- Head admission is a language-level pure-fragment policy. -/
def OrdinaryHead (head : String) : Prop :=
  PeTTa.Eval.ioHead head = false ∧ PeTTa.StdLib.known head = false ∧
    head ∉ ["let","let*","case","if","collapse","superpose","empty","quote","unique","match","eval",
      "evalc","chain","unify","function","return","cons-atom","decons-atom",
      "collapse-bind","superpose-bind","metta","context-space","call-native",
      "switch-minimal","Error","Empty","NotReducible"]

def ConstructorHead (program : Program) (head : String) : Prop :=
  OrdinaryHead head ∧ ∀ equation ∈ program.equations, equation.head ≠ head

def DefinedHead (program : Program) (head : String) : Prop :=
  OrdinaryHead head ∧ ∃ equation ∈ program.equations, equation.head = head

/-- Passive constructor data, with free variables admitted by an explicit
scope. The default empty scope is the existing ground return profile.
Defined names remain passive as bare symbols; an applied constructor head
must have no defining equation. Both return markers remain excluded. -/
inductive Value (program : Program) : Atom → (scope : List String := []) → Prop where
  | symbol {scope : List String} (name : String)
      (nonempty : name ≠ "Empty") (ordinary : name ≠ "NotReducible") :
      Value program (.symbol name) scope
  | variable {name : String} {scope : List String} :
      name ∈ scope → Value program (.var name) scope
  | grounded {scope : List String} (value : GroundedValue) :
      Value program (.grounded value) scope
  | unit {scope : List String} : Value program (.expression []) scope
  | constructor {head : String} {arguments : List Atom} {scope : List String} :
      ConstructorHead program head → (∀ argument ∈ arguments, Value program argument scope) →
      Value program (.expression (.symbol head :: arguments)) scope

/-- A bare name is data even when its applied form has defining equations. -/
theorem OrdinaryHead.symbol_value {program : Program} {head : String} {scope : List String}
    (ordinary : OrdinaryHead head) : Value program (.symbol head) scope :=
  .symbol head (fun same => ordinary.2.2 (by simp [same]))
    (fun same => ordinary.2.2 (by simp [same]))

theorem DefinedHead.not_constructor_value {program : Program} {head : String}
    (defined : DefinedHead program head) (arguments : List Atom) (scope : List String) :
    ¬Value program (.expression (.symbol head :: arguments)) scope := by
  intro value
  cases value with
  | constructor passive _ =>
      obtain ⟨equation,member,headed⟩ := defined.2
      exact passive.2 equation member headed

/-- The physical source position and the local body substitution travel
 together. Equal rows in distinct positions remain distinct work items. -/
abbrev ClauseWork := Nat × MORK.Subst × Atom

/-- Complete clause selection uses the independent structural matcher,
including evidence for every rejected row. -/
inductive ClauseScan (head : String) (values : List Atom) :
    Nat → List Equation → List ClauseWork → Prop where
  | nil (position : Nat) : ClauseScan head values position [] []
  | other {position : Nat} {equation : Equation} {equations : List Equation}
      {selected : List ClauseWork} :
      equation.head ≠ head → ClauseScan head values (position+1) equations selected →
      ClauseScan head values position (equation::equations) selected
  | miss {position : Nat} {equation : Equation} {equations : List Equation}
      {selected : List ClauseWork} :
      equation.head = head →
      "cons" ∉ PeTTa.SpaceSemantics.patternHeads (.expression equation.arguments) →
      (∀ bindings, ¬MORK.MatchAtomRel [] (.expression equation.arguments) (.expression values) bindings) →
      ClauseScan head values (position+1) equations selected →
      ClauseScan head values position (equation::equations) selected
  | hit {position : Nat} {equation : Equation} {equations : List Equation}
      {selected : List ClauseWork} {bindings : MORK.Subst} :
      equation.head = head →
      "cons" ∉ PeTTa.SpaceSemantics.patternHeads (.expression equation.arguments) →
      MORK.MatchAtomRel [] (.expression equation.arguments) (.expression values) bindings →
      ClauseScan head values (position+1) equations selected →
      ClauseScan head values position (equation::equations)
        ((position,bindings,equation.body)::selected)

/-- Pure argument positions are licensed by their enclosing call policy. -/
inductive TargetAllowed : PeTTa.Eval.Target → Prop where
  | data : TargetAllowed .data
  | function {head : String} : OrdinaryHead head → TargetAllowed (.function head)

mutual
/-- Complete finite pure evaluation; its children are source derivations,
not callbacks to an evaluator or predicates over a machine's answer list. -/
inductive Evaluation (program : Program) : MORK.Subst → Atom → List Atom → Type where
  | variable {bindings : MORK.Subst} {name : String} :
      Value program (MORK.applySubst bindings (.var name)) →
      Evaluation program bindings (.var name) [MORK.applySubst bindings (.var name)]
  | symbol {bindings : MORK.Subst} {name : String} :
      Value program (.symbol name) → Evaluation program bindings (.symbol name) [.symbol name]
  | grounded {bindings : MORK.Subst} (value : GroundedValue) :
      Evaluation program bindings (.grounded value) [.grounded value]
  | unit {bindings : MORK.Subst} : Evaluation program bindings (.expression []) [.expression []]
  | constructor {bindings : MORK.Subst} {head : String} {arguments answers : List Atom} :
      ConstructorHead program head →
      Arguments program bindings .data (.symbol head::arguments) [] 0 answers →
      Evaluation program bindings (.expression (.symbol head::arguments)) answers
  | call {bindings : MORK.Subst} {head : String} {arguments answers : List Atom} :
      DefinedHead program head →
      Arguments program bindings (.function head) arguments [] 0 answers →
      Evaluation program bindings (.expression (.symbol head::arguments)) answers

/-- Argument traversal has an explicit continuation target. Each alternative
finishes the remaining arguments and its call before the next alternative. -/
inductive Arguments (program : Program) : MORK.Subst → PeTTa.Eval.Target →
    List Atom → List Atom → Nat → List Atom → Type where
  | done {bindings target values index answers} :
      Invocation program bindings target values answers →
      Arguments program bindings target [] values index answers
  | next {bindings target first rest values index heads answers} :
      TargetAllowed target → Evaluation program bindings first heads →
      ArgumentCases program bindings target rest values index heads answers →
      Arguments program bindings target (first::rest) values index answers

inductive ArgumentCases (program : Program) : MORK.Subst → PeTTa.Eval.Target →
    List Atom → List Atom → Nat → List Atom → List Atom → Type where
  | nil {bindings target rest values index} :
      ArgumentCases program bindings target rest values index [] []
  | cons {bindings target rest values index head heads children remaining} :
      Arguments program bindings target rest (values++[head]) (index+1) children →
      ArgumentCases program bindings target rest values index heads remaining →
      ArgumentCases program bindings target rest values index (head::heads) (children++remaining)

inductive Invocation (program : Program) : MORK.Subst → PeTTa.Eval.Target →
    List Atom → List Atom → Type where
  | constructor {bindings values} :
      Value program (.expression values) → Invocation program bindings .data values [.expression values]
  | equations {bindings head values selected answers} :
      OrdinaryHead head → ClauseScan head values 0 program.equations selected →
      selected ≠ [] → Bodies program selected answers →
      Invocation program bindings (.function head) values answers

inductive Bodies (program : Program) : List ClauseWork → List Atom → Type where
  | nil : Bodies program [] []
  | cons {position bindings body selected children rest} :
      Evaluation program bindings body children → Bodies program selected rest →
      Bodies program ((position,bindings,body)::selected) (children++rest)
end


/-- Reordering stored equations preserves constructor admission. -/
theorem ConstructorHead.perm_program {program other : Program} {head : String}
    (same : program.equations.Perm other.equations) (source : ConstructorHead program head) :
    ConstructorHead other head :=
  ⟨source.1,fun equation member => source.2 equation (same.mem_iff.mpr member)⟩

theorem DefinedHead.perm_program {program other : Program} {head : String}
    (same : program.equations.Perm other.equations) (source : DefinedHead program head) :
    DefinedHead other head := by
  obtain ⟨ordinary,equation,member,headed⟩ := source
  exact ⟨ordinary,equation,same.mem_iff.mp member,headed⟩

theorem Value.perm_program {program other : Program} {atom : Atom} {scope : List String}
    (same : program.equations.Perm other.equations) (source : Value program atom scope) :
    Value other atom scope := by
  induction source with
  | symbol name nonempty ordinary => exact .symbol name nonempty ordinary
  | «variable» member => exact .variable member
  | grounded value => exact .grounded value
  | unit => exact .unit
  | constructor passive _ ih => exact .constructor (passive.perm_program same) ih

/-- Enlarging the set of permitted free names does not change data admission. -/
theorem Value.weaken {program : Program} {atom : Atom} {before after : List String}
    (source : Value program atom before) (included : ∀ name ∈ before, name ∈ after) :
    Value program atom after := by
  induction source with
  | symbol name nonempty ordinary => exact .symbol name nonempty ordinary
  | «variable» member => exact .variable (included _ member)
  | grounded value => exact .grounded value
  | unit => exact .unit
  | constructor passive _ ih => exact .constructor passive (fun argument member => ih argument member included)

/-- Substituting passive data for the permitted free names preserves the
constructor grammar. Applied defined heads cannot enter through a capture. -/
theorem Value.substitute {program : Program} {atom : Atom} {scope targetScope : List String}
    (value : Value program atom scope) (environment : String → Atom)
    (allowed : ∀ name ∈ scope, Value program (environment name) targetScope) :
    Value program (HE.Spec.Type.RuntimeRefinement.applyTypeValuation environment atom) targetScope := by
  induction value with
  | symbol name nonempty ordinary =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using
        (Value.symbol (program := program) (scope := targetScope) name nonempty ordinary)
  | «variable» member =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using allowed _ member
  | grounded scalar =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using
        (Value.grounded (program := program) (scope := targetScope) scalar)
  | unit =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation,List.map_nil] using
        (Value.unit (program := program) (scope := targetScope))
  | constructor passive _values ih =>
      simp only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation,List.map_cons]
      apply Value.constructor passive
      intro atom member
      obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
      exact ih argument present allowed

/-- Simultaneous name changes preserve passive constructor syntax. -/
theorem Value.rename {program : Program} {atom : Atom} {scope : List String}
    (valid : Value program atom scope) (names : String → String) :
    Value program (HE.Spec.Type.RuntimeRefinement.renameTypeVars names atom) (scope.map names) := by
  induction valid with
  | symbol name nonempty ordinary =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      exact .symbol name nonempty ordinary
  | «variable» member =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      exact .variable (List.mem_map_of_mem member)
  | grounded scalar =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      exact .grounded scalar
  | unit =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars,List.map_nil]
      exact .unit
  | constructor passive _each ih =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars,List.map_cons]
      apply Value.constructor passive
      intro value member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present

private theorem ClauseScan.swap_equations {head : String} {values : List Atom} {position : Nat}
    {first second : Equation} {equations : List Equation} {selected : List ClauseWork}
    (source : ClauseScan head values position (first::second::equations) selected) :
    ∃ other, ClauseScan head values position (second::first::equations) other ∧
      (selected.map Prod.snd).Perm (other.map Prod.snd) := by
  cases source with
  | other firstOther tail =>
      cases tail with
      | other secondOther tail => exact ⟨_,.other secondOther (.other firstOther tail),.refl _⟩
      | miss secondHead secondPattern secondMiss tail =>
          exact ⟨_,.miss secondHead secondPattern secondMiss (.other firstOther tail),.refl _⟩
      | hit secondHead secondPattern secondHit tail =>
          exact ⟨_,.hit secondHead secondPattern secondHit (.other firstOther tail),.refl _⟩
  | miss firstHead firstPattern firstMiss tail =>
      cases tail with
      | other secondOther tail =>
          exact ⟨_,.other secondOther (.miss firstHead firstPattern firstMiss tail),.refl _⟩
      | miss secondHead secondPattern secondMiss tail =>
          exact ⟨_,.miss secondHead secondPattern secondMiss
            (.miss firstHead firstPattern firstMiss tail),.refl _⟩
      | hit secondHead secondPattern secondHit tail =>
          exact ⟨_,.hit secondHead secondPattern secondHit
            (.miss firstHead firstPattern firstMiss tail),.refl _⟩
  | hit firstHead firstPattern firstHit tail =>
      cases tail with
      | other secondOther tail =>
          exact ⟨_,.other secondOther (.hit firstHead firstPattern firstHit tail),.refl _⟩
      | miss secondHead secondPattern secondMiss tail =>
          exact ⟨_,.miss secondHead secondPattern secondMiss
            (.hit firstHead firstPattern firstHit tail),.refl _⟩
      | hit secondHead secondPattern secondHit tail =>
          exact ⟨_,.hit secondHead secondPattern secondHit
            (.hit firstHead firstPattern firstHit tail),.swap _ _ _⟩

/-- A storage permutation transports every selected copy. Physical positions
are recomputed; local substitutions and bodies retain their multiplicity. -/
theorem ClauseScan.perm_equations {head : String} {values : List Atom}
    {equations otherEquations : List Equation} (same : equations.Perm otherEquations)
    {position : Nat} {selected : List ClauseWork}
    (source : ClauseScan head values position equations selected) :
    ∃ other, ClauseScan head values position otherEquations other ∧
      (selected.map Prod.snd).Perm (other.map Prod.snd) := by
  induction same generalizing position selected with
  | nil => cases source; exact ⟨[],.nil _,.nil⟩
  | cons equation _ ih =>
      cases source with
      | other different tail =>
          obtain ⟨other,scanned,paired⟩ := ih tail
          exact ⟨other,.other different scanned,paired⟩
      | miss headed ordinary refused tail =>
          obtain ⟨other,scanned,paired⟩ := ih tail
          exact ⟨other,.miss headed ordinary refused scanned,paired⟩
      | hit headed ordinary matched tail =>
          obtain ⟨other,scanned,paired⟩ := ih tail
          exact ⟨_,.hit headed ordinary matched scanned,paired.cons _⟩
  | swap => exact source.swap_equations
  | trans _ _ first second =>
      obtain ⟨middle,scanned,paired⟩ := first source
      obtain ⟨other,scannedOther,pairedOther⟩ := second scanned
      exact ⟨other,scannedOther,paired.trans pairedOther⟩

private theorem ArgumentCases.chunks {program : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} {rest values heads answers : List Atom} {index : Nat}
    (source : ArgumentCases program bindings target rest values index heads answers) :
    ∃ chunks : List (List Atom),
      List.Forall₂ (fun head children => Nonempty
        (Arguments program bindings target rest (values++[head]) (index+1) children)) heads chunks ∧
      answers = chunks.flatten := by
  match source with
  | .nil => exact ⟨[],.nil,rfl⟩
  | .cons first tail =>
      obtain ⟨chunks,paired,erased⟩ := tail.chunks
      exact ⟨_,.cons ⟨first⟩ paired,by simp only [List.flatten_cons,erased]⟩
termination_by structural source

private theorem ArgumentCases.of_chunks {program : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} {rest values heads : List Atom} {index : Nat}
    {chunks : List (List Atom)}
    (paired : List.Forall₂ (fun head children => Nonempty
      (Arguments program bindings target rest (values++[head]) (index+1) children)) heads chunks) :
    Nonempty (ArgumentCases program bindings target rest values index heads chunks.flatten) := by
  induction paired with
  | nil => exact ⟨.nil⟩
  | cons first _ ih =>
      obtain ⟨first⟩ := first
      obtain ⟨tail⟩ := ih
      exact ⟨.cons first tail⟩

/-- Independent pure alternatives can change traversal order. Their caller
continuations and every answer occurrence are retained. -/
theorem ArgumentCases.perm_heads {program : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} {rest values heads otherHeads answers : List Atom} {index : Nat}
    (source : ArgumentCases program bindings target rest values index heads answers)
    (same : heads.Perm otherHeads) :
    ∃ otherAnswers, Nonempty
      (ArgumentCases program bindings target rest values index otherHeads otherAnswers) ∧
      answers.Perm otherAnswers := by
  obtain ⟨chunks,paired,erased⟩ := source.chunks
  obtain ⟨otherChunks,otherPaired,reordered⟩ := List.perm_comp_forall₂ same.symm paired
  exact ⟨otherChunks.flatten,ArgumentCases.of_chunks otherPaired,by
    rw [erased]; exact reordered.symm.flatten⟩

private theorem Bodies.chunks {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) :
    ∃ chunks : List (List Atom),
      List.Forall₂ (fun work children => Nonempty (Evaluation program work.1 work.2 children))
        (selected.map Prod.snd) chunks ∧ answers = chunks.flatten := by
  match source with
  | .nil => exact ⟨[],.nil,rfl⟩
  | .cons first tail =>
      obtain ⟨chunks,paired,erased⟩ := tail.chunks
      exact ⟨_,.cons ⟨first⟩ paired,by simp only [List.flatten_cons,erased]⟩
termination_by structural source

private theorem Bodies.of_chunks {program : Program} (selected : List ClauseWork)
    {chunks : List (List Atom)}
    (paired : List.Forall₂ (fun work children => Nonempty (Evaluation program work.1 work.2 children))
      (selected.map Prod.snd) chunks) : Nonempty (Bodies program selected chunks.flatten) := by
  induction selected generalizing chunks with
  | nil => cases paired; exact ⟨.nil⟩
  | cons work selected ih =>
      cases paired with
      | cons first tail =>
          obtain ⟨first⟩ := first
          obtain ⟨tail⟩ := ih tail
          exact ⟨.cons first tail⟩

theorem Bodies.perm_work {program : Program} {selected otherSelected : List ClauseWork}
    {answers : List Atom} (source : Bodies program selected answers)
    (same : (selected.map Prod.snd).Perm (otherSelected.map Prod.snd)) :
    ∃ otherAnswers, Nonempty (Bodies program otherSelected otherAnswers) ∧
      answers.Perm otherAnswers := by
  obtain ⟨chunks,paired,erased⟩ := source.chunks
  obtain ⟨otherChunks,otherPaired,reordered⟩ := List.perm_comp_forall₂ same.symm paired
  exact ⟨otherChunks.flatten,Bodies.of_chunks otherSelected otherPaired,by
    rw [erased]; exact reordered.symm.flatten⟩

mutual
/-- Complete pure source work survives a permutation of stored equation
copies. Only the resulting traversal order changes, including under nested
argument alternatives and recursion. No effectful schedule is reordered. -/
theorem Evaluation.perm_program {program other : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers)
    (same : program.equations.Perm other.equations) :
    ∃ otherAnswers, Nonempty (Evaluation other bindings expression otherAnswers) ∧
      answers.Perm otherAnswers := by
  match source with
  | .«variable» value => exact ⟨_,⟨.variable (value.perm_program same)⟩,.refl _⟩
  | .symbol value => exact ⟨_,⟨.symbol (value.perm_program same)⟩,.refl _⟩
  | .grounded value => exact ⟨_,⟨.grounded value⟩,.refl _⟩
  | .unit => exact ⟨_,⟨.unit⟩,.refl _⟩
  | .constructor passive arguments =>
      obtain ⟨answers,⟨arguments⟩,paired⟩ := arguments.perm_program same
      exact ⟨answers,⟨.constructor (passive.perm_program same) arguments⟩,paired⟩
  | .call defined arguments =>
      obtain ⟨answers,⟨arguments⟩,paired⟩ := arguments.perm_program same
      exact ⟨answers,⟨.call (defined.perm_program same) arguments⟩,paired⟩
termination_by structural source

theorem Arguments.perm_program {program other : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} {arguments values answers : List Atom} {index : Nat}
    (source : Arguments program bindings target arguments values index answers)
    (same : program.equations.Perm other.equations) :
    ∃ otherAnswers, Nonempty (Arguments other bindings target arguments values index otherAnswers) ∧
      answers.Perm otherAnswers := by
  match source with
  | .done invoked =>
      obtain ⟨answers,⟨invoked⟩,paired⟩ := invoked.perm_program same
      exact ⟨answers,⟨.done invoked⟩,paired⟩
  | .next allowed evaluated continued =>
      obtain ⟨heads,⟨evaluated⟩,headsPaired⟩ := evaluated.perm_program same
      obtain ⟨middle,⟨continued⟩,answersPaired⟩ := continued.perm_program same
      obtain ⟨answers,⟨continued⟩,reordered⟩ := continued.perm_heads headsPaired
      exact ⟨answers,⟨.next allowed evaluated continued⟩,answersPaired.trans reordered⟩
termination_by structural source

theorem ArgumentCases.perm_program {program other : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} {rest values heads answers : List Atom} {index : Nat}
    (source : ArgumentCases program bindings target rest values index heads answers)
    (same : program.equations.Perm other.equations) :
    ∃ otherAnswers, Nonempty (ArgumentCases other bindings target rest values index heads otherAnswers) ∧
      answers.Perm otherAnswers := by
  match source with
  | .nil => exact ⟨[],⟨.nil⟩,.nil⟩
  | .cons first tail =>
      obtain ⟨firstAnswers,⟨first⟩,firstPaired⟩ := first.perm_program same
      obtain ⟨tailAnswers,⟨tail⟩,tailPaired⟩ := tail.perm_program same
      exact ⟨firstAnswers++tailAnswers,⟨.cons first tail⟩,firstPaired.append tailPaired⟩
termination_by structural source

theorem Invocation.perm_program {program other : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} {values answers : List Atom}
    (source : Invocation program bindings target values answers)
    (same : program.equations.Perm other.equations) :
    ∃ otherAnswers, Nonempty (Invocation other bindings target values otherAnswers) ∧
      answers.Perm otherAnswers := by
  match source with
  | .constructor value => exact ⟨_,⟨.constructor (value.perm_program same)⟩,.refl _⟩
  | .equations ordinary scanned nonempty bodies =>
      obtain ⟨selected,scanned,workPaired⟩ := scanned.perm_equations same
      obtain ⟨middle,⟨bodies⟩,answersPaired⟩ := bodies.perm_program same
      obtain ⟨answers,⟨bodies⟩,reordered⟩ := bodies.perm_work workPaired
      have selectedNonempty : selected ≠ [] := by
        intro empty
        have lengthZero := workPaired.length_eq
        simp only [List.length_map,empty,List.length_nil] at lengthZero
        exact nonempty (List.length_eq_zero_iff.mp lengthZero)
      exact ⟨answers,⟨.equations ordinary scanned selectedNonempty bodies⟩,answersPaired.trans reordered⟩
termination_by structural source

theorem Bodies.perm_program {program other : Program} {selected : List ClauseWork}
    {answers : List Atom} (source : Bodies program selected answers)
    (same : program.equations.Perm other.equations) :
    ∃ otherAnswers, Nonempty (Bodies other selected otherAnswers) ∧ answers.Perm otherAnswers := by
  match source with
  | .nil => exact ⟨[],⟨.nil⟩,.nil⟩
  | .cons first tail =>
      obtain ⟨firstAnswers,⟨first⟩,firstPaired⟩ := first.perm_program same
      obtain ⟨tailAnswers,⟨tail⟩,tailPaired⟩ := tail.perm_program same
      exact ⟨firstAnswers++tailAnswers,⟨.cons first tail⟩,firstPaired.append tailPaired⟩
termination_by structural source
end


/-- Assemble singleton child derivations in their actual list positions.
Each copy gets its own continuation node, even when two pairs are equal. -/
def Arguments.single_results {program : Program} {bindings : MORK.Subst}
    {target : PeTTa.Eval.Target} (allowed : TargetAllowed target)
    (pairs : List (Atom × Atom))
    (children : ∀ pair ∈ pairs, Evaluation program bindings pair.1 [pair.2])
    {values : List Atom} {index : Nat} {answers : List Atom}
    (complete : Invocation program bindings target (values++pairs.map Prod.snd) answers) :
    Arguments program bindings target (pairs.map Prod.fst) values index answers := by
  match pairs with
  | [] => simpa only [List.map_nil,List.append_nil] using Arguments.done complete
  | pair::rest =>
      have restComplete : Invocation program bindings target
          ((values++[pair.2])++rest.map Prod.snd) answers := by
        simpa only [List.map_cons,List.append_assoc,List.singleton_append] using complete
      have later := Arguments.single_results allowed rest
        (fun child member => children child (List.mem_cons_of_mem _ member))
        (values := values++[pair.2]) (index := index+1) restComplete
      have branches : ArgumentCases program bindings target (rest.map Prod.fst) values index
          [pair.2] answers := by
        simpa only [List.append_nil] using
          (ArgumentCases.cons (values := values) (index := index) later .nil)
      simpa only [List.map_cons] using
        Arguments.next allowed (children pair List.mem_cons_self) branches
termination_by structural pairs

/-- Ground passive data has a finite source completion under any caller.
This constructs the derivation tree rather than assuming evaluation idempotent. -/
theorem Value.evaluates {program : Program} {atom : Atom} (value : Value program atom)
    (bindings : MORK.Subst) : Nonempty (Evaluation program bindings atom [atom]) := by
  classical
  generalize emptyScope : ([] : List String) = scope at value
  induction value with
  | symbol name nonempty ordinary => exact ⟨.symbol (.symbol name nonempty ordinary)⟩
  | «variable» member => rw [←emptyScope] at member; cases member
  | grounded scalar => exact ⟨.grounded scalar⟩
  | unit => exact ⟨.unit⟩
  | @constructor head arguments _ passive values ih =>
      have closedValues : ∀ argument ∈ arguments, Value program argument := by
        simpa only [←emptyScope] using values
      have headValue : Value program (.symbol head) := passive.1.symbol_value
      let pairs := (.symbol head::arguments).map fun atom => (atom,atom)
      have children (pair : Atom × Atom) (member : pair ∈ pairs) :
          Nonempty (Evaluation program bindings pair.1 [pair.2]) := by
        obtain ⟨atom,present,rfl⟩ := List.mem_map.mp member
        rcases List.mem_cons.mp present with rfl | present
        · exact ⟨.symbol headValue⟩
        · exact ih atom present emptyScope
      have complete : Invocation program bindings .data
          ([]++pairs.map Prod.snd) [.expression (.symbol head::arguments)] := by
        simpa only [pairs,List.map_map,Function.comp_def,List.map_id',List.nil_append] using
          (Invocation.constructor (bindings := bindings) (Value.constructor passive closedValues))
      have path := Arguments.single_results .data pairs
        (fun pair member => Classical.choice (children pair member)) (values := []) (index := 0) complete
      exact ⟨.constructor passive (by
        simpa only [pairs,List.map_map,Function.comp_def,List.map_id'] using path)⟩

/-- Complete source selection produces the existing PeTTa selector's exact
ordered work list, including duplicate stored copies. -/
theorem ClauseScan.petta_exact {head : String} {values : List Atom} {position : Nat}
    {equations : List Equation} {selected : List ClauseWork}
    (source : ClauseScan head values position equations selected) :
    equations.filterMap (fun equation => if equation.head = head then
      (PeTTa.SpaceSemantics.matchValue.matchValues [] equation.arguments values).map
        (fun bindings => PeTTa.Eval.Control.evaluate bindings equation.body) else none) =
      selected.map (fun work => PeTTa.Eval.Control.evaluate work.2.1 work.2.2) := by
  have flat (arguments : List Atom)
      (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads (.expression arguments)) :
      PeTTa.SpaceSemantics.matchValue.matchValues [] arguments values =
        PeTTa.SpaceSemantics.matchValue [] (.expression arguments) (.expression values) := by
    rw [PeTTa.SpaceSemantics.matchValue_expression_of_not_cons]
    intro first rest same
    apply ordinary
    subst same
    simp [PeTTa.SpaceSemantics.patternHeads]
  induction source with
  | nil => rfl
  | other different _rest ih => simp [different,ih]
  | @miss position equation equations selected same ordinary absent _rest ih =>
      have refused : MORK.matchAtom [] (.expression equation.arguments) (.expression values) = none := by
        cases found : MORK.matchAtom [] (.expression equation.arguments) (.expression values) with
        | none => rfl
        | some bindings => exact (absent bindings (MORK.matchAtom_sound found)).elim
      simp [same,flat _ ordinary,ConstructorMatch.matchValue_eq_structural _ ordinary,refused,ih]
  | hit same ordinary matched _rest ih =>
      simp [same,flat _ ordinary,ConstructorMatch.matchValue_eq_structural _ ordinary,
        MORK.matchAtom_complete matched,ih]

private theorem OrdinaryHead.control_free {head : String} (ordinary : OrdinaryHead head) :
    head ∉ ["let","let*","case","if","collapse","superpose","empty","quote","unique"] := by
  intro member
  exact ordinary.2.2 (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    tauto)

/-- An ordinary head is not `match`, which is a primitive name. -/
private theorem OrdinaryHead.call_free {head : String} (ordinary : OrdinaryHead head) :
    head ∉ ["let","let*","case","if","collapse","superpose","empty","quote","unique","match"] := by
  intro member
  exact ordinary.2.2 (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    tauto)

private theorem ConstructorHead.inert {program : Program} {head : String}
    (passive : ConstructorHead program head) :
    (PeTTa.Eval.ioHead head || PeTTa.StdLib.known head ||
      program.equations.any (·.head == head)) = false := by
  have absent : program.equations.any (·.head == head) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨equation,member,same⟩ := List.any_eq_true.mp yes
    exact passive.2 equation member (eq_of_beq same)
  simp [passive.1.1,passive.1.2.1,absent]

private theorem DefinedHead.callable {program : Program} {head : String}
    (defined : DefinedHead program head) :
    (PeTTa.Eval.ioHead head || PeTTa.StdLib.known head ||
      program.equations.any (·.head == head)) = true := by
  obtain ⟨equation,member,same⟩ := defined.2
  have selected : program.equations.any (·.head == head) = true :=
    List.any_eq_true.mpr ⟨equation,member,by simp [same]⟩
  simp [selected]

private theorem TargetAllowed.eager {program : Program} {target : PeTTa.Eval.Target}
    (plain : program.declarations = []) (allowed : TargetAllowed target) (index : Nat) :
    (match target with
      | .function head => PeTTa.Eval.argumentIsRaw program head index
      | .data => false) = false := by
  cases allowed with
  | data => rfl
  | function ordinary => simp [PeTTa.Eval.argumentIsRaw,plain,ordinary.2.1]

open PeTTa.Eval (Control Frame Target Configuration theory finished Returns)
open PeTTa.Effects (State)
open private path_trans from Mettapedia.Languages.MeTTa.PeTTa.Eval

/-- Exact ordered sequencing is used by both argument alternatives and
selected equation bodies; the source position is carried by the work list. -/
abbrev SequencePath (program : Program) (state : State) (controls : List Control)
    (collected answers : List Atom) : Prop :=
  (theory program).MultiStep {state,control := .sequence controls collected}
    (finished state (collected++answers) [] [])

mutual
/-- Every complete pure source tree produces an actual PeTTa execution path,
with the entire ordered answer list and the unchanged pure world. -/
theorem Evaluation.petta_path {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers)
    (plain : program.declarations = []) (state : State) :
    Returns program bindings state expression state answers := by
  match source with
  | .«variable» _value => exact PeTTa.Eval.variable_returns _ _ _ _
  | .symbol _value => exact PeTTa.Eval.symbol_returns _ _ _ _
  | .grounded value => exact PeTTa.Eval.grounded_returns _ _ _ value
  | .unit =>
      exact .step (PeTTa.Eval.step_transition rfl)
        (PeTTa.Eval.data_arguments_values_return program bindings state [] 0)
  | .constructor passive arguments =>
      exact PeTTa.Eval.data_call_answers _ _ _ _ _ _ _ passive.inert
        (arguments.petta_path plain state) passive.1.control_free
  | .call defined arguments =>
      exact PeTTa.Eval.call_answers _ _ _ _ _ _ _ defined.callable
        (arguments.petta_path plain state) defined.1.call_free
termination_by structural source

theorem Arguments.petta_path {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {answers : List Atom}
    (source : Arguments program bindings target arguments values index answers)
    (plain : program.declarations = []) (state : State) :
    (theory program).MultiStep {state,control := .arguments bindings target arguments values index}
      (finished state answers [] []) := by
  match source with
  | .done invoked => exact invoked.petta_path plain state index
  | @Arguments.next _ bindings target first rest values index heads answers allowed evaluated continued =>
      refine .step (PeTTa.Eval.step_transition ?_) (path_trans
        (PeTTa.Eval.path_with_caller_frames program
          [.argument bindings target rest values index] (evaluated.petta_path plain state)) ?_)
      · cases allowed with
        | data => rfl
        | function ordinary =>
            simp [PeTTa.Eval.step,PeTTa.Eval.argumentIsRaw,plain,ordinary.2.1,PeTTa.Eval.withFrames]
      · exact .step (.argument_return rfl rfl) (continued.petta_path plain state [])
termination_by structural source

theorem ArgumentCases.petta_path {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {heads answers : List Atom}
    (source : ArgumentCases program bindings target arguments values index heads answers)
    (plain : program.declarations = []) (state : State) (collected : List Atom) :
    SequencePath program state
      (heads.map fun value => .arguments bindings target arguments (values++[value]) (index+1))
      collected answers := by
  match source with
  | .nil =>
      simp only [SequencePath,List.map_nil,List.append_nil]
      exact .step (.sequence_done rfl) (.refl _)
  | .cons next rest =>
      simpa only [SequencePath,List.map_cons,List.append_assoc] using
        PeTTa.Eval.sequence_cons_answers program state state state _ _ collected _ _
          (next.petta_path plain state) (rest.petta_path plain state _)
termination_by structural source

theorem Invocation.petta_path {program : Program} {bindings : MORK.Subst} {target : Target}
    {values answers : List Atom} (source : Invocation program bindings target values answers)
    (plain : program.declarations = []) (state : State) (index : Nat) :
    (theory program).MultiStep {state,control := .arguments bindings target [] values index}
      (finished state answers [] []) := by
  match source with
  | .constructor _value => exact PeTTa.Eval.data_arguments_values_return _ _ _ _ _
  | @Invocation.equations _ bindings head values selected answers ordinary scan covered bodies =>
      refine .step (.equations rfl ordinary.1 ordinary.2.1) ?_
      have clausesEq : PeTTa.Eval.clauses program head values = _ := scan.petta_exact
      have nonempty : PeTTa.Eval.clauses program head values ≠ [] := by
        rw [clausesEq]
        simpa using covered
      obtain ⟨first, rest, listed⟩ := List.exists_cons_of_ne_nil nonempty
      change (theory program).MultiStep
        {state,control := PeTTa.Eval.application program head values} _
      rw [PeTTa.Eval.application_of_selected listed, ← listed, clausesEq]
      exact bodies.petta_path plain state []
termination_by structural source

theorem Bodies.petta_path {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) (plain : program.declarations = [])
    (state : State) (collected : List Atom) :
    SequencePath program state (selected.map fun work => .evaluate work.2.1 work.2.2) collected answers := by
  match source with
  | .nil =>
      simp only [SequencePath,List.map_nil,List.append_nil]
      exact .step (.sequence_done rfl) (.refl _)
  | .cons child rest =>
      simpa only [SequencePath,List.map_cons,List.append_assoc] using
        PeTTa.Eval.sequence_cons_answers program state state state _ _ collected _ _
          (child.petta_path plain state) (rest.petta_path plain state _)
termination_by structural source

end

/-- The recursive source tree is admitted by PeTTa's independent whole-program
judgment as well as its executable machine. -/
theorem Evaluation.petta_source {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers)
    (plain : program.declarations = []) (state : State) :
    PeTTa.DeclarativeSpec.Runs program {state,control := .evaluate bindings expression}
      (.complete state answers [] []) :=
  (PeTTa.Eval.completed_run_iff_derivation _ _ _ _ _ _).mp
    (PeTTa.Eval.path_has_sufficient_fuel _ _ _ _ _ _ (source.petta_path plain state))

/-- A finite source tree characterizes every completed PeTTa observation
from its load, including all answer copies, the reached store and I/O. -/
theorem Evaluation.petta_completed_iff {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers)
    (plain : program.declarations = []) (before after : State)
    (observed input output : List Atom) :
    (∃ fuel, PeTTa.Eval.run program fuel {state := before,control := .evaluate bindings expression} =
      .complete after observed input output) ↔
      after = before ∧ observed = answers ∧ input = [] ∧ output = [] :=
  PeTTa.Eval.path_completed_iff program _ before answers [] []
    (source.petta_path plain before) after observed input output

/-- Argument values have already been materialized at invocation. Matching
introduces each clause's own local substitution, so changing the saved caller
substitution does not change this source phase or its physical work list. -/
def Invocation.rebind {program : Program} {bindings : MORK.Subst} {target : Target}
    {values answers : List Atom} (source : Invocation program bindings target values answers)
    (next : MORK.Subst) : Invocation program next target values answers := by
  cases source with
  | constructor value => exact .constructor value
  | equations ordinary scan covered bodies => exact .equations ordinary scan covered bodies

mutual
/-- A finite source tree can move its input substitution into the source
syntax. Clause positions, argument alternatives and complete answer copies
are unchanged; no HE or machine-evaluation premise is used. -/
theorem Evaluation.substituted {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers) :
    Nonempty (Evaluation program [] (MORK.applySubst bindings expression) answers) := by
  match source with
  | .«variable» value => exact value.evaluates []
  | .symbol value => exact ⟨.symbol value⟩
  | .grounded scalar => exact ⟨.grounded scalar⟩
  | .unit => exact ⟨.unit⟩
  | @Evaluation.constructor _ bindings head arguments answers passive children =>
      obtain ⟨mapped⟩ := children.substituted
      have lowered : Arguments program [] .data
          (.symbol head::MORK.applySubst.applySubstList bindings arguments) [] 0 answers := by
        simpa only [MORK.applySubst,MORK.applySubst.applySubstList] using mapped
      refine ⟨?_⟩
      simpa only [MORK.applySubst,MORK.applySubst.applySubstList] using
        (Evaluation.constructor passive lowered)
  | .call defined children =>
      obtain ⟨mapped⟩ := children.substituted
      refine ⟨?_⟩
      simpa only [MORK.applySubst,MORK.applySubst.applySubstList] using
        (Evaluation.call defined mapped)
termination_by structural source

theorem Arguments.substituted {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {answers : List Atom}
    (source : Arguments program bindings target arguments values index answers) :
    Nonempty (Arguments program [] target (MORK.applySubst.applySubstList bindings arguments)
      values index answers) := by
  match source with
  | .done invoked => exact ⟨.done (invoked.rebind [])⟩
  | .next allowed first continued =>
      obtain ⟨evaluated⟩ := first.substituted
      obtain ⟨rest⟩ := continued.substituted
      exact ⟨.next allowed evaluated rest⟩
termination_by structural source

theorem ArgumentCases.substituted {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {heads answers : List Atom}
    (source : ArgumentCases program bindings target arguments values index heads answers) :
    Nonempty (ArgumentCases program [] target (MORK.applySubst.applySubstList bindings arguments)
      values index heads answers) := by
  match source with
  | .nil => exact ⟨.nil⟩
  | .cons first remaining =>
      obtain ⟨continued⟩ := first.substituted
      obtain ⟨rest⟩ := remaining.substituted
      exact ⟨.cons continued rest⟩
termination_by structural source
end


/-- A completed source tree on a passive substitution image has its unique
singleton result. Both trees are constructed independently; the existing
PeTTa correspondence and deterministic completion identify their answers. -/
theorem Evaluation.passive_exact {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers) (plain : program.declarations = [])
    (passive : Value program (MORK.applySubst bindings expression)) :
    answers = [MORK.applySubst bindings expression] := by
  obtain ⟨materialized⟩ := source.substituted
  obtain ⟨data⟩ := passive.evaluates []
  have completed := (materialized.petta_completed_iff plain PeTTa.Effects.empty PeTTa.Effects.empty
    answers [] []).mpr ⟨rfl,rfl,rfl,rfl⟩
  have exactData := (data.petta_completed_iff plain PeTTa.Effects.empty PeTTa.Effects.empty
    answers [] []).mp completed
  exact exactData.2.1

/-- Passive selected bodies preserve their complete source occurrence list. -/
theorem Bodies.passive_answers {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) (plain : program.declarations = [])
    (passive : ∀ item ∈ selected, Value program (MORK.applySubst item.2.1 item.2.2)) :
    answers = selected.map (fun item => MORK.applySubst item.2.1 item.2.2) := by
  match source with
  | .nil => rfl
  | .cons child rest =>
      rw [child.passive_exact plain (passive _ List.mem_cons_self),
        rest.passive_answers plain (fun item member => passive item (List.mem_cons_of_mem _ member))]
      rfl
termination_by structural source

/-- A completed invocation extends to a source call when its argument syntax
already consists of passive values. Each argument keeps its own source node. -/
theorem Invocation.with_value_arguments {program : Program} {head : String}
    {values answers : List Atom} (source : Invocation program [] (.function head) values answers)
    (defined : DefinedHead program head) (passive : ∀ value ∈ values, Value program value) :
    Nonempty (Evaluation program [] (.expression (.symbol head::values)) answers) := by
  let pairs := values.map (fun value => (value,value))
  have arguments := Arguments.single_results (program := program) (.function defined.1) pairs
    (fun pair member => Classical.choice (by
      obtain ⟨value,present,same⟩ := List.mem_map.mp member
      cases same
      exact (passive value present).evaluates []))
    (values := []) (index := 0)
    (by simpa only [pairs,List.map_map,Function.comp_def,List.map_id',List.nil_append] using source)
  exact ⟨.call defined (by
    simpa only [pairs,List.map_map,Function.comp_def,List.map_id'] using arguments)⟩

/-- A passive value mentions only the free names admitted by its scope. -/
theorem Value.variables {program : Program} {atom : Atom} {scope : List String}
    (value : Value program atom scope) :
    ∀ name, HE.Spec.Match.Merge.AtomOccurs atom name → name ∈ scope := by
  induction value with
  | symbol => intro name occurs; cases occurs
  | «variable» member => intro name occurs; cases occurs; exact member
  | grounded => intro name occurs; cases occurs
  | unit =>
      intro name occurs
      cases occurs with
      | expression member _occurs => exact (List.not_mem_nil member).elim
  | @constructor head arguments _ _passive _values ih =>
      intro name occurs
      cases occurs with
      | @expression _ child _ member occurrence =>
          rcases List.mem_cons.mp member with rfl | member
          · cases occurrence
          · exact ih child member name occurrence

/-- The empty-scope specialization is syntactically ground, independently
of storage or readiness annotations. -/
theorem Value.variable_free {program : Program} {atom : Atom} (value : Value program atom) :
    ∀ name, ¬HE.Spec.Match.Merge.AtomOccurs atom name := by
  intro name occurs
  exact List.not_mem_nil (value.variables name occurs)

/-- Passive answers cannot become control markers at a return boundary. -/
theorem Value.not_stopped {program : Program} {atom : Atom} {scope : List String}
    (value : Value program atom scope) :
    ¬HE.Spec.Eval.IsEmptyOrErrorRel atom := by
  cases value with
  | symbol name nonempty _ordinary =>
      simpa [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty] using nonempty
  | «variable» => simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty]
  | grounded scalar =>
      simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty]
  | unit => simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty]
  | @constructor head arguments _ passive _values =>
      have ordinary : head ≠ "Error" := fun same => passive.1.2.2 (by simp [same])
      simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty,ordinary]

mutual
/-- The finite source tree proves the return contract at every depth;
it is not a postcondition assumed of the machine's output. -/
theorem Evaluation.values {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers) :
    ∀ answer ∈ answers, Value program answer := by
  match source with
  | .«variable» value | .symbol value =>
      intro answer member
      obtain rfl := List.mem_singleton.mp member
      exact value
  | .grounded scalar =>
      intro answer member
      obtain rfl := List.mem_singleton.mp member
      exact .grounded scalar
  | .unit =>
      intro answer member
      obtain rfl := List.mem_singleton.mp member
      exact .unit
  | .constructor _passive arguments | .call _defined arguments => exact arguments.values
termination_by structural source

theorem Arguments.values {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {answers : List Atom}
    (source : Arguments program bindings target arguments values index answers) :
    ∀ answer ∈ answers, Value program answer := by
  match source with
  | .done invoked => exact invoked.values
  | .next _allowed _evaluated continued => exact continued.values
termination_by structural source

theorem ArgumentCases.values {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {heads answers : List Atom}
    (source : ArgumentCases program bindings target arguments values index heads answers) :
    ∀ answer ∈ answers, Value program answer := by
  match source with
  | .nil => intro answer member; cases member
  | .cons next rest =>
      intro answer member
      exact (List.mem_append.mp member).elim (next.values answer) (rest.values answer)
termination_by structural source

theorem Invocation.values {program : Program} {bindings : MORK.Subst} {target : Target}
    {values answers : List Atom} (source : Invocation program bindings target values answers) :
    ∀ answer ∈ answers, Value program answer := by
  match source with
  | .constructor value =>
      intro answer member
      obtain rfl := List.mem_singleton.mp member
      exact value
  | .equations _ordinary _scan _covered bodies => exact bodies.values
termination_by structural source

theorem Bodies.values {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) : ∀ answer ∈ answers, Value program answer := by
  match source with
  | .nil => intro answer member; cases member
  | .cons child rest =>
      intro answer member
      exact (List.mem_append.mp member).elim (child.values answer) (rest.values answer)
termination_by structural source
end

mutual
/-- The finite successful-call fragment produces an occurrence. Failure and
divergent calls do not acquire a completion by an empty source prefix. -/
theorem Evaluation.nonempty {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom} (source : Evaluation program bindings expression answers) :
    answers ≠ [] := by
  match source with
  | .«variable» _ | .symbol _ | .grounded _ | .unit => simp
  | .constructor _ arguments | .call _ arguments => exact arguments.nonempty
termination_by structural source

theorem Arguments.nonempty {program : Program} {bindings : MORK.Subst} {target : PeTTa.Eval.Target}
    {arguments values : List Atom} {index : Nat} {answers : List Atom}
    (source : Arguments program bindings target arguments values index answers) : answers ≠ [] := by
  match source with
  | .done called => exact called.nonempty
  | .next _ child cases => exact cases.nonempty child.nonempty
termination_by structural source

theorem ArgumentCases.nonempty {program : Program} {bindings : MORK.Subst} {target : PeTTa.Eval.Target}
    {arguments values : List Atom} {index : Nat} {heads answers : List Atom}
    (source : ArgumentCases program bindings target arguments values index heads answers)
    (selected : heads ≠ []) : answers ≠ [] := by
  match source with
  | .nil => exact (selected rfl).elim
  | .cons child _rest => exact fun empty => child.nonempty (List.append_eq_nil_iff.mp empty).1
termination_by structural source

theorem Invocation.nonempty {program : Program} {bindings : MORK.Subst} {target : PeTTa.Eval.Target}
    {values answers : List Atom} (source : Invocation program bindings target values answers) : answers ≠ [] := by
  match source with
  | .constructor _ => simp
  | .equations _ _ selected bodies => exact bodies.nonempty selected
termination_by structural source

theorem Bodies.nonempty {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) (entered : selected ≠ []) : answers ≠ [] := by
  match source with
  | .nil => exact (entered rfl).elim
  | .cons child _rest => exact fun empty => child.nonempty (List.append_eq_nil_iff.mp empty).1
termination_by structural source
end

/-- Any reached certified HE frame reads a completed common-fragment answer
without changing it. The local marking and rebuilding policies stay abstract. -/
theorem Evaluation.answer_read_exact {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers)
    (policy : HE.Spec.Eval.Completed.Policy) (frame : HE.Spec.Eval.Completed.Frame)
    {answer : Atom} (member : answer ∈ answers) (value : HE.Spec.Eval.Entry.Value)
    (represented : value.erase = answer) :
    frame.read policy value = value := by
  apply HE.Spec.Eval.Completed.Frame.read_variable_free
  rw [represented]
  exact (source.values answer member).variable_free

/-- Grounded operations are outside the pure HE/PeTTa common fragment. -/
def noForeign : HE.Spec.Eval.GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

theorem OrdinaryHead.he_non_grounded {head : String} (ordinary : OrdinaryHead head)
    (arguments : List Atom) :
    HE.Spec.Eval.NonGroundedCallRel noForeign (.expression (.symbol head::arguments)) := by
  constructor
  · rintro ⟨operator,values,_shape,executed⟩
    exact executed
  · change decide (head ∈ ["eval","evalc","chain","unify","cons-atom","decons-atom",
      "function","collapse-bind","superpose-bind","metta","context-space","call-native"]) = false
    apply decide_eq_false_iff_not.mpr
    intro selected
    apply ordinary.2.2
    simp only [List.mem_cons,List.not_mem_nil,or_false] at selected ⊢
    tauto

/-- The shared fragment uses the existing equation representation. Type
declarations remain the dialect's separate policy, outside this space view. -/
def equationSpace (program : Program) : HE.Space :=
  HE.Space.ofList (program.equations.map Equation.toAtom)

/-- Every body variable is supplied by its own raw clause pattern. -/
def RangeRestricted (program : Program) : Prop :=
  ∀ equation ∈ program.equations, ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars equation.body,
    name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars
      (.expression (.symbol equation.head::equation.arguments))

/-- A selected source occurrence and HE work item retain the same raw body
and pattern instance. Binding records need not have the same representation. -/
def ClauseInstance (query : Atom) (selected : ClauseWork)
    (work : HE.Spec.Eval.Steps.EquationWork) : Prop :=
  work.position = selected.1 ∧ work.right = selected.2.2 ∧
    MORK.applySubst selected.2.1 work.left = query ∧
    MORK.MatchAtomRel [] work.left query selected.2.1

private theorem ClauseScan.he_rows {head : String} {values : List Atom} {position : Nat}
    {equations : List Equation} {selected : List ClauseWork}
    (source : ClauseScan head values position equations selected)
    (live : List Atom) (frame : HE.Spec.Eval.Completed.Frame)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol head::values)) = [])
    (ground : MORK.isGroundAtom (.expression (.symbol head::values)) = true) :
    ∃ blocks, List.Forall₂ (fun row block => HE.Spec.Eval.Steps.EquationRowResultsRel
        live (.expression (.symbol head::values)) frame.bindings row.2 row.1 block)
        ((equations.map Equation.toAtom).zipIdx position) blocks ∧
      List.Forall₂ (ClauseInstance (.expression (.symbol head::values))) selected blocks.flatten := by
  have instanceAt (index : Nat) (equation : Equation) :
      ∃ pattern body, HE.Spec.Eval.Steps.AlphaVariantRel live
        (.expression (.symbol head::values)) frame.bindings
        (PeTTa.EagerDFS.Destination.ClauseChoice.pattern equation) equation.body pattern body := by
    let caller : PeTTa.EagerDFS.Destination.Control :=
      {bindings := HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations frame.bindings,
        goals := [],destination := .expression []}
    exact ⟨_,_,ConstructorMatch.protected_petta_clause_he_alpha caller index equation live
      (.expression (.symbol head::values)) frame.bindings⟩
  induction source with
  | nil => exact ⟨[],.nil,.nil⟩
  | @other position equation equations selected different _rest ih =>
      obtain ⟨blocks,rows,related⟩ := ih
      obtain ⟨pattern,body,variant⟩ := instanceAt position equation
      have refused : HE.Spec.Eval.Steps.EquationRowResultsRel live
          (.expression (.symbol head::values)) frame.bindings position equation.toAtom [] := by
        apply HE.Spec.Eval.Steps.EquationRowResultsRel.miss _ _ _ pattern body variant
        intro otherPattern otherBody otherVariant matched output compatible
        obtain ⟨valuation,image⟩ :=
          (ConstructorMatch.fresh_candidate_iff_raw_solution otherVariant closed frame.certified.satisfiable).mp
            ⟨output,matched,compatible⟩
        simp only [PeTTa.EagerDFS.Destination.ClauseChoice.pattern,
          HE.Spec.Type.RuntimeRefinement.applyTypeValuation,List.map_cons,Atom.expression.injEq,
          List.cons.injEq,Atom.symbol.injEq] at image
        exact different image.1
      exact ⟨[]::blocks,.cons refused rows,related⟩
  | @miss position equation equations selected same _ordinary absent _rest ih =>
      obtain ⟨blocks,rows,related⟩ := ih
      obtain ⟨pattern,body,variant⟩ := instanceAt position equation
      have refused : HE.Spec.Eval.Steps.EquationRowResultsRel live
          (.expression (.symbol head::values)) frame.bindings position equation.toAtom [] := by
        apply HE.Spec.Eval.Steps.EquationRowResultsRel.miss _ _ _ pattern body variant
        intro otherPattern otherBody otherVariant matched output compatible
        obtain ⟨substitution,matching⟩ :=
          (ConstructorMatch.fresh_candidate_iff_source_match otherVariant closed ground frame.certified.satisfiable).mp
            ⟨output,matched,compatible⟩
        simp only [PeTTa.EagerDFS.Destination.ClauseChoice.pattern,same] at matching
        cases matching with
        | expr_cons first rest => cases first; exact absent _ rest
      exact ⟨[]::blocks,.cons refused rows,related⟩
  | @hit position equation equations selected substitution same _ordinary matched _rest ih =>
      obtain ⟨blocks,rows,related⟩ := ih
      obtain ⟨pattern,body,variant⟩ := instanceAt position equation
      have full : MORK.MatchAtomRel []
          (PeTTa.EagerDFS.Destination.ClauseChoice.pattern equation)
          (.expression (.symbol head::values)) substitution := by
        simp only [PeTTa.EagerDFS.Destination.ClauseChoice.pattern,same]
        exact .expr_cons .symbol matched
      obtain ⟨image,output,matchedBindings,matching,merged⟩ := ConstructorMatch.source_match_fresh_candidate
        variant closed ground frame.certified.satisfiable full
      exact ⟨[_]::blocks,.cons (.hit _ _ _ _ _ _ _ variant matching merged) rows,
        .cons ⟨rfl,rfl,image,full⟩ related⟩

/-- A complete structural source scan constructs a complete HE frontier.
Every accepted physical copy is paired with its own source substitution;
every omitted row excludes all legal fresh instances. -/
theorem ClauseScan.he_frontier {program : Program} {head : String} {values : List Atom}
    {selected : List ClauseWork} (source : ClauseScan head values 0 program.equations selected)
    (live : List Atom) (frame : HE.Spec.Eval.Completed.Frame)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol head::values)) = [])
    (ground : MORK.isGroundAtom (.expression (.symbol head::values)) = true) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live
        (.expression (.symbol head::values)) frame.bindings works ∧
      List.Forall₂ (ClauseInstance (.expression (.symbol head::values))) selected works := by
  obtain ⟨blocks,rows,related⟩ := source.he_rows live frame closed ground
  exact ⟨blocks.flatten,.completed rows,related⟩

/-- Every independently completed HE frontier pairs with the same source
scan. The relation retains actual raw captures and source positions while
allowing each HE completion its own legal fresh syntax and binding record. -/
theorem ClauseScan.he_frontier_all {program : Program} {head : String} {values : List Atom}
    {selected : List ClauseWork} (source : ClauseScan head values 0 program.equations selected)
    (live : List Atom) (frame : HE.Spec.Eval.Completed.Frame)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol head::values)) = [])
    (ground : MORK.isGroundAtom (.expression (.symbol head::values)) = true)
    {works : List HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live
      (.expression (.symbol head::values)) frame.bindings works) :
    List.Forall₂ (ClauseInstance (.expression (.symbol head::values))) selected works := by
  obtain ⟨chosen,completed,paired⟩ := source.he_frontier live frame closed ground
  have sameSource := completed.source_related frontier
  apply List.forall₂_of_length_eq_of_get (paired.length_eq.trans sameSource.length_eq)
  intro index leftBound rightBound
  have middleBound : index < chosen.length := by rwa [←paired.length_eq]
  have original := paired.get leftBound middleBound
  have sourceFields := sameSource.get middleBound rightBound
  refine ⟨sourceFields.1.symm.trans original.1,sourceFields.2.2.symm.trans original.2.1,?_,?_⟩
  · rw [←sourceFields.2.1]
    exact original.2.2.1
  · rw [←sourceFields.2.1]
    exact original.2.2.2

/-- A covered source call can be empty in HE exactly when its complete
independent source scan is empty. This concerns completion, not a prefix. -/
theorem ClauseScan.he_frontier_empty_iff {program : Program} {head : String} {values : List Atom}
    {selected : List ClauseWork} (source : ClauseScan head values 0 program.equations selected)
    (live : List Atom) (frame : HE.Spec.Eval.Completed.Frame)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol head::values)) = [])
    (ground : MORK.isGroundAtom (.expression (.symbol head::values)) = true)
    {works : List HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live
      (.expression (.symbol head::values)) frame.bindings works) :
    works = [] ↔ selected = [] := by
  have paired := source.he_frontier_all live frame closed ground frontier
  constructor
  · intro empty
    rw [empty] at paired
    exact List.forall₂_nil_right_iff.mp paired
  · intro empty
    rw [empty] at paired
    exact List.forall₂_nil_left_iff.mp paired

/-- The untagged HE tuple protocol cannot transport a scalar `Error` as an
ordinary tuple element in every position. This syntactic admission concerns
the comparison fragment, not either dialect's full source semantics. -/
inductive NoErrorSymbol : Atom → Prop where
  | symbol {name : String} : name ≠ "Error" → NoErrorSymbol (.symbol name)
  | variable (name : String) : NoErrorSymbol (.var name)
  | grounded (value : GroundedValue) : NoErrorSymbol (.grounded value)
  | expression {children : List Atom} :
      (∀ child ∈ children, NoErrorSymbol child) → NoErrorSymbol (.expression children)

theorem NoErrorSymbol.not_error_symbol {atom : Atom} (safe : NoErrorSymbol atom) :
    atom ≠ .symbol "Error" := by
  cases safe <;> simp_all

theorem NoErrorSymbol.children {children : List Atom}
    (safe : NoErrorSymbol (.expression children)) :
    ∀ child ∈ children, NoErrorSymbol child := by
  cases safe with
  | expression children => exact children

theorem NoErrorSymbol.substitute {atom : Atom} (safe : NoErrorSymbol atom)
    (environment : String → Atom)
    (allowed : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars atom, NoErrorSymbol (environment name)) :
    NoErrorSymbol (HE.Spec.Type.RuntimeRefinement.applyTypeValuation environment atom) := by
  induction safe with
  | symbol different =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using NoErrorSymbol.symbol different
  | «variable» name =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using
        allowed name (by simp [HE.Spec.Type.Presentation.TypeSubst.typeVars])
  | grounded scalar =>
      simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using NoErrorSymbol.grounded scalar
  | expression _children ih =>
      simp only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
      apply NoErrorSymbol.expression
      intro atom member
      obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
      apply ih argument present
      intro name used
      apply allowed name
      exact HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem present name used

theorem NoErrorSymbol.tuple_clean {children : List Atom}
    (safe : ∀ child ∈ children, NoErrorSymbol child) :
    HE.isEmptyOrError (.expression children) = false := by
  cases children with
  | nil => simp [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]
  | cons head tail =>
      have different := (safe head List.mem_cons_self).not_error_symbol
      cases head <;>
        simp_all [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]

theorem Value.children {program : Program} {children : List Atom} {scope : List String}
    (value : Value program (.expression children) scope) :
    ∀ child ∈ children, Value program child scope := by
  cases value with
  | unit => intro child member; cases member
  | @constructor head arguments _ passive values =>
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact passive.1.symbol_value
      · exact values child member

theorem Value.constructor_head {program : Program} {head : Atom} {tail : List Atom} {scope : List String}
    (value : Value program (.expression (head::tail)) scope) :
    ∃ name, head = .symbol name ∧ ConstructorHead program name := by
  cases value with
  | constructor passive _values => exact ⟨_,rfl,passive⟩

theorem Value.boolean_clean {program : Program} {atom : Atom} {scope : List String}
    (value : Value program atom scope) :
    HE.isEmptyOrError atom = false := by
  cases value with
  | symbol name nonempty _ordinary =>
      simp [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty,nonempty]
  | «variable» => simp [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]
  | grounded scalar => simp [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]
  | unit => simp [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]
  | @constructor head arguments _ passive _values =>
      have different : head ≠ "Error" := fun same => passive.1.2.2 (by simp [same])
      simp [HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty,different]

theorem NoErrorSymbol.rename {atom : Atom} (safe : NoErrorSymbol atom)
    (names : String → String) : NoErrorSymbol (HE.Spec.Type.RuntimeRefinement.renameTypeVars names atom) := by
  induction safe with
  | symbol different =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      exact .symbol different
  | «variable» name =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      exact .variable (names name)
  | grounded scalar =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      exact .grounded scalar
  | expression _each ih =>
      simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars]
      apply NoErrorSymbol.expression
      intro value member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present

/-- Every stored capture is passive constructor data in the retained name
scope. This structural admission makes no claim about child evaluation. -/
def PassiveEnvironment (program : Program) (scope : List String)
    (environment : HE.Spec.Eval.Entry.Value.Environment) : Prop :=
  ∀ row ∈ environment, Value program row.2.erase scope ∧ NoErrorSymbol row.2.erase

theorem PassiveEnvironment.weaken {program : Program} {scope targetScope : List String}
    {environment : HE.Spec.Eval.Entry.Value.Environment}
    (passive : PassiveEnvironment program scope environment)
    (included : ∀ name ∈ scope, name ∈ targetScope) :
    PassiveEnvironment program targetScope environment :=
  fun row member => ⟨(passive row member).1.weaken included,(passive row member).2⟩

/-- First-hit lookup returns a stored passive capture or the original open
variable. Names outside the admitted scope still introduce no error marker. -/
theorem PassiveEnvironment.resolve {program : Program} {scope : List String}
    {environment : HE.Spec.Eval.Entry.Value.Environment}
    (passive : PassiveEnvironment program scope environment) :
    (∀ name ∈ scope, Value program (HE.Spec.Eval.Entry.Value.resolve environment name).erase scope) ∧
      (∀ name, NoErrorSymbol (HE.Spec.Eval.Entry.Value.resolve environment name).erase) := by
  induction environment with
  | nil =>
      constructor
      · intro name member
        simpa [HE.Spec.Eval.Entry.Value.resolve,List.lookup,HE.Spec.Eval.Entry.Value.erase] using
          (Value.variable (program := program) member)
      · intro name
        simpa [HE.Spec.Eval.Entry.Value.resolve,List.lookup,HE.Spec.Eval.Entry.Value.erase] using
          NoErrorSymbol.variable name
  | cons row rest ih =>
      have tail : PassiveEnvironment program scope rest :=
        fun pair member => passive pair (List.mem_cons_of_mem row member)
      obtain ⟨values,safe⟩ := ih tail
      have stored := passive row List.mem_cons_self
      constructor
      · intro name member
        by_cases same : name = row.1
        · simpa [HE.Spec.Eval.Entry.Value.resolve,List.lookup,same] using stored.1
        · have different : (name == row.1) = false := by simp [same]
          simpa [HE.Spec.Eval.Entry.Value.resolve,List.lookup,different] using values name member
      · intro name
        by_cases same : name = row.1
        · simpa [HE.Spec.Eval.Entry.Value.resolve,List.lookup,same] using stored.2
        · have different : (name == row.1) = false := by simp [same]
          simpa [HE.Spec.Eval.Entry.Value.resolve,List.lookup,different] using safe name

/-- Materialization preserves passive syntax under either rebuilding policy,
including captures carrying held marks or still-open private variables. -/
theorem PassiveEnvironment.substitute {program : Program} {scope : List String}
    {environment : HE.Spec.Eval.Entry.Value.Environment}
    (passive : PassiveEnvironment program scope environment)
    (policy : HE.Spec.Eval.Entry.RebuildPolicy) (value : HE.Spec.Eval.Entry.Value)
    (valid : Value program value.erase scope) (safe : NoErrorSymbol value.erase) :
    Value program (HE.Spec.Eval.Entry.Value.substitute policy
      (HE.Spec.Eval.Entry.Value.resolve environment) value).erase scope ∧
      NoErrorSymbol (HE.Spec.Eval.Entry.Value.substitute policy
        (HE.Spec.Eval.Entry.Value.resolve environment) value).erase := by
  rw [HE.Spec.Eval.Entry.Value.erase_substitute]
  exact ⟨valid.substitute _ passive.resolve.1,safe.substitute _ (fun name _used => passive.resolve.2 name)⟩

/-- A passive binding updates all older captures by the same substitution.
Both newly stored and rewritten rows retain the structural admission. -/
theorem PassiveEnvironment.bind {program : Program} {scope : List String}
    {environment : HE.Spec.Eval.Entry.Value.Environment}
    (passive : PassiveEnvironment program scope environment)
    (policy : HE.Spec.Eval.Entry.RebuildPolicy) (name : String) (value : HE.Spec.Eval.Entry.Value)
    (valid : Value program value.erase scope) (safe : NoErrorSymbol value.erase) :
    PassiveEnvironment program scope (HE.Spec.Eval.Entry.Value.bind policy environment name value) := by
  let resolved := HE.Spec.Eval.Entry.Value.substitute policy
    (HE.Spec.Eval.Entry.Value.resolve environment) value
  have stored : Value program resolved.erase scope ∧ NoErrorSymbol resolved.erase :=
    passive.substitute policy value valid safe
  have singleton : PassiveEnvironment program scope [(name,resolved)] := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact stored
  intro row member
  change row ∈ (name,resolved) :: _ at member
  rcases List.mem_cons.mp member with rfl | member
  · exact stored
  · obtain ⟨previous,present,rfl⟩ := List.mem_map.mp member
    have previousPassive := passive previous (List.mem_of_mem_filter present)
    exact singleton.substitute policy previous.2 previousPassive.1 previousPassive.2

section PassiveUnification
open HE.Spec.Eval.Entry.Value

private theorem passive_unification (program : Program) (scope : List String)
    (policy : HE.Spec.Eval.Entry.RebuildPolicy) :
    (∀ {environment output left right}, AppliedUnifyRel policy environment left right output →
      PassiveEnvironment program scope environment →
      (Value program left.erase scope ∧ NoErrorSymbol left.erase) →
      (Value program right.erase scope ∧ NoErrorSymbol right.erase) →
      PassiveEnvironment program scope output) ∧
    (∀ {environment output left right}, UnifyRel policy environment left right output →
      PassiveEnvironment program scope environment →
      (Value program left.erase scope ∧ NoErrorSymbol left.erase) →
      (Value program right.erase scope ∧ NoErrorSymbol right.erase) →
      PassiveEnvironment program scope output) ∧
    (∀ {environment output left right}, UnifyListRel policy environment left right output →
      PassiveEnvironment program scope environment →
      (∀ value ∈ left, Value program value.erase scope ∧ NoErrorSymbol value.erase) →
      (∀ value ∈ right, Value program value.erase scope ∧ NoErrorSymbol value.erase) →
      PassiveEnvironment program scope output) := by
  let admitted := fun value : HE.Spec.Eval.Entry.Value =>
    Value program value.erase scope ∧ NoErrorSymbol value.erase
  let applied := fun environment left right output (_ : AppliedUnifyRel policy environment left right output) =>
    PassiveEnvironment program scope environment → admitted left → admitted right →
      PassiveEnvironment program scope output
  let ordinary := fun environment left right output (_ : UnifyRel policy environment left right output) =>
    PassiveEnvironment program scope environment → admitted left → admitted right →
      PassiveEnvironment program scope output
  let many := fun environment left right output (_ : UnifyListRel policy environment left right output) =>
    PassiveEnvironment program scope environment → (∀ value ∈ left, admitted value) →
      (∀ value ∈ right, admitted value) → PassiveEnvironment program scope output
  have identical {environment left right} (same : left.erase = right.erase) :
      applied environment left right environment (.identical same) := by
    intro passive _left _right
    exact passive
  have bindLeft {environment name right}
      (absent : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars right.erase) :
      applied environment (.var name) right (bind policy environment name right) (.bindLeft absent) := by
    intro passive _left right
    exact passive.bind policy name _ right.1 right.2
  have bindRight {environment left name} (nonvar : ∀ other, left.erase ≠ .var other)
      (absent : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars left.erase) :
      applied environment left (.var name) (bind policy environment name left) (.bindRight nonvar absent) := by
    intro passive left _right
    exact passive.bind policy name _ left.1 left.2
  have expression {environment output left right earlier later}
      (children : UnifyListRel policy environment left right output)
      (ih : many environment left right output children) :
      applied environment (.expression earlier left) (.expression later right) output (.expression children) := by
    intro passive leftValid rightValid
    simp only [admitted,HE.Spec.Eval.Entry.Value.erase] at leftValid rightValid
    apply ih passive
    · intro value member
      exact ⟨leftValid.1.children value.erase (List.mem_map_of_mem member),
        leftValid.2.children value.erase (List.mem_map_of_mem member)⟩
    · intro value member
      exact ⟨rightValid.1.children value.erase (List.mem_map_of_mem member),
        rightValid.2.children value.erase (List.mem_map_of_mem member)⟩
  have materialized {environment output left right}
      (derived : AppliedUnifyRel policy environment
        (substitute policy (resolve environment) left) (substitute policy (resolve environment) right) output)
      (ih : applied environment _ _ output derived) :
      ordinary environment left right output (.ordinary derived) := by
    intro passive leftValid rightValid
    exact ih passive (passive.substitute policy left leftValid.1 leftValid.2)
      (passive.substitute policy right rightValid.1 rightValid.2)
  have nil (environment) : many environment [] [] environment (.nil environment) := by
    intro passive _left _right
    exact passive
  have cons {environment next output left right lefts rights}
      (head : UnifyRel policy environment left right next)
      (tail : UnifyListRel policy next lefts rights output)
      (ih : ordinary environment left right next head) (it : many next lefts rights output tail) :
      many environment (left :: lefts) (right :: rights) output (.cons head tail) := by
    intro passive leftValid rightValid
    exact it (ih passive (leftValid left List.mem_cons_self) (rightValid right List.mem_cons_self))
      (fun value member => leftValid value (List.mem_cons_of_mem left member))
      (fun value member => rightValid value (List.mem_cons_of_mem right member))
  exact ⟨fun derived => AppliedUnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => UnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => UnifyListRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived⟩

/-- Every reached child in structural matching preserves passive captures.
The induction follows unifier transitions, including materialization and
both variable-binding orientations. -/
theorem PassiveEnvironment.unify {program : Program} {scope : List String}
    {policy : HE.Spec.Eval.Entry.RebuildPolicy} {environment output left right}
    (passive : PassiveEnvironment program scope environment)
    (matched : UnifyRel policy environment left right output)
    (leftValid : Value program left.erase scope ∧ NoErrorSymbol left.erase)
    (rightValid : Value program right.erase scope ∧ NoErrorSymbol right.erase) :
    PassiveEnvironment program scope output :=
  (passive_unification program scope policy).2.1 matched passive leftValid rightValid

/-- Sibling matches use each preceding child's actual reached environment.
The same structural admission is preserved for an arbitrary argument list. -/
theorem PassiveEnvironment.unifyList {program : Program} {scope : List String}
    {policy : HE.Spec.Eval.Entry.RebuildPolicy} {environment output left right}
    (passive : PassiveEnvironment program scope environment)
    (matched : UnifyListRel policy environment left right output)
    (leftValid : ∀ value ∈ left, Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (rightValid : ∀ value ∈ right, Value program value.erase scope ∧ NoErrorSymbol value.erase) :
    PassiveEnvironment program scope output :=
  (passive_unification program scope policy).2.2 matched passive leftValid rightValid

/-- A call's outer applied head need not itself be passive. Matching only
compares its child symbols and passive arguments, after materializing both
lists in the incoming frame. This includes heads with defining equations. -/
theorem PassiveEnvironment.unifyExpression {program : Program} {scope : List String}
    {policy : HE.Spec.Eval.Entry.RebuildPolicy} {environment output left right earlier later}
    (passive : PassiveEnvironment program scope environment)
    (matched : UnifyRel policy environment (.expression earlier left) (.expression later right) output)
    (leftValid : ∀ value ∈ left, Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (rightValid : ∀ value ∈ right, Value program value.erase scope ∧ NoErrorSymbol value.erase) :
    PassiveEnvironment program scope output := by
  cases matched with
  | ordinary derived =>
      simp only [HE.Spec.Eval.Entry.Value.substitute] at derived
      cases derived with
      | identical => exact passive
      | expression children =>
          apply passive.unifyList children
          · intro value member
            obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
            exact passive.substitute policy original (leftValid original present).1 (leftValid original present).2
          · intro value member
            obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
            exact passive.substitute policy original (rightValid original present).1 (rightValid original present).2

end PassiveUnification

/-- Scoped passive data and active first-order code in the shared fragment.
Active applications retain a literal ordinary head; computed operator heads
are outside this comparison grammar. Readiness is not inferred from erasure. -/
inductive CodeRel (program : Program) (scope : List String) : HE.Spec.Eval.Entry.Value → Prop where
  | variable {name : String} : name ∈ scope → CodeRel program scope (.var name)
  | data {value : HE.Spec.Eval.Entry.Value} :
      Value program value.erase scope → NoErrorSymbol value.erase → CodeRel program scope value
  | active {head : String} {arguments : List HE.Spec.Eval.Entry.Value} :
      OrdinaryHead head → (∀ argument ∈ arguments, CodeRel program scope argument) →
      CodeRel program scope (.expression .active (.symbol head :: arguments))

/-- Code admission depends on stored equation membership, not its order. -/
theorem CodeRel.perm_program {program other : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (same : program.equations.Perm other.equations)
    (source : CodeRel program scope value) : CodeRel other scope value := by
  induction source with
  | «variable» member => exact .variable member
  | data value safe => exact .data (value.perm_program same) safe
  | active ordinary _ ih => exact .active ordinary ih

theorem CodeRel.occurs_covered {program : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value) :
    ∀ name, HE.Spec.Match.Merge.AtomOccurs value.erase name → name ∈ scope := by
  induction code with
  | «variable» member =>
      intro name occurs
      simp only [HE.Spec.Eval.Entry.Value.erase] at occurs
      cases occurs
      exact member
  | data valid _safe => exact valid.variables
  | @active head arguments _ordinary _each ih =>
      intro name occurs
      simp only [HE.Spec.Eval.Entry.Value.erase,List.map_cons] at occurs
      cases occurs with
      | expression member occurrence =>
          rcases List.mem_cons.mp member with rfl | member
          · cases occurrence
          · obtain ⟨child,present,same⟩ := List.mem_map.mp member
            cases same
            exact ih child present name occurrence

theorem CodeRel.vars_covered {program : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value) :
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars value.erase, name ∈ scope := by
  intro name member
  exact code.occurs_covered name ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr member)

theorem CodeRel.safe {program : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value) :
    NoErrorSymbol value.erase := by
  induction code with
  | «variable» => simpa only [HE.Spec.Eval.Entry.Value.erase] using NoErrorSymbol.variable _
  | data _valid safe => exact safe
  | active ordinary _each ih =>
      simp only [HE.Spec.Eval.Entry.Value.erase,List.map_cons]
      apply NoErrorSymbol.expression
      intro atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact .symbol (fun same => ordinary.2.2 (by simp [same]))
      · obtain ⟨child,present,same⟩ := List.mem_map.mp member
        cases same
        exact ih child present

/-- A variable operator cannot silently become a defining head through a
capture in the shared first-order fragment. Both dialects retain their own
rules for inputs outside this admission. -/
theorem CodeRel.no_variable_head {program : Program} {scope : List String}
    (readiness : HE.Spec.Eval.Entry.Status) (name : String)
    (arguments : List HE.Spec.Eval.Entry.Value) :
    ¬CodeRel program scope (.expression readiness (.var name :: arguments)) := by
  intro code
  cases code with
  | data valid _safe =>
      simp only [HE.Spec.Eval.Entry.Value.erase,List.map_cons] at valid
      cases valid

theorem CodeRel.active_of_not_value {program : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value)
    (pending : ¬Value program value.erase scope) : value.status = .active := by
  cases code with
  | «variable» => simp only [HE.Spec.Eval.Entry.Value.status]
  | data valid _safe => exact (pending valid).elim
  | active => simp only [HE.Spec.Eval.Entry.Value.status]

theorem OrdinaryHead.symbol_code {program : Program} {scope : List String} {head : String}
    (ordinary : OrdinaryHead head) : CodeRel program scope (.symbol head) := by
  apply CodeRel.data
  · simpa only [HE.Spec.Eval.Entry.Value.erase] using
      (ordinary.symbol_value (program := program) (scope := scope))
  · simpa only [HE.Spec.Eval.Entry.Value.erase] using
      (NoErrorSymbol.symbol (fun same => ordinary.2.2 (by simp [same])))

theorem CodeRel.children {program : Program} {scope : List String}
    {status : HE.Spec.Eval.Entry.Status} {children : List HE.Spec.Eval.Entry.Value}
    (code : CodeRel program scope (.expression status children)) :
    ∀ child ∈ children, CodeRel program scope child := by
  cases code with
  | data valid safe =>
      intro child member
      simp only [HE.Spec.Eval.Entry.Value.erase] at valid safe
      exact .data (valid.children child.erase (List.mem_map_of_mem member))
        (safe.children child.erase (List.mem_map_of_mem member))
  | active ordinary each =>
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact ordinary.symbol_code
      · exact each child member

/-- Substitution inserts passive scoped captures. Active parents remain active;
open passive data retains its admission under either rebuilding policy.
An arbitrary active call is not a permitted capture for this law. -/
theorem CodeRel.substitute {program : Program} {scope targetScope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value)
    (policy : HE.Spec.Eval.Entry.RebuildPolicy) (environment : String → HE.Spec.Eval.Entry.Value)
    (allowed : ∀ name ∈ scope,
      Value program (environment name).erase targetScope ∧ NoErrorSymbol (environment name).erase) :
    CodeRel program targetScope (HE.Spec.Eval.Entry.Value.substitute policy environment value) := by
  induction code with
  | «variable» member =>
      simpa only [HE.Spec.Eval.Entry.Value.substitute] using
        (CodeRel.data (allowed _ member).1 (allowed _ member).2)
  | @data value valid safe =>
      apply CodeRel.data
      · rw [HE.Spec.Eval.Entry.Value.erase_substitute]
        exact valid.substitute _ (fun name member => (allowed name member).1)
      · rw [HE.Spec.Eval.Entry.Value.erase_substitute]
        apply safe.substitute
        intro name used
        exact (allowed name (valid.variables name
          ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr used))).2
  | @active head arguments ordinary _each ih =>
      have active (before after : Atom) :
          HE.Spec.Eval.Entry.Value.rebuildStatus policy .active before after = .active := by
        cases policy <;> simp [HE.Spec.Eval.Entry.Value.rebuildStatus]
      simp only [HE.Spec.Eval.Entry.Value.substitute,active,List.map_cons]
      apply CodeRel.active ordinary
      intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present

theorem CodeRel.rename {program : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value) (names : String → String) :
    CodeRel program (scope.map names) (HE.Spec.Eval.Entry.Value.rename names value) :=
  code.substitute .preserve (fun name => .var (names name))
    (fun name member => ⟨by
      simpa only [HE.Spec.Eval.Entry.Value.erase] using
        (Value.variable (program := program) (name := names name) (List.mem_map_of_mem member)),
      by simpa only [HE.Spec.Eval.Entry.Value.erase] using NoErrorSymbol.variable (names name)⟩)

/-- Enlarging the retained name scope preserves both active code and passive
open captures. It does not change any entry status. -/
theorem CodeRel.weaken {program : Program} {scope targetScope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value)
    (included : ∀ name ∈ scope, name ∈ targetScope) : CodeRel program targetScope value := by
  induction code with
  | «variable» member => exact .variable (included _ member)
  | data valid safe => exact .data (valid.weaken included) safe
  | active ordinary _each ih => exact .active ordinary ih

/-- Materialized children retain code admission across the sibling traversal.
The capture restriction is structural, independent of child completion. -/
theorem CodeRel.read_passive {program : Program} {scope : List String}
    {value : HE.Spec.Eval.Entry.Value} (code : CodeRel program scope value)
    (policy : HE.Spec.Eval.Completed.Policy) (frame : HE.Spec.Eval.Completed.Frame)
    (passive : PassiveEnvironment program scope frame.environment) :
    CodeRel program scope (frame.read policy value) :=
  code.substitute policy.rebuilding (HE.Spec.Eval.Entry.Value.resolve frame.environment)
    (fun name member => ⟨passive.resolve.1 name member,passive.resolve.2 name⟩)

theorem CodeRel.closed {program : Program} {value : HE.Spec.Eval.Entry.Value}
    (code : CodeRel program [] value) : ∀ name, ¬HE.Spec.Match.Merge.AtomOccurs value.erase name := by
  intro name occurs
  exact List.not_mem_nil (code.occurs_covered name occurs)

theorem CodeRel.read_closed {program : Program} {value : HE.Spec.Eval.Entry.Value}
    (code : CodeRel program [] value) (policy : HE.Spec.Eval.Completed.Policy)
    (frame : HE.Spec.Eval.Completed.Frame) : frame.read policy value = value :=
  HE.Spec.Eval.Completed.Frame.read_variable_free policy frame value code.closed

theorem CodeRel.closed_vars {program : Program} {value : HE.Spec.Eval.Entry.Value}
    (code : CodeRel program [] value) : HE.Spec.Type.Presentation.TypeSubst.typeVars value.erase = [] := by
  cases shape : HE.Spec.Type.Presentation.TypeSubst.typeVars value.erase with
  | nil => rfl
  | cons name rest =>
      exact (List.not_mem_nil (code.vars_covered name (by rw [shape]; exact List.mem_cons_self))).elim

private theorem closed_ground (atom : Atom) :
    (∀ name, ¬HE.Spec.Match.Merge.AtomOccurs atom name) → MORK.isGroundAtom atom = true := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, ∀ name, ¬HE.Spec.Match.Merge.AtomOccurs atom name) →
        MORK.isGroundAtom.isGroundList atoms = true) with
  | symbol | grounded => intro _closed; rfl
  | var name => intro closed; exact (closed name (.var name)).elim
  | expression atoms ih =>
      intro closed
      exact ih (fun atom member name occurs => closed name (.expression member occurs))
  | nil => rfl
  | cons atom atoms first rest =>
      rename_i closed
      simp only [MORK.isGroundAtom.isGroundList,Bool.and_eq_true]
      exact ⟨first (closed atom List.mem_cons_self),rest (fun item member =>
        closed item (List.mem_cons_of_mem _ member))⟩

theorem CodeRel.ground {program : Program} {value : HE.Spec.Eval.Entry.Value}
    (code : CodeRel program [] value) : MORK.isGroundAtom value.erase = true :=
  closed_ground _ code.closed

/-- A rule body is admitted as active code in its own pattern-variable scope.
This is a syntactic condition, independent of an evaluator's output. -/
def CodeProgram (program : Program) : Prop :=
  ∀ equation ∈ program.equations, CodeRel program
    (HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol equation.head::equation.arguments)))
    (HE.Spec.Eval.Entry.Value.ofAtom equation.body)

theorem CodeProgram.perm_program {program other : Program}
    (same : program.equations.Perm other.equations) (code : CodeProgram program) :
    CodeProgram other := by
  intro equation member
  exact (code equation (same.mem_iff.mpr member)).perm_program same

theorem CodeProgram.range {program : Program} (code : CodeProgram program) : RangeRestricted program := by
  intro equation member name occurs
  exact (code equation member).vars_covered name
    (by simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using occurs)

/-- Clause arguments contain passive constructor patterns. This is a syntax
admission, independent of any evaluator result or matching implementation. -/
def ConstructorPatterns (program : Program) : Prop :=
  ∀ equation ∈ program.equations, OrdinaryHead equation.head ∧
    ∀ argument ∈ equation.arguments,
      Value program argument (HE.Spec.Type.Presentation.TypeSubst.typeVars
        (.expression (.symbol equation.head :: equation.arguments))) ∧ NoErrorSymbol argument

/-- Pattern capture inserts passive source values, while tuple traversal is
only control: the tuple itself need not be a passive value. -/
private theorem match_data_capture {program : Program} {seed after : MORK.Subst}
    {pattern subject : Atom} (matched : MORK.MatchAtomRel seed pattern subject after) :
    (Value program subject → NoErrorSymbol subject →
      (∀ pair ∈ seed, Value program pair.2 ∧ NoErrorSymbol pair.2) →
      ∀ pair ∈ after, Value program pair.2 ∧ NoErrorSymbol pair.2) ∧
    (∀ patterns values, pattern = .expression patterns → subject = .expression values →
      (∀ value ∈ values, Value program value ∧ NoErrorSymbol value) →
      (∀ pair ∈ seed, Value program pair.2 ∧ NoErrorSymbol pair.2) →
      ∀ pair ∈ after, Value program pair.2 ∧ NoErrorSymbol pair.2) := by
  induction matched with
  | var_fresh _fresh =>
      constructor
      · intro valid safe seeded pair member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨valid,safe⟩
        · exact seeded pair member
      · intro patterns values impossible
        cases impossible
  | var_bound _found =>
      constructor
      · intro _valid _safe seeded; exact seeded
      · intro patterns values impossible; cases impossible
  | symbol | grounded =>
      constructor
      · intro _valid _safe seeded; exact seeded
      · intro patterns values impossible; cases impossible
  | expr_nil =>
      constructor
      · intro _valid _safe seeded; exact seeded
      · intro patterns values _left _right _values seeded; exact seeded
  | @expr_cons before middle after pattern subject patterns subjects first tail headIH tailIH =>
      have forest (values : ∀ value ∈ subject::subjects, Value program value ∧ NoErrorSymbol value)
          (seeded : ∀ pair ∈ before, Value program pair.2 ∧ NoErrorSymbol pair.2) :
          ∀ pair ∈ after, Value program pair.2 ∧ NoErrorSymbol pair.2 :=
        tailIH.2 patterns subjects rfl rfl
          (fun value member => values value (List.mem_cons_of_mem _ member))
          (headIH.1 (values subject List.mem_cons_self).1
            (values subject List.mem_cons_self).2 seeded)
      constructor
      · intro valid safe seeded
        exact forest (fun value member => ⟨valid.children value member,safe.children value member⟩) seeded
      · intro left right sameLeft sameRight values seeded
        cases sameLeft
        cases sameRight
        exact forest values seeded

/-- Every actual capture is safe data. This is earned from the selected
source match, not assumed for its eventual evaluation. -/
theorem ClauseScan.captured_values {program : Program} {head : String} {values : List Atom}
    {position : Nat} {equations : List Equation} {selected : List ClauseWork}
    (source : ClauseScan head values position equations selected)
    (data : ∀ value ∈ values, Value program value ∧ NoErrorSymbol value) :
    ∀ item ∈ selected, ∀ pair ∈ item.2.1, Value program pair.2 ∧ NoErrorSymbol pair.2 := by
  induction source with
  | nil => simp
  | other _different _rest ih | miss _same _ordinary _absent _rest ih => exact ih
  | hit _same _ordinary matched _rest ih =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact (match_data_capture matched).2 _ _ rfl rfl data (by simp)
      · exact ih item member

private theorem source_variables (atom : Atom) :
    MORK.atomFreeVars atom = HE.Spec.Type.Presentation.TypeSubst.typeVars atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      MORK.atomFreeVars.atomFreeVarsList atoms = HE.Spec.Type.Presentation.TypeSubst.typeVarsList atoms) with
  | symbol | var | grounded => rfl
  | expression atoms ih => exact ih
  | nil => rfl
  | cons atom atoms first rest => exact congrArg₂ List.append first rest

/-- A captured pattern variable reads one of the actual safe entries, rather
than a guessed representative or a reconstructed implementation table. -/
theorem ClauseInstance.variable_data {program : Program} {query : Atom} {selected : ClauseWork}
    {work : HE.Spec.Eval.Steps.EquationWork} (related : ClauseInstance query selected work)
    (captured : ∀ pair ∈ selected.2.1, Value program pair.2 ∧ NoErrorSymbol pair.2)
    {name : String} (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars work.left) :
    Value program (MORK.applySubst selected.2.1 (.var name)) ∧
      NoErrorSymbol (MORK.applySubst selected.2.1 (.var name)) := by
  obtain ⟨value,found⟩ := related.2.2.2.lookup_covered name (by rwa [source_variables])
  have entry := found
  unfold MORK.Subst.lookup at entry
  obtain ⟨pair,present,rfl⟩ := Option.map_eq_some_iff.mp entry
  simpa only [MORK.applySubst,found,Option.getD_some] using
    captured pair (List.mem_of_find?_eq_some present)

theorem equationSpace.no_annotations (program : Program) (target : Atom) :
    HE.Spec.Type.AnnotationTypesRel target (equationSpace program).atoms [] := by
  change HE.Spec.Type.AnnotationTypesRel target (program.equations.map Equation.toAtom) []
  induction program.equations with
  | nil => exact .nil
  | cons equation equations rest =>
      exact .skip (by simp [Equation.toAtom]) rest

/-- Every passive value has a complete nonempty source type query in the
equation-only space. This uses intrinsic grounded types, not an evaluator. -/
theorem Value.he_types {program : Program} {atom : Atom} {scope : List String}
    (value : Value program atom scope) :
    ∃ actual later, HE.Spec.Type.StorageTypesRel (equationSpace program) atom (actual::later) := by
  cases value with
  | symbol name _nonempty _ordinary =>
      exact ⟨_,[],.symbolUndefined (equationSpace.no_annotations _ _)⟩
  | «variable» member => exact ⟨_,[],.variable _ _⟩
  | grounded scalar =>
      cases scalar with
      | int number => exact ⟨_,[],.groundedKnown (.int number) (by decide +kernel)⟩
      | bool boolean => exact ⟨_,[],.groundedKnown (.bool boolean) (by decide +kernel)⟩
      | string text => exact ⟨_,[],.groundedKnown (.string text) (by decide +kernel)⟩
      | custom type payload =>
          by_cases undefined : Atom.symbol type = Atom.undefinedType
          · exact ⟨_,[],.groundedUndefined (by simpa only [←undefined] using
              (HE.Spec.Type.IntrinsicGroundedTypeRel.custom type payload))⟩
          · exact ⟨_,[],.groundedKnown (.custom type payload) undefined⟩
  | unit => exact ⟨_,[],.unit _⟩
  | constructor _passive _values =>
      exact ⟨_,[],.expressionUndefined (equationSpace.no_annotations _ _)⟩

/-- An undefined constructor head earns a complete empty HE frontier against
the actual equation table, for every retained caller constraint record. -/
theorem ConstructorHead.he_frontier_empty {program : Program} {head : String}
    (passive : ConstructorHead program head) (arguments live : List Atom) (incoming : HE.Bindings) :
    HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live
      (.expression (.symbol head::arguments)) incoming [] := by
  let caller : PeTTa.EagerDFS.Destination.Control :=
    {bindings := HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming,
      goals := [],destination := .expression []}
  have emptyChoices (control : PeTTa.EagerDFS.Destination.Control) :
      PeTTa.EagerDFS.Destination.ClauseChoice.choices program control head arguments
        (.expression []) [] = [] := by
    unfold PeTTa.EagerDFS.Destination.ClauseChoice.choices
    apply List.filterMap_eq_nil_iff.mpr
    intro position _member
    cases row : program.equations[position]? with
    | none => simp [PeTTa.EagerDFS.Destination.ClauseChoice.trial,row]
    | some equation =>
        have different := passive.2 equation (List.mem_of_getElem? row)
        simp [PeTTa.EagerDFS.Destination.ClauseChoice.trial,
          PeTTa.EagerDFS.Destination.ClauseChoice.attempt,row,different]
  obtain ⟨works,completed,related⟩ := ConstructorMatch.protected_petta_choices_he_frontier
    program caller head arguments (.expression []) [] live incoming
    (fun environment =>
      (PeTTa.EagerDFS.Destination.solves_binding_equations environment incoming).symm)
  rw [emptyChoices] at related
  cases related
  exact completed

private theorem Value.he_noninterpreted {program : Program} {allowed : List String}
    (value : HE.Spec.Eval.Entry.Value) (valid : Value program value.erase allowed)
    (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) (scope : List String)
    (policy : HE.Spec.Eval.Completed.Policy)
    (unassigned : HE.Spec.Eval.Completed.FrameUnassignedOn frame value.erase)
    {action : HE.Spec.Eval.Entry.Action}
    (entered : HE.Spec.Eval.Entry.Rel policy.reentry value.status value.erase Atom.undefinedType action)
    (simple : action ≠ .interpret) :
    HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope value Atom.undefinedType frame [(value,frame)] (policy := policy) := by
  have read := unassigned.read_eq policy
  cases action with
  | deliver =>
      simpa only [read] using
        (HE.Spec.Eval.Completed.AtomRel.delivered (space := equationSpace program) (dispatch := noForeign)
          (lookup := HE.Spec.Eval.Completed.rawLookup) (live := live) (scope := scope)
          (value := value) (expected := Atom.undefinedType) (frame := frame) (policy := policy)
          (by simpa only [read] using entered))
  | cast =>
      obtain ⟨actual,later,types⟩ := valid.he_types
      simpa only [read] using
        (HE.Spec.Eval.Completed.AtomRel.undefined_cast (space := equationSpace program) (dispatch := noForeign)
          (lookup := HE.Spec.Eval.Completed.rawLookup) (live := live) (scope := scope)
          (value := value) (frame := frame) (policy := policy) (actual := actual) (later := later)
          (by simpa only [read] using entered)
          (by simpa only [read,HE.Spec.Eval.Completed.rawLookup,HE.Spec.Type.rawTypeLookupRel] using types))
  | interpret => exact (simple rfl).elim

mutual
/-- Passive, packet-safe data whose free variables are unassigned completes under HE without changing its
syntax or frame. Every nested occurrence status and local policy is allowed;
the resulting annotation is supplied by the actual source publication rules. -/
theorem Value.he_completes_unassigned {program : Program} {allowed : List String} (value : HE.Spec.Eval.Entry.Value) :
    Value program value.erase allowed → NoErrorSymbol value.erase →
    ∀ (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) (scope : List String)
      (policy : HE.Spec.Eval.Completed.Policy),
    HE.Spec.Eval.Completed.FrameUnassignedOn frame value.erase →
    ∃ output, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope value Atom.undefinedType frame [(output,frame)] (policy := policy) ∧
      output.erase = value.erase := by
  let space := equationSpace program
  match value with
  | .symbol name =>
      intro valid _safe frame live scope policy unassigned
      obtain ⟨action,entered⟩ := HE.Spec.Eval.Entry.total policy.reentry .active (.symbol name) Atom.undefinedType
      have simple : action ≠ .interpret := by intro same; subst action; cases entered
      exact ⟨_,Value.he_noninterpreted _ valid frame live scope policy unassigned
        (by simpa only [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Entry.Value.status] using entered) simple,rfl⟩
  | .var name =>
      intro valid _safe frame live scope policy unassigned
      have entered : HE.Spec.Eval.Entry.Rel policy.reentry .active (.var name)
          Atom.undefinedType .deliver :=
        .pass (by simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty])
          (.variable name) (Or.inr (Or.inr rfl))
      exact ⟨_,Value.he_noninterpreted _ valid frame live scope policy unassigned (action := .deliver)
        (by simpa only [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Entry.Value.status] using entered)
        (by decide +kernel),rfl⟩
  | .grounded scalar =>
      intro valid _safe frame live scope policy unassigned
      obtain ⟨action,entered⟩ := HE.Spec.Eval.Entry.total policy.reentry .active (.grounded scalar) Atom.undefinedType
      have simple : action ≠ .interpret := by intro same; subst action; cases entered
      exact ⟨_,Value.he_noninterpreted _ valid frame live scope policy unassigned
        (by simpa only [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Entry.Value.status] using entered) simple,rfl⟩
  | .expression readiness children =>
      intro valid safe frame live scope policy unassigned
      have read := unassigned.read_eq policy
      obtain ⟨action,entered⟩ := HE.Spec.Eval.Entry.total policy.reentry readiness
        (.expression (children.map HE.Spec.Eval.Entry.Value.erase)) Atom.undefinedType
      by_cases simple : action ≠ .interpret
      · refine ⟨_,Value.he_noninterpreted _ valid frame live scope policy unassigned ?_ simple,rfl⟩
        simpa only [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Entry.Value.status] using entered
      · have same : action = .interpret := Classical.not_not.mp simple
        subst action
        have values : ∀ child ∈ children, Value program child.erase allowed := by
          intro child member
          exact (show Value program (.expression (children.map HE.Spec.Eval.Entry.Value.erase)) allowed by
            simpa only [HE.Spec.Eval.Entry.Value.erase] using valid).children
              child.erase (List.mem_map_of_mem member)
        have safeValues : ∀ child ∈ children, NoErrorSymbol child.erase := by
          intro child member
          exact (show NoErrorSymbol (.expression (children.map HE.Spec.Eval.Entry.Value.erase)) by
            simpa only [HE.Spec.Eval.Entry.Value.erase] using safe).children
              child.erase (List.mem_map_of_mem member)
        have childUnassigned : ∀ child ∈ children,
            HE.Spec.Eval.Completed.FrameUnassignedOn frame child.erase := by
          intro child member name used
          apply unassigned name
          simpa only [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Type.Presentation.TypeSubst.typeVars] using
            HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
              (List.mem_map_of_mem member) name used
        obtain ⟨outputs,tuple,erased⟩ := values_he_tuple_unassigned children values safeValues
          frame (Atom.undefinedType::live) scope policy childUnassigned
        cases children with
        | nil => cases entered
        | cons operator arguments =>
            obtain ⟨name,head,passive⟩ := Value.constructor_head
              (by simpa only [HE.Spec.Eval.Entry.Value.erase,List.map_cons] using valid)
            have outputErase : (HE.Spec.Eval.Entry.Value.expression .active outputs).erase =
                (HE.Spec.Eval.Entry.Value.expression readiness (operator::arguments)).erase := by
              simpa only [HE.Spec.Eval.Entry.Value.erase] using congrArg Atom.expression erased
            have outputValue : Value program (HE.Spec.Eval.Entry.Value.expression .active outputs).erase allowed := by
              rw [outputErase]
              exact valid
            have called : HE.Spec.Eval.Completed.CallRel space noForeign HE.Spec.Eval.Completed.rawLookup
                live scope (.expression .active outputs) Atom.undefinedType frame
                [(.expression .active outputs,frame)] (policy := policy) := by
              apply HE.Spec.Eval.Completed.CallRel.absent
              · exact fun failed => outputValue.not_stopped (Or.inr failed)
              · rw [outputErase]
                simpa only [HE.Spec.Eval.Entry.Value.erase,List.map_cons,head] using
                  passive.1.he_non_grounded (arguments.map HE.Spec.Eval.Entry.Value.erase)
              · rw [outputErase]
                simpa only [HE.Spec.Eval.Entry.Value.erase,List.map_cons,head] using
                  passive.he_frontier_empty (arguments.map HE.Spec.Eval.Entry.Value.erase)
                    (Atom.undefinedType::live) frame.bindings
            have outputUnassigned : HE.Spec.Eval.Completed.FrameUnassignedOn frame
                (HE.Spec.Eval.Entry.Value.expression .active outputs).erase := by
              rw [outputErase]
              exact unassigned
            have outputRead := outputUnassigned.read_eq policy
            have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
                (fun result : HE.Spec.Eval.Completed.Result => HE.isErrorAtom result.1.erase)
                ([((.expression .active outputs),frame)].map (HE.Spec.Eval.Completed.readResult policy))
                [((.expression .active outputs),frame)] := by
              have noError : HE.isErrorAtom (HE.Spec.Eval.Entry.Value.expression .active outputs).erase = false := by
                have clean := outputValue.boolean_clean
                simp only [HE.isEmptyOrError,Bool.or_eq_false_iff] at clean
                exact clean.2
              simpa [HE.Spec.Eval.Completed.readResult,outputRead,noError] using
                (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
                  (isError := fun result : HE.Spec.Eval.Completed.Result => HE.isErrorAtom result.1.erase)
                  (raw := [((.expression .active outputs),frame)])
                  ⟨((.expression .active outputs),frame),by simp,noError⟩)
            have complete := HE.Spec.Eval.Completed.AtomRel.tuple
              (space := space) (dispatch := noForeign) (lookup := HE.Spec.Eval.Completed.rawLookup)
              (live := live) (scope := scope) (value := .expression readiness (operator::arguments))
              (expected := Atom.undefinedType) (frame := frame) (readiness := readiness)
              (operator := operator) (arguments := arguments) (policy := policy)
              (by simpa only [read,HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Entry.Value.status,List.map_cons] using entered)
              read (by
                rw [head]
                exact (HE.Spec.Type.StorageTypesRel.symbolUndefined (equationSpace.no_annotations _ _)).occurrences)
              tuple (by
                simpa only [List.append_nil] using
                  (HE.Spec.Eval.Completed.CallsRel.cons (children := [((.expression .active outputs),frame)])
                    (rest := []) called .nil)) priority
            refine ⟨HE.Spec.Eval.Entry.Value.publish policy.marking
              (HE.Spec.Eval.Entry.Value.expression readiness (operator::arguments)).erase
              frame.source (.expression .active outputs),?_,?_⟩
            · simpa only [List.map_cons,List.map_nil,HE.Spec.Eval.Completed.publishResult,read] using complete
            · simpa only [HE.Spec.Eval.Entry.Value.erase_publish] using outputErase
termination_by sizeOf value
decreasing_by all_goals simp_wf

/-- Passive annotated operands construct a complete singleton tuple packet.
The packet carries the actual child values and their marks. -/
theorem values_he_tuple_unassigned {program : Program} {allowed : List String} (children : List HE.Spec.Eval.Entry.Value) :
    (∀ child ∈ children, Value program child.erase allowed) →
    (∀ child ∈ children, NoErrorSymbol child.erase) →
    ∀ (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) (scope : List String)
      (policy : HE.Spec.Eval.Completed.Policy),
    (∀ child ∈ children, HE.Spec.Eval.Completed.FrameUnassignedOn frame child.erase) →
    ∃ outputs, HE.Spec.Eval.Completed.TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope children frame [(.expression .active outputs,frame)] (policy := policy) ∧
      outputs.map HE.Spec.Eval.Entry.Value.erase = children.map HE.Spec.Eval.Entry.Value.erase := by
  match children with
  | [] =>
      intro _values _safe frame live scope policy _unassigned
      exact ⟨[],.nil,rfl⟩
  | first::rest =>
      intro values safe frame live scope policy unassigned
      have firstValue := values first List.mem_cons_self
      have firstSafe := safe first List.mem_cons_self
      have restValues := fun child member => values child (List.mem_cons_of_mem first member)
      have restSafe := fun child member => safe child (List.mem_cons_of_mem first member)
      have firstUnassigned := unassigned first List.mem_cons_self
      have restUnassigned := fun child member => unassigned child (List.mem_cons_of_mem first member)
      cases rest with
      | nil =>
          obtain ⟨output,completed,erased⟩ := Value.he_completes_unassigned first firstValue firstSafe frame live scope policy firstUnassigned
          have outputValue : Value program output.erase allowed := by rw [erased]; exact firstValue
          have clean := outputValue.boolean_clean
          refine ⟨[output],?_,by simp [erased]⟩
          simpa [HE.Spec.Eval.Completed.tupleSingleton,clean] using
            (HE.Spec.Eval.Completed.TupleRel.singleton completed)
      | cons second remaining =>
          obtain ⟨output,completed,erased⟩ := Value.he_completes_unassigned first firstValue firstSafe frame
            (.expression ((second::remaining).map HE.Spec.Eval.Entry.Value.erase)::live) scope policy firstUnassigned
          obtain ⟨outputs,tailCompleted,tailErased⟩ := values_he_tuple_unassigned (second::remaining) restValues restSafe frame (output.erase::live) scope policy restUnassigned
          have outputValue : Value program output.erase allowed := by rw [erased]; exact firstValue
          have clean : HE.isEmptyOrError (HE.Spec.Eval.Entry.Value.expression .active outputs).erase = false := by
            have allSafe : ∀ atom ∈ (second::remaining).map HE.Spec.Eval.Entry.Value.erase,
                NoErrorSymbol atom := by
              intro atom member
              obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
              exact restSafe child present
            simpa only [HE.Spec.Eval.Entry.Value.erase,tailErased] using
              NoErrorSymbol.tuple_clean allSafe
          have branches := HE.Spec.Eval.Completed.TupleBranchesRel.continuing
            (space := equationSpace program) (dispatch := noForeign) (lookup := HE.Spec.Eval.Completed.rawLookup)
            (live := live) (scope := scope) (policy := policy) (head := (output,frame))
            (heads := []) (tail := second::remaining)
            (children := [((.expression .active outputs),frame)]) (rest := [])
            outputValue.not_stopped tailCompleted .nil
          refine ⟨output::outputs,?_,by simp [erased,tailErased]⟩
          simpa [HE.Spec.Eval.Completed.tuplePrepend,clean] using
            (HE.Spec.Eval.Completed.TupleRel.cons completed branches)

termination_by sizeOf children
decreasing_by all_goals simp_wf <;> omega
end

/-- Closed passive data earns the unassigned-entry premise independently of
its chosen retained frame. The open and closed profiles use one completion proof. -/
theorem Value.he_completes {program : Program} (value : HE.Spec.Eval.Entry.Value)
    (valid : Value program value.erase) (safe : NoErrorSymbol value.erase)
    (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) (scope : List String)
    (policy : HE.Spec.Eval.Completed.Policy) :
    ∃ output, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope value Atom.undefinedType frame [(output,frame)] (policy := policy) ∧
      output.erase = value.erase := by
  apply Value.he_completes_unassigned value valid safe frame live scope policy
  have read := HE.Spec.Eval.Completed.Frame.read_variable_free policy frame value valid.variable_free
  simpa only [read] using HE.Spec.Eval.Completed.FrameUnassignedOn.after_read policy frame value

/-- The closed tuple law is the empty-scope instance of passive tuple completion. -/
theorem values_he_tuple {program : Program} (children : List HE.Spec.Eval.Entry.Value)
    (values : ∀ child ∈ children, Value program child.erase)
    (safe : ∀ child ∈ children, NoErrorSymbol child.erase)
    (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) (scope : List String)
    (policy : HE.Spec.Eval.Completed.Policy) :
    ∃ outputs, HE.Spec.Eval.Completed.TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope children frame [(.expression .active outputs,frame)] (policy := policy) ∧
      outputs.map HE.Spec.Eval.Entry.Value.erase = children.map HE.Spec.Eval.Entry.Value.erase := by
  apply values_he_tuple_unassigned children values safe frame live scope policy
  intro child member
  have read := HE.Spec.Eval.Completed.Frame.read_variable_free policy frame child
    (values child member).variable_free
  simpa only [read] using HE.Spec.Eval.Completed.FrameUnassignedOn.after_read policy frame child

/-- Passive open data completes after its captures are materialized. The
same completion induction handles either reentry and rebuilding policy. -/
theorem PassiveEnvironment.he_completes {program : Program} {allowed : List String}
    (frame : HE.Spec.Eval.Completed.Frame)
    (passive : PassiveEnvironment program allowed frame.environment)
    (value : HE.Spec.Eval.Entry.Value)
    (valid : Value program value.erase allowed) (safe : NoErrorSymbol value.erase)
    (live : List Atom) (scope : List String) (policy : HE.Spec.Eval.Completed.Policy) :
    ∃ output, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope value Atom.undefinedType frame [(output,frame)] (policy := policy) ∧
      output.erase = (frame.read policy value).erase := by
  obtain ⟨readValid,readSafe⟩ := passive.substitute policy.rebuilding value valid safe
  obtain ⟨output,completed,erased⟩ := Value.he_completes_unassigned (frame.read policy value)
    readValid readSafe frame live scope policy (HE.Spec.Eval.Completed.FrameUnassignedOn.after_read policy frame value)
  exact ⟨output,completed.input_read_eq (HE.Spec.Eval.Completed.Frame.read_idempotent policy frame value),erased⟩

/-- Bound-variable entry is a specialization of passive materialization, not
an additional evaluator induction. -/
theorem PassiveEnvironment.variable_he_completes {program : Program} {allowed : List String}
    (frame : HE.Spec.Eval.Completed.Frame)
    (passive : PassiveEnvironment program allowed frame.environment)
    (name : String) (member : name ∈ allowed) (live : List Atom) (scope : List String)
    (policy : HE.Spec.Eval.Completed.Policy) :
    ∃ output, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (.var name) Atom.undefinedType frame [(output,frame)] (policy := policy) ∧
      output.erase = (frame.read policy (.var name)).erase := by
  apply PassiveEnvironment.he_completes frame passive (.var name)
  · simpa only [HE.Spec.Eval.Entry.Value.erase] using Value.variable (program := program) member
  · simpa only [HE.Spec.Eval.Entry.Value.erase] using NoErrorSymbol.variable name

theorem Value.not_refusal {program : Program} {atom : Atom} {scope : List String}
    (valid : Value program atom scope) :
    atom ≠ Atom.notReducible := by
  cases valid <;> simp_all [Atom.notReducible]

theorem Value.not_function_pending {program : Program} {value : HE.Spec.Eval.Entry.Value}
    {scope : List String} (valid : Value program value.erase scope)
    (policy : HE.Spec.Eval.Completed.Policy) :
    ¬HE.Spec.Eval.Completed.FunctionPending policy value := by
  rintro ⟨⟨body,shape⟩,_ready⟩
  rw [shape] at valid
  cases valid with
  | constructor passive _values => exact passive.1.2.2 (by simp)

theorem Evaluation.input_ordinary {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom} (source : Evaluation program bindings expression answers) :
    Value program (MORK.applySubst bindings expression) ∨
      ∃ head arguments, OrdinaryHead head ∧
        MORK.applySubst bindings expression = .expression (.symbol head::arguments) := by
  cases source with
  | «variable» valid => exact Or.inl valid
  | symbol valid => exact Or.inl valid
  | grounded scalar => exact Or.inl (.grounded scalar)
  | unit => exact Or.inl .unit
  | @constructor _bindings head arguments answers passive _children =>
      exact Or.inr ⟨head,MORK.applySubst.applySubstList bindings arguments,passive.1,by
        simp only [MORK.applySubst,MORK.applySubst.applySubstList]⟩
  | @call _bindings head arguments answers defined _children =>
      exact Or.inr ⟨head,MORK.applySubst.applySubstList bindings arguments,defined.1,by
        simp only [MORK.applySubst,MORK.applySubst.applySubstList]⟩

/-- An ordinary source body's producer cannot become a minimal function
wrapper merely because its fresh variables were materialized. -/
theorem Evaluation.input_not_function {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom} (source : Evaluation program bindings expression answers)
    {value : HE.Spec.Eval.Entry.Value} (represented : value.erase = MORK.applySubst bindings expression)
    (policy : HE.Spec.Eval.Completed.Policy) :
    ¬HE.Spec.Eval.Completed.FunctionPending policy value := by
  rcases source.input_ordinary with valid | ⟨head,arguments,ordinary,image⟩
  · exact (show Value program value.erase by rw [represented]; exact valid).not_function_pending policy
  · rintro ⟨⟨body,shape⟩,_ready⟩
    rw [represented,image] at shape
    have same : head = "function" := Atom.symbol.inj (List.cons.inj (Atom.expression.inj shape)).1
    exact ordinary.2.2 (by simp [same])

theorem Evaluation.input_returnable {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom} (source : Evaluation program bindings expression answers) :
    MORK.applySubst bindings expression ≠ Atom.notReducible ∧
      ¬HE.Spec.Eval.IsEmptyOrErrorRel (MORK.applySubst bindings expression) := by
  rcases source.input_ordinary with valid | ⟨head,arguments,ordinary,image⟩
  · exact ⟨valid.not_refusal,valid.not_stopped⟩
  · rw [image]
    constructor
    · simp [Atom.notReducible]
    · have clean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
      simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty,clean]

/-- The full return gate is constructed from the passive-data source phase;
neither refusal nor failure is inferred from an empty execution prefix. -/
theorem Value.he_return {program : Program} (value : HE.Spec.Eval.Entry.Value)
    (valid : Value program value.erase) (safe : NoErrorSymbol value.erase)
    (original : HE.Spec.Eval.Entry.Value) (frame : HE.Spec.Eval.Completed.Frame)
    (live : List Atom) (scope : List String) (policy : HE.Spec.Eval.Completed.Policy) :
    ∃ output, HE.Spec.Eval.Completed.ReturnRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope original Atom.undefinedType value frame [(output,frame)] (policy := policy) ∧
      output.erase = value.erase := by
  obtain ⟨output,completed,erased⟩ := Value.he_completes value valid safe frame live scope policy
  exact ⟨output,.evaluate valid.not_refusal valid.not_stopped completed,erased⟩

private theorem passive_equation_bodies {program : Program}
    (policy : HE.Spec.Eval.Completed.Policy) (live : List Atom) (scope : List String)
    (original : HE.Spec.Eval.Entry.Value) (before : HE.Spec.Eval.Completed.Frame)
    {works : List HE.Spec.Eval.Steps.EquationWork} {environments : List HE.Spec.Eval.Entry.Value.Environment}
    (paired : List.Forall₂ (fun work environment =>
      HE.Spec.Eval.Entry.Value.UnifyRel policy.rebuilding before.environment original
        (HE.Spec.Eval.Entry.Value.ofAtom work.pattern) environment ∧
      HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate work.bindings
        (HE.Spec.Eval.Entry.Value.eraseEnvironment environment)) works environments)
    {answers : List Atom}
    (instances : List.Forall₂ (fun work answer => Value program answer ∧ NoErrorSymbol answer ∧
      ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation work.bindings →
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation work.body = answer) works answers) :
    ∃ results, HE.Spec.Eval.Completed.EquationBodiesRel (equationSpace program) noForeign
        HE.Spec.Eval.Completed.rawLookup live scope original Atom.undefinedType before works results (policy := policy) ∧
      results.map (fun result => result.1.erase) = answers ∧
      List.Forall₂ (fun work result => result.2.bindings = work.bindings) works results := by
  induction paired generalizing answers with
  | nil => cases instances; exact ⟨[],.nil,rfl,.nil⟩
  | @cons work environment works environments one rest ih =>
      cases instances with
      | @cons _ answer _ answers admitted remaining =>
          let after : HE.Spec.Eval.Completed.Frame := ⟨work.bindings,environment,one.2⟩
          let body := after.read policy (HE.Spec.Eval.Entry.Value.ofAtom work.body)
          have bodyErase : body.erase = answer := by
            simpa only [body,after,HE.Spec.Eval.Completed.Frame.read,
              HE.Spec.Eval.Entry.Value.erase_substitute_environment,HE.Spec.Eval.Entry.Value.erase_ofAtom] using
              one.2.forced_read work.body answer admitted.2.2
          have bodyValue : Value program body.erase := by rw [bodyErase]; exact admitted.1
          have bodySafe : NoErrorSymbol body.erase := by rw [bodyErase]; exact admitted.2.1
          obtain ⟨output,returned,erased⟩ := Value.he_return body bodyValue bodySafe original after live scope policy
          obtain ⟨results,tail,tailErased,tailFrames⟩ := ih remaining
          refine ⟨(output,after)::results,?_,?_,.cons rfl tailFrames⟩
          · simpa only [List.singleton_append] using
              (HE.Spec.Eval.Completed.EquationBodiesRel.ordinary_cons (space := equationSpace program)
                (dispatch := noForeign) (lookup := HE.Spec.Eval.Completed.rawLookup)
                (live := live) (scope := scope) (original := original) (expected := Atom.undefinedType)
                (frame := before) (work := work) (works := works) (output := after)
                (children := [(output,after)]) (rest := results) (policy := policy)
                rfl one.1 (bodyValue.not_function_pending policy) returned tail)
          · simp only [List.map_cons,erased,bodyErase,tailErased]

/-- A complete physical frontier with model-determined passive bodies
constructs the full HE call phase. The admission premises concern only source
constraints and data; contextual unifiers, frames and return executions are
constructed here. Every stored occurrence contributes one result. -/
theorem passive_equation_call {program : Program}
    (policy : HE.Spec.Eval.Completed.Policy) (live : List Atom) (scope : List String)
    (original : HE.Spec.Eval.Entry.Value) (before : HE.Spec.Eval.Completed.Frame)
    {works : List HE.Spec.Eval.Steps.EquationWork} {answers : List Atom}
    (ordinary : HE.Spec.Eval.NonGroundedCallRel noForeign original.erase)
    (clean : ¬HE.Spec.Eval.IsErrorRel original.erase)
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program)
      (Atom.undefinedType::live) original.erase before.bindings works)
    (nonempty : works ≠ [])
    (instances : List.Forall₂ (fun work answer => Value program answer ∧ NoErrorSymbol answer ∧
      ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation work.bindings →
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation work.body = answer) works answers) :
    ∃ results, HE.Spec.Eval.Completed.CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope original Atom.undefinedType before results (policy := policy) ∧
      results.map (fun result => result.1.erase) = answers ∧
      List.Forall₂ (fun work result => result.2.bindings = work.bindings) works results := by
  obtain ⟨environments,paired⟩ := HE.Spec.Eval.Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) before.certified frontier
  obtain ⟨results,bodies,erased,frames⟩ := passive_equation_bodies policy live scope original before paired instances
  exact ⟨results,.equations clean ordinary frontier nonempty bodies,erased,frames⟩

/-- Materialization follows an actual completed frontier occurrence and its
reached certified frame. The RHS can contain further calls; only its source
variables must be covered by the selected raw pattern. -/
theorem frontier_body_read
    {space : HE.Space} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel space live query incoming works)
    (present : work ∈ works) (substitution : MORK.Subst)
    (instanceImage : MORK.applySubst substitution work.left = query)
    (covered : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars work.right,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars work.left)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (after : HE.Spec.Eval.Completed.Frame) (represented : after.bindings = work.bindings)
    (policy : HE.Spec.Eval.Completed.Policy) :
    (after.read policy (HE.Spec.Eval.Entry.Value.ofAtom work.body)).erase =
      MORK.applySubst substitution work.right := by
  obtain ⟨matched,occurrence⟩ := frontier.occurrence present
  have certified : HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate work.bindings
      (HE.Spec.Eval.Entry.Value.eraseEnvironment after.environment) := by
    simpa only [represented] using after.certified
  have exactRead := ConstructorMatch.query_occurrence_template_readout substitution occurrence
    instanceImage covered closed certified
  simpa only [HE.Spec.Eval.Completed.Frame.read,HE.Spec.Eval.Entry.Value.erase_substitute_environment,
    HE.Spec.Eval.Entry.Value.erase_ofAtom] using exactRead

/-- The completed frontier retains enough source origin to inherit the
program's body-variable coverage at every selected physical occurrence. -/
theorem equationSpace.work_inherits {program : Program} (property : Atom → Atom → Prop)
    (source : ∀ equation ∈ program.equations,
      property (.expression (.symbol equation.head::equation.arguments)) equation.body)
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works) :
    property work.left work.right := by
  obtain ⟨_matched,occurrence⟩ := frontier.occurrence present
  obtain ⟨equation,member,shape⟩ := List.mem_map.mp (List.mem_of_getElem? occurrence.stored)
  change Atom.expression [.symbol "=",.expression (.symbol equation.head::equation.arguments),equation.body] =
    Atom.expression [.symbol "=",work.left,work.right] at shape
  have first := List.cons.inj (List.cons.inj (Atom.expression.inj shape)).2
  have second := List.cons.inj first.2
  rw [←first.1,←second.1]
  exact source equation member

theorem RangeRestricted.work_covered {program : Program} (range : RangeRestricted program)
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works) :
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars work.right,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars work.left :=
  equationSpace.work_inherits (fun pattern body =>
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars body,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars pattern) range frontier present

/-- Complete frontier membership supplies passive fresh pattern children. -/
theorem ConstructorPatterns.work_pattern_children {program : Program}
    (patterns : ConstructorPatterns program)
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works) :
    ∃ children,
      HE.Spec.Eval.Entry.Value.ofAtom work.pattern = .expression .active children ∧
      ∀ child ∈ children,
        Value program child.erase (HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern) ∧
          NoErrorSymbol child.erase := by
  have inherited : ∃ head arguments,
      work.left = .expression (.symbol head :: arguments) ∧
      ∀ child ∈ (.symbol head :: arguments : List Atom),
        Value program child (HE.Spec.Type.Presentation.TypeSubst.typeVars work.left) ∧ NoErrorSymbol child := by
    apply equationSpace.work_inherits (fun pattern _body => ∃ head arguments,
      pattern = .expression (.symbol head :: arguments) ∧
      ∀ child ∈ (.symbol head :: arguments : List Atom),
        Value program child (HE.Spec.Type.Presentation.TypeSubst.typeVars pattern) ∧ NoErrorSymbol child) ?_ frontier present
    intro equation member
    obtain ⟨ordinary,valid⟩ := patterns equation member
    refine ⟨equation.head,equation.arguments,rfl,?_⟩
    intro child present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨ordinary.symbol_value,.symbol (fun same => ordinary.2.2 (by simp [same]))⟩
    · exact valid child present
  obtain ⟨_matched,occurrence⟩ := frontier.occurrence present
  obtain ⟨names,_injective,patternShape,_bodyShape,_fresh⟩ := occurrence.selected.1
  obtain ⟨head,arguments,leftShape,rawValid⟩ := inherited
  have patternImage := HE.EquationFreshening.alphaRename_eq patternShape
  have scopeImage : HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern =
      (HE.Spec.Type.Presentation.TypeSubst.typeVars work.left).map names := by
    rw [patternImage,HE.Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
  refine ⟨((.symbol head :: arguments).map (HE.Spec.Type.RuntimeRefinement.renameTypeVars names)).map HE.Spec.Eval.Entry.Value.ofAtom,?_,?_⟩
  · rw [patternImage,leftShape]
    simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars,HE.Spec.Eval.Entry.Value.ofAtom,List.map_cons,List.map_map,Function.comp_def]
  · intro child member
    obtain ⟨renamed,renamedMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨original,rawMember,rfl⟩ := List.mem_map.mp renamedMember
    rw [HE.Spec.Eval.Entry.Value.erase_ofAtom,scopeImage]
    exact ⟨(rawValid original rawMember).1.rename names,(rawValid original rawMember).2.rename names⟩

/-- An actual fresh clause match preserves passive captures in the caller
scope extended by the fresh pattern names. -/
theorem ConstructorPatterns.clause_entry_passive {program : Program}
    (patterns : ConstructorPatterns program)
    {scope : List String} {rebuilding : HE.Spec.Eval.Entry.RebuildPolicy}
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works)
    {environment output : HE.Spec.Eval.Entry.Value.Environment}
    {readiness : HE.Spec.Eval.Entry.Status} {callChildren : List HE.Spec.Eval.Entry.Value}
    (passive : PassiveEnvironment program scope environment)
    (values : ∀ child ∈ callChildren, Value program child.erase scope ∧ NoErrorSymbol child.erase)
    (unified : HE.Spec.Eval.Entry.Value.UnifyRel rebuilding environment
      (.expression readiness callChildren) (HE.Spec.Eval.Entry.Value.ofAtom work.pattern) output) :
    PassiveEnvironment program (scope ++ HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern) output := by
  obtain ⟨children,shape,valid⟩ := patterns.work_pattern_children frontier present
  rw [shape] at unified
  apply (passive.weaken (fun _ member => List.mem_append.mpr (Or.inl member))).unifyExpression unified
  · intro child member
    exact ⟨(values child member).1.weaken (fun _ included => List.mem_append.mpr (Or.inl included)),
      (values child member).2⟩
  · intro child member
    exact ⟨(valid child member).1.weaken (fun _ included => List.mem_append.mpr (Or.inr included)),
      (valid child member).2⟩

/-- A frontier's actual alpha-variant body is admitted in its fresh pattern
scope, before any body evaluation or environment materialization. -/
theorem CodeProgram.work_body_code {program : Program} (code : CodeProgram program)
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works) :
    CodeRel program (HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern)
      (HE.Spec.Eval.Entry.Value.ofAtom work.body) := by
  obtain ⟨_matched,occurrence⟩ := frontier.occurrence present
  obtain ⟨names,_injective,patternShape,bodyShape,_fresh⟩ := occurrence.selected.1
  have rawCode : CodeRel program (HE.Spec.Type.Presentation.TypeSubst.typeVars work.left)
      (HE.Spec.Eval.Entry.Value.ofAtom work.right) :=
    equationSpace.work_inherits (fun pattern body => CodeRel program
      (HE.Spec.Type.Presentation.TypeSubst.typeVars pattern) (HE.Spec.Eval.Entry.Value.ofAtom body))
      code frontier present
  have freshCode := rawCode.rename names
  rw [HE.Spec.Eval.Entry.Value.rename_ofAtom,←HE.EquationFreshening.alphaRename_eq bodyShape,
    ←HE.Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars,
    ←HE.EquationFreshening.alphaRename_eq patternShape] at freshCode
  exact freshCode

/-- Clause entry earns both passive reached captures and code admission for
the materialized body. This is a local law with no child-completion premise. -/
theorem ConstructorPatterns.clause_entry {program : Program}
    (patterns : ConstructorPatterns program) (code : CodeProgram program)
    {scope : List String} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works)
    (policy : HE.Spec.Eval.Completed.Policy)
    {environment : HE.Spec.Eval.Entry.Value.Environment} (after : HE.Spec.Eval.Completed.Frame)
    {readiness : HE.Spec.Eval.Entry.Status} {callChildren : List HE.Spec.Eval.Entry.Value}
    (passive : PassiveEnvironment program scope environment)
    (values : ∀ child ∈ callChildren, Value program child.erase scope ∧ NoErrorSymbol child.erase)
    (unified : HE.Spec.Eval.Entry.Value.UnifyRel policy.rebuilding environment
      (.expression readiness callChildren) (HE.Spec.Eval.Entry.Value.ofAtom work.pattern) after.environment) :
    PassiveEnvironment program (scope ++ HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern) after.environment ∧
    CodeRel program (scope ++ HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern)
      (after.read policy (HE.Spec.Eval.Entry.Value.ofAtom work.body)) := by
  have reached := patterns.clause_entry_passive frontier present passive values unified
  refine ⟨reached,?_⟩
  exact ((code.work_body_code frontier present).weaken
    (fun _ member => List.mem_append.mpr (Or.inr member))).read_passive policy after reached

/-- The actual selected work item extends its caller only privately. All
protected binding and continuation observations keep the same solution theory. -/
theorem ClauseInstance.caller_observations
    {space : HE.Space} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    {selected : ClauseWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel space live query incoming works)
    (present : work ∈ works) (related : ClauseInstance query selected work)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = []) :
    HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
      (HE.EquationScope.visibleNames live query incoming) incoming work.bindings := by
  obtain ⟨matched,occurrence⟩ := frontier.occurrence present
  exact ConstructorMatch.fresh_candidate_caller_theory selected.2.1 occurrence.selected.1
    related.2.2.1 closed ⟨matched,occurrence.selected.2,occurrence.result.1⟩

/-- Fresh instantiation preserves retained names and the caller's complete
old support, so successive private instances can be composed. -/
theorem ClauseInstance.caller_extension
    {space : HE.Space} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    {selected : ClauseWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel space live query incoming works)
    (present : work ∈ works) (related : ClauseInstance query selected work)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = []) :
    HE.Spec.Bindings.ScopeObservation.ConservativeExtension
      (live.flatMap HE.Spec.Type.Presentation.TypeSubst.typeVars) incoming work.bindings := by
  obtain ⟨_matched,occurrence⟩ := frontier.occurrence present
  refine ⟨fun name member => (occurrence.result.1.support name).mpr (Or.inr member),
    (related.caller_observations frontier present closed).restrict ?_⟩
  intro name member
  exact (HE.EquationScope.visible_closed_iff closed name).mpr (List.mem_append.mp member)

/-- Every model of the reached HE work item materializes the same raw body
as its paired source substitution, including templates containing more calls. -/
theorem ClauseInstance.body_model {program : Program} (range : RangeRestricted program)
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    {selected : ClauseWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works) (related : ClauseInstance query selected work)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (valuation : String → Atom)
    (satisfied : HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation work.bindings) :
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation work.body =
      MORK.applySubst selected.2.1 selected.2.2 := by
  obtain ⟨matched,occurrence⟩ := frontier.occurrence present
  have candidate : HE.Spec.Eval.Steps.UnifyCandidateRel query work.pattern incoming work.bindings :=
    ⟨matched,occurrence.selected.2,occurrence.result.1⟩
  have patternFixed := ((candidate.solutions valuation).mp satisfied).1.symm.trans
    (HE.Spec.Type.Presentation.applyTypeValuation_of_typeVars_eq_nil valuation query closed)
  simpa only [related.2.1] using ConstructorMatch.source_template_model selected.2.1
    occurrence.selected.1 related.2.2.1 (range.work_covered frontier present) valuation patternFixed

/-- The fresh body in an actual reached frame is closed executable code.
Rule scope, safe captures and the certified source constraints earn the
claim; no completion of the recursive body is a premise. -/
theorem ClauseInstance.body_code {program : Program} (code : CodeProgram program)
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {works : List HE.Spec.Eval.Steps.EquationWork} {work : HE.Spec.Eval.Steps.EquationWork}
    {selected : ClauseWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live query incoming works)
    (present : work ∈ works) (related : ClauseInstance query selected work)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (captured : ∀ pair ∈ selected.2.1, Value program pair.2 ∧ NoErrorSymbol pair.2)
    (after : HE.Spec.Eval.Completed.Frame) (reached : after.bindings = work.bindings)
    (policy : HE.Spec.Eval.Completed.Policy) :
    CodeRel program [] (after.read policy (HE.Spec.Eval.Entry.Value.ofAtom work.body)) := by
  obtain ⟨matched,occurrence⟩ := frontier.occurrence present
  have candidate : HE.Spec.Eval.Steps.UnifyCandidateRel query work.pattern incoming work.bindings :=
    ⟨matched,occurrence.selected.2,occurrence.result.1⟩
  obtain ⟨names,_injective,patternShape,_bodyShape,_fresh⟩ := occurrence.selected.1
  have freshCode := code.work_body_code frontier present
  rw [HE.EquationFreshening.alphaRename_eq patternShape,
    HE.Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars] at freshCode
  apply freshCode.substitute policy.rebuilding (HE.Spec.Eval.Entry.Value.resolve after.environment)
  intro freshName member
  obtain ⟨name,inScope,same⟩ := List.mem_map.mp member
  subst freshName
  have fixed : (HE.Spec.Eval.Entry.Value.eraseEnvironment after.environment).apply (.var (names name)) =
      MORK.applySubst selected.2.1 (.var name) := by
    apply after.certified.forced_read
    intro valuation satisfied
    rw [reached] at satisfied
    have patternFixed := ((candidate.solutions valuation).mp satisfied).1.symm.trans
      (HE.Spec.Type.Presentation.applyTypeValuation_of_typeVars_eq_nil valuation query closed)
    rw [HE.EquationFreshening.alphaRename_eq patternShape,
      HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars] at patternFixed
    have equal := patternFixed.trans
      ((ConstructorMatch.source_read selected.2.1 work.left).trans related.2.2.1).symm
    simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation,Function.comp_apply] using
      (HE.Spec.Type.Presentation.applyTypeValuation_eq_iff_on_typeVars _ _ _).mp equal name inScope
  have image : (HE.Spec.Eval.Entry.Value.resolve after.environment (names name)).erase =
      MORK.applySubst selected.2.1 (.var name) := by
    rw [HE.Spec.Eval.Entry.Value.erase_resolve]
    simpa only [HE.Spec.Type.Presentation.TypeSubst.apply] using fixed
  have safe := related.variable_data captured inScope
  exact ⟨by rw [image]; exact safe.1,by rw [image]; exact safe.2⟩

namespace RecursiveTransport

open HE.Spec.Eval.Completed (Policy Result AtomRel TupleRel TupleBranchesRel CallsRel CallRel
  EquationBodiesRel ReturnRel tuplePrepend tupleSingleton readResult publishResult)

private theorem unit_frontier (program : Program) (live : List Atom)
    (frame : HE.Spec.Eval.Completed.Frame) :
    HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live (.expression []) frame.bindings [] := by
  have row (position : Nat) (equation : Equation) : HE.Spec.Eval.Steps.EquationRowResultsRel
      live (.expression []) frame.bindings position equation.toAtom [] := by
    let control : PeTTa.EagerDFS.Destination.Control :=
      {bindings := [],goals := [],destination := .expression []}
    have variant := ConstructorMatch.protected_petta_clause_he_alpha control position equation live
      (.expression []) frame.bindings
    apply HE.Spec.Eval.Steps.EquationRowResultsRel.miss _ _ _ _ _ variant
    intro pattern body fresh matched output merged
    obtain ⟨valuation,image⟩ :=
      (ConstructorMatch.fresh_candidate_iff_raw_solution fresh rfl frame.certified.satisfiable).mp
        ⟨output,matched,merged⟩
    simp only [PeTTa.EagerDFS.Destination.ClauseChoice.pattern,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,List.map_cons,Atom.expression.injEq,List.cons_ne_nil] at image
  have rows (equations : List Equation) (position : Nat) : List.Forall₂
      (fun entry block => HE.Spec.Eval.Steps.EquationRowResultsRel live (.expression []) frame.bindings entry.2 entry.1 block)
      ((equations.map Equation.toAtom).zipIdx position)
      (List.replicate equations.length ([] : List HE.Spec.Eval.Steps.EquationWork)) := by
    induction equations generalizing position with
    | nil => exact .nil
    | cons equation equations ih => exact .cons (row position equation) (ih (position+1))
  have empty (n : Nat) : (List.replicate n ([] : List HE.Spec.Eval.Steps.EquationWork)).flatten = [] := by
    induction n <;> simp_all
  simpa only [empty] using HE.Spec.Eval.Steps.EquationFrontierRel.completed (space := equationSpace program)
    (rows program.equations 0)

def SafeResult (program : Program) (result : Result) : Prop :=
  Value program result.1.erase ∧ NoErrorSymbol result.1.erase

def Packet (program : Program) (result : Result) : Prop :=
  ∃ children, result.1 = .expression .active children ∧
    ∀ child ∈ children, Value program child.erase ∧ NoErrorSymbol child.erase

theorem Packet.clean {program : Program} {result : Result} (packet : Packet program result) :
    HE.isEmptyOrError result.1.erase = false := by
  obtain ⟨children,shape,values⟩ := packet
  rw [shape]
  simp only [HE.Spec.Eval.Entry.Value.erase]
  apply NoErrorSymbol.tuple_clean
  intro child member
  obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
  exact (values value present).2

theorem Packet.prepend {program : Program} {head : HE.Spec.Eval.Entry.Value} {result : Result}
    (safe : Value program head.erase ∧ NoErrorSymbol head.erase) (packet : Packet program result) :
    Packet program (tuplePrepend head result) := by
  have clean := packet.clean
  obtain ⟨children,shape,values⟩ := packet
  refine ⟨head::children,?_,?_⟩
  · unfold tuplePrepend
    rw [clean]
    simp only [Bool.false_eq_true,↓reduceIte,shape]
  · intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact safe
    · exact values value member

/-- Assembly only fills a tuple's already-evaluated prefix. It neither runs
an evaluator nor invents another argument traversal. -/
def assemblePrefix (values : List HE.Spec.Eval.Entry.Value) (result : Result) : Result :=
  values.foldr tuplePrepend result

theorem assemblePrefix_nil : assemblePrefix [] = id := by funext result; rfl

theorem assemblePrefix_singleton (head : HE.Spec.Eval.Entry.Value) :
    assemblePrefix [head] = tuplePrepend head := by funext result; rfl

theorem assemblePrefix_snoc (values : List HE.Spec.Eval.Entry.Value) (head : HE.Spec.Eval.Entry.Value)
    (result : Result) : assemblePrefix (values++[head]) result = assemblePrefix values (tuplePrepend head result) := by
  simp only [assemblePrefix,List.foldr_append,List.foldr_cons,List.foldr_nil]

theorem empty_tuple_branches
    {space dispatch lookup live scope heads results policy}
    (derived : TupleBranchesRel space dispatch lookup live scope [] heads results (policy := policy))
    (clean : ∀ head ∈ heads, ¬ HE.Spec.Eval.IsEmptyOrErrorRel head.1.erase) :
    results = heads.map tupleSingleton := by
  match derived with
  | .nil => rfl
  | .stopped failed _rest => exact (clean _ List.mem_cons_self failed).elim
  | @TupleBranchesRel.continuing _ _ _ _ _ _ head heads children rest _ ordinary child tail =>
      cases child
      have boolean : HE.isEmptyOrError head.1.erase = false := by
        apply Bool.eq_false_iff.mpr
        intro stopped
        exact clean head List.mem_cons_self
          ((HE.Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr stopped)
      have later := empty_tuple_branches tail (fun head member => clean head (List.mem_cons_of_mem _ member))
      simp only [List.map_cons,List.map_nil,List.singleton_append,tupleSingleton,boolean]
      rw [later]
      simp [tuplePrepend,HE.Spec.Eval.Entry.Value.erase,HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]
termination_by heads.length
decreasing_by simp_wf

/-- Completed tuple and call phases compose at the source publication
boundary, retaining each actual result frame and nested readiness mark. -/
theorem expression_complete {program : Program} {head : String}
    (ordinary : OrdinaryHead head) (arguments : List HE.Spec.Eval.Entry.Value)
    (closed : CodeRel program [] (.expression .active (.symbol head::arguments)))
    (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) {rows raw : List Result}
    (tuple : TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      (Atom.undefinedType::live) scope (.symbol head::arguments) frame rows (policy := policy))
    (calls : CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope Atom.undefinedType rows raw (policy := policy))
    (safe : ∀ result ∈ raw, SafeResult program result) :
    AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
      (.expression .active (.symbol head::arguments)) Atom.undefinedType frame
      (raw.map (publishResult policy (.expression (.symbol head::arguments.map HE.Spec.Eval.Entry.Value.erase))))
      (policy := policy) := by
  let input : HE.Spec.Eval.Entry.Value := .expression .active (.symbol head::arguments)
  have read := closed.read_closed policy frame
  have resultRead : raw.map (readResult policy) = raw := by
    calc
      _ = raw.map id := by
        apply List.map_congr_left
        intro result member
        exact Prod.ext (HE.Spec.Eval.Completed.Frame.read_variable_free policy result.2 result.1
          (safe result member).1.variable_free) rfl
      _ = raw := List.map_id _
  have noError (result : Result) (member : result ∈ raw) : HE.isErrorAtom result.1.erase = false := by
    have clean := (safe result member).1.boolean_clean
    simp only [HE.isEmptyOrError,Bool.or_eq_false_iff] at clean
    exact clean.2
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => HE.isErrorAtom result.1.erase) (raw.map (readResult policy)) raw := by
    rw [resultRead]
    cases raw with
    | nil => exact .allErrors (by simp)
    | cons first rest =>
        have filter : (first::rest).filter (fun result => !HE.isErrorAtom result.1.erase) = first::rest := by
          apply List.filter_eq_self.mpr
          intro result member
          simp only [noError result member,Bool.not_false]
        simpa only [filter] using
          (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
            (isError := fun result : Result => HE.isErrorAtom result.1.erase)
            (raw := first::rest) ⟨first,List.mem_cons_self,noError first List.mem_cons_self⟩)
  have headClean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
  have entered : HE.Spec.Eval.Entry.Rel policy.reentry (frame.read policy input).status
      (frame.read policy input).erase Atom.undefinedType .interpret := by
    rw [read]
    simp only [HE.Spec.Eval.Entry.Value.status,HE.Spec.Eval.Entry.Value.erase,List.map_cons]
    apply HE.Spec.Eval.Entry.Rel.expression
    · simp [HE.Spec.Eval.IsEmptyOrErrorRel,
        HE.Spec.Eval.IsErrorRel,Atom.empty,headClean]
    · simp [Atom.undefinedType,Atom.atomType,Atom.expressionType,Atom.variableType]
    · exact Or.inr rfl
  simpa only [read,input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using
    (AtomRel.tuple entered read
      (by simpa only [HE.Spec.Eval.Entry.Value.erase,Multiset.coe_singleton] using
        (HE.Spec.Type.StorageTypesRel.symbolUndefined (equationSpace.no_annotations program (.symbol head))).occurrences)
      tuple calls priority)

theorem assemblePrefix_empty {program : Program} (values : List HE.Spec.Eval.Entry.Value)
    (safe : ∀ value ∈ values, Value program value.erase ∧ NoErrorSymbol value.erase)
    (frame : HE.Spec.Eval.Completed.Frame) :
    assemblePrefix values (.expression .active [],frame) = (.expression .active values,frame) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have later := ih (fun value member => safe value (List.mem_cons_of_mem _ member))
      change tuplePrepend first (assemblePrefix rest (.expression .active [],frame)) = _
      rw [later]
      have clean : HE.isEmptyOrError (HE.Spec.Eval.Entry.Value.expression .active rest).erase = false := by
        exact Packet.clean (result := (.expression .active rest,frame))
          ⟨rest,rfl,fun value member => safe value (List.mem_cons_of_mem _ member)⟩
      simp only [tuplePrepend,clean,Bool.false_eq_true,↓reduceIte]

def invocationAtoms (target : Target) (values : List Atom) : List Atom :=
  match target with
  | .data => values
  | .function head => .symbol head::values

theorem invocationAtoms_snoc (target : Target) (values : List Atom) (head : Atom) :
    invocationAtoms target (values++[head]) = invocationAtoms target values++[head] := by
  cases target <;> rfl

private theorem substitution_list (bindings : MORK.Subst) (atoms : List Atom) :
    MORK.applySubst.applySubstList bindings atoms = atoms.map (MORK.applySubst bindings) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp only [MORK.applySubst.applySubstList,List.map_cons,ih]

private theorem expression_view (value : HE.Spec.Eval.Entry.Value) {head : String} {arguments : List Atom}
    (image : value.erase = .expression (.symbol head::arguments)) :
    ∃ readiness children, value = .expression readiness (.symbol head::children) ∧
      children.map HE.Spec.Eval.Entry.Value.erase = arguments := by
  cases value with
  | symbol | var | grounded => simp [HE.Spec.Eval.Entry.Value.erase] at image
  | expression readiness children =>
      cases children with
      | nil => simp [HE.Spec.Eval.Entry.Value.erase] at image
      | cons operator children =>
          have shape : operator.erase = .symbol head ∧ children.map HE.Spec.Eval.Entry.Value.erase = arguments := by
            simpa only [HE.Spec.Eval.Entry.Value.erase,List.map_cons,Atom.expression.injEq,List.cons.injEq] using image
          have same : operator = .symbol head := by
            cases operator <;> simp_all [HE.Spec.Eval.Entry.Value.erase]
          exact ⟨readiness,children,by rw [same],shape.2⟩

private theorem invocation_code {program : Program} {head : String}
    {arguments : List Atom} {values : List HE.Spec.Eval.Entry.Value}
    (ordinary : OrdinaryHead head)
    (image : values.map HE.Spec.Eval.Entry.Value.erase = .symbol head :: arguments)
    (safe : ∀ value ∈ values, Value program value.erase ∧ NoErrorSymbol value.erase) :
    CodeRel program [] (.expression .active values) := by
  obtain ⟨readiness,children,shape,_⟩ := expression_view (.expression .active values)
    (by simpa only [HE.Spec.Eval.Entry.Value.erase] using congrArg Atom.expression image)
  have same : values = .symbol head :: children :=
    (HE.Spec.Eval.Entry.Value.expression.inj shape).2
  rw [same] at safe ⊢
  exact .active ordinary (fun value member =>
    .data (safe value (List.mem_cons_of_mem _ member)).1
      (safe value (List.mem_cons_of_mem _ member)).2)

theorem constructor_call_exact {program : Program} {head : String} {arguments : List Atom}
    (constructor : ConstructorHead program head) {value : HE.Spec.Eval.Entry.Value}
    (image : value.erase = .expression (.symbol head::arguments))
    {policy : Policy} {live : List Atom} {scope : List String} {expected : Atom}
    {frame : HE.Spec.Eval.Completed.Frame} {results : List Result}
    (source : CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope value expected frame results (policy := policy)) : results = [(value,frame)] := by
  have nonGrounded := constructor.1.he_non_grounded arguments
  cases source with
  | error failed =>
      obtain ⟨tail,shape⟩ := failed
      have same : head = "Error" := Atom.symbol.inj (List.cons.inj (Atom.expression.inj (image.symm.trans shape))).1
      exact (constructor.1.2.2 (by simp [same])).elim
  | embedded _clean _host embedded _invoked _boundary =>
      rw [image,nonGrounded.2] at embedded
      cases embedded
  | absent => rfl
  | equations _clean _host frontier nonempty _bodies =>
      rw [image] at frontier
      have lengthZero := frontier.length_eq (constructor.he_frontier_empty arguments (expected::live) frame.bindings)
      exact (nonempty (List.length_eq_zero_iff.mp lengthZero)).elim

theorem prepend_symbol_tuple {program : Program} {head : String} (ordinary : OrdinaryHead head)
    (arguments : List HE.Spec.Eval.Entry.Value) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) {rows : List Result}
    (tuple : TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      (.symbol head::live) scope arguments frame rows (policy := policy)) :
    TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (.symbol head::arguments) frame (rows.map (tuplePrepend (.symbol head))) (policy := policy) := by
  have value : Value program (.symbol head) := .symbol head
    (fun same => ordinary.2.2 (by simp [same])) (fun same => ordinary.2.2 (by simp [same]))
  have safe : NoErrorSymbol (.symbol head) := .symbol (fun same => ordinary.2.2 (by simp [same]))
  have evaluated (live : List Atom) : AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (.symbol head) Atom.undefinedType frame [(.symbol head,frame)] (policy := policy) := by
    obtain ⟨output,completed,erased⟩ := Value.he_completes (.symbol head)
      (by simpa only [HE.Spec.Eval.Entry.Value.erase] using value)
      (by simpa only [HE.Spec.Eval.Entry.Value.erase] using safe) frame live scope policy
    have same : output = .symbol head := by
      cases output <;> simp_all [HE.Spec.Eval.Entry.Value.erase]
    simpa only [same] using completed
  cases arguments with
  | nil =>
      cases tuple
      have nonempty : head ≠ "Empty" := fun same => ordinary.2.2 (by simp [same])
      simpa [tupleSingleton,tuplePrepend,HE.Spec.Eval.Entry.Value.erase,
        HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty,nonempty] using
        TupleRel.singleton (evaluated live)
  | cons first rest =>
      exact .cons (evaluated (.expression ((first::rest).map HE.Spec.Eval.Entry.Value.erase)::live))
        (by simpa only [List.append_nil] using
          (TupleBranchesRel.continuing (head := (.symbol head,frame))
            (by simpa only [HE.Spec.Eval.Entry.Value.erase] using value.not_stopped)
            (by simpa only [HE.Spec.Eval.Entry.Value.erase] using tuple) TupleBranchesRel.nil))

mutual
/-- Every admitted finite source completion constructs the entire HE batch.
The induction follows the source tree, including recursive bodies and every
argument alternative; no evaluator correctness callback is assumed. -/
theorem he_evaluation {program : Program} {bindings : MORK.Subst} {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (input : HE.Spec.Eval.Entry.Value)
    (code : CodeRel program [] input) (image : input.erase = MORK.applySubst bindings expression) :
    ∃ results, AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope input Atom.undefinedType frame results (policy := policy) ∧
      results.map (fun result => result.1.erase) = answers ∧
      ∀ result ∈ results, SafeResult program result := by
  by_cases passive : Value program input.erase
  · obtain ⟨output,completed,erased⟩ := Value.he_completes input passive code.safe frame live scope policy
    have exactAnswers := source.passive_exact plain (by rw [←image]; exact passive)
    refine ⟨[(output,frame)],completed,?_,?_⟩
    · simpa only [List.map_cons,List.map_nil,erased,image] using exactAnswers.symm
    · intro result member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨by rw [erased]; exact passive,by rw [erased]; exact code.safe⟩
  · match source with
    | .«variable» valid | .symbol valid => exact (passive (by rw [image]; exact valid)).elim
    | .grounded scalar => exact (passive (by rw [image]; exact .grounded scalar)).elim
    | .unit => exact (passive (by rw [image]; exact .unit)).elim
    | @Evaluation.constructor _ bindings head arguments answers constructor children =>
        have view : input.erase = .expression (.symbol head::arguments.map (MORK.applySubst bindings)) := by
          simpa only [MORK.applySubst,MORK.applySubst.applySubstList,substitution_list] using image
        obtain ⟨readiness,annotated,same,represented⟩ := expression_view input view
        subst input
        have active := code.active_of_not_value passive
        simp only [HE.Spec.Eval.Entry.Value.status] at active
        subst readiness
        obtain ⟨rows,raw,tuple,calls,erased,_packets,safe⟩ := he_arguments children programCode plain policy
          (Atom.undefinedType::live) live scope frame (.symbol head::annotated) [] code.children
          (by simpa only [List.map_cons,HE.Spec.Eval.Entry.Value.erase,MORK.applySubst] using congrArg (List.cons (.symbol head)) represented)
          (by simp [invocationAtoms]) (by simp)
        have completed := expression_complete constructor.1 annotated code policy live scope frame tuple
          (by simpa only [assemblePrefix_nil,List.map_id] using calls) safe
        refine ⟨_,completed,?_,?_⟩
        · simpa only [List.map_map,Function.comp_def,HE.Spec.Eval.Completed.publishResult_erase] using erased
        · intro result member
          obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
          simpa only [SafeResult,HE.Spec.Eval.Completed.publishResult_erase] using safe before present
    | @Evaluation.call _ bindings head arguments answers defined children =>
        have view : input.erase = .expression (.symbol head::arguments.map (MORK.applySubst bindings)) := by
          simpa only [MORK.applySubst,MORK.applySubst.applySubstList,substitution_list] using image
        obtain ⟨readiness,annotated,same,represented⟩ := expression_view input view
        subst input
        have active := code.active_of_not_value passive
        simp only [HE.Spec.Eval.Entry.Value.status] at active
        subst readiness
        have prefixSafe : ∀ value ∈ [HE.Spec.Eval.Entry.Value.symbol head],
            Value program value.erase ∧ NoErrorSymbol value.erase := by
          intro value member
          obtain rfl := List.mem_singleton.mp member
          simp only [HE.Spec.Eval.Entry.Value.erase]
          exact ⟨.symbol head (fun same => defined.1.2.2 (by simp [same]))
            (fun same => defined.1.2.2 (by simp [same])),
            .symbol (fun same => defined.1.2.2 (by simp [same]))⟩
        obtain ⟨rows,raw,tuple,calls,erased,_packets,safe⟩ := he_arguments children programCode plain policy
          (.symbol head::Atom.undefinedType::live) live scope frame annotated [.symbol head]
          (fun value member => code.children value (List.mem_cons_of_mem _ member)) represented
          (by simp only [List.map_cons,List.map_nil,HE.Spec.Eval.Entry.Value.erase,invocationAtoms]) prefixSafe
        have whole := prepend_symbol_tuple defined.1 annotated policy (Atom.undefinedType::live) scope frame tuple
        have completed := expression_complete defined.1 annotated code policy live scope frame whole
          (by simpa only [assemblePrefix_singleton] using calls) safe
        refine ⟨_,completed,?_,?_⟩
        · simpa only [List.map_map,Function.comp_def,HE.Spec.Eval.Completed.publishResult_erase] using erased
        · intro result member
          obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
          simpa only [SafeResult,HE.Spec.Eval.Completed.publishResult_erase] using safe before present
termination_by structural source

theorem he_arguments {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {answers : List Atom}
    (source : Arguments program bindings target arguments values index answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (tupleLive callLive : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (annotated prefixValues : List HE.Spec.Eval.Entry.Value)
    (code : ∀ value ∈ annotated, CodeRel program [] value)
    (image : annotated.map HE.Spec.Eval.Entry.Value.erase = arguments.map (MORK.applySubst bindings))
    (prefixImage : prefixValues.map HE.Spec.Eval.Entry.Value.erase = invocationAtoms target values)
    (prefixSafe : ∀ value ∈ prefixValues, Value program value.erase ∧ NoErrorSymbol value.erase) :
    ∃ rows raw, TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        tupleLive scope annotated frame rows (policy := policy) ∧
      CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup callLive scope Atom.undefinedType
        (rows.map (assemblePrefix prefixValues)) raw (policy := policy) ∧
      raw.map (fun result => result.1.erase) = answers ∧
      (∀ row ∈ rows, Packet program row) ∧ ∀ result ∈ raw, SafeResult program result := by
  match source with
  | .done invoked =>
      have empty : annotated = [] := List.map_eq_nil_iff.mp image
      subst annotated
      obtain ⟨raw,called,erased,safe⟩ := he_invocation invoked programCode plain policy callLive scope frame
        prefixValues prefixImage prefixSafe
      refine ⟨[ (.expression .active [],frame)],raw,.nil,?_,erased,?_,safe⟩
      · simpa only [List.map_cons,List.map_nil,assemblePrefix_empty prefixValues prefixSafe frame,List.append_nil] using
          (CallsRel.cons (children := raw) (rest := []) called CallsRel.nil)
      · intro row member
        obtain rfl := List.mem_singleton.mp member
        exact ⟨[],rfl,by simp⟩
  | .next _allowed first continued =>
      cases annotated with
      | nil => simp only [List.map_nil,List.map_cons,List.nil_eq,List.cons_ne_nil] at image
      | cons head tail =>
          have images := List.cons.inj image
          let headLive := if tail = [] then tupleLive else .expression (tail.map HE.Spec.Eval.Entry.Value.erase)::tupleLive
          obtain ⟨heads,evaluated,headImage,headSafe⟩ := he_evaluation first programCode plain policy headLive scope frame
            head (code head List.mem_cons_self) images.1
          obtain ⟨rows,raw,branches,calls,erased,packets,safe⟩ := he_cases continued programCode plain policy
            tupleLive callLive scope tail prefixValues heads
            (fun value member => code value (List.mem_cons_of_mem _ member)) images.2 prefixImage prefixSafe headImage headSafe
          refine ⟨rows,raw,?_,calls,erased,packets,safe⟩
          cases tail with
          | nil =>
              rw [empty_tuple_branches branches (fun head member => (headSafe head member).1.not_stopped)]
              exact .singleton (by simpa only [headLive,↓reduceIte] using evaluated)
          | cons next rest =>
              exact .cons (by simpa only [headLive,List.cons_ne_nil,↓reduceIte] using evaluated) branches
termination_by structural source

theorem he_cases {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {heads answers : List Atom}
    (source : ArgumentCases program bindings target arguments values index heads answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (tupleLive callLive : List Atom) (scope : List String)
    (annotated prefixValues : List HE.Spec.Eval.Entry.Value) (actual : List Result)
    (code : ∀ value ∈ annotated, CodeRel program [] value)
    (image : annotated.map HE.Spec.Eval.Entry.Value.erase = arguments.map (MORK.applySubst bindings))
    (prefixImage : prefixValues.map HE.Spec.Eval.Entry.Value.erase = invocationAtoms target values)
    (prefixSafe : ∀ value ∈ prefixValues, Value program value.erase ∧ NoErrorSymbol value.erase)
    (headImage : actual.map (fun result => result.1.erase) = heads)
    (headSafe : ∀ result ∈ actual, SafeResult program result) :
    ∃ rows raw, TupleBranchesRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        tupleLive scope annotated actual rows (policy := policy) ∧
      CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup callLive scope Atom.undefinedType
        (rows.map (assemblePrefix prefixValues)) raw (policy := policy) ∧
      raw.map (fun result => result.1.erase) = answers ∧
      (∀ row ∈ rows, Packet program row) ∧ ∀ result ∈ raw, SafeResult program result := by
  match source with
  | .nil =>
      have empty : actual = [] := List.map_eq_nil_iff.mp headImage
      subst actual
      exact ⟨[],[],.nil,.nil,rfl,by simp,by simp⟩
  | .cons next remaining =>
      cases actual with
      | nil => simp only [List.map_nil,List.nil_eq,List.cons_ne_nil] at headImage
      | cons head tail =>
          have images := List.cons.inj headImage
          have headData := headSafe head List.mem_cons_self
          have extendedImage : (prefixValues++[head.1]).map HE.Spec.Eval.Entry.Value.erase =
              invocationAtoms target (values++[head.1.erase]) := by
            rw [List.map_append,List.map_cons,List.map_nil,prefixImage,invocationAtoms_snoc]
          have extendedSafe : ∀ value ∈ prefixValues++[head.1], Value program value.erase ∧ NoErrorSymbol value.erase := by
            intro value member
            rcases List.mem_append.mp member with member | member
            · exact prefixSafe value member
            · obtain rfl := List.mem_singleton.mp member; exact headData
          obtain ⟨children,first,tuple,calls,firstImage,childPackets,firstSafe⟩ := he_arguments next programCode plain policy
            (head.1.erase::tupleLive) callLive scope head.2 annotated (prefixValues++[head.1]) code image
            (by simpa only [images.1] using extendedImage) extendedSafe
          obtain ⟨rest,last,branches,restCalls,lastImage,restPackets,lastSafe⟩ := he_cases remaining programCode plain policy
            tupleLive callLive scope annotated prefixValues tail code image prefixImage prefixSafe images.2
            (fun result member => headSafe result (List.mem_cons_of_mem _ member))
          refine ⟨children.map (tuplePrepend head.1)++rest,first++last,
            .continuing headData.1.not_stopped tuple branches,?_,?_,?_,?_⟩
          · simpa only [List.map_append,List.map_map,Function.comp_def,←assemblePrefix_snoc] using calls.append restCalls
          · simp only [List.map_append,firstImage,lastImage]
          · intro row member
            rcases List.mem_append.mp member with member | member
            · obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
              exact Packet.prepend headData (childPackets child present)
            · exact restPackets row member
          · intro result member
            rcases List.mem_append.mp member with member | member
            · exact firstSafe result member
            · exact lastSafe result member
termination_by structural source

theorem he_invocation {program : Program} {bindings : MORK.Subst} {target : Target} {values answers : List Atom}
    (source : Invocation program bindings target values answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (prefixValues : List HE.Spec.Eval.Entry.Value)
    (image : prefixValues.map HE.Spec.Eval.Entry.Value.erase = invocationAtoms target values)
    (safe : ∀ value ∈ prefixValues, Value program value.erase ∧ NoErrorSymbol value.erase) :
    ∃ raw, CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
        (.expression .active prefixValues) Atom.undefinedType frame raw (policy := policy) ∧
      raw.map (fun result => result.1.erase) = answers ∧ ∀ result ∈ raw, SafeResult program result := by
  match source with
  | .constructor valid =>
      have value : Value program (HE.Spec.Eval.Entry.Value.expression .active prefixValues).erase := by
        simpa only [HE.Spec.Eval.Entry.Value.erase,image,invocationAtoms] using valid
      have noError : NoErrorSymbol (HE.Spec.Eval.Entry.Value.expression .active prefixValues).erase := by
        simp only [HE.Spec.Eval.Entry.Value.erase]
        exact .expression (fun atom member => by
          obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
          exact (safe entry present).2)
      have call : CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
          (.expression .active prefixValues) Atom.undefinedType frame
          [(.expression .active prefixValues,frame)] (policy := policy) := by
        cases prefixValues with
        | nil =>
            apply CallRel.absent (fun failed => value.not_stopped (Or.inr failed))
            · constructor
              · rintro ⟨operator,values,_shape,executed⟩; exact executed
              · simp [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Minimal.embeddedInstruction]
            · simpa only [HE.Spec.Eval.Entry.Value.erase,List.map_nil] using unit_frontier program (Atom.undefinedType::live) frame
        | cons operator arguments =>
            obtain ⟨name,head,constructor⟩ := (show Value program
              (.expression ((operator::arguments).map HE.Spec.Eval.Entry.Value.erase)) from
                by simpa only [HE.Spec.Eval.Entry.Value.erase] using value).constructor_head
            apply CallRel.absent (fun failed => value.not_stopped (Or.inr failed))
            · rw [HE.Spec.Eval.Entry.Value.erase,List.map_cons,head]
              exact constructor.1.he_non_grounded _
            · rw [HE.Spec.Eval.Entry.Value.erase,List.map_cons,head]
              exact constructor.he_frontier_empty _ _ _
      exact ⟨_,call,by simp only [List.map_cons,List.map_nil,HE.Spec.Eval.Entry.Value.erase,image,invocationAtoms],
        fun result member => by obtain rfl := List.mem_singleton.mp member; exact ⟨value,noError⟩⟩
  | @Invocation.equations _ bindings head values selected answers ordinary scan nonempty bodies =>
      have code : CodeRel program [] (.expression .active prefixValues) :=
        invocation_code ordinary (by simpa only [invocationAtoms] using image) safe
      have represented : (HE.Spec.Eval.Entry.Value.expression .active prefixValues).erase =
          .expression (.symbol head::values) := by
        simp only [HE.Spec.Eval.Entry.Value.erase,image,invocationAtoms]
      obtain ⟨works,frontier,paired⟩ := scan.he_frontier (Atom.undefinedType::live) frame
        (by rw [←represented]; exact code.closed_vars)
        (by rw [←represented]; exact code.ground)
      rw [←represented] at frontier paired
      have selectedData : ∀ value ∈ values, Value program value ∧ NoErrorSymbol value := by
        intro value member
        have present : value ∈ prefixValues.map HE.Spec.Eval.Entry.Value.erase := by
          rw [image]; exact List.mem_cons_of_mem _ member
        obtain ⟨entry,entryPresent,same⟩ := List.mem_map.mp present
        rw [←same]
        exact safe entry entryPresent
      obtain ⟨raw,completed,erased,resultSafe⟩ := he_bodies bodies programCode plain policy live scope frame
        (.expression .active prefixValues) code.closed_vars frontier (fun _ member => member) paired
        (scan.captured_values selectedData)
      have worksNonempty : works ≠ [] := by
        intro empty
        rw [empty] at paired
        exact nonempty (List.forall₂_nil_right_iff.mp paired)
      refine ⟨raw,.equations ?_ ?_ frontier worksNonempty completed,erased,resultSafe⟩
      · rw [represented]
        have headClean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
        simp [HE.Spec.Eval.IsErrorRel,headClean]
      · rw [represented]
        exact ordinary.he_non_grounded values
termination_by structural source

theorem he_bodies {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (original : HE.Spec.Eval.Entry.Value)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars original.erase = [])
    {allWorks works : List HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program)
      (Atom.undefinedType::live) original.erase frame.bindings allWorks)
    (included : ∀ work ∈ works, work ∈ allWorks)
    (paired : List.Forall₂ (ClauseInstance original.erase) selected works)
    (captured : ∀ item ∈ selected, ∀ pair ∈ item.2.1, Value program pair.2 ∧ NoErrorSymbol pair.2) :
    ∃ raw, EquationBodiesRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
        original Atom.undefinedType frame works raw (policy := policy) ∧
      raw.map (fun result => result.1.erase) = answers ∧ ∀ result ∈ raw, SafeResult program result := by
  match source with
  | .nil => cases paired; exact ⟨[],.nil,rfl,by simp⟩
  | @Bodies.cons _ position bindings sourceBody selected children answers child remaining =>
      let item : ClauseWork := (position,bindings,sourceBody)
      cases paired with
      | @cons _ work _ works related pairs =>
          have present := included work List.mem_cons_self
          obtain ⟨matched,occurrence⟩ := frontier.occurrence present
          have candidate : HE.Spec.Eval.Steps.UnifyCandidateRel original.erase work.pattern frame.bindings work.bindings :=
            ⟨matched,occurrence.selected.2,occurrence.result.1⟩
          obtain ⟨environment,unified,certified⟩ := HE.Spec.Eval.Entry.Value.UnifyRel.of_source_candidate
            (policy := policy.rebuilding) (left := original) (right := HE.Spec.Eval.Entry.Value.ofAtom work.pattern)
            frame.certified (by simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using candidate)
          let after : HE.Spec.Eval.Completed.Frame := ⟨work.bindings,environment,certified⟩
          let body := after.read policy (HE.Spec.Eval.Entry.Value.ofAtom work.body)
          have bodyCode : CodeRel program [] body := related.body_code programCode frontier present closed
            (captured item List.mem_cons_self) after rfl policy
          have bodyImage : body.erase = MORK.applySubst item.2.1 item.2.2 := by
            simpa only [related.2.1] using frontier_body_read frontier present item.2.1 related.2.2.1
              (programCode.range.work_covered frontier present) closed after rfl policy
          obtain ⟨first,evaluated,firstImage,firstSafe⟩ := he_evaluation child programCode plain policy live scope after body bodyCode bodyImage
          have returnable := child.input_returnable
          have returned : ReturnRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
              original Atom.undefinedType body after first (policy := policy) :=
            .evaluate (by rw [bodyImage]; exact returnable.1) (by rw [bodyImage]; exact returnable.2) evaluated
          obtain ⟨rest,tail,restImage,restSafe⟩ := he_bodies remaining programCode plain policy live scope frame original closed
            frontier (fun work member => included work (List.mem_cons_of_mem _ member)) pairs
            (fun item member => captured item (List.mem_cons_of_mem _ member))
          refine ⟨first++rest,.ordinary_cons rfl unified (child.input_not_function bodyImage policy) returned tail,?_,?_⟩
          · simp only [List.map_append,firstImage,restImage]
          · intro result member
            rcases List.mem_append.mp member with member | member
            · exact firstSafe result member
            · exact restSafe result member
termination_by structural source
end

private theorem data_priority_singleton {program : Program} (policy : Policy) (result : Result)
    (value : Value program result.1.erase) {selected : List Result}
    (priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => HE.isErrorAtom result.1.erase) [readResult policy result] selected) :
    selected = [result] := by
  have read : readResult policy result = result := Prod.ext
    (HE.Spec.Eval.Completed.Frame.read_variable_free policy result.2 result.1 value.variable_free) rfl
  rw [read] at priority
  have clean := value.boolean_clean
  simp only [HE.isEmptyOrError,Bool.or_eq_false_iff] at clean
  have expected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => HE.isErrorAtom result.1.erase) [result] [result] := by
    simpa only [List.filter_cons,clean.2,Bool.not_false,↓reduceIte,List.filter_nil] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => HE.isErrorAtom result.1.erase)
        (raw := [result]) ⟨result,List.mem_cons_self,clean.2⟩)
  exact priority.functional expected

set_option maxRecDepth 4096 in
mutual
/-- Every completed HE phase on passive admitted data has exactly one
corresponding value and retains the caller's entire constraint record.
Readiness and the actual reached frame are kept in the witness. -/
theorem passive_atom_exact {program : Program} (value : HE.Spec.Eval.Entry.Value)
    (valid : Value program value.erase) (safe : NoErrorSymbol value.erase)
    (policy : Policy) (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame)
    {results : List Result}
    (source : AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope value Atom.undefinedType frame results (policy := policy)) :
    ∃ output after, results = [(output,after)] ∧ output.erase = value.erase ∧ after.bindings = frame.bindings := by
  have read := HE.Spec.Eval.Completed.Frame.read_variable_free policy frame value valid.variable_free
  obtain ⟨action,entered⟩ := HE.Spec.Eval.Entry.total policy.reentry value.status value.erase Atom.undefinedType
  have actualEntry : HE.Spec.Eval.Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase Atom.undefinedType action := by simpa only [read] using entered
  cases action with
  | deliver => exact ⟨value,frame,by simpa only [read] using source.delivery_exact actualEntry,rfl,rfl⟩
  | cast =>
      obtain ⟨after,bindings,shape⟩ := source.undefined_cast_exact actualEntry
      exact ⟨value,after,by simpa only [read] using shape,rfl,bindings⟩
  | interpret =>
      obtain ⟨operator,arguments,shape⟩ := entered.interpret_shape
      have structured : Value program (.expression (operator::arguments)) := by rw [←shape]; exact valid
      obtain ⟨head,headShape,constructor⟩ := structured.constructor_head
      have image : value.erase = .expression (.symbol head::arguments) := by rw [shape,headShape]
      obtain ⟨readiness,children,same,childrenImage⟩ := expression_view value image
      subst value
      have finish {rows raw selected : List Result}
          (tuple : TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
            (Atom.undefinedType::live) scope (.symbol head::children) frame rows (policy := policy))
          (calls : CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
            live scope Atom.undefinedType rows raw (policy := policy))
          (priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
            (fun result : Result => HE.isErrorAtom result.1.erase) (raw.map (readResult policy)) selected) :
          ∃ output after,
            selected.map (publishResult policy (HE.Spec.Eval.Entry.Value.expression readiness (.symbol head::children)).erase) =
              [(output,after)] ∧ output.erase =
                (HE.Spec.Eval.Entry.Value.expression readiness (.symbol head::children)).erase ∧
              after.bindings = frame.bindings := by
        have childValues : ∀ child ∈ HE.Spec.Eval.Entry.Value.symbol head::children, Value program child.erase := by
          have rawValid : Value program (.expression ((HE.Spec.Eval.Entry.Value.symbol head::children).map HE.Spec.Eval.Entry.Value.erase)) := by
            simpa only [HE.Spec.Eval.Entry.Value.erase] using valid
          intro child member
          exact rawValid.children child.erase (List.mem_map_of_mem member)
        have childSafe : ∀ child ∈ HE.Spec.Eval.Entry.Value.symbol head::children, NoErrorSymbol child.erase := by
          have rawSafe : NoErrorSymbol (.expression ((HE.Spec.Eval.Entry.Value.symbol head::children).map HE.Spec.Eval.Entry.Value.erase)) := by
            simpa only [HE.Spec.Eval.Entry.Value.erase] using safe
          intro child member
          exact rawSafe.children child.erase (List.mem_map_of_mem member)
        obtain ⟨outputs,after,rowsShape,erased,bindings,_outputSafe⟩ :=
          passive_tuple_exact (.symbol head::children) childValues childSafe policy (Atom.undefinedType::live) scope frame tuple
        have resultImage : (HE.Spec.Eval.Entry.Value.expression .active outputs).erase =
            (HE.Spec.Eval.Entry.Value.expression readiness (.symbol head::children)).erase := by
          simpa only [HE.Spec.Eval.Entry.Value.erase] using congrArg Atom.expression erased
        rw [rowsShape] at calls
        cases calls with
        | cons called remaining =>
            cases remaining
            have calledShape := constructor_call_exact constructor (resultImage.trans image) called
            rw [calledShape,List.append_nil] at priority
            have resultValue : Value program (HE.Spec.Eval.Entry.Value.expression .active outputs).erase := by
              rw [resultImage]; exact valid
            have selectedShape := data_priority_singleton policy (.expression .active outputs,after) resultValue
              (by simpa only [List.map_cons,List.map_nil] using priority)
            rw [selectedShape]
            refine ⟨(publishResult policy
              (HE.Spec.Eval.Entry.Value.expression readiness (.symbol head::children)).erase
              (.expression .active outputs,after)).1,after,rfl,?_,bindings⟩
            exact (HE.Spec.Eval.Completed.publishResult_erase policy
              (HE.Spec.Eval.Entry.Value.expression readiness (.symbol head::children)).erase
              (.expression .active outputs,after)).trans resultImage
      have undefined : HE.Spec.Type.StorageTypesRel (equationSpace program) (.symbol head) [Atom.undefinedType] :=
        .symbolUndefined (equationSpace.no_annotations _ _)
      cases source with
      | delivered actual => exact HE.Spec.Eval.Entry.Action.noConfusion (HE.Spec.Eval.Entry.functional actual actualEntry)
      | cast actual _ _ => exact HE.Spec.Eval.Entry.Action.noConfusion (HE.Spec.Eval.Entry.functional actual actualEntry)
      | tuple _entered materialized _typed tuple calls priority =>
          rw [read] at materialized
          cases materialized
          simpa only [read] using finish tuple calls priority
      | function _entered materialized selected _invoked _priority =>
          rw [read] at materialized
          cases materialized
          have impossible := selected.undefined_exact (by simpa only [HE.Spec.Eval.Entry.Value.erase] using undefined)
          cases impossible
      | fallback _entered materialized selected tuple calls priority =>
          rw [read] at materialized
          cases materialized
          have exhausted := selected.undefined_exact (by simpa only [HE.Spec.Eval.Entry.Value.erase] using undefined)
          have noErrors := (HE.Spec.Eval.Completed.InvocationSelection.exhausted.inj exhausted).1
          subst noErrors
          simpa only [read,HE.Spec.Eval.Completed.diagnosticResults,List.map_nil,List.append_nil] using
            finish tuple calls (by simpa only [HE.Spec.Eval.Completed.diagnosticResults,List.map_nil,List.append_nil] using priority)
      | selectionFailed _entered materialized selected _priority =>
          rw [read] at materialized
          cases materialized
          have impossible := selected.undefined_exact (by simpa only [HE.Spec.Eval.Entry.Value.erase] using undefined)
          have boolean := (HE.Spec.Eval.Completed.InvocationSelection.exhausted.inj impossible).2
          cases boolean
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf

theorem passive_tuple_exact {program : Program} (children : List HE.Spec.Eval.Entry.Value)
    (values : ∀ child ∈ children, Value program child.erase)
    (safe : ∀ child ∈ children, NoErrorSymbol child.erase)
    (policy : Policy) (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame)
    {results : List Result}
    (source : TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope children frame results (policy := policy)) :
    ∃ outputs after, results = [(.expression .active outputs,after)] ∧
      outputs.map HE.Spec.Eval.Entry.Value.erase = children.map HE.Spec.Eval.Entry.Value.erase ∧
      after.bindings = frame.bindings ∧
      ∀ output ∈ outputs, Value program output.erase ∧ NoErrorSymbol output.erase := by
  match children with
  | [] => cases source; exact ⟨[],frame,rfl,rfl,rfl,by simp⟩
  | first::rest =>
      have firstValue := values first List.mem_cons_self
      have firstSafe := safe first List.mem_cons_self
      cases rest with
      | nil =>
          cases source with
          | singleton evaluated =>
              obtain ⟨output,after,shape,erased,bindings⟩ := passive_atom_exact first firstValue firstSafe policy live scope frame evaluated
              have outputValue : Value program output.erase := by rw [erased]; exact firstValue
              refine ⟨[output],after,?_,by simp only [List.map_cons,List.map_nil,erased],bindings,?_⟩
              · simp only [shape,List.map_cons,List.map_nil,tupleSingleton,outputValue.boolean_clean,
                  Bool.false_eq_true,↓reduceIte]
              · intro result member
                obtain rfl := List.mem_singleton.mp member
                exact ⟨outputValue,by rw [erased]; exact firstSafe⟩
      | cons second remaining =>
          cases source with
          | cons evaluated branches =>
              obtain ⟨head,middle,shape,headImage,middleBindings⟩ := passive_atom_exact first firstValue firstSafe policy
                (.expression ((second::remaining).map HE.Spec.Eval.Entry.Value.erase)::live) scope frame evaluated
              have headValue : Value program head.erase := by rw [headImage]; exact firstValue
              have headSafe : NoErrorSymbol head.erase := by rw [headImage]; exact firstSafe
              rw [shape] at branches
              cases branches with
              | stopped failed _ => exact (headValue.not_stopped failed).elim
              | continuing _ordinary tail rest =>
                  cases rest
                  obtain ⟨outputs,after,tailShape,tailImage,afterBindings,outputSafe⟩ := passive_tuple_exact
                    (second::remaining) (fun value member => values value (List.mem_cons_of_mem _ member))
                    (fun value member => safe value (List.mem_cons_of_mem _ member)) policy
                    (head.erase::live) scope middle tail
                  have clean := (show Packet program (.expression .active outputs,after) from ⟨outputs,rfl,outputSafe⟩).clean
                  refine ⟨head::outputs,after,?_,?_,afterBindings.trans middleBindings,?_⟩
                  · simp only [tailShape,List.map_cons,List.map_nil,List.append_nil,tuplePrepend,
                      clean,Bool.false_eq_true,↓reduceIte]
                  · simp only [List.map_cons,headImage,tailImage]
                  · intro result member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact ⟨headValue,headSafe⟩
                    · exact outputSafe result member
termination_by sizeOf children
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega
end

theorem data_call_exact {program : Program} {status children}
    (valid : Value program (HE.Spec.Eval.Entry.Value.expression status children).erase) {policy live scope frame results}
    (source : CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (.expression status children) Atom.undefinedType frame results (policy := policy)) :
    results = [(.expression status children,frame)] := by
  cases children with
  | nil =>
      cases source with
      | error failed => simp [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.IsErrorRel] at failed
      | embedded _ _ embedded _ _ => simp [HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.Minimal.embeddedInstruction] at embedded
      | absent => rfl
      | equations _ _ frontier nonempty _ =>
          simp only [HE.Spec.Eval.Entry.Value.erase,List.map_nil] at frontier
          have empty := frontier.length_eq (unit_frontier program (Atom.undefinedType::live) frame)
          exact (nonempty (List.length_eq_zero_iff.mp empty)).elim
  | cons operator arguments =>
      have raw : Value program (.expression (operator.erase::arguments.map HE.Spec.Eval.Entry.Value.erase)) := by
        simpa only [HE.Spec.Eval.Entry.Value.erase,List.map_cons] using valid
      obtain ⟨name,same,constructor⟩ := raw.constructor_head
      exact constructor_call_exact (arguments := arguments.map HE.Spec.Eval.Entry.Value.erase) constructor
        (by simp only [HE.Spec.Eval.Entry.Value.erase,List.map_cons,same]) source

private theorem data_priority_exact {program : Program} (policy : Policy) {raw selected : List Result}
    (safe : ∀ result ∈ raw, SafeResult program result)
    (priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => HE.isErrorAtom result.1.erase) (raw.map (readResult policy)) selected) :
    selected = raw := by
  have read : raw.map (readResult policy) = raw := by
    conv_rhs => rw [←List.map_id raw]
    apply List.map_congr_left
    intro result member
    exact Prod.ext (HE.Spec.Eval.Completed.Frame.read_variable_free policy result.2 result.1
      (safe result member).1.variable_free) rfl
  rw [read] at priority
  have clean (result : Result) (member : result ∈ raw) : HE.isErrorAtom result.1.erase = false := by
    have value := (safe result member).1.boolean_clean
    exact (Bool.or_eq_false_iff.mp value).2
  have expected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => HE.isErrorAtom result.1.erase) raw raw := by
    cases raw with
    | nil => exact .allErrors (by simp)
    | cons first rest =>
        have filter : (first::rest).filter (fun result => !HE.isErrorAtom result.1.erase) = first::rest := by
          apply List.filter_eq_self.mpr
          intro result member
          simp only [clean result member,Bool.not_false]
        simpa only [filter] using
          (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
            (isError := fun result : Result => HE.isErrorAtom result.1.erase)
            (raw := first::rest) ⟨first,List.mem_cons_self,clean first List.mem_cons_self⟩)
  exact priority.functional expected

theorem expression_phases {program : Program} {head : String} (ordinary : OrdinaryHead head)
    (arguments : List HE.Spec.Eval.Entry.Value)
    (code : CodeRel program [] (.expression .active (.symbol head::arguments)))
    {policy live scope frame results}
    (source : AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
      (.expression .active (.symbol head::arguments)) Atom.undefinedType frame results (policy := policy)) :
    ∃ rows raw selected,
      TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        (Atom.undefinedType::live) scope (.symbol head::arguments) frame rows (policy := policy) ∧
      CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope Atom.undefinedType rows raw (policy := policy) ∧
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => HE.isErrorAtom result.1.erase) (raw.map (readResult policy)) selected ∧
      results = selected.map (publishResult policy (.expression (.symbol head::arguments.map HE.Spec.Eval.Entry.Value.erase))) := by
  have read := code.read_closed policy frame
  have clean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
  have entered : HE.Spec.Eval.Entry.Rel policy.reentry
      (frame.read policy (.expression .active (.symbol head::arguments))).status
      (frame.read policy (.expression .active (.symbol head::arguments))).erase Atom.undefinedType .interpret := by
    rw [read]
    simp only [HE.Spec.Eval.Entry.Value.status,HE.Spec.Eval.Entry.Value.erase,List.map_cons]
    apply HE.Spec.Eval.Entry.Rel.expression
    · simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty,clean]
    · simp [Atom.undefinedType,Atom.atomType,Atom.expressionType,Atom.variableType]
    · exact Or.inr rfl
  simpa only [read,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using
    source.undefined_operator_phases entered read
      (by simpa only [HE.Spec.Eval.Entry.Value.erase] using
        HE.Spec.Type.StorageTypesRel.symbolUndefined (equationSpace.no_annotations program (.symbol head)))

theorem symbol_tuple_suffix {program : Program} {head : String} (ordinary : OrdinaryHead head)
    {arguments : List HE.Spec.Eval.Entry.Value} {policy live scope frame rows}
    (source : TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (.symbol head::arguments) frame rows (policy := policy)) :
    ∃ after children, after.bindings = frame.bindings ∧ rows = children.map (tuplePrepend (.symbol head)) ∧
      TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        (.symbol head::live) scope arguments after children (policy := policy) := by
  have valid : Value program (.symbol head) := .symbol head
    (fun same => ordinary.2.2 (by simp [same])) (fun same => ordinary.2.2 (by simp [same]))
  have safe : NoErrorSymbol (.symbol head) := .symbol (fun same => ordinary.2.2 (by simp [same]))
  have exactHead {headLive results}
      (evaluated : AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup headLive scope
        (.symbol head) Atom.undefinedType frame results (policy := policy)) :
      ∃ after, results = [(.symbol head,after)] ∧ after.bindings = frame.bindings := by
    obtain ⟨output,after,shape,erased,bindings⟩ := passive_atom_exact (.symbol head)
      (by simpa only [HE.Spec.Eval.Entry.Value.erase] using valid)
      (by simpa only [HE.Spec.Eval.Entry.Value.erase] using safe)
      policy headLive scope frame evaluated
    have same : output = .symbol head := by cases output <;> simp_all [HE.Spec.Eval.Entry.Value.erase]
    exact ⟨after,by rw [shape,same],bindings⟩
  cases arguments with
  | nil =>
      cases source with
      | singleton evaluated =>
          obtain ⟨after,shape,bindings⟩ := exactHead evaluated
          refine ⟨after,[ (.expression .active [],after)],bindings,?_,.nil⟩
          rw [shape]
          simp [tupleSingleton,tuplePrepend,HE.Spec.Eval.Entry.Value.erase,
            HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty,
            show head ≠ "Empty" from fun same => ordinary.2.2 (by simp [same])]
  | cons first rest =>
      cases source with
      | cons evaluated branches =>
          obtain ⟨after,shape,bindings⟩ := exactHead evaluated
          rw [shape] at branches
          cases branches with
          | stopped failed _ => exact (valid.not_stopped (by simpa only [HE.Spec.Eval.Entry.Value.erase] using failed)).elim
          | @continuing _ _ _ _ _ _ _ _ children _ _ _ tail rest =>
              cases rest
              exact ⟨after,children,bindings,by simp only [List.append_nil],
                by simpa only [HE.Spec.Eval.Entry.Value.erase] using tail⟩

theorem empty_tuple_branches_of_safe {program : Program} {policy live scope heads}
    (safe : ∀ result ∈ heads, SafeResult program result) :
    TupleBranchesRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope [] heads (heads.map tupleSingleton) (policy := policy) := by
  induction heads with
  | nil => exact .nil
  | cons head heads ih =>
      have data := safe head List.mem_cons_self
      have singleton : tupleSingleton head = (.expression .active [head.1],head.2) := by
        simp only [tupleSingleton,data.1.boolean_clean,Bool.false_eq_true,↓reduceIte]
      have prepend : tuplePrepend head.1 (.expression .active [],head.2) = tupleSingleton head := by
        rw [singleton]
        simp [tuplePrepend,HE.Spec.Eval.Entry.Value.erase,HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty]
      simpa only [List.map_cons,List.map_nil,List.singleton_append,prepend] using
        TupleBranchesRel.continuing data.1.not_stopped TupleRel.nil
          (ih (fun result member => safe result (List.mem_cons_of_mem _ member)))

def Covers (live : List Atom) (names : List String) : Prop :=
  ∀ name ∈ names, name ∈ live.flatMap HE.Spec.Type.Presentation.TypeSubst.typeVars

theorem Covers.cons {live : List Atom} {names : List String} (covered : Covers live names) (atom : Atom) :
    Covers (atom::live) names := by
  intro name member
  exact List.mem_append_right _ (covered name member)

def PreservesAt (names : List String) (before : HE.Spec.Eval.Completed.Frame) (results : List Result) : Prop :=
  ∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.ConservativeExtension names before.bindings result.2.bindings

mutual
/-- Every completed HE phase agrees with the independent recursive source
tree. The proof quantifies over the actual completed batch and reached
frames, rather than selecting the particular forward construction. -/
theorem he_evaluation_exact {program : Program} {bindings : MORK.Subst} {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (input : HE.Spec.Eval.Entry.Value)
    (code : CodeRel program [] input) (image : input.erase = MORK.applySubst bindings expression)
    {results : List Result}
    (completed : AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope input Atom.undefinedType frame results (policy := policy)) :
    results.map (fun result => result.1.erase) = answers ∧
      (∀ result ∈ results, SafeResult program result) ∧
      ∀ names, Covers live names → PreservesAt names frame results := by
  by_cases passive : Value program input.erase
  · obtain ⟨output,after,shape,erased,bindings⟩ := passive_atom_exact input passive code.safe policy live scope frame completed
    rw [shape]
    refine ⟨?_,?_,?_⟩
    · simpa only [List.map_cons,List.map_nil,erased,image] using
        (source.passive_exact plain (by rw [←image]; exact passive)).symm
    · intro result member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨by rw [erased]; exact passive,by rw [erased]; exact code.safe⟩
    · intro names _covered result member
      obtain rfl := List.mem_singleton.mp member
      exact HE.Spec.Bindings.ScopeObservation.ConservativeExtension.of_eq names bindings
  · match source with
    | .«variable» valid | .symbol valid => exact (passive (by rw [image]; exact valid)).elim
    | .grounded scalar => exact (passive (by rw [image]; exact .grounded scalar)).elim
    | .unit => exact (passive (by rw [image]; exact .unit)).elim
    | @Evaluation.constructor _ bindings head arguments answers constructor children =>
        have view : input.erase = .expression (.symbol head::arguments.map (MORK.applySubst bindings)) := by
          simpa only [MORK.applySubst,MORK.applySubst.applySubstList,substitution_list] using image
        obtain ⟨readiness,annotated,same,represented⟩ := expression_view input view
        subst input
        have active := code.active_of_not_value passive
        simp only [HE.Spec.Eval.Entry.Value.status] at active
        subst readiness
        obtain ⟨rows,raw,selected,tuple,calls,priority,shape⟩ := expression_phases constructor.1 annotated code completed
        have actual := he_arguments_exact children programCode plain policy
          (Atom.undefinedType::live) live scope frame (.symbol head::annotated) [] code.children
          (by simpa only [List.map_cons,HE.Spec.Eval.Entry.Value.erase,MORK.applySubst] using congrArg (List.cons (.symbol head)) represented)
          (by simp [invocationAtoms]) (by simp) tuple
          (by simpa only [assemblePrefix_nil,List.map_id] using calls)
        have selectedShape := data_priority_exact policy actual.2.2.1 priority
        rw [shape,selectedShape]
        refine ⟨?_,?_,?_⟩
        · simpa only [List.map_map,Function.comp_def,HE.Spec.Eval.Completed.publishResult_erase] using actual.1
        · intro result member
          obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
          simpa only [SafeResult,HE.Spec.Eval.Completed.publishResult_erase] using actual.2.2.1 before present
        · intro names covered result member
          obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
          exact (actual.2.2.2 names (covered.cons Atom.undefinedType) covered).2 before present
    | @Evaluation.call _ bindings head arguments answers defined children =>
        have view : input.erase = .expression (.symbol head::arguments.map (MORK.applySubst bindings)) := by
          simpa only [MORK.applySubst,MORK.applySubst.applySubstList,substitution_list] using image
        obtain ⟨readiness,annotated,same,represented⟩ := expression_view input view
        subst input
        have active := code.active_of_not_value passive
        simp only [HE.Spec.Eval.Entry.Value.status] at active
        subst readiness
        obtain ⟨rows,raw,selected,tuple,calls,priority,shape⟩ := expression_phases defined.1 annotated code completed
        obtain ⟨after,tailRows,bindings,rowsShape,tailTuple⟩ := symbol_tuple_suffix defined.1 tuple
        have prefixSafe : ∀ value ∈ [HE.Spec.Eval.Entry.Value.symbol head],
            Value program value.erase ∧ NoErrorSymbol value.erase := by
          intro value member
          obtain rfl := List.mem_singleton.mp member
          simp only [HE.Spec.Eval.Entry.Value.erase]
          exact ⟨.symbol head (fun same => defined.1.2.2 (by simp [same]))
            (fun same => defined.1.2.2 (by simp [same])),
            .symbol (fun same => defined.1.2.2 (by simp [same]))⟩
        rw [rowsShape] at calls
        have actual := he_arguments_exact children programCode plain policy
          (.symbol head::Atom.undefinedType::live) live scope after annotated [.symbol head]
          (fun value member => code.children value (List.mem_cons_of_mem _ member)) represented
          (by simp only [List.map_cons,List.map_nil,HE.Spec.Eval.Entry.Value.erase,invocationAtoms]) prefixSafe
          tailTuple (by simpa only [assemblePrefix_singleton] using calls)
        have selectedShape := data_priority_exact policy actual.2.2.1 priority
        rw [shape,selectedShape]
        refine ⟨?_,?_,?_⟩
        · simpa only [List.map_map,Function.comp_def,HE.Spec.Eval.Completed.publishResult_erase] using actual.1
        · intro result member
          obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
          simpa only [SafeResult,HE.Spec.Eval.Completed.publishResult_erase] using actual.2.2.1 before present
        · intro names covered result member
          obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
          have extended := (actual.2.2.2 names ((covered.cons Atom.undefinedType).cons (.symbol head)) covered).2 before present
          rw [bindings] at extended
          exact extended
termination_by structural source

theorem he_arguments_exact {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {answers : List Atom}
    (source : Arguments program bindings target arguments values index answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (tupleLive callLive : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (annotated prefixValues : List HE.Spec.Eval.Entry.Value)
    (code : ∀ value ∈ annotated, CodeRel program [] value)
    (image : annotated.map HE.Spec.Eval.Entry.Value.erase = arguments.map (MORK.applySubst bindings))
    (prefixImage : prefixValues.map HE.Spec.Eval.Entry.Value.erase = invocationAtoms target values)
    (prefixSafe : ∀ value ∈ prefixValues, Value program value.erase ∧ NoErrorSymbol value.erase)
    {rows raw : List Result}
    (tuple : TupleRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      tupleLive scope annotated frame rows (policy := policy))
    (calls : CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup callLive scope Atom.undefinedType
      (rows.map (assemblePrefix prefixValues)) raw (policy := policy)) :
    raw.map (fun result => result.1.erase) = answers ∧
      (∀ row ∈ rows, Packet program row) ∧ (∀ result ∈ raw, SafeResult program result) ∧
      ∀ names, Covers tupleLive names → Covers callLive names →
        PreservesAt names frame rows ∧ PreservesAt names frame raw := by
  match source with
  | .done invoked =>
      have empty : annotated = [] := List.map_eq_nil_iff.mp image
      subst annotated
      cases tuple
      simp only [List.map_cons,List.map_nil,assemblePrefix_empty prefixValues prefixSafe frame] at calls
      cases calls with
      | cons called remaining =>
          cases remaining
          have actual := he_invocation_exact invoked programCode plain policy callLive scope frame
            prefixValues prefixImage prefixSafe called
          refine ⟨by simpa only [List.append_nil] using actual.1,?_,?_,?_⟩
          · intro row member
            obtain rfl := List.mem_singleton.mp member
            exact ⟨[],rfl,by simp⟩
          · simpa only [List.append_nil] using actual.2.1
          · intro names _tupleCovered callCovered
            constructor
            · intro row member
              obtain rfl := List.mem_singleton.mp member
              exact HE.Spec.Bindings.ScopeObservation.ConservativeExtension.refl _ _
            · simpa only [List.append_nil] using actual.2.2 names callCovered
  | .next _allowed first continued =>
      cases annotated with
      | nil => simp only [List.map_nil,List.map_cons,List.nil_eq,List.cons_ne_nil] at image
      | cons head tail =>
          have images := List.cons.inj image
          cases tail with
          | nil =>
              cases tuple with
              | singleton evaluated =>
                  have actual := he_evaluation_exact first programCode plain policy tupleLive scope frame head
                    (code head List.mem_cons_self) images.1 evaluated
                  exact he_cases_exact continued programCode plain policy tupleLive callLive scope frame [] prefixValues _
                    (fun _ member => (List.not_mem_nil member).elim) images.2 prefixImage prefixSafe
                    actual.1 actual.2.1 (fun names covered _ => actual.2.2 names covered)
                    (empty_tuple_branches_of_safe actual.2.1) calls
          | cons next rest =>
              cases tuple with
              | cons evaluated branches =>
                  have actual := he_evaluation_exact first programCode plain policy
                    (.expression ((next::rest).map HE.Spec.Eval.Entry.Value.erase)::tupleLive) scope frame head
                    (code head List.mem_cons_self) images.1 evaluated
                  exact he_cases_exact continued programCode plain policy tupleLive callLive scope frame (next::rest) prefixValues _
                    (fun value member => code value (List.mem_cons_of_mem _ member)) images.2 prefixImage prefixSafe
                    actual.1 actual.2.1 (fun names covered _ => actual.2.2 names (covered.cons _)) branches calls
termination_by structural source

theorem he_cases_exact {program : Program} {bindings : MORK.Subst} {target : Target}
    {arguments values : List Atom} {index : Nat} {heads answers : List Atom}
    (source : ArgumentCases program bindings target arguments values index heads answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (tupleLive callLive : List Atom) (scope : List String)
    (origin : HE.Spec.Eval.Completed.Frame)
    (annotated prefixValues : List HE.Spec.Eval.Entry.Value) (actual : List Result)
    (code : ∀ value ∈ annotated, CodeRel program [] value)
    (image : annotated.map HE.Spec.Eval.Entry.Value.erase = arguments.map (MORK.applySubst bindings))
    (prefixImage : prefixValues.map HE.Spec.Eval.Entry.Value.erase = invocationAtoms target values)
    (prefixSafe : ∀ value ∈ prefixValues, Value program value.erase ∧ NoErrorSymbol value.erase)
    (headImage : actual.map (fun result => result.1.erase) = heads)
    (headSafe : ∀ result ∈ actual, SafeResult program result)
    (headPreserved : ∀ names, Covers tupleLive names → Covers callLive names → PreservesAt names origin actual)
    {rows raw : List Result}
    (branches : TupleBranchesRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      tupleLive scope annotated actual rows (policy := policy))
    (calls : CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup callLive scope Atom.undefinedType
      (rows.map (assemblePrefix prefixValues)) raw (policy := policy)) :
    raw.map (fun result => result.1.erase) = answers ∧
      (∀ row ∈ rows, Packet program row) ∧ (∀ result ∈ raw, SafeResult program result) ∧
      ∀ names, Covers tupleLive names → Covers callLive names →
        PreservesAt names origin rows ∧ PreservesAt names origin raw := by
  match source with
  | .nil =>
      have empty : actual = [] := List.map_eq_nil_iff.mp headImage
      subst actual
      cases branches
      cases calls
      exact ⟨rfl,by simp,by simp,fun _ _ _ => ⟨by simp [PreservesAt],by simp [PreservesAt]⟩⟩
  | .cons next remaining =>
      cases actual with
      | nil => simp only [List.map_nil,List.nil_eq,List.cons_ne_nil] at headImage
      | cons head tail =>
          have images := List.cons.inj headImage
          have headData := headSafe head List.mem_cons_self
          cases branches with
          | stopped failed _ => exact (headData.1.not_stopped failed).elim
          | @continuing _ _ _ _ _ _ _ _ children rest _ _ordinary tuple branches =>
              have extendedImage : (prefixValues++[head.1]).map HE.Spec.Eval.Entry.Value.erase =
                  invocationAtoms target (values++[head.1.erase]) := by
                rw [List.map_append,List.map_cons,List.map_nil,prefixImage,invocationAtoms_snoc]
              have extendedSafe : ∀ value ∈ prefixValues++[head.1], Value program value.erase ∧ NoErrorSymbol value.erase := by
                intro value member
                rcases List.mem_append.mp member with member | member
                · exact prefixSafe value member
                · obtain rfl := List.mem_singleton.mp member; exact headData
              have divided : CallsRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
                  callLive scope Atom.undefinedType
                  (children.map (assemblePrefix (prefixValues++[head.1]))++rest.map (assemblePrefix prefixValues)) raw
                  (policy := policy) := by
                simpa only [List.map_append,List.map_map,Function.comp_def,←assemblePrefix_snoc] using calls
              obtain ⟨first,last,shape,firstCalls,lastCalls⟩ := divided.split _ _
              have firstExact := he_arguments_exact next programCode plain policy
                (head.1.erase::tupleLive) callLive scope head.2 annotated (prefixValues++[head.1]) code image
                (by simpa only [images.1] using extendedImage) extendedSafe tuple firstCalls
              have lastExact := he_cases_exact remaining programCode plain policy tupleLive callLive scope
                origin annotated prefixValues tail code image prefixImage prefixSafe images.2
                (fun result member => headSafe result (List.mem_cons_of_mem _ member))
                (fun names tupleCovered callCovered result member =>
                  headPreserved names tupleCovered callCovered result (List.mem_cons_of_mem _ member)) branches lastCalls
              refine ⟨?_,?_,?_,?_⟩
              · simp only [shape,List.map_append,firstExact.1,lastExact.1]
              · intro row member
                rcases List.mem_append.mp member with member | member
                · obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
                  exact Packet.prepend headData (firstExact.2.1 child present)
                · exact lastExact.2.1 row member
              · rw [shape]
                intro result member
                rcases List.mem_append.mp member with member | member
                · exact firstExact.2.2.1 result member
                · exact lastExact.2.2.1 result member
              · intro names tupleCovered callCovered
                have earlier := headPreserved names tupleCovered callCovered head List.mem_cons_self
                have middle := firstExact.2.2.2 names (tupleCovered.cons head.1.erase) callCovered
                have later := lastExact.2.2.2 names tupleCovered callCovered
                constructor
                · intro row member
                  rcases List.mem_append.mp member with member | member
                  · obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
                    simpa only [HE.Spec.Eval.Completed.tuplePrepend_frame] using earlier.trans (middle.1 child present)
                  · exact later.1 row member
                · rw [shape]
                  intro result member
                  rcases List.mem_append.mp member with member | member
                  · exact earlier.trans (middle.2 result member)
                  · exact later.2 result member
termination_by structural source

theorem he_invocation_exact {program : Program} {bindings : MORK.Subst} {target : Target} {values answers : List Atom}
    (source : Invocation program bindings target values answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (prefixValues : List HE.Spec.Eval.Entry.Value)
    (image : prefixValues.map HE.Spec.Eval.Entry.Value.erase = invocationAtoms target values)
    (safe : ∀ value ∈ prefixValues, Value program value.erase ∧ NoErrorSymbol value.erase)
    {raw : List Result}
    (completed : CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
      (.expression .active prefixValues) Atom.undefinedType frame raw (policy := policy)) :
    raw.map (fun result => result.1.erase) = answers ∧
      (∀ result ∈ raw, SafeResult program result) ∧
      ∀ names, Covers live names → PreservesAt names frame raw := by
  match source with
  | .constructor valid =>
      have value : Value program (HE.Spec.Eval.Entry.Value.expression .active prefixValues).erase := by
        simpa only [HE.Spec.Eval.Entry.Value.erase,image,invocationAtoms] using valid
      have shape := data_call_exact value completed
      rw [shape]
      refine ⟨by simp only [List.map_cons,List.map_nil,HE.Spec.Eval.Entry.Value.erase,image,invocationAtoms],?_,?_⟩
      · intro result member
        obtain rfl := List.mem_singleton.mp member
        refine ⟨value,?_⟩
        simp only [HE.Spec.Eval.Entry.Value.erase]
        exact .expression (fun atom member => by
          obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
          exact (safe entry present).2)
      · intro names _covered result member
        obtain rfl := List.mem_singleton.mp member
        exact HE.Spec.Bindings.ScopeObservation.ConservativeExtension.refl _ _
  | @Invocation.equations _ bindings head values selected answers ordinary scan nonempty bodies =>
      have code : CodeRel program [] (.expression .active prefixValues) :=
        invocation_code ordinary (by simpa only [invocationAtoms] using image) safe
      have represented : (HE.Spec.Eval.Entry.Value.expression .active prefixValues).erase =
          .expression (.symbol head::values) := by
        simp only [HE.Spec.Eval.Entry.Value.erase,image,invocationAtoms]
      have closed : HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol head::values)) = [] := by
        rw [←represented]; exact code.closed_vars
      have ground : MORK.isGroundAtom (.expression (.symbol head::values)) = true := by
        rw [←represented]; exact code.ground
      have clean : ¬HE.Spec.Eval.IsErrorRel (HE.Spec.Eval.Entry.Value.expression .active prefixValues).erase := by
        rw [represented]
        have headClean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
        simp [HE.Spec.Eval.IsErrorRel,headClean]
      cases completed with
      | error failed => exact (clean failed).elim
      | embedded _ _ embedded _ _ =>
          rw [represented,(ordinary.he_non_grounded values).2] at embedded
          cases embedded
      | absent _ _ frontier =>
          rw [represented] at frontier
          exact (nonempty ((scan.he_frontier_empty_iff (Atom.undefinedType::live) frame closed ground frontier).mp rfl)).elim
      | equations _ _ frontier _ completed =>
          have paired := scan.he_frontier_all (Atom.undefinedType::live) frame closed ground
            (by simpa only [represented] using frontier)
          rw [←represented] at paired
          have selectedData : ∀ value ∈ values, Value program value ∧ NoErrorSymbol value := by
            intro value member
            have present : value ∈ prefixValues.map HE.Spec.Eval.Entry.Value.erase := by
              rw [image]; exact List.mem_cons_of_mem _ member
            obtain ⟨entry,entryPresent,same⟩ := List.mem_map.mp present
            rw [←same]
            exact safe entry entryPresent
          exact he_bodies_exact bodies programCode plain policy live scope frame
            (.expression .active prefixValues) code.closed_vars frontier (fun _ member => member) paired
            (scan.captured_values selectedData) completed
termination_by structural source

theorem he_bodies_exact {program : Program} {selected : List ClauseWork} {answers : List Atom}
    (source : Bodies program selected answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (original : HE.Spec.Eval.Entry.Value)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars original.erase = [])
    {allWorks works : List HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program)
      (Atom.undefinedType::live) original.erase frame.bindings allWorks)
    (included : ∀ work ∈ works, work ∈ allWorks)
    (paired : List.Forall₂ (ClauseInstance original.erase) selected works)
    (captured : ∀ item ∈ selected, ∀ pair ∈ item.2.1, Value program pair.2 ∧ NoErrorSymbol pair.2)
    {raw : List Result}
    (completed : EquationBodiesRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup live scope
      original Atom.undefinedType frame works raw (policy := policy)) :
    raw.map (fun result => result.1.erase) = answers ∧
      (∀ result ∈ raw, SafeResult program result) ∧
      ∀ names, Covers live names → PreservesAt names frame raw := by
  match source with
  | .nil => cases paired; cases completed; exact ⟨rfl,by simp,by simp [PreservesAt]⟩
  | @Bodies.cons _ position bindings sourceBody selected children answers child remaining =>
      let item : ClauseWork := (position,bindings,sourceBody)
      cases paired with
      | @cons _ work _ works related pairs =>
          cases completed with
          | @cons _ _ _ produced _ _ _ _ _ _ _ after first rest _ reached _unified producer returned tail =>
              have present := included work List.mem_cons_self
              let body := after.read policy (HE.Spec.Eval.Entry.Value.ofAtom work.body)
              have bodyCode : CodeRel program [] body := related.body_code programCode frontier present closed
                (captured item List.mem_cons_self) after reached policy
              have bodyImage : body.erase = MORK.applySubst item.2.1 item.2.2 := by
                simpa only [related.2.1] using frontier_body_read frontier present item.2.1 related.2.2.1
                  (programCode.range.work_covered frontier present) closed after reached policy
              have producedShape : produced = [(body,after)] := by
                cases producer with
                | producerRaw => rfl
                | producerFunction pending _ => exact (child.input_not_function bodyImage policy pending).elim
              rw [producedShape] at returned
              have returnedOne := returned.single
              cases returnedOne with
              | returned returned =>
                  have returnable := child.input_returnable
                  have firstExact : first.map (fun result => result.1.erase) = children ∧
                      (∀ result ∈ first, SafeResult program result) ∧
                      ∀ names, Covers live names → PreservesAt names after first := by
                    cases returned with
                    | notReducible failed => exact (returnable.1 (bodyImage.symm.trans failed)).elim
                    | stopped failed => exact (returnable.2 (by rwa [bodyImage] at failed)).elim
                    | evaluate _ _ evaluated =>
                        exact he_evaluation_exact child programCode plain policy live scope after body bodyCode bodyImage evaluated
                  have restExact := he_bodies_exact remaining programCode plain policy live scope frame original closed
                    frontier (fun work member => included work (List.mem_cons_of_mem _ member)) pairs
                    (fun item member => captured item (List.mem_cons_of_mem _ member)) tail
                  refine ⟨by simp only [List.map_append,firstExact.1,restExact.1],?_,?_⟩
                  · intro result member
                    rcases List.mem_append.mp member with member | member
                    · exact firstExact.2.1 result member
                    · exact restExact.2.1 result member
                  · intro names covered result member
                    rcases List.mem_append.mp member with member | member
                    · have introduced := (related.caller_extension frontier present closed).restrict
                        (fun name present => covered.cons Atom.undefinedType name present)
                      rw [←reached] at introduced
                      exact introduced.trans (firstExact.2.2 names covered result member)
                    · exact restExact.2.2 names covered result member
termination_by structural source
end

/-- Recursive private instantiation preserves every caller observation in
the existing visible-query/live/binding scope, for every completed batch. -/
theorem he_evaluation_caller_observations {program : Program} {bindings : MORK.Subst}
    {expression : Atom} {answers : List Atom}
    (source : Evaluation program bindings expression answers) (programCode : CodeProgram program)
    (plain : program.declarations = []) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (input : HE.Spec.Eval.Entry.Value)
    (code : CodeRel program [] input) (image : input.erase = MORK.applySubst bindings expression)
    {results : List Result}
    (completed : AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope input Atom.undefinedType frame results (policy := policy)) :
    ∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
      (HE.EquationScope.visibleNames live input.erase frame.bindings) frame.bindings result.2.bindings := by
  have protectedResults := (he_evaluation_exact source programCode plain policy live scope frame input code image completed).2.2
    (live.flatMap HE.Spec.Type.Presentation.TypeSubst.typeVars) (fun _ member => member)
  intro result present
  apply (protectedResults result present).observations.restrict
  intro name member
  exact List.mem_append.mpr ((HE.EquationScope.visible_closed_iff code.closed_vars name).mp member)

end RecursiveTransport

/-- The actual source scan, rather than a supplied HE frontier or output
table, constructs the complete call for passive instantiated bodies. Source
copies, nonempty caller constraints and each reached binding frame survive. -/
theorem ClauseScan.he_passive_call {program : Program} {head : String} {values : List Atom}
    {selected : List ClauseWork} (source : ClauseScan head values 0 program.equations selected)
    (range : RangeRestricted program) (ordinary : OrdinaryHead head) (nonempty : selected ≠ [])
    (policy : HE.Spec.Eval.Completed.Policy) (live : List Atom) (scope : List String)
    (original : HE.Spec.Eval.Entry.Value) (frame : HE.Spec.Eval.Completed.Frame)
    (represented : original.erase = .expression (.symbol head::values))
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars original.erase = [])
    (ground : MORK.isGroundAtom original.erase = true)
    (passive : ∀ item ∈ selected, Value program (MORK.applySubst item.2.1 item.2.2) ∧
      NoErrorSymbol (MORK.applySubst item.2.1 item.2.2)) :
    ∃ works results,
      HE.Spec.Eval.Completed.CallRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope original Atom.undefinedType frame results (policy := policy) ∧
      results.map (fun result => result.1.erase) =
        selected.map (fun item => MORK.applySubst item.2.1 item.2.2) ∧
      List.Forall₂ (ClauseInstance original.erase) selected works ∧
      List.Forall₂ (fun work result => result.2.bindings = work.bindings) works results ∧
      ∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
        (HE.EquationScope.visibleNames (Atom.undefinedType::live) original.erase frame.bindings)
        frame.bindings result.2.bindings := by
  obtain ⟨works,frontier,paired⟩ := source.he_frontier (Atom.undefinedType::live) frame
    (by simpa only [represented] using closed) (by simpa only [represented] using ground)
  rw [←represented] at frontier paired
  have admitted : List.Forall₂ (fun work answer => Value program answer ∧ NoErrorSymbol answer ∧
      ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation work.bindings →
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation work.body = answer)
      works (selected.map (fun item => MORK.applySubst item.2.1 item.2.2)) := by
    apply List.forall₂_map_right_iff.mpr
    have selectedMembers := (List.forall₂_and_left selected works).mpr
      ⟨fun _ member => member,paired⟩
    have bothMembers := (List.forall₂_and_left works selected).mpr
      ⟨fun _ member => member,selectedMembers.flip⟩
    exact bothMembers.imp (fun work item related =>
      ⟨(passive item related.2.1).1,(passive item related.2.1).2,
        fun valuation model => related.2.2.body_model range frontier related.1 closed valuation model⟩)
  have workNonempty : works ≠ [] := by
    intro empty
    apply nonempty
    rw [empty] at paired
    exact List.forall₂_nil_right_iff.mp paired
  have notError : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
  obtain ⟨results,called,erased,frames⟩ := passive_equation_call policy live scope original frame
    (by simpa only [represented] using ordinary.he_non_grounded values)
    (by
      rw [represented]
      rintro ⟨tail,shape⟩
      exact notError (Atom.symbol.inj (List.cons.inj (Atom.expression.inj shape)).1))
    frontier workNonempty admitted
  refine ⟨works,results,called,erased,paired,frames,?_⟩
  intro result member
  obtain ⟨index,bound,same⟩ := List.getElem_of_mem member
  have workBound : index < works.length := by rw [frames.length_eq]; exact bound
  have sourceBound : index < selected.length := by rw [paired.length_eq]; exact workBound
  have one := paired.get sourceBound workBound
  have after := frames.get workBound bound
  simp only [List.get_eq_getElem] at one after
  rw [←same,after]
  exact one.caller_observations frontier (List.getElem_mem workBound) closed

/-- A complete call with passive source arguments and instantiated bodies
constructs full HE evaluation, including tuple traversal, return, readout,
success priority and occurrence publication under every local policy. -/
theorem ClauseScan.he_passive_evaluation {program : Program} {head : String}
    (arguments : List HE.Spec.Eval.Entry.Value) {selected : List ClauseWork}
    (source : ClauseScan head (arguments.map HE.Spec.Eval.Entry.Value.erase) 0 program.equations selected)
    (range : RangeRestricted program) (ordinary : OrdinaryHead head) (nonempty : selected ≠ [])
    (policy : HE.Spec.Eval.Completed.Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame)
    (values : ∀ argument ∈ arguments, Value program argument.erase)
    (safe : ∀ argument ∈ arguments, NoErrorSymbol argument.erase)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars
      (.expression (.symbol head::arguments.map HE.Spec.Eval.Entry.Value.erase)) = [])
    (ground : MORK.isGroundAtom
      (.expression (.symbol head::arguments.map HE.Spec.Eval.Entry.Value.erase)) = true)
    (passive : ∀ item ∈ selected, Value program (MORK.applySubst item.2.1 item.2.2) ∧
      NoErrorSymbol (MORK.applySubst item.2.1 item.2.2)) :
    ∃ results, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope (.expression .active (.symbol head::arguments)) Atom.undefinedType frame results
        (policy := policy) ∧
      results.map (fun result => result.1.erase) =
        selected.map (fun item => MORK.applySubst item.2.1 item.2.2) ∧
      ∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
        (HE.EquationScope.visibleNames (Atom.undefinedType::live)
          (.expression (.symbol head::arguments.map HE.Spec.Eval.Entry.Value.erase)) frame.bindings)
        frame.bindings result.2.bindings := by
  let input : HE.Spec.Eval.Entry.Value := .expression .active (.symbol head::arguments)
  have headValue : Value program (.symbol head) := ordinary.symbol_value
  have headSafe : NoErrorSymbol (.symbol head) :=
    .symbol (fun same => ordinary.2.2 (by simp [same]))
  obtain ⟨operands,tuple,erased⟩ := values_he_tuple (program := program) (.symbol head::arguments)
    (by
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [HE.Spec.Eval.Entry.Value.erase] using headValue
      · exact values value member)
    (by
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [HE.Spec.Eval.Entry.Value.erase] using headSafe
      · exact safe value member)
    frame (Atom.undefinedType::live) scope policy
  have operandErase : (HE.Spec.Eval.Entry.Value.expression .active operands).erase = input.erase := by
    simpa only [input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using congrArg Atom.expression erased
  obtain ⟨_works,results,called,resultErased,_paired,_frames,retained⟩ := source.he_passive_call range ordinary nonempty
    policy live scope (.expression .active operands) frame
    (by simpa only [input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using operandErase)
    (by simpa only [operandErase,input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using closed)
    (by simpa only [operandErase,input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using ground) passive
  have resultValue : ∀ result ∈ results, Value program result.1.erase := by
    intro result member
    have present : result.1.erase ∈ results.map (fun result => result.1.erase) := List.mem_map_of_mem member
    rw [resultErased] at present
    obtain ⟨item,present,same⟩ := List.mem_map.mp present
    rw [←same]
    exact (passive item present).1
  have resultRead : results.map (HE.Spec.Eval.Completed.readResult policy) = results := by
    calc
      _ = results.map id := by
        apply List.map_congr_left
        intro result member
        exact Prod.ext (HE.Spec.Eval.Completed.Frame.read_variable_free policy result.2 result.1
          (resultValue result member).variable_free) rfl
      _ = results := List.map_id _
  have noError : ∀ result ∈ results, HE.isErrorAtom result.1.erase = false := by
    intro result member
    have clean := (resultValue result member).boolean_clean
    simp only [HE.isEmptyOrError,Bool.or_eq_false_iff] at clean
    exact clean.2
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : HE.Spec.Eval.Completed.Result => HE.isErrorAtom result.1.erase)
      (results.map (HE.Spec.Eval.Completed.readResult policy)) results := by
    rw [resultRead]
    cases results with
    | nil => exact .allErrors (by simp)
    | cons first remaining =>
        have kept : (first::remaining).filter (fun result => !HE.isErrorAtom result.1.erase) =
            first::remaining := by
          apply List.filter_eq_self.mpr
          intro result member
          simp only [noError result member,Bool.not_false]
        simpa only [kept] using
          (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
            (isError := fun result : HE.Spec.Eval.Completed.Result => HE.isErrorAtom result.1.erase)
            (raw := first::remaining) ⟨first,List.mem_cons_self,noError first List.mem_cons_self⟩)
  have inputClosed : ∀ name, ¬HE.Spec.Match.Merge.AtomOccurs input.erase name := by
    intro name occurs
    have member := HE.Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
    have noVars : HE.Spec.Type.Presentation.TypeSubst.typeVars input.erase = [] := by
      simpa only [input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using closed
    simp only [noVars,List.not_mem_nil] at member
  have read := HE.Spec.Eval.Completed.Frame.read_variable_free policy frame input inputClosed
  have notError : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
  have notStopped : ¬HE.Spec.Eval.IsEmptyOrErrorRel input.erase := by
    simp [input,HE.Spec.Eval.Entry.Value.erase,HE.Spec.Eval.IsEmptyOrErrorRel,
      HE.Spec.Eval.IsErrorRel,Atom.empty,notError]
  have entered : HE.Spec.Eval.Entry.Rel policy.reentry (frame.read policy input).status
      (frame.read policy input).erase Atom.undefinedType .interpret := by
    rw [read]
    simp only [input,HE.Spec.Eval.Entry.Value.status,HE.Spec.Eval.Entry.Value.erase,List.map_cons]
    apply HE.Spec.Eval.Entry.Rel.expression
    · simpa only [input,HE.Spec.Eval.Entry.Value.erase,List.map_cons] using notStopped
    · simp [Atom.undefinedType,Atom.atomType,Atom.expressionType,Atom.variableType]
    · exact Or.inr rfl
  have completed := HE.Spec.Eval.Completed.AtomRel.tuple
    (space := equationSpace program) (dispatch := noForeign) (lookup := HE.Spec.Eval.Completed.rawLookup)
    (live := live) (scope := scope) (value := input) (expected := Atom.undefinedType)
    (frame := frame) (readiness := .active) (operator := .symbol head) (arguments := arguments)
    (policy := policy) entered read
    (by simpa only [HE.Spec.Eval.Entry.Value.erase,Multiset.coe_singleton] using
      (HE.Spec.Type.StorageTypesRel.symbolUndefined (equationSpace.no_annotations program (.symbol head))).occurrences) tuple
    (by simpa only [List.append_nil] using
      (HE.Spec.Eval.Completed.CallsRel.cons (children := results) (rest := []) called .nil)) priority
  refine ⟨results.map (HE.Spec.Eval.Completed.publishResult policy input.erase),?_,?_,?_⟩
  · simpa only [read,input] using completed
  · simpa only [List.map_map,Function.comp_def,HE.Spec.Eval.Completed.publishResult_erase] using resultErased
  · intro result member
    obtain ⟨before,present,rfl⟩ := List.mem_map.mp member
    simpa only [HE.Spec.Eval.Completed.publishResult,operandErase,input,
      HE.Spec.Eval.Entry.Value.erase,List.map_cons] using retained before present

/-- The same finite source scan and body derivations construct completed HE
and PeTTa evaluations. This comparison includes physical answer copies and
arbitrary certified HE caller frames. Its passive-body admission is explicit. -/
theorem ClauseScan.passive_completed_pair {program : Program} {head : String}
    {values : List Atom} {selected : List ClauseWork} {answers : List Atom}
    (source : ClauseScan head values 0 program.equations selected)
    (bodies : Bodies program selected answers) (plain : program.declarations = [])
    (range : RangeRestricted program) (defined : DefinedHead program head) (nonempty : selected ≠ [])
    (valueData : ∀ value ∈ values, Value program value)
    (safeData : ∀ value ∈ values, NoErrorSymbol value)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars (.expression (.symbol head::values)) = [])
    (ground : MORK.isGroundAtom (.expression (.symbol head::values)) = true)
    (passive : ∀ item ∈ selected, Value program (MORK.applySubst item.2.1 item.2.2) ∧
      NoErrorSymbol (MORK.applySubst item.2.1 item.2.2))
    (policy : HE.Spec.Eval.Completed.Policy) (live : List Atom) (scope : List String)
    (frame : HE.Spec.Eval.Completed.Frame) (state : PeTTa.Effects.State) :
    ∃ results, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope (HE.Spec.Eval.Entry.Value.ofAtom (.expression (.symbol head::values)))
        Atom.undefinedType frame results (policy := policy) ∧
      results.map (fun result => result.1.erase) = answers ∧
      (∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
        (HE.EquationScope.visibleNames (Atom.undefinedType::live)
          (.expression (.symbol head::values)) frame.bindings) frame.bindings result.2.bindings) ∧
      PeTTa.DeclarativeSpec.Runs program {state,control := .evaluate [] (.expression (.symbol head::values))}
        (.complete state answers [] []) := by
  have eraseArguments : (values.map HE.Spec.Eval.Entry.Value.ofAtom).map HE.Spec.Eval.Entry.Value.erase = values := by
    simp only [List.map_map,Function.comp_def,HE.Spec.Eval.Entry.Value.erase_ofAtom,List.map_id']
  have annotatedScan : ClauseScan head
      ((values.map HE.Spec.Eval.Entry.Value.ofAtom).map HE.Spec.Eval.Entry.Value.erase)
      0 program.equations selected := by rw [eraseArguments]; exact source
  obtain ⟨results,completed,erased,retained⟩ := annotatedScan.he_passive_evaluation
    (values.map HE.Spec.Eval.Entry.Value.ofAtom) range defined.1 nonempty policy live scope frame
    (by
      intro argument member
      obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
      simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using valueData value present)
    (by
      intro argument member
      obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
      simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using safeData value present)
    (by simpa only [eraseArguments] using closed) (by simpa only [eraseArguments] using ground) passive
  have invocation : Invocation program [] (.function head) values answers :=
    .equations defined.1 source nonempty bodies
  obtain ⟨query⟩ := invocation.with_value_arguments defined valueData
  refine ⟨results,?_,erased.trans (bodies.passive_answers plain (fun item member => (passive item member).1)).symm,?_,
    query.petta_source plain state⟩
  · simpa only [HE.Spec.Eval.Entry.Value.ofAtom,List.map_cons] using completed
  · simpa only [eraseArguments] using retained

namespace RecursiveControls

def numeral : Nat → Atom
  | 0 => .symbol "Z"
  | n+1 => .expression [.symbol "S",numeral n]

def boxed : Atom := .expression [.symbol "Box",.symbol "Z"]
def tailCall : Atom := .expression [.symbol "strip",.var "x"]
def base : Equation := ⟨"strip",[.symbol "Z"],boxed⟩
def stepRule : Equation := ⟨"strip",[.expression [.symbol "S",.var "x"]],tailCall⟩
def forkRule : Equation := ⟨"fork",[.var "x"],tailCall⟩
def program : Program := {equations := [base,stepRule,forkRule,forkRule],declarations := []}

theorem ordinary_strip : OrdinaryHead "strip" := by
  unfold OrdinaryHead
  decide +kernel
theorem ordinary_fork : OrdinaryHead "fork" := by
  unfold OrdinaryHead
  decide +kernel
theorem passive_s : ConstructorHead program "S" := by
  constructor
  · unfold OrdinaryHead; decide +kernel
  · simp [program,base,stepRule,forkRule]
theorem passive_box : ConstructorHead program "Box" := by
  constructor
  · unfold OrdinaryHead; decide +kernel
  · simp [program,base,stepRule,forkRule]

theorem numeral_value (n : Nat) : Value program (numeral n) := by
  induction n with
  | zero => exact .symbol "Z" (by decide +kernel) (by decide +kernel)
  | succ n ih =>
      exact .constructor passive_s (by
        intro value member
        obtain rfl := List.mem_singleton.mp member
        exact ih)

theorem boxed_value : Value program boxed :=
  .constructor passive_box (by
    intro value member
    obtain rfl := List.mem_singleton.mp member
    exact .symbol "Z" (by decide +kernel) (by decide +kernel))

theorem defined_strip : DefinedHead program "strip" :=
  ⟨ordinary_strip,base,List.mem_cons_self,rfl⟩

theorem defined_fork : DefinedHead program "fork" :=
  ⟨ordinary_fork,forkRule,by simp [program],rfl⟩

/-- The existing recursive, duplicate-clause program has passive open patterns. -/
theorem constructor_patterns : ConstructorPatterns program := by
  intro equation present
  change equation ∈ [base,stepRule,forkRule,forkRule] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at present
  rcases present with rfl | rfl | rfl
  · refine ⟨ordinary_strip,?_⟩
    intro argument member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.symbol "Z" (by decide +kernel) (by decide +kernel),.symbol (by decide +kernel)⟩
  · refine ⟨ordinary_strip,?_⟩
    intro argument member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨.constructor passive_s ?_,.expression ?_⟩
    · intro child present
      obtain rfl := List.mem_singleton.mp present
      exact .variable (by decide +kernel)
    · intro child present
      rcases List.mem_cons.mp present with rfl | present
      · exact .symbol (by decide +kernel)
      · obtain rfl := List.mem_singleton.mp present
        exact .variable "x"
  · refine ⟨ordinary_fork,?_⟩
    intro argument member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.variable (by decide +kernel),.variable "x"⟩

/-- Placing a defined call inside a pattern is rejected even though its
body may be harmless data. Open callers could capture that active call. -/
theorem active_clause_pattern_rejected :
    ¬ConstructorPatterns {program with equations :=
      ⟨"fork",[tailCall],.symbol "Z"⟩ :: program.equations} := by
  let bad : Program := {program with equations :=
    ⟨"fork",[tailCall],.symbol "Z"⟩ :: program.equations}
  change ¬ConstructorPatterns bad
  intro admitted
  have valid := (admitted ⟨"fork",[tailCall],.symbol "Z"⟩ List.mem_cons_self).2
    tailCall List.mem_cons_self
  have defined : DefinedHead bad "strip" :=
    ⟨ordinary_strip,base,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  exact defined.not_constructor_value [.var "x"] _ valid.1

private theorem base_scan : ClauseScan "strip" [numeral 0] 0 program.equations [(0,[],boxed)] := by
  dsimp only [program]
  apply ClauseScan.hit (equation := base) rfl (by decide +kernel) (.expr_cons .symbol .expr_nil)
  apply ClauseScan.miss (equation := stepRule) rfl (by decide +kernel)
  · intro bindings matched
    simp only [stepRule] at matched
    cases matched with
    | expr_cons head _tail => cases head
  · exact .other (by decide +kernel) (.other (by decide +kernel) (.nil 4))

private theorem step_scan (n : Nat) : ClauseScan "strip" [numeral (n+1)] 0 program.equations
    [(1,[("x",numeral n)],tailCall)] := by
  dsimp only [program]
  apply ClauseScan.miss (equation := base) rfl (by decide +kernel)
  · intro bindings matched
    simp only [base,numeral] at matched
    cases matched with
    | expr_cons head _tail => cases head
  · exact .hit rfl (by decide +kernel)
      (.expr_cons (.expr_cons .symbol (.expr_cons (.var_fresh rfl) .expr_nil)) .expr_nil)
      (.other (by decide +kernel) (.other (by decide +kernel) (.nil 4)))

private theorem fork_scan (n : Nat) : ClauseScan "fork" [numeral n] 0 program.equations
    [(2,[("x",numeral n)],tailCall),(3,[("x",numeral n)],tailCall)] :=
  .other (by decide +kernel) (.other (by decide +kernel)
    (.hit rfl (by decide +kernel) (.expr_cons (.var_fresh rfl) .expr_nil)
      (.hit rfl (by decide +kernel) (.expr_cons (.var_fresh rfl) .expr_nil) (.nil 4))))

private def boundBody (n : Nat)
    (called : Invocation program [("x",numeral n)] (.function "strip") [numeral n] [boxed]) :
    Evaluation program [("x",numeral n)] tailCall [boxed] := by
  apply Evaluation.call defined_strip
  simpa only [List.map_cons,List.map_nil,List.nil_append] using
    (Arguments.single_results (.function ordinary_strip) [(.var "x",numeral n)]
      (fun pair member => by
        obtain rfl := List.mem_singleton.mp member
        simpa [MORK.applySubst,MORK.Subst.lookup] using
          (Evaluation.variable (bindings := [("x",numeral n)]) (name := "x")
            (by simpa [MORK.applySubst,MORK.Subst.lookup] using numeral_value n)))
      (values := []) (index := 0) called)

/-- Structural recursion follows the represented natural, without any fixed
interpreter depth bound or hidden nested evaluation allowance. -/
private theorem strip_invocation (n : Nat) (bindings : MORK.Subst) :
    Nonempty (Invocation program bindings (.function "strip") [numeral n] [boxed]) := by
  induction n generalizing bindings with
  | zero =>
      obtain ⟨body⟩ := boxed_value.evaluates []
      exact ⟨.equations ordinary_strip base_scan (by simp) (.cons body .nil)⟩
  | succ n ih =>
      obtain ⟨called⟩ := ih [("x",numeral n)]
      exact ⟨.equations ordinary_strip (step_scan n) (by simp) (.cons (boundBody n called) .nil)⟩

/-- Two equal physical clauses each recursively strip an arbitrarily deep
constructor input. Their equal answers remain two separate occurrences. -/
theorem duplicate_recursive_source (n : Nat) :
    Nonempty (Evaluation program [] (.expression [.symbol "fork",numeral n]) [boxed,boxed]) := by
  obtain ⟨stripped⟩ := strip_invocation n [("x",numeral n)]
  have body := boundBody n stripped
  have called : Invocation program [] (.function "fork") [numeral n] [boxed,boxed] :=
    .equations ordinary_fork (fork_scan n) (by simp) (.cons body (.cons body .nil))
  obtain ⟨argument⟩ := (numeral_value n).evaluates []
  refine ⟨.call defined_fork ?_⟩
  simpa only [List.map_cons,List.map_nil,List.nil_append] using
    (Arguments.single_results (.function ordinary_fork) [(numeral n,numeral n)]
      (fun pair member => by
        obtain rfl := List.mem_singleton.mp member
        exact argument) (values := []) (index := 0) called)

/-- The actual independent PeTTa source produces exactly those two answers
for every input depth and every initial pure world. -/
theorem duplicate_recursive_petta (n : Nat) (state : PeTTa.Effects.State) :
    PeTTa.DeclarativeSpec.Runs program
      {state,control := .evaluate [] (.expression [.symbol "fork",numeral n])}
      (.complete state [boxed,boxed] [] []) := by
  obtain ⟨source⟩ := duplicate_recursive_source n
  exact source.petta_source rfl state

/-- Every input depth produces two fresh recursive body occurrences with
the same materialized tail call, under arbitrary retained caller constraints. -/
theorem duplicate_recursive_frontier (n : Nat) (live : List Atom)
    (frame : HE.Spec.Eval.Completed.Frame) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program) live
        (.expression [.symbol "fork",numeral n]) frame.bindings works ∧
      works.map HE.Spec.Eval.Steps.EquationWork.position = [2,3] ∧
      ∀ work ∈ works,
        HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
          (HE.EquationScope.visibleNames live (.expression [.symbol "fork",numeral n]) frame.bindings)
          frame.bindings work.bindings ∧
        ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation work.bindings →
          HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation work.body =
            .expression [.symbol "strip",numeral n] := by
  have closedNumeral : HE.Spec.Type.Presentation.TypeSubst.typeVars (numeral n) = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simp [numeral,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList,ih]
  have groundNumeral : MORK.isGroundAtom (numeral n) = true := by
    clear closedNumeral
    induction n with
    | zero => rfl
    | succ n ih => simp [numeral,MORK.isGroundAtom,MORK.isGroundAtom.isGroundList,ih]
  have closed : HE.Spec.Type.Presentation.TypeSubst.typeVars
      (.expression [.symbol "fork",numeral n]) = [] := by
    simp [HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,closedNumeral]
  have range : RangeRestricted program := by
    simp [RangeRestricted,program,base,stepRule,forkRule,tailCall,boxed,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,HE.Spec.Type.Presentation.TypeSubst.typeVarsList]
  obtain ⟨works,frontier,paired⟩ := (fork_scan n).he_frontier live frame closed
    (by simp [MORK.isGroundAtom,MORK.isGroundAtom.isGroundList,groundNumeral])
  cases paired with
  | cons first tail =>
      cases tail with
      | cons second empty =>
          cases empty
          refine ⟨_,frontier,by simp only [List.map_cons,List.map_nil,first.1,second.1],?_⟩
          intro work member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · refine ⟨first.caller_observations frontier List.mem_cons_self closed,?_⟩
            intro valuation satisfied
            simpa [tailCall,MORK.applySubst,MORK.applySubst.applySubstList,MORK.Subst.lookup] using
              first.body_model range frontier List.mem_cons_self closed valuation satisfied
          · refine ⟨second.caller_observations frontier (List.mem_cons_of_mem _ List.mem_cons_self) closed,?_⟩
            intro valuation satisfied
            simpa [tailCall,MORK.applySubst,MORK.applySubst.applySubstList,MORK.Subst.lookup] using
              second.body_model range frontier (List.mem_cons_of_mem _ List.mem_cons_self) closed valuation satisfied

theorem numeral_safe (n : Nat) : NoErrorSymbol (numeral n) := by
  induction n with
  | zero => exact .symbol (by decide +kernel)
  | succ n ih =>
      apply NoErrorSymbol.expression
      intro atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact .symbol (by decide +kernel)
      · obtain rfl := List.mem_singleton.mp member; exact ih

theorem boxed_safe : NoErrorSymbol boxed := by
  apply NoErrorSymbol.expression
  intro atom member
  rcases List.mem_cons.mp member with rfl | member
  · exact .symbol (by decide +kernel)
  · obtain rfl := List.mem_singleton.mp member
    exact .symbol (by decide +kernel)

private theorem tail_code (scope : List String) (covered : "x" ∈ scope) :
    CodeRel program scope (HE.Spec.Eval.Entry.Value.ofAtom tailCall) := by
  have children : CodeRel program scope
      (.expression .active [.symbol "strip",.var "x"]) := by
    apply CodeRel.active ordinary_strip
    intro atom member
    obtain rfl := List.mem_singleton.mp member
    exact .variable covered
  simpa only [tailCall,HE.Spec.Eval.Entry.Value.ofAtom,List.map_cons,List.map_nil] using children

theorem program_code : CodeProgram program := by
  intro equation member
  simp only [program,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · apply CodeRel.data
    · simpa only [base,HE.Spec.Eval.Entry.Value.erase_ofAtom,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.append_nil] using boxed_value
    · simpa only [base,HE.Spec.Eval.Entry.Value.erase_ofAtom] using boxed_safe
  all_goals
    apply tail_code
    simp [stepRule,forkRule,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList]

private theorem call_code (head : String) (ordinary : OrdinaryHead head) (n : Nat) :
    CodeRel program [] (HE.Spec.Eval.Entry.Value.ofAtom (.expression [.symbol head,numeral n])) := by
  have children : CodeRel program [] (.expression .active
      [.symbol head,HE.Spec.Eval.Entry.Value.ofAtom (numeral n)]) := by
    apply CodeRel.active ordinary
    intro atom member
    obtain rfl := List.mem_singleton.mp member
    exact .data (by simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using numeral_value n)
      (by simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using numeral_safe n)
  simpa only [HE.Spec.Eval.Entry.Value.ofAtom,List.map_cons,List.map_nil] using children

/-- Recursive bodies complete in HE for arbitrary input depth, policy and
certified caller. Equal source clauses contribute two equal answer copies. -/
theorem duplicate_recursive_he (n : Nat) (policy : HE.Spec.Eval.Completed.Policy)
    (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame) :
    ∃ results, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope (HE.Spec.Eval.Entry.Value.ofAtom (.expression [.symbol "fork",numeral n]))
        Atom.undefinedType frame results (policy := policy) ∧
      results.map (fun result => result.1.erase) = [boxed,boxed] ∧
      ∀ result ∈ results, RecursiveTransport.SafeResult program result := by
  obtain ⟨source⟩ := duplicate_recursive_source n
  exact RecursiveTransport.he_evaluation source program_code rfl policy live scope frame _
    (call_code "fork" ordinary_fork n)
    (by simp only [HE.Spec.Eval.Entry.Value.erase_ofAtom,MORK.applySubst_nil])

private def nestedQuery (n : Nat) : Atom := .expression
  [.symbol "Box",.expression [.symbol "fork",numeral n],.expression [.symbol "fork",numeral n]]

private def nestedAnswer : Atom := .expression [.symbol "Box",boxed,boxed]

private theorem nested_value : Value program nestedAnswer := by
  apply Value.constructor passive_box
  intro atom member
  have same : atom = boxed := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  rw [same]; exact boxed_value

private theorem nested_source (n : Nat) :
    Nonempty (Evaluation program [] (nestedQuery n) [nestedAnswer,nestedAnswer,nestedAnswer,nestedAnswer]) := by
  obtain ⟨forked⟩ := duplicate_recursive_source n
  let done : Arguments program [] .data [] [.symbol "Box",boxed,boxed] 3 [nestedAnswer] :=
    .done (.constructor nested_value)
  let second : Arguments program [] .data [.expression [.symbol "fork",numeral n]]
      [.symbol "Box",boxed] 2 [nestedAnswer,nestedAnswer] :=
    .next .data forked (ArgumentCases.cons (values := [.symbol "Box",boxed]) (index := 2) (head := boxed)
      done (ArgumentCases.cons (values := [.symbol "Box",boxed]) (index := 2) (head := boxed) done .nil))
  let first : Arguments program [] .data
      [.expression [.symbol "fork",numeral n],.expression [.symbol "fork",numeral n]]
      [.symbol "Box"] 1 [nestedAnswer,nestedAnswer,nestedAnswer,nestedAnswer] :=
    .next .data forked (ArgumentCases.cons (values := [.symbol "Box"]) (index := 1) (head := boxed)
      second (ArgumentCases.cons (values := [.symbol "Box"]) (index := 1) (head := boxed) second .nil))
  exact ⟨.constructor passive_box (.next .data (.symbol (.symbol "Box" (by decide +kernel)
    (by decide +kernel))) (ArgumentCases.cons (values := []) (index := 0) (head := .symbol "Box") first .nil))⟩

private theorem nested_code (n : Nat) :
    CodeRel program [] (HE.Spec.Eval.Entry.Value.ofAtom (nestedQuery n)) := by
  have children : CodeRel program [] (.expression .active
      [.symbol "Box",HE.Spec.Eval.Entry.Value.ofAtom (.expression [.symbol "fork",numeral n]),
        HE.Spec.Eval.Entry.Value.ofAtom (.expression [.symbol "fork",numeral n])]) := by
    apply CodeRel.active passive_box.1
    intro atom member
    have same : atom = HE.Spec.Eval.Entry.Value.ofAtom (.expression [.symbol "fork",numeral n]) := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
    rw [same]
    exact call_code "fork" ordinary_fork n
  simpa only [nestedQuery,HE.Spec.Eval.Entry.Value.ofAtom,List.map_cons,List.map_nil] using children

/-- Two recursive binary choices in separate argument positions retain four
equal completed answers in both dialects, at every recursion depth. -/
theorem nested_recursive_completed_pair (n : Nat) (policy : HE.Spec.Eval.Completed.Policy)
    (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame)
    (state : PeTTa.Effects.State) :
    ∃ results, HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
        live scope (HE.Spec.Eval.Entry.Value.ofAtom (nestedQuery n)) Atom.undefinedType frame results
        (policy := policy) ∧
      results.map (fun result => result.1.erase) = [nestedAnswer,nestedAnswer,nestedAnswer,nestedAnswer] ∧
      PeTTa.DeclarativeSpec.Runs program {state,control := .evaluate [] (nestedQuery n)}
        (.complete state [nestedAnswer,nestedAnswer,nestedAnswer,nestedAnswer] [] []) := by
  obtain ⟨source⟩ := nested_source n
  obtain ⟨results,completed,erased,_safe⟩ := RecursiveTransport.he_evaluation source program_code rfl
    policy live scope frame _ (nested_code n)
    (by simp only [HE.Spec.Eval.Entry.Value.erase_ofAtom,MORK.applySubst_nil])
  exact ⟨results,completed,erased,source.petta_source rfl state⟩

/-- Every completion of the nested recursive choice has the same four
answer occurrences, including arbitrary certified caller constraints. -/
theorem nested_recursive_completion_exact (n : Nat) (policy : HE.Spec.Eval.Completed.Policy)
    (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame)
    {results : List HE.Spec.Eval.Completed.Result}
    (completed : HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (HE.Spec.Eval.Entry.Value.ofAtom (nestedQuery n)) Atom.undefinedType frame results
      (policy := policy)) :
    results.map (fun result => result.1.erase) = [nestedAnswer,nestedAnswer,nestedAnswer,nestedAnswer] := by
  obtain ⟨source⟩ := nested_source n
  exact (RecursiveTransport.he_evaluation_exact source program_code rfl policy live scope frame _ (nested_code n)
    (by simp only [HE.Spec.Eval.Entry.Value.erase_ofAtom,MORK.applySubst_nil]) completed).1

/-- Sharing the two independent argument choices would lose two answers.
No completed derivation of this source query has that two-answer readout. -/
theorem nested_recursive_cannot_drop_choice (n : Nat) (policy : HE.Spec.Eval.Completed.Policy)
    (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame)
    {results : List HE.Spec.Eval.Completed.Result}
    (completed : HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (HE.Spec.Eval.Entry.Value.ofAtom (nestedQuery n)) Atom.undefinedType frame results
      (policy := policy)) : results.length ≠ 2 := by
  have length := congrArg List.length (nested_recursive_completion_exact n policy live scope frame completed)
  simp only [List.length_map,List.length_cons,List.length_nil] at length
  omega

/-- The all-depth recursive choice also preserves the full incoming caller
observer, including aliases and names in retained continuation syntax. -/
theorem nested_recursive_caller_observations (n : Nat) (policy : HE.Spec.Eval.Completed.Policy)
    (live : List Atom) (scope : List String) (frame : HE.Spec.Eval.Completed.Frame)
    {results : List HE.Spec.Eval.Completed.Result}
    (completed : HE.Spec.Eval.Completed.AtomRel (equationSpace program) noForeign HE.Spec.Eval.Completed.rawLookup
      live scope (HE.Spec.Eval.Entry.Value.ofAtom (nestedQuery n)) Atom.undefinedType frame results
      (policy := policy)) :
    ∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
      (HE.EquationScope.visibleNames live (nestedQuery n) frame.bindings) frame.bindings result.2.bindings := by
  obtain ⟨source⟩ := nested_source n
  simpa only [HE.Spec.Eval.Entry.Value.erase_ofAtom] using
    RecursiveTransport.he_evaluation_caller_observations source program_code rfl policy live scope frame _ (nested_code n)
      (by simp only [HE.Spec.Eval.Entry.Value.erase_ofAtom,MORK.applySubst_nil]) completed

/-- Readiness cannot silently turn a recursive call into passive data in the
common fragment. This is a source-admission separation, not a backend quirk. -/
theorem held_recursive_call_not_admitted (n : Nat) :
    ¬CodeRel program [] (.expression .held [.symbol "strip",HE.Spec.Eval.Entry.Value.ofAtom (numeral n)]) := by
  intro code
  cases code with
  | data valid _safe =>
      simp only [HE.Spec.Eval.Entry.Value.erase,List.map_cons,List.map_nil,
        HE.Spec.Eval.Entry.Value.erase_ofAtom] at valid
      cases valid with
      | constructor passive _values => exact passive.2 base List.mem_cons_self rfl

end RecursiveControls

namespace PassiveCallControls

open HE.Spec.Eval HE.Spec.Eval.Completed HE.Spec.Eval.Steps
open HE.Spec.Match.Merge HE.Spec.Bindings.ScopeObservation

private def datum : Atom := .expression [.symbol "Box",.symbol "Z"]
private def query : Atom := .expression [.symbol "emit"]
private def equation : Equation := ⟨"emit",[],datum⟩
private def program : Program := {equations := [equation,equation],declarations := []}
private def work (bindings : HE.Bindings) (position : Nat) : EquationWork :=
  ⟨position,query,datum,query,datum,bindings⟩

private theorem datum_value : Value program datum := by
  apply Value.constructor
  · constructor
    · unfold OrdinaryHead; decide +kernel
    · simp [program,equation]
  · intro atom member
    obtain rfl := List.mem_singleton.mp member
    exact .symbol "Z" (by decide +kernel) (by decide +kernel)

private theorem datum_safe : NoErrorSymbol datum :=
  .expression (by
    intro atom member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .symbol (by decide +kernel))

private theorem frontier (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) :
    EquationFrontierRel (equationSpace program) live query frame.bindings
      [work frame.bindings 0,work frame.bindings 1] := by
  have variant : AlphaVariantRel live query frame.bindings query datum query datum := by
    refine ⟨id,Function.injective_id,.expression (.cons (.symbol _) .nil),
      .expression (.cons (.symbol _) (.cons (.symbol _) .nil)),?_⟩
    intro name occurs
    rcases occurs with occurs | occurs
    · have member := atomOccurs_mem_typeVars occurs
      simp [query,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at member
    · exact ((datum_value.variable_free name) occurs).elim
  have matched : MatchRel equalityGroundedSemantic query query HE.Bindings.empty :=
    .expression (.cons (.symSym _ semanticLoopFree_empty)
      (.mk (order := []) (List.Perm.refl _) .nil) .nil) semanticLoopFree_empty
  have merged : LogicalMergeRel HE.Bindings.empty frame.bindings frame.bindings :=
    ⟨by simpa only [HE.Bindings.empty,List.nil_append] using HE.BindingSourceAgreement.refl frame.bindings,
      frame.certified.satisfiable⟩
  have hit (position : Nat) : EquationRowResultsRel live query frame.bindings position equation.toAtom
      [work frame.bindings position] := .hit _ _ _ _ _ _ _ variant matched merged
  apply EquationFrontierRel.completed (blocks := [[work frame.bindings 0],[work frame.bindings 1]])
  exact .cons (hit 0) (.cons (hit 1) .nil)

/-- A real completed source call retains two equal physical clauses and
their result frames for every certified caller, including alias-bearing
nonempty callers. No identity decoder or supplied evaluation reply is used. -/
theorem duplicate_call (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom) (scope : List String) (policy : Policy) :
    ∃ results, CallRel (equationSpace program) noForeign rawLookup live scope
        (Entry.Value.ofAtom query) Atom.undefinedType frame results (policy := policy) ∧
      results.map (fun result => result.1.erase) = [datum,datum] ∧
      List.Forall₂ (fun work result => result.2.bindings = work.bindings)
        [work frame.bindings 0,work frame.bindings 1] results := by
  apply passive_equation_call policy live scope (Entry.Value.ofAtom query) frame
  · have ordinary : OrdinaryHead "emit" := by unfold OrdinaryHead; decide +kernel
    simpa only [Entry.Value.erase_ofAtom,query] using ordinary.he_non_grounded []
  · simp [IsErrorRel,Entry.Value.erase_ofAtom,query]
  · simpa only [Entry.Value.erase_ofAtom] using frontier frame (Atom.undefinedType::live)
  · simp
  · have admitted (position : Nat) : Value program datum ∧ NoErrorSymbol datum ∧
        ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation (work frame.bindings position).bindings →
          HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation (work frame.bindings position).body = datum :=
      ⟨datum_value,datum_safe,fun _ _ => by simp [work,datum,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]⟩
    exact .cons (admitted 0) (.cons (admitted 1) .nil)

private def bindingRule : Equation :=
  ⟨"pack",[.var "x"],.expression [.symbol "Box",.var "x",.var "x"]⟩
private def bindingProgram : Program := {equations := [bindingRule,bindingRule],declarations := []}
private def bindingDatum : Atom := .expression [.symbol "Box",.symbol "A",.symbol "A"]
private abbrev bindingSelected : List ClauseWork :=
  [(0,[("x",.symbol "A")],bindingRule.body),(1,[("x",.symbol "A")],bindingRule.body)]

private theorem bindingDatum_value : Value bindingProgram bindingDatum := by
  apply Value.constructor
  · constructor
    · unfold OrdinaryHead; decide +kernel
    · simp [bindingProgram,bindingRule]
  · intro atom member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .symbol "A" (by decide +kernel) (by decide +kernel)

private theorem bindingDatum_safe : NoErrorSymbol bindingDatum :=
  .expression (by
    intro atom member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .symbol (by decide +kernel))

private def binding_body : Evaluation bindingProgram [("x",.symbol "A")] bindingRule.body [bindingDatum] := by
  apply Evaluation.constructor
  · constructor
    · unfold OrdinaryHead; decide +kernel
    · simp [bindingProgram,bindingRule]
  · apply Arguments.next .data (.symbol (.symbol "Box" (by decide +kernel) (by decide +kernel)))
    apply ArgumentCases.cons (children := [bindingDatum]) (remaining := [])
    · apply Arguments.next .data (.variable (by
        simpa [MORK.applySubst,MORK.Subst.lookup] using
          (Value.symbol (program := bindingProgram) "A" (by decide +kernel) (by decide +kernel))))
      apply ArgumentCases.cons (children := [bindingDatum]) (remaining := [])
      · apply Arguments.next .data (.variable (by
          simpa [MORK.applySubst,MORK.Subst.lookup] using
            (Value.symbol (program := bindingProgram) "A" (by decide +kernel) (by decide +kernel))))
        exact .cons (.done (.constructor bindingDatum_value)) .nil
      · exact .nil
    · exact .nil

/-- Captured rule variables, repeated body uses and duplicate stored copies
survive full evaluation in both dialects, for every certified caller frame. -/
theorem captured_duplicate_completed (frame : HE.Spec.Eval.Completed.Frame) (live : List Atom)
    (scope : List String) (policy : Policy) (state : PeTTa.Effects.State) :
    ∃ results, AtomRel (equationSpace bindingProgram) noForeign rawLookup live scope
        (Entry.Value.ofAtom (.expression [.symbol "pack",.symbol "A"])) Atom.undefinedType frame results
        (policy := policy) ∧ results.map (fun result => result.1.erase) = [bindingDatum,bindingDatum] ∧
      (∀ result ∈ results, HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
        (HE.EquationScope.visibleNames (Atom.undefinedType::live)
          (.expression [.symbol "pack",.symbol "A"]) frame.bindings) frame.bindings result.2.bindings) ∧
      PeTTa.DeclarativeSpec.Runs bindingProgram
        {state,control := .evaluate [] (.expression [.symbol "pack",.symbol "A"])}
        (.complete state [bindingDatum,bindingDatum] [] []) := by
  have scan : ClauseScan "pack" [.symbol "A"] 0 bindingProgram.equations bindingSelected :=
    .hit rfl (by decide +kernel) (.expr_cons (.var_fresh rfl) .expr_nil)
      (.hit rfl (by decide +kernel) (.expr_cons (.var_fresh rfl) .expr_nil) (.nil 2))
  have range : RangeRestricted bindingProgram := by
    simp [RangeRestricted,bindingProgram,bindingRule,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList]
  have ordinary : OrdinaryHead "pack" := by unfold OrdinaryHead; decide +kernel
  apply scan.passive_completed_pair (.cons binding_body (.cons binding_body .nil)) rfl range
    ⟨ordinary,bindingRule,List.mem_cons_self,rfl⟩ (by simp) ?_ ?_ (by decide +kernel)
    (by decide +kernel) ?_ policy live scope frame state
  · intro value member
    obtain rfl := List.mem_singleton.mp member
    exact .symbol "A" (by decide +kernel) (by decide +kernel)
  · intro value member
    obtain rfl := List.mem_singleton.mp member
    exact .symbol (by decide +kernel)
  · intro item member
    simp only [bindingSelected,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simpa [bindingRule,bindingDatum,MORK.applySubst,MORK.applySubst.applySubstList,MORK.Subst.lookup] using
        (show Value bindingProgram bindingDatum ∧ NoErrorSymbol bindingDatum from
          ⟨bindingDatum_value,bindingDatum_safe⟩)

end PassiveCallControls

namespace MarkerHeadControls

open HE.Spec.Eval HE.Spec.Eval.Completed

private def program : Program := {equations := [],declarations := []}
private def expression : Atom := .expression [.symbol "Empty",.symbol "A"]
private def contextual : Entry.Value := Entry.Value.ofAtom expression

/-- The common passive-value grammar excludes an active control-marker head. -/
theorem marker_not_passive : ¬Value program expression := by
  intro value
  cases value with
  | constructor passive _values =>
      exact passive.1.2.2 (by simp)

/-- PeTTa's independent source retains this ordinary constructor expression. -/
theorem petta_retains_marker_head :
    PeTTa.DeclarativeSpec.Runs program
      {state := PeTTa.Effects.empty,control := .evaluate [] expression}
      (.complete PeTTa.Effects.empty [expression] [] []) := by
  apply (PeTTa.Eval.completed_run_iff_derivation _ _ _ _ _ _).mp
  apply PeTTa.Eval.path_has_sufficient_fuel
  exact PeTTa.Eval.unary_constructor_of_returns program [] _ _ "Empty"
    (.symbol "A") (.symbol "A") (by decide +kernel) (by decide +kernel)
    (PeTTa.Eval.symbol_returns _ _ _ _)

/-- Active HE tuple evaluation reaches the marker before the other argument.
This is a source rule consequence for every occurrence-marking policy. -/
theorem he_active_marker_head (policy : Policy) :
    AtomRel HE.Space.empty noForeign rawLookup [] [] contextual Atom.undefinedType Frame.empty
      [(.symbol "Empty",Frame.empty)] (policy := policy) := by
  apply AtomRel.tuple (readiness := .active) (operator := .symbol "Empty")
    (arguments := [.symbol "A"]) (rows := [(.symbol "Empty",Frame.empty)])
    (raw := [(.symbol "Empty",Frame.empty)]) (selected := [(.symbol "Empty",Frame.empty)])
  · simp only [Frame.read_empty,contextual,expression,Entry.Value.ofAtom,
      List.map_cons,List.map_nil,Entry.Value.status,Entry.Value.erase]
    exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
      (by decide +kernel) (Or.inr rfl)
  · simp [contextual,expression,Entry.Value.ofAtom]
  · simpa only [Entry.Value.erase,HE.Space.empty,Multiset.coe_singleton] using
      (HE.Spec.Type.StorageTypesRel.symbolUndefined (name := "Empty") HE.Spec.Type.AnnotationTypesRel.nil).occurrences
  · apply TupleRel.cons (heads := [(.symbol "Empty",Frame.empty)])
    · have delivered := AtomRel.delivered (space := HE.Space.empty) (dispatch := noForeign)
        (lookup := rawLookup) (scope := [])
        (live := [.expression [.symbol "A"],Atom.undefinedType])
        (value := .symbol "Empty") (expected := Atom.undefinedType) (frame := Frame.empty)
        (policy := policy)
        (by
          simp only [Frame.read_empty,Entry.Value.status,Entry.Value.erase]
          exact Entry.Rel.stopped (Or.inl rfl))
      simpa only [Frame.read_empty,Entry.Value.erase,List.map_cons,List.map_nil] using delivered
    · exact .stopped (by simp [IsEmptyOrErrorRel,Entry.Value.erase,Atom.empty]) .nil
  · apply CallsRel.cons (children := [(.symbol "Empty",Frame.empty)]) (rest := []) _ .nil
    apply CallRel.absent (space := HE.Space.empty) (dispatch := noForeign) (lookup := rawLookup)
      (value := .symbol "Empty") (expected := Atom.undefinedType) (frame := Frame.empty)
    · simp [IsErrorRel,Entry.Value.erase]
    · simp [NonGroundedCallRel,Minimal.HostCall,noForeign,Minimal.embeddedInstruction,Entry.Value.erase]
    · apply HE.Spec.Eval.Steps.EquationFrontierRel.completed (blocks := [])
      change List.Forall₂ _ [] []
      exact .nil
  · simpa [readResult,Frame.read_empty,Entry.Value.erase,HE.isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => HE.isErrorAtom result.1.erase)
        (raw := [(.symbol "Empty",Frame.empty)])
        ⟨(.symbol "Empty",Frame.empty),by simp,by simp [Entry.Value.erase,HE.isErrorAtom]⟩)

/-- Reuse of explicitly held data is a different licensed evaluation context. -/
theorem he_held_marker_head :
    AtomRel HE.Space.empty noForeign rawLookup [] []
      (.expression .held [.symbol "Empty",.symbol "A"]) Atom.undefinedType Frame.empty
      [(.expression .held [.symbol "Empty",.symbol "A"],Frame.empty)] (policy := .ready) := by
  simpa only [Frame.read_empty] using
    (AtomRel.reuse_expression (space := HE.Space.empty) (dispatch := noForeign)
      (lookup := rawLookup) (live := []) (scope := []) (expected := Atom.undefinedType)
      (value := .expression .held [.symbol "Empty",.symbol "A"])
      (frame := Frame.empty) (children := [.symbol "Empty",.symbol "A"])
      (policy := .ready) (by simp) rfl)

/-- Erasing occurrence readiness cannot supply a complete evaluator state,
even in the empty theory with no native operations and one fixed demand. -/
theorem no_atom_only_ready_evaluator :
    ¬∃ meaning : Atom → List Atom, ∀ (value : Entry.Value) (results : List Result),
      AtomRel HE.Space.empty noForeign rawLookup [] [] value Atom.undefinedType Frame.empty
        results (policy := .ready) →
      meaning value.erase = results.map (fun result => result.1.erase) := by
  rintro ⟨meaning,correct⟩
  have active : meaning expression = [Atom.empty] := by
    simpa [contextual,expression,Entry.Value.ofAtom,Entry.Value.erase,Atom.empty] using
      correct contextual _ (he_active_marker_head .ready)
  have held : meaning expression = [expression] := by
    simpa [expression,Entry.Value.erase] using
      correct (.expression .held [.symbol "Empty",.symbol "A"]) _ he_held_marker_head
  have same := active.symm.trans held
  simp [expression,Atom.empty] at same

private def errorTailInput : Atom :=
  .expression [.symbol "Box",.symbol "Error",.symbol "A"]
private def errorTail : Entry.Value := .expression .active [.symbol "Error",.symbol "A"]

/-- The prospective constructor fragment admits this program. Its PeTTa
connection is valid, but the unrestricted HE comparison would be false. -/
theorem error_tail_pure_source : Nonempty (Evaluation program [] errorTailInput [errorTailInput]) := by
  apply Value.evaluates
  apply Value.constructor
  · constructor
    · unfold OrdinaryHead; decide +kernel
    · simp [program]
  · intro argument member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      exact .symbol _ (by decide +kernel) (by decide +kernel)

/-- The stronger return admission rejects exactly this scalar-tag collision;
the full PeTTa source control remains available independently above. -/
theorem error_tail_not_packet_safe : ¬NoErrorSymbol errorTailInput := by
  intro safe
  have bad : NoErrorSymbol (.symbol "Error") := safe.children _ (by simp)
  exact bad.not_error_symbol rfl

theorem petta_retains_error_tail :
    PeTTa.DeclarativeSpec.Runs program
      {state := PeTTa.Effects.empty,control := .evaluate [] errorTailInput}
      (.complete PeTTa.Effects.empty [errorTailInput] [] []) := by
  obtain ⟨source⟩ := error_tail_pure_source
  exact source.petta_source rfl _

private theorem scalar_source (policy : Policy) (live : List Atom) (name : String)
    (nonempty : name ≠ "Empty") :
    AtomRel HE.Space.empty noForeign rawLookup live [] (.symbol name) Atom.undefinedType Frame.empty
      [(.symbol name,Frame.empty)] (policy := policy) := by
  simpa only [Frame.read_empty] using
    (AtomRel.undefined_cast (space := HE.Space.empty) (dispatch := noForeign)
      (lookup := rawLookup) (live := live) (scope := []) (value := .symbol name)
      (frame := Frame.empty) (policy := policy) (actual := Atom.undefinedType) (later := [])
      (by
        simp only [Frame.read_empty,Entry.Value.erase,Entry.Value.status]
        exact Entry.Rel.cast
          (by simpa [IsEmptyOrErrorRel,IsErrorRel,Atom.empty] using nonempty)
          (.symbol name) (by decide +kernel) (Or.inl ⟨name,rfl⟩) (by simp [Atom.unit]))
      (by
        simp only [Frame.read_empty,Entry.Value.erase,rawLookup,HE.Spec.Type.rawTypeLookupRel]
        exact HE.Spec.Type.StorageTypesRel.symbolUndefined HE.Spec.Type.AnnotationTypesRel.nil))

private theorem error_tail_tuple (policy : Policy) (live : List Atom) :
    TupleRel HE.Space.empty noForeign rawLookup live [] [.symbol "Error",.symbol "A"] Frame.empty
      [(errorTail,Frame.empty)] (policy := policy) := by
  have finalArgument : TupleRel HE.Space.empty noForeign rawLookup (.symbol "Error"::live) []
      [.symbol "A"] Frame.empty [(.expression .active [.symbol "A"],Frame.empty)]
        (policy := policy) := by
    simpa [tupleSingleton,Entry.Value.erase,HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty] using
      (TupleRel.singleton (scalar_source policy _ "A" (by decide +kernel)))
  have rest := TupleBranchesRel.continuing
    (space := HE.Space.empty) (dispatch := noForeign) (lookup := rawLookup)
    (live := live) (scope := []) (policy := policy)
    (head := (.symbol "Error",Frame.empty)) (heads := []) (tail := [.symbol "A"])
    (children := [(.expression .active [.symbol "A"],Frame.empty)]) (rest := [])
    (by simp [IsEmptyOrErrorRel,IsErrorRel,Entry.Value.erase,Atom.empty])
    (by simpa only [Entry.Value.erase] using finalArgument) .nil
  simpa [tuplePrepend,errorTail,Entry.Value.erase,HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom,Atom.empty] using
    (TupleRel.cons (scalar_source policy _ "Error" (by decide +kernel)) rest)

/-- HE's tuple protocol classifies an assembled `(Error A)` tail as a failure
outcome. This follows from the published source rules, with no native effects,
bindings, equations or implementation representation involved. -/
theorem he_propagates_assembled_error_tail (policy : Policy) :
    AtomRel HE.Space.empty noForeign rawLookup [] [] (Entry.Value.ofAtom errorTailInput)
      Atom.undefinedType Frame.empty [(errorTail,Frame.empty)] (policy := policy) := by
  have tuple : TupleRel HE.Space.empty noForeign rawLookup [Atom.undefinedType] []
      [.symbol "Box",.symbol "Error",.symbol "A"] Frame.empty [(errorTail,Frame.empty)]
        (policy := policy) := by
    have rest := TupleBranchesRel.continuing
      (space := HE.Space.empty) (dispatch := noForeign) (lookup := rawLookup)
      (live := [Atom.undefinedType]) (scope := []) (policy := policy)
      (head := (.symbol "Box",Frame.empty)) (heads := [])
      (tail := [.symbol "Error",.symbol "A"])
      (children := [(errorTail,Frame.empty)]) (rest := [])
      (by simp [IsEmptyOrErrorRel,IsErrorRel,Entry.Value.erase,Atom.empty])
      (by simpa only [Entry.Value.erase] using
        error_tail_tuple policy [.symbol "Box",Atom.undefinedType]) .nil
    simpa [tuplePrepend,errorTail,Entry.Value.erase,HE.isEmptyOrError,HE.isEmptyAtom,HE.isErrorAtom] using
      (TupleRel.cons (scalar_source policy _ "Box" (by decide +kernel)) rest)
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => HE.isErrorAtom result.1.erase)
      ([(errorTail,Frame.empty)].map (readResult policy)) [(errorTail,Frame.empty)] := by
    simpa [readResult,Frame.read_empty] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.allErrors
        (isError := fun result : Result => HE.isErrorAtom result.1.erase)
        (raw := [(errorTail,Frame.empty)]) (by simp [errorTail,Entry.Value.erase,HE.isErrorAtom]))
  have completed := AtomRel.tuple (space := HE.Space.empty) (dispatch := noForeign)
    (lookup := rawLookup) (live := []) (scope := [])
    (value := Entry.Value.ofAtom errorTailInput) (expected := Atom.undefinedType)
    (frame := Frame.empty) (readiness := .active) (operator := .symbol "Box")
    (arguments := [.symbol "Error",.symbol "A"]) (policy := policy)
    (by
      simp only [Frame.read_empty,errorTailInput,Entry.Value.ofAtom,List.map_cons,List.map_nil,
        Entry.Value.status,Entry.Value.erase]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
        (by decide +kernel) (Or.inr rfl))
    (by simp [errorTailInput,Entry.Value.ofAtom])
    (by simpa only [Entry.Value.erase,HE.Space.empty,Multiset.coe_singleton] using
      (HE.Spec.Type.StorageTypesRel.symbolUndefined (name := "Box") HE.Spec.Type.AnnotationTypesRel.nil).occurrences)
    tuple (by
      simpa only [List.append_nil] using
        (CallsRel.cons (children := [(errorTail,Frame.empty)]) (rest := [])
          (CallRel.error (by simp [IsErrorRel,errorTail,Entry.Value.erase])) .nil)) priority
  cases hm : policy.marking <;>
    simpa [publishResult,Entry.Value.publish,Entry.publish,Entry.Value.withStatus,errorTail,
      Entry.Value.erase,HE.isErrorAtom,Entry.Value.status,hm] using completed

/-- The prospective full constructor grammar cannot be identified with HE's
published tuple semantics merely by forgetting answer order or bindings. -/
theorem error_tail_observations_differ :
    [errorTailInput] ≠ [errorTail.erase] := by
  simp [errorTailInput,errorTail,Entry.Value.erase]

end MarkerHeadControls

namespace StorageControls

private def left : Equation := ⟨"pick",[],.symbol "A"⟩
private def right : Equation := ⟨"pick",[],.symbol "B"⟩
private def program : Program := {equations := [left,right,left],declarations := []}
private def reordered : Program := {equations := [right,left,left],declarations := []}

private theorem ordinary : OrdinaryHead "pick" := by
  unfold OrdinaryHead
  decide +kernel

private def symbols (program : Program) (name : String)
    (nonempty : name ≠ "Empty") (notRefusal : name ≠ "NotReducible") :
    Evaluation program [] (.symbol name) [.symbol name] :=
  .symbol (.symbol name nonempty notRefusal)

/-- Distinct answers make traversal order observable before the bag quotient;
the repeated first clause is still a separate physical source occurrence. -/
theorem original_source : Nonempty
    (Evaluation program [] (.expression [.symbol "pick"]) [.symbol "A",.symbol "B",.symbol "A"]) := by
  have scan : ClauseScan "pick" [] 0 program.equations
      [(0,[],.symbol "A"),(1,[],.symbol "B"),(2,[],.symbol "A")] :=
    .hit rfl (by decide +kernel) .expr_nil
      (.hit rfl (by decide +kernel) .expr_nil
        (.hit rfl (by decide +kernel) .expr_nil (.nil 3)))
  exact ⟨.call ⟨ordinary,left,by simp [program],rfl⟩
    (.done (.equations ordinary scan (by simp)
      (.cons (symbols program "A" (by decide +kernel) (by decide +kernel))
        (.cons (symbols program "B" (by decide +kernel) (by decide +kernel))
          (.cons (symbols program "A" (by decide +kernel) (by decide +kernel)) .nil)))))⟩

theorem reordered_source : Nonempty
    (Evaluation reordered [] (.expression [.symbol "pick"]) [.symbol "B",.symbol "A",.symbol "A"]) := by
  have scan : ClauseScan "pick" [] 0 reordered.equations
      [(0,[],.symbol "B"),(1,[],.symbol "A"),(2,[],.symbol "A")] :=
    .hit rfl (by decide +kernel) .expr_nil
      (.hit rfl (by decide +kernel) .expr_nil
        (.hit rfl (by decide +kernel) .expr_nil (.nil 3)))
  exact ⟨.call ⟨ordinary,right,by simp [reordered],rfl⟩
    (.done (.equations ordinary scan (by simp)
      (.cons (symbols reordered "B" (by decide +kernel) (by decide +kernel))
        (.cons (symbols reordered "A" (by decide +kernel) (by decide +kernel))
          (.cons (symbols reordered "A" (by decide +kernel) (by decide +kernel)) .nil)))))⟩

theorem storage_and_answer_permutation :
    program.equations.Perm reordered.equations ∧
      ([Atom.symbol "A",Atom.symbol "B",Atom.symbol "A"] : Multiset Atom) =
        ([Atom.symbol "B",Atom.symbol "A",Atom.symbol "A"] : Multiset Atom) :=
  ⟨.swap _ _ _,Quot.sound (.swap _ _ _)⟩

theorem ordered_lists_differ :
    ([.symbol "A",.symbol "B",.symbol "A"] : List Atom) ≠
      [.symbol "B",.symbol "A",.symbol "A"] := by decide +kernel

theorem bag_cannot_drop_duplicate :
    ([Atom.symbol "A",Atom.symbol "B",Atom.symbol "A"] : Multiset Atom) ≠
      ([Atom.symbol "A",Atom.symbol "B"] : Multiset Atom) := by
  intro same
  have cardinality := congrArg Multiset.card same
  simp at cardinality

end StorageControls

end Mettapedia.Languages.MeTTa.Translation.PureConstructor

namespace Mettapedia.Languages.MeTTa.Translation.OpenContinuation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HE.Spec.Eval
open HE.Spec.Eval.Completed (Frame CastLookup ArgumentRequest AtomRel
  TupleRel TupleBranchesRel ArgumentsRel ArgumentBranchesRel)
open PeTTa.EagerDFS.Destination
open HE.Spec.Bindings.ScopeObservation (observedTuples)
open PureConstructor (NoErrorSymbol)

abbrev HResult := HE.Spec.Eval.Completed.Result

/-- The successful tuple and typed-argument spines share continuation transport,
while retaining their different source demands and assembly operations. -/
inductive Kind where
  | tuple
  | arguments

def packet (kind : Kind) (values : List Entry.Value) : Entry.Value :=
  match kind with
  | .tuple => .expression .active values
  | .arguments => Entry.Value.argumentPacket values

def prepend (kind : Kind) (head : Entry.Value) : HResult → HResult :=
  match kind with
  | .tuple => HE.Spec.Eval.Completed.tuplePrepend head
  | .arguments => HE.Spec.Eval.Completed.argumentPrepend head

def childLive (kind : Kind) (requests : List ArgumentRequest) (live : List Atom) : List Atom :=
  match kind, requests with
  | .tuple, [] => live
  | .tuple, _ :: _ => .expression (requests.map (fun request => request.1.erase)) :: live
  | .arguments, _ => HE.Spec.Eval.Completed.argumentScope requests ++ live

def demand (kind : Kind) (request : ArgumentRequest) : Atom :=
  match kind with
  | .tuple => Atom.undefinedType
  | .arguments => request.2

def goals (values slots : List Atom) (older : List Goal) : List Goal :=
  (values.zip slots).map (fun row => Goal.evaluate row.1 row.2) ++ older

/-- The same model observes the evaluated prefix, untouched siblings and caller
packet. Prefix values are deliberately not materialized before the final frame. -/
def PacketRel (frame : Frame) (control : Control)
    (evaluated remaining : List Entry.Value) (pending prefixSlots sourceTail sourcePending : List Atom) : Prop :=
  observedTuples frame.bindings ((evaluated ++ remaining).map Entry.Value.erase ++ pending) =
    solutionTuples control.bindings (prefixSlots ++ sourceTail ++ sourcePending)

/-- A focused decomposition of an existing scoped source state. The pending
alternatives, origin path, world, context and enclosing collection scopes are
retained rather than erased to a local branch evaluator. -/
structure SourcePoint (Context : Type) extends Cursor Context where
  supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator
  scope : CollectionScope Context
  parents : List (CollectionScope Context)
  origins : List Nat
  pending : List (CollectionWork Context)
  frontier : scope.frontier = (toCursor.control,toCursor.context,origins) :: pending

def SourcePoint.state {Context : Type} (point : SourcePoint Context) : ScopedCursor Context :=
  (point.supply, ⟨point.world,point.scope :: point.parents⟩)

abbrev SilentPath {Context : Type} (policy : PeTTa.EagerDFS.Destination.Policy)
    (program : PeTTa.SpaceSemantics.Program) :=
  Relation.ReflTransGen (fun (before after : SourcePoint Context) =>
    Source.ScopedStep Source.FreshOperations.owned policy program before.state (.silent after.state))

/-- A local child occurrence has an actual source path and retains the whole
joint packet at its reached cut. This is a certificate for that occurrence,
not an assumed correctness theorem for the recursive child evaluator. -/
structure ChildCompletion {Context : Type}
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) (program : PeTTa.SpaceSemantics.Program)
    (evaluated : List Entry.Value) (prefixSlots : List Atom) (remaining : List ArgumentRequest)
    (sourceTail slots pending sourcePending : List Atom) (older : List Goal)
    (sourceValue slot : Atom) (before : SourcePoint Context) (head : HResult) (after : SourcePoint Context) : Prop where
  entered : before.control.goals = .evaluate sourceValue slot :: goals sourceTail slots older
  path : SilentPath sourcePolicy program before after
  reached : after.control.goals = goals sourceTail slots older
  packet : PacketRel head.2 after.control (evaluated ++ [head.1]) (remaining.map Prod.fst)
    pending (prefixSlots ++ [slot]) sourceTail sourcePending

structure Outcome (Context : Type) where
  values : List Entry.Value
  frame : Frame
  cursor : SourcePoint Context

def Outcome.prepend {Context : Type} (head : Entry.Value) (outcome : Outcome Context) : Outcome Context :=
  {outcome with values := head :: outcome.values}

def Outcome.result {Context : Type} (kind : Kind) (outcome : Outcome Context) : HResult :=
  (packet kind outcome.values, outcome.frame)

theorem packet_clean (kind : Kind) (values : List Entry.Value)
    (safe : ∀ value ∈ values, NoErrorSymbol value.erase) :
    HE.isEmptyOrError (packet kind values).erase = false := by
  cases kind with
  | arguments =>
      simp only [packet,Entry.Value.argumentPacket,Entry.Value.erase,List.map_cons,List.map_nil]
      rfl
  | tuple =>
      simp only [packet,Entry.Value.erase]
      apply NoErrorSymbol.tuple_clean
      intro atom member
      obtain ⟨value,valueMember,image⟩ := List.mem_map.mp member
      subst atom
      exact safe value valueMember

@[simp] theorem prepend_packet (kind : Kind) (head : Entry.Value) (values : List Entry.Value)
    (frame : Frame) (safe : ∀ value ∈ values, NoErrorSymbol value.erase) : prepend kind head (packet kind values, frame) =
      (packet kind (head :: values), frame) := by
  cases kind with
  | arguments => simp [prepend,packet]
  | tuple =>
      have clean := packet_clean .tuple values safe
      simp only [packet,Entry.Value.erase] at clean
      simp only [prepend,packet,HE.Spec.Eval.Completed.tuplePrepend,Entry.Value.erase,
        clean,Bool.false_eq_true,↓reduceIte]

mutual
/-- A paired continuation proof over the existing independent HE child
judgment. Every head occurrence has its own tail proof and reached frame.
These finite manifests preserve multiplicity; completeness of an arbitrary
PeTTa child-search frontier is a separate obligation. -/
inductive OpenSpine {Context : Type} (kind : Kind)
    (space : HE.Space) (dispatch : HE.Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : HE.Spec.Eval.Completed.Policy)
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) (program : PeTTa.SpaceSemantics.Program)
    (scope : List String) (pending sourcePending : List Atom) (older : List Goal) :
    List Atom → List Entry.Value → List Atom → List ArgumentRequest → List Atom → List Atom →
      Frame → SourcePoint Context → List (Outcome Context) → Prop where
  | nil {live evaluated prefixSlots frame cursor}
      (lengths : evaluated.length = prefixSlots.length)
      (related : PacketRel frame cursor.control evaluated [] pending prefixSlots [] sourcePending)
      (ended : cursor.control.goals = older) :
      OpenSpine kind space dispatch lookup policy sourcePolicy program scope pending sourcePending older
        live evaluated prefixSlots [] [] [] frame cursor [⟨[],frame,cursor⟩]
  | cons {live evaluated prefixSlots request requests sourceValue sourceTail slot slots frame cursor heads outcomes}
      (related : PacketRel frame cursor.control evaluated ((request :: requests).map Prod.fst)
        pending prefixSlots (sourceValue :: sourceTail) sourcePending)
      (head : AtomRel space dispatch lookup (childLive kind requests live) scope request.1
        (demand kind request) frame heads (policy := policy))
      (branches : OpenBranchSpines kind space dispatch lookup policy sourcePolicy program scope
        pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots
        cursor heads outcomes) :
      OpenSpine kind space dispatch lookup policy sourcePolicy program scope pending sourcePending older
        live evaluated prefixSlots (request :: requests) (sourceValue :: sourceTail) (slot :: slots)
        frame cursor outcomes

inductive OpenBranchSpines {Context : Type} (kind : Kind)
    (space : HE.Space) (dispatch : HE.Spec.Eval.GroundedDispatch) (lookup : CastLookup) (policy : HE.Spec.Eval.Completed.Policy)
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) (program : PeTTa.SpaceSemantics.Program)
    (scope : List String) (pending sourcePending : List Atom) (older : List Goal) :
    List Atom → List Entry.Value → List Atom → List ArgumentRequest → Atom → List Atom → Atom →
      List Atom → SourcePoint Context → List HResult → List (Outcome Context) → Prop where
  | nil {live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor} : OpenBranchSpines kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor [] []
  | cons {live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor head heads reached children rest}
      (safe : NoErrorSymbol head.1.erase)
      (ordinary : ¬ HE.Spec.Eval.IsEmptyOrErrorRel head.1.erase)
      (completion : ChildCompletion sourcePolicy program evaluated prefixSlots requests sourceTail slots
        pending sourcePending older sourceValue slot cursor head reached)
      (childSpine : OpenSpine kind space dispatch lookup policy sourcePolicy program scope pending sourcePending older
        (head.1.erase :: live) (evaluated ++ [head.1]) (prefixSlots ++ [slot]) requests sourceTail slots
        head.2 reached children)
      (restSpines : OpenBranchSpines kind space dispatch lookup policy sourcePolicy program scope
        pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads rest) :
      OpenBranchSpines kind space dispatch lookup policy sourcePolicy program scope
        pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor
        (head :: heads) (children.map (Outcome.prepend head.1) ++ rest)
end

variable {Context : Type} {kind : Kind} {space : HE.Space} {dispatch : HE.Spec.Eval.GroundedDispatch}
  {lookup : CastLookup} {policy : HE.Spec.Eval.Completed.Policy}
  {sourcePolicy : PeTTa.EagerDFS.Destination.Policy} {program : PeTTa.SpaceSemantics.Program}
  {scope : List String} {pending sourcePending : List Atom} {older : List Goal}

mutual
/-- Every completed occurrence uses the final tail frame for its whole prefix.
The accompanying path is an actual finite source execution at the saved cut. -/
theorem OpenSpine.completed
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceTail slots frame cursor outcomes) :
    ∀ outcome ∈ outcomes,
      (∀ value ∈ outcome.values, NoErrorSymbol value.erase) ∧
      SilentPath sourcePolicy program cursor outcome.cursor ∧ outcome.cursor.control.goals = older ∧
      evaluated.length + outcome.values.length = prefixSlots.length + slots.length ∧
      PacketRel outcome.frame outcome.cursor.control evaluated outcome.values
        pending prefixSlots slots sourcePending := by
  match spine with
  | .nil lengths related ended =>
      intro outcome member
      simp only [List.mem_singleton] at member
      subst outcome
      exact ⟨by simp, .refl, ended, by simpa using lengths, related⟩
  | .cons related head branches => exact branches.completed
termination_by (requests.length, 0)
decreasing_by all_goals simp_wf; omega

 theorem OpenBranchSpines.completed
    {live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes}
    (branches : OpenBranchSpines (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes) :
    ∀ outcome ∈ outcomes,
      (∀ value ∈ outcome.values, NoErrorSymbol value.erase) ∧
      SilentPath sourcePolicy program cursor outcome.cursor ∧ outcome.cursor.control.goals = older ∧
      evaluated.length + outcome.values.length = prefixSlots.length + (slot :: slots).length ∧
      PacketRel outcome.frame outcome.cursor.control evaluated outcome.values
        pending prefixSlots (slot :: slots) sourcePending := by
  match branches with
  | .nil => simp
  | .cons (head := head) safe ordinary completion childSpine restSpines =>
      intro outcome member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨child,childMember,image⟩ := List.mem_map.mp member
        subst outcome
        obtain ⟨clean,path,ended,lengths,related⟩ := childSpine.completed child childMember
        refine ⟨?_,completion.path.trans path,ended,?_,?_⟩
        · intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact safe
          · exact clean value member
        · simp only [List.length_append,List.length_singleton] at lengths
          change evaluated.length + (child.values.length + 1) = prefixSlots.length + (slots.length + 1)
          omega
        · simpa only [Outcome.prepend,PacketRel,List.append_assoc,List.singleton_append] using related
      · exact restSpines.completed outcome member
termination_by (requests.length, heads.length + 1)
decreasing_by all_goals simp_wf; omega
end

/-- Final assembly changes packet shape, not the reached constraint theory.
No earlier head is read independently from its later siblings. -/
theorem OpenSpine.assembled_packet
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceTail slots frame cursor outcomes)
    {outcome : Outcome Context} (member : outcome ∈ outcomes) :
    observedTuples outcome.frame.bindings
        (.expression ((evaluated ++ outcome.values).map Entry.Value.erase) :: pending) =
      solutionTuples outcome.cursor.control.bindings (.expression (prefixSlots ++ slots) :: sourcePending) := by
  obtain ⟨_clean,_path,_ended,lengths,related⟩ := spine.completed outcome member
  apply ConstructorMatch.joint_packet_assemble_prefix
  · simpa only [List.length_map,List.length_append] using lengths
  · simpa only [PacketRel,List.append_assoc] using related

/-- The local source component embeds into the retained source state without
forgetting any saved alternative, origin, context or parent scope. -/
def SourcePoint.afterLocal {Context : Type} (point : SourcePoint Context) (after : Cursor Context) :
    SourcePoint Context :=
  {toCursor := after, supply := point.supply, scope := retainChild point.scope point.pending point.origins after,
    parents := point.parents, origins := point.origins, pending := point.pending, frontier := rfl}

theorem SourcePoint.local_step {Context : Type} (point : SourcePoint Context)
    {sourcePolicy : PeTTa.EagerDFS.Destination.Policy} {program : PeTTa.SpaceSemantics.Program}
    {after : Cursor Context} (source : Source.Step sourcePolicy program point.toCursor (.silent after)) :
    Source.ScopedStep Source.FreshOperations.owned sourcePolicy program point.state
      (.silent (point.afterLocal after).state) := by
  exact .active point.supply point.world point.scope point.parents point.control point.context
    point.origins point.pending _ point.frontier (.next after source)

/-- The actual source variable rule allocates its result after any evaluated
prefix. Its two scoped transitions preserve all retained caller components. -/
theorem source_variable_child
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) (program : PeTTa.SpaceSemantics.Program)
    (frame : Frame) (before : SourcePoint Context) (head : Entry.Value)
    (sourceName slotName : String) (evaluated : List Entry.Value) (prefixSlots : List Atom)
    (requests : List ArgumentRequest) (sourceTail slots pending sourcePending : List Atom) (older : List Goal)
    (related : observedTuples frame.bindings
        (evaluated.map Entry.Value.erase ++ head.erase ::
          (requests.map (fun request => request.1.erase) ++ pending)) =
      solutionTuples before.control.bindings (prefixSlots ++ .var sourceName :: (sourceTail ++ sourcePending)))
    (storeFresh : ∀ pair ∈ before.control.bindings,
      slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (prefixSlots ++ .var sourceName :: (sourceTail ++ sourcePending)))
    (atGoal : before.control.goals = .evaluate (.var sourceName) (.var slotName) :: goals sourceTail slots older) :
    ∃ after,
      ChildCompletion sourcePolicy program evaluated prefixSlots requests sourceTail slots pending sourcePending older
        (.var sourceName) (.var slotName) before (head,frame) after ∧
      after.supply = before.supply ∧ after.pending = before.pending ∧ after.origins = before.origins ∧
      after.parents = before.parents ∧ after.world = before.world ∧ after.context = before.context := by
  have observed := ConstructorMatch.private_destination_joint_prefix related slotName storeFresh packetFresh
  obtain ⟨model,satisfied⟩ := frame.certified.satisfiable
  have available : (evaluated.map Entry.Value.erase ++ head.erase ::
      (requests.map (fun request => request.1.erase) ++ pending)).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation model) ∈
      solutionTuples (before.control.bindings ++ [(.var sourceName,.var slotName)])
        (prefixSlots ++ .var slotName :: (sourceTail ++ sourcePending)) := by
    rw [← observed]
    exact ⟨model,satisfied,rfl⟩
  obtain ⟨environment,solved,_⟩ := available
  obtain ⟨old,equation⟩ := (solves_append_equation _ _ _ _).mp solved
  let middle : Cursor Context := {before.toCursor with control :=
    {before.control with goals := .equate (.var sourceName) (.var slotName) :: goals sourceTail slots older}}
  let after : Cursor Context := {before.toCursor with control :=
    {before.control with
      bindings := before.control.bindings ++ [(.var sourceName,.var slotName)]
      goals := goals sourceTail slots older}}
  have first : Source.Step sourcePolicy program before.toCursor (.silent middle) :=
    .expanded (.var sourceName) (.var slotName) (goals sourceTail slots older) _ atGoal rfl (.variableValue sourceName)
  have second : Source.Step sourcePolicy program middle (.silent after) :=
    .accepted (.var sourceName) (.var slotName) (goals sourceTail slots older) _ rfl
      (.accepted environment old equation)
  refine ⟨(before.afterLocal middle).afterLocal after,⟨atGoal,?_,rfl,?_⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (Relation.ReflTransGen.single (before.local_step first)).trans
      (Relation.ReflTransGen.single ((before.afterLocal middle).local_step second))
  · simpa only [PacketRel,List.map_append,List.map_cons,List.map_nil,List.map_map,List.singleton_append,
      List.nil_append,SourcePoint.afterLocal,middle,after,List.cons_append,List.append_assoc,Function.comp_def] using observed

/-- Open variable delivery earns its local child certificate. The source result
slot is fresh, so allocating it preserves the entire still-open caller packet.
The HE derivation and both actual scoped source steps are constructed here. -/
theorem variable_child
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) (program : PeTTa.SpaceSemantics.Program)
    (policy : HE.Spec.Eval.Completed.Policy) (space : HE.Space) (dispatch : HE.Spec.Eval.GroundedDispatch)
    (lookup : CastLookup) (scope : List String) (live : List Atom) (frame : Frame)
    (before : SourcePoint Context) (name sourceName slotName : String) (expected : Atom)
    (requests : List ArgumentRequest) (sourceTail slots pending sourcePending : List Atom) (older : List Goal)
    (unassigned : HE.Spec.Eval.Completed.FrameUnassignedOn frame (.var name))
    (related : observedTuples frame.bindings
        (.var name :: (requests.map (fun request => request.1.erase) ++ pending)) =
      solutionTuples before.control.bindings (.var sourceName :: (sourceTail ++ sourcePending)))
    (storeFresh : ∀ pair ∈ before.control.bindings,
      slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (.var sourceName :: (sourceTail ++ sourcePending)))
    (atGoal : before.control.goals = .evaluate (.var sourceName) (.var slotName) :: goals sourceTail slots older) :
    ∃ after,
      AtomRel space dispatch lookup live scope (.var name) expected frame [(.var name,frame)] (policy := policy) ∧
      ChildCompletion sourcePolicy program [] [] requests sourceTail slots pending sourcePending older
        (.var sourceName) (.var slotName) before (.var name,frame) after ∧
      after.supply = before.supply ∧ after.pending = before.pending ∧ after.origins = before.origins ∧
      after.parents = before.parents ∧ after.world = before.world ∧ after.context = before.context := by
  have assigned : HE.Spec.Eval.Completed.FrameUnassignedOn frame (Entry.Value.var name).erase := by
    simpa only [Entry.Value.erase] using unassigned
  have fixed := assigned.read_eq policy
  have he : AtomRel space dispatch lookup live scope (.var name) expected frame
      [(.var name,frame)] (policy := policy) := by
    have delivered := AtomRel.delivered (space := space) (dispatch := dispatch) (lookup := lookup)
      (live := live) (scope := scope) (value := Entry.Value.var name) (expected := expected)
      (frame := frame) (policy := policy) (by
        rw [fixed]
        simp only [Entry.Value.erase,Entry.Value.status]
        exact Entry.Rel.pass (by simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,Atom.empty])
          (.variable name) (Or.inr (Or.inr rfl)))
    simpa only [fixed] using delivered
  obtain ⟨after,completed,retained⟩ := source_variable_child sourcePolicy program frame before (.var name)
    sourceName slotName [] [] requests sourceTail slots pending sourcePending older
    (by simpa only [List.map_nil,List.nil_append,Entry.Value.erase] using related) storeFresh
    (by simpa only [List.nil_append] using packetFresh) atGoal
  exact ⟨after,he,completed,retained⟩

/-- Passive captures earn compatible variable entry without changing either
source language. Earlier values, unevaluated siblings and caller observations
remain one joint packet; no recursive child completion is assumed. -/
theorem passive_variable_child
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) (program : PeTTa.SpaceSemantics.Program)
    (policy : HE.Spec.Eval.Completed.Policy) (allowed scope : List String) (live : List Atom) (frame : Frame)
    (passive : PureConstructor.PassiveEnvironment program allowed frame.environment)
    (before : SourcePoint Context) (name sourceName slotName : String) (member : name ∈ allowed)
    (evaluated : List Entry.Value) (prefixSlots : List Atom)
    (requests : List ArgumentRequest) (sourceTail slots pending sourcePending : List Atom) (older : List Goal)
    (related : observedTuples frame.bindings
        (evaluated.map Entry.Value.erase ++ .var name ::
          (requests.map (fun request => request.1.erase) ++ pending)) =
      solutionTuples before.control.bindings (prefixSlots ++ .var sourceName :: (sourceTail ++ sourcePending)))
    (storeFresh : ∀ pair ∈ before.control.bindings,
      slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (prefixSlots ++ .var sourceName :: (sourceTail ++ sourcePending)))
    (atGoal : before.control.goals = .evaluate (.var sourceName) (.var slotName) :: goals sourceTail slots older) :
    ∃ output after,
      AtomRel (PureConstructor.equationSpace program) PureConstructor.noForeign HE.Spec.Eval.Completed.rawLookup
        live scope (.var name) Atom.undefinedType frame [(output,frame)] (policy := policy) ∧
      ChildCompletion sourcePolicy program evaluated prefixSlots requests sourceTail slots pending sourcePending older
        (.var sourceName) (.var slotName) before (output,frame) after ∧
      output.erase = (frame.read policy (.var name)).erase ∧
      (PureConstructor.Value program output.erase allowed ∧ NoErrorSymbol output.erase) ∧
      after.supply = before.supply ∧ after.pending = before.pending ∧ after.origins = before.origins ∧
      after.parents = before.parents ∧ after.world = before.world ∧ after.context = before.context := by
  obtain ⟨output,he,erased⟩ := passive.variable_he_completes frame name member live scope policy
  have same : observedTuples frame.bindings
      (evaluated.map Entry.Value.erase ++ output.erase :: (requests.map (fun request => request.1.erase) ++ pending)) =
      observedTuples frame.bindings
      (evaluated.map Entry.Value.erase ++ .var name :: (requests.map (fun request => request.1.erase) ++ pending)) := by
    apply HE.Spec.Bindings.ScopeObservation.observedTuples_congr_models
    intro model satisfied
    have preserved : HE.Spec.Type.RuntimeRefinement.applyTypeValuation model output.erase =
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation model (.var name) := by
      rw [erased,HE.Spec.Eval.Completed.Frame.read,Entry.Value.erase_substitute_environment,Entry.Value.erase]
      exact frame.certified.preserves_model model satisfied (.var name)
    simp only [List.map_append,List.map_cons,preserved]
  obtain ⟨after,completed,retained⟩ := source_variable_child sourcePolicy program frame before output
    sourceName slotName evaluated prefixSlots requests sourceTail slots pending sourcePending older
    (same.trans related) storeFresh packetFresh atGoal
  have admitted : PureConstructor.Value program output.erase allowed ∧ NoErrorSymbol output.erase := by
    rw [erased,HE.Spec.Eval.Completed.Frame.read,Entry.Value.substitute]
    exact ⟨passive.resolve.1 name member,passive.resolve.2 name⟩
  exact ⟨output,after,he,completed,erased,admitted,retained⟩

theorem OpenSpine.prepend_results
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceTail slots frame cursor outcomes)
    (head : Entry.Value) :
    (outcomes.map (Outcome.result kind)).map (prepend kind head) =
      (outcomes.map (Outcome.prepend head)).map (Outcome.result kind) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro outcome member
  exact prepend_packet kind head outcome.values outcome.frame (spine.completed outcome member).1

theorem OpenBranchSpines.heads_ordinary
    {live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes}
    (branches : OpenBranchSpines (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes) :
    ∀ head ∈ heads, ¬ HE.Spec.Eval.IsEmptyOrErrorRel head.1.erase := by
  match branches with
  | .nil => simp
  | .cons safe ordinary completion childSpine restSpines =>
      intro head member
      rcases List.mem_cons.mp member with rfl | member
      · exact ordinary
      · exact restSpines.heads_ordinary head member
termination_by heads.length
decreasing_by simp_wf

mutual
/-- The transport certificate reconstructs the existing HE tuple derivation;
it does not replace its source judgment with a fixed-substitution evaluator. -/
theorem OpenSpine.he_tuple
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) .tuple space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceTail slots frame cursor outcomes) :
    TupleRel space dispatch lookup live scope (requests.map Prod.fst) frame
      (outcomes.map (Outcome.result .tuple)) (policy := policy) := by
  match spine with
  | .nil lengths related ended => exact .nil
  | .cons (request := request) (requests := remainingRequests) related head branches =>
      match remainingRequests with
      | [] =>
          have completed := branches.he_tuple
          have same := PureConstructor.RecursiveTransport.empty_tuple_branches completed branches.heads_ordinary
          rw [same]
          exact .singleton head
      | second :: remaining =>
          apply TupleRel.cons
          · simpa only [childLive,List.map_cons,List.map_map,Function.comp_def,demand] using head
          · exact branches.he_tuple
termination_by (requests.length, 0)
decreasing_by all_goals simp_wf; omega

 theorem OpenBranchSpines.he_tuple
    {live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes}
    (branches : OpenBranchSpines (Context := Context) .tuple space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes) :
    TupleBranchesRel space dispatch lookup live scope (requests.map Prod.fst) heads
      (outcomes.map (Outcome.result .tuple)) (policy := policy) := by
  match branches with
  | .nil => exact .nil
  | .cons (head := head) safe ordinary completion childSpine restSpines =>
      have assembled := childSpine.prepend_results head.1
      have continued := TupleBranchesRel.continuing ordinary childSpine.he_tuple restSpines.he_tuple
      simpa only [List.map_append,prepend] using assembled ▸ continued
termination_by (requests.length, heads.length + 1)
decreasing_by all_goals simp_wf; omega

 theorem OpenSpine.he_arguments
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) .arguments space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceTail slots frame cursor outcomes) :
    ArgumentsRel space dispatch lookup live scope requests frame
      (outcomes.map (Outcome.result .arguments)) (policy := policy) := by
  match spine with
  | .nil lengths related ended => exact .nil
  | .cons related head branches => exact .cons head (branches.he_arguments _)
termination_by (requests.length, 0)
decreasing_by all_goals simp_wf; omega

 theorem OpenBranchSpines.he_arguments
    {live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes}
    (branches : OpenBranchSpines (Context := Context) .arguments space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceValue sourceTail slot slots cursor heads outcomes)
    (original : Entry.Value) :
    ArgumentBranchesRel space dispatch lookup live scope original requests heads
      (outcomes.map (Outcome.result .arguments)) (policy := policy) := by
  match branches with
  | .nil => exact .nil
  | .cons (head := head) safe ordinary completion childSpine restSpines =>
      have assembled := childSpine.prepend_results head.1
      have continued := ArgumentBranchesRel.continuing (original := original)
        (fun stopped => ordinary stopped.1) childSpine.he_arguments (restSpines.he_arguments original)
      simpa only [List.map_append,prepend] using assembled ▸ continued
termination_by (requests.length, heads.length + 1)
decreasing_by all_goals simp_wf; omega
end

/-- Finite open-spine transport preserves the existing HE source derivation,
actual retained source paths and the multiset of correlated packet observations
for its explicitly certified occurrence manifest. This is not a claim that
those local paths exhaust an arbitrary recursive PeTTa search frontier. -/
theorem OpenSpine.transport
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending older live evaluated prefixSlots requests sourceTail slots frame cursor outcomes) :
    (match kind with
      | .tuple => TupleRel space dispatch lookup live scope (requests.map Prod.fst) frame
          (outcomes.map (Outcome.result .tuple)) (policy := policy)
      | .arguments => ArgumentsRel space dispatch lookup live scope requests frame
          (outcomes.map (Outcome.result .arguments)) (policy := policy)) ∧
      (∀ outcome ∈ outcomes, SilentPath sourcePolicy program cursor outcome.cursor ∧
        outcome.cursor.control.goals = older) ∧
      ((outcomes.map fun outcome => observedTuples outcome.frame.bindings
          (.expression ((evaluated ++ outcome.values).map Entry.Value.erase) :: pending)) :
        Multiset (Set (List Atom))) =
      ((outcomes.map fun outcome => solutionTuples outcome.cursor.control.bindings
          (.expression (prefixSlots ++ slots) :: sourcePending)) : Multiset (Set (List Atom))) := by
  refine ⟨?_,?_,?_⟩
  · cases kind with
    | tuple => exact spine.he_tuple
    | arguments => exact spine.he_arguments
  · intro outcome member
    have complete := spine.completed outcome member
    exact ⟨complete.2.1,complete.2.2.1⟩
  · apply Multiset.coe_eq_coe.mpr
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro outcome member
    exact spine.assembled_packet member

/-- At the eager-data assembly cut, the spine's final packet feeds the actual
source equation step. Matching and refusal use the reached child frame rather
than a saved initial caller substitution. -/
theorem OpenSpine.assembled_equate
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    {target destination : Atom}
    (spine : OpenSpine (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      (target :: pending) (destination :: sourcePending)
      (.equate (.expression (prefixSlots ++ slots)) destination :: older)
      live evaluated prefixSlots requests sourceTail slots frame cursor outcomes)
    {outcome : Outcome Context} (member : outcome ∈ outcomes)
    {after : Equations}
    (accepted : Refinement outcome.cursor.control.bindings (.expression (prefixSlots ++ slots)) destination (some after)) :
    ∃ output,
      Source.Step sourcePolicy program outcome.cursor.toCursor
        (.silent {outcome.cursor.toCursor with control :=
          {outcome.cursor.control with bindings := after,goals := older}}) ∧
      HE.Spec.Eval.Steps.UnifyCandidateRel
        (.expression ((evaluated ++ outcome.values).map Entry.Value.erase)) target outcome.frame.bindings output ∧
      observedTuples output pending = solutionTuples after sourcePending := by
  exact ConstructorMatch.source_equate_joint_pending sourcePolicy program outcome.cursor.toCursor
    (spine.assembled_packet member) (spine.completed outcome member).2.2.1 accepted

/-- An assembled open call earns the complete source clause frontier,
including refused rows and duplicate physical positions. Only finite caller
protection is added; the reached equations and goals are unchanged. -/
theorem OpenSpine.call_frontier
    (head : String) (sourceArguments : List Atom) (destination : Atom) (callerOlder : List Goal)
    {live evaluated prefixSlots requests sourceTail slots frame cursor outcomes}
    (spine : OpenSpine (Context := Context) kind space dispatch lookup policy sourcePolicy program scope
      pending sourcePending (.invoke head sourceArguments destination :: callerOlder)
      live evaluated prefixSlots requests sourceTail slots frame cursor outcomes)
    {outcome : Outcome Context} (member : outcome ∈ outcomes)
    (shape : prefixSlots ++ slots = .symbol head :: sourceArguments) :
    ∃ guarded choices works,
      guarded.bindings = outcome.cursor.control.bindings ∧
      guarded.goals = .invoke head sourceArguments destination :: callerOlder ∧
      choices = ClauseChoice.choices program guarded head sourceArguments destination callerOlder ∧
      ClauseChoice.Frontier program guarded head sourceArguments destination callerOlder
        (List.range program.equations.length) choices ∧
      HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        (.expression ((evaluated ++ outcome.values).map Entry.Value.erase)) outcome.frame.bindings works ∧
      List.Forall₂ (ConstructorMatch.ClausePendingAgreement guarded
        (.expression (.symbol head :: sourceArguments)) destination callerOlder pending sourcePending)
        choices works ∧
      (works.map (fun work => (work.position,observedTuples work.bindings pending)) : Multiset (Nat × Set (List Atom))) =
        (choices.map (fun selected => (selected.1,solutionTuples selected.2.bindings sourcePending)) :
          Multiset (Nat × Set (List Atom))) := by
  have related := spine.assembled_packet member
  rw [shape] at related
  let query : Atom := .expression ((evaluated ++ outcome.values).map Entry.Value.erase)
  let sourceAtoms := outcome.cursor.control.bindings.flatMap (fun pair => [pair.1,pair.2]) ++
    .expression (.symbol head :: sourceArguments) :: sourcePending
  let forbidden := HE.EquationScope.visibleNames (pending ++ live) query outcome.frame.bindings ++
    HE.Spec.Bindings.ScopeObservation.specBindingVars outcome.frame.bindings ++
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList (query :: pending) ++
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList sourceAtoms
  let guarded := protectControl outcome.cursor.control forbidden.toFinset
  let choices := ClauseChoice.choices program guarded head sourceArguments destination callerOlder
  obtain ⟨works,frontier,paired,observations⟩ := ConstructorMatch.protected_petta_joint_choices_he_frontier
    program outcome.cursor.control head sourceArguments destination callerOlder live query outcome.frame.bindings
    pending sourcePending related
  exact ⟨guarded,choices,works,rfl,(spine.completed outcome member).2.2.1,rfl,
    (ClauseChoice.choices_iff_frontier program guarded head sourceArguments destination callerOlder choices).mp rfl,
    frontier,paired,observations⟩

namespace Controls

private def active : Control :=
  {bindings := [],goals := [.evaluate (.var "x") (.var "result")],destination := .var "caller"}

private def saved : Control :=
  {bindings := [],goals := [.equate (.var "caller") (.symbol "saved")],destination := .var "caller"}

private def initial : SourcePoint Unit :=
  {toCursor := ⟨⟨PeTTa.Effects.empty,[],[]⟩,active,()⟩,
    supply := Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator.empty 0 0,
    scope := ⟨[(active,(),[0]),(saved,(),[1])],[],none⟩,
    parents := [],origins := [0],pending := [(saved,(),[1])],frontier := rfl}

/-- The earned local instance retains an open result/caller alias. Its joint
observer admits equal positions and refuses an independently chosen pair;
there is also an actual older alternative in the retained source state. -/
theorem variable_pair_keeps_correlation (policy : HE.Spec.Eval.Completed.Policy)
    (dispatch : HE.Spec.Eval.GroundedDispatch) :
    ∃ after : SourcePoint Unit,
      AtomRel HE.Space.empty dispatch HE.Spec.Eval.Completed.rawLookup [] ["x"] (.var "x")
        Atom.undefinedType Frame.empty [(.var "x",Frame.empty)] (policy := policy) ∧
      SilentPath .eagerValue {equations := [],declarations := []} initial after ∧
      after.control.goals = [] ∧
      after.supply = initial.supply ∧ after.pending = initial.pending ∧ after.origins = initial.origins ∧
      after.parents = initial.parents ∧ after.world = initial.world ∧ after.context = initial.context ∧
      [.symbol "A",.symbol "A"] ∈ solutionTuples after.control.bindings [.var "result",.var "x"] ∧
      [.symbol "A",.symbol "B"] ∉ solutionTuples after.control.bindings [.var "result",.var "x"] := by
  have related : observedTuples Frame.empty.bindings [.var "x",.var "x"] =
      solutionTuples initial.control.bindings [.var "x",.var "x"] := by
    apply ConstructorMatch.reached_pending_observations
    intro environment
    simp [HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied,Frame.empty,HE.Bindings.empty,initial,active,Solves]
  have unassigned : HE.Spec.Eval.Completed.FrameUnassignedOn Frame.empty (.var "x") := by
    intro name used present
    simp only [Frame.empty,Entry.Value.eraseEnvironment,List.map_nil,
      HE.Spec.Type.Presentation.TypeSubst.keys,List.not_mem_nil] at present
  obtain ⟨after,he,completed,supply,alternatives,origins,parents,world,context⟩ := variable_child .eagerValue {equations := [],declarations := []}
    policy HE.Space.empty dispatch HE.Spec.Eval.Completed.rawLookup ["x"] [] Frame.empty initial
    "x" "x" "result" Atom.undefinedType [] [] [] [.var "x"] [.var "x"] [] unassigned
    (by simpa using related) (by simp [initial,active]) (by decide +kernel) rfl
  have packet : observedTuples Frame.empty.bindings [.var "x",.var "x"] =
      solutionTuples after.control.bindings [.var "result",.var "x"] := by
    simpa only [PacketRel,List.nil_append,List.append_nil,List.map_nil,List.map_cons,
      Entry.Value.erase,List.singleton_append] using completed.packet
  refine ⟨after,he,completed.path,completed.reached,supply,alternatives,origins,parents,world,context,?_,?_⟩
  · rw [← packet]
    refine ⟨fun _ => .symbol "A",?_,?_⟩
    · simp [HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied,Frame.empty,HE.Bindings.empty]
    · simp only [List.map_cons,List.map_nil,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  · rw [← packet]
    rintro ⟨valuation,_satisfied,readout⟩
    simp only [List.map_cons,List.map_nil,HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at readout
    have first := (List.cons.inj readout).1
    have second := (List.cons.inj (List.cons.inj readout).2).1
    have impossible : (Atom.symbol "A") = .symbol "B" := first.symm.trans second
    exact (by decide +kernel : ("A" : String) ≠ "B") (Atom.symbol.inj impossible)

private def passiveProgram : PeTTa.SpaceSemantics.Program := {equations := [],declarations := []}
private def openConstructor : Entry.Value := .expression .held [.symbol "Box",.var "y"]

private def openFrame : Frame :=
  ⟨⟨[("x",openConstructor.erase)],[]⟩,[("x",openConstructor)],by
    apply HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate.of_normal_theory
    · simp [Entry.Value.eraseEnvironment,openConstructor,Entry.Value.erase,
        HE.Spec.Type.Presentation.TypeSubst.Normal,HE.Spec.Type.Presentation.TypeSubst.keys,
        HE.Spec.Type.Presentation.TypeSubst.typeVars,HE.Spec.Type.Presentation.TypeSubst.typeVarsList]
    · intro valuation
      simp [Entry.Value.eraseEnvironment,
        HE.Spec.Type.Presentation.Theory.TypeSubstSatisfied,HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied]⟩

private def openControl : Control :=
  {active with bindings := HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations openFrame.bindings}

private def openInitial : SourcePoint Unit :=
  {toCursor := ⟨initial.world,openControl,()⟩,supply := initial.supply,
    scope := ⟨[(openControl,(),[0]),(saved,(),[1])],[],none⟩,
    parents := [],origins := [0],pending := [(saved,(),[1])],frontier := rfl}

/-- A genuinely bound open constructor is shared with an earlier result and
the still-free caller variable. Delivery retains an older source alternative. -/
theorem passive_bound_constructor_keeps_joint_prefix (policy : HE.Spec.Eval.Completed.Policy) :
    ∃ output after,
      AtomRel (PureConstructor.equationSpace passiveProgram) PureConstructor.noForeign
        HE.Spec.Eval.Completed.rawLookup [] ["x","y"] (.var "x") Atom.undefinedType openFrame
        [(output,openFrame)] (policy := policy) ∧
      ChildCompletion .eagerValue passiveProgram [.var "x"] [.var "x"] [] [] [] [.var "y"] [.var "y"] []
        (.var "x") (.var "result") openInitial (output,openFrame) after ∧
      output.erase = .expression [.symbol "Box",.var "y"] ∧
      PureConstructor.CodeRel passiveProgram ["x","y"] output ∧
      after.supply = openInitial.supply ∧ after.pending = openInitial.pending ∧
      after.origins = openInitial.origins ∧ after.parents = openInitial.parents ∧
      after.world = openInitial.world ∧ after.context = openInitial.context := by
  have passive : PureConstructor.PassiveEnvironment passiveProgram ["x","y"] openFrame.environment := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    simp only [openConstructor,Entry.Value.erase,List.map_cons,List.map_nil]
    have constructor : PureConstructor.ConstructorHead passiveProgram "Box" :=
      ⟨by unfold PureConstructor.OrdinaryHead; decide +kernel,by simp [passiveProgram]⟩
    constructor
    · apply PureConstructor.Value.constructor constructor
      intro argument present
      obtain rfl := List.mem_singleton.mp present
      exact .variable (by decide +kernel)
    · apply NoErrorSymbol.expression
      intro atom present
      rcases List.mem_cons.mp present with rfl | present
      · exact .symbol (by decide +kernel)
      · obtain rfl := List.mem_singleton.mp present
        exact .variable "y"
  have related : observedTuples openFrame.bindings [.var "x",.var "x",.var "y"] =
      solutionTuples openInitial.control.bindings [.var "x",.var "x",.var "y"] := by
    apply ConstructorMatch.reached_pending_observations
    intro environment
    exact (solves_binding_equations environment openFrame.bindings).symm
  obtain ⟨output,after,he,completed,erased,admitted,retained⟩ := passive_variable_child .eagerValue passiveProgram
    policy ["x","y"] ["x","y"] [] openFrame passive openInitial "x" "x" "result" (by decide +kernel)
    [.var "x"] [.var "x"] [] [] [] [.var "y"] [.var "y"] []
    (by simpa only [List.map_cons,List.map_nil,Entry.Value.erase,List.append_nil,List.nil_append,List.singleton_append] using related)
    (by simp [openInitial,openControl,openFrame,openConstructor,Entry.Value.erase,
      HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,HE.Spec.Type.Presentation.TypeSubst.typeVarsList])
    (by decide +kernel) rfl
  refine ⟨output,after,he,completed,?_,.data admitted.1 admitted.2,retained⟩
  simpa [Frame.read,Entry.Value.substitute,Entry.Value.resolve,openFrame,List.lookup,openConstructor,
    Entry.Value.erase] using erased

end Controls

namespace ActiveBindingControls

open PureConstructor
open HE.Spec.Type.Presentation HE.Spec.Type.RuntimeRefinement
open HE.Spec.Type.Presentation.BindingTheory

private def call : Atom := .expression [.symbol "f"]
private def callValue : Entry.Value := .expression .active [.symbol "f"]
private def rule : PeTTa.SpaceSemantics.Equation := ⟨"f",[],.symbol "A"⟩
private def sampleProgram : PeTTa.SpaceSemantics.Program := {equations := [rule],declarations := []}
private def bindings : HE.Bindings := ⟨[("x",call)],[]⟩
private def environment : Entry.Value.Environment := [("x",callValue)]

private theorem certified : ReadoutCertificate bindings (Entry.Value.eraseEnvironment environment) := by
  apply ReadoutCertificate.of_normal_theory
  · simp [environment,callValue,Entry.Value.eraseEnvironment,Entry.Value.erase,
      TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars,TypeSubst.typeVarsList]
  · intro valuation
    simp [HE.Spec.Type.Presentation.Theory.TypeSubstSatisfied,TypeBindingSatisfied,
      bindings,environment,call,callValue,Entry.Value.eraseEnvironment,Entry.Value.erase]

private def frame : Frame := ⟨bindings,environment,certified⟩

private theorem ordinary : OrdinaryHead "f" := by
  unfold OrdinaryHead
  decide +kernel

/-- The active-call separator is excluded by the structural capture admission,
for every retained-name scope, even though its bare head remains passive. -/
theorem active_binding_not_passive (scope : List String) :
    Value sampleProgram (.symbol "f") scope ∧
      ¬PassiveEnvironment sampleProgram scope frame.environment := by
  refine ⟨ordinary.symbol_value,?_⟩
  intro passive
  have captured := (passive ("x",callValue) (by simp [frame,environment])).1
  apply DefinedHead.not_constructor_value (program := sampleProgram) (head := "f")
    ⟨ordinary,rule,by simp [sampleProgram],rfl⟩ [] scope
  simpa only [callValue,Entry.Value.erase,List.map_cons,List.map_nil] using captured

private def source : Evaluation sampleProgram [] call [.symbol "A"] := by
  have scanned : ClauseScan "f" [] 0 sampleProgram.equations [(0,[],.symbol "A")] :=
    .hit (equation := rule) rfl (by decide +kernel) .expr_nil (.nil 1)
  have bodies : Bodies sampleProgram [(0,[],.symbol "A")] [.symbol "A"] :=
    .cons (.symbol (.symbol "A" (by decide +kernel) (by decide +kernel))) .nil
  exact .call ⟨ordinary,rule,by simp [sampleProgram],rfl⟩
    (.done (.equations ordinary scanned (by decide +kernel) bodies))

private theorem program_code : CodeProgram sampleProgram := by
  intro equation member
  have same : equation = rule := by simpa only [sampleProgram,List.mem_singleton] using member
  subst equation
  have code : CodeRel sampleProgram [] (Entry.Value.symbol "A") := by
    apply CodeRel.data
    · simpa only [Entry.Value.erase] using
        (PureConstructor.Value.symbol (program := sampleProgram) "A" (by decide +kernel) (by decide +kernel))
    · simpa only [Entry.Value.erase] using (NoErrorSymbol.symbol (by decide +kernel : "A" ≠ "Error"))
  simpa only [rule,Entry.Value.ofAtom,TypeSubst.typeVars,TypeSubst.typeVarsList,List.append_nil] using code

private theorem call_code : CodeRel sampleProgram [] callValue := by
  apply CodeRel.active ordinary
  intro child member
  cases member

private def incoming : Equations := [(.var "x",call)]
private def completedBindings : Equations := incoming ++ [(.var "x",.var "out")]
private def before : Cursor Unit :=
  ⟨⟨PeTTa.Effects.empty,[],[]⟩,
    {bindings := incoming,goals := [.evaluate (.var "x") (.var "out")],destination := .var "out"},()⟩
private def middle : Cursor Unit :=
  {before with control := {before.control with goals := [.equate (.var "x") (.var "out")]}}
private def after : Cursor Unit :=
  {before with control := {before.control with bindings := completedBindings,goals := []}}

private theorem source_steps (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) :
    Source.Step sourcePolicy sampleProgram before (.silent middle) ∧
      Source.Step sourcePolicy sampleProgram middle (.silent after) ∧
      Source.Step sourcePolicy sampleProgram after (.finish (.value call completedBindings,after)) := by
  let constant : Environment := fun _ => encode call
  have variableRead (name : String) : PeTTa.EagerDFS.Destination.read constant (.var name) = call := by
    rw [PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation]
    simp only [applyTypeValuation,constant,decode_encode]
  have constantRead : PeTTa.EagerDFS.Destination.read constant call = call := by
    rw [PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation]
    simp only [call,applyTypeValuation,List.map_cons,List.map_nil]
  have solved : Solves constant completedBindings := by
    intro pair member
    have choices : pair = (.var "x",call) ∨ pair = (.var "x",.var "out") := by
      simpa only [completedBindings,incoming,List.mem_append,List.mem_singleton] using member
    rcases choices with rfl | rfl
    · exact (variableRead "x").trans constantRead.symm
    · exact (variableRead "x").trans (variableRead "out").symm
  obtain ⟨model,resolved⟩ := resolve_complete ⟨_,solved⟩
  have modelled := resolve_sound resolved
  have head := modelled (.var "x",call) (by simp [completedBindings,incoming])
  have output := modelled (.var "x",.var "out") (by simp [completedBindings])
  have readCall : read model call = call := by simp [call,read_eq_applyTypeValuation,applyTypeValuation]
  have returned : read model (.var "out") = call := output.symm.trans (head.trans readCall)
  refine ⟨.expanded (.var "x") (.var "out") [] _ rfl rfl (.variableValue "x"),?_,?_⟩
  · apply Source.Step.accepted (.var "x") (.var "out") [] completedBindings rfl
    apply Refinement.accepted constant
    · intro pair member
      exact solved pair (List.mem_append_left _ member)
    · exact (variableRead "x").trans (variableRead "out").symm
  · simpa only [after,before,returned] using
      (Source.Step.returned (policy := sourcePolicy) (program := sampleProgram) (cursor := after) model rfl resolved)

private theorem initial_agreement (packet : List Atom) :
    observedTuples frame.bindings packet = solutionTuples before.control.bindings packet := by
  apply ConstructorMatch.reached_pending_observations
  intro model
  simpa only [frame,bindings,before,incoming,bindingAtomEquations,List.map_cons,List.map_nil,List.append_nil] using
    (solves_binding_equations model bindings).symm

/-- With `(= (f) A)` and an active binding `x = (f)`, the HE source reads then
executes the call, whereas the PeTTa variable rule returns the bound expression
as data. The program satisfies the existing pure code admission. Thus joint
binding agreement alone cannot extend the closed comparison to all open entry
syntax; this is a source-policy separator, not an implementation discrepancy. -/
theorem active_binding_separates_dispatch (policy : HE.Spec.Eval.Completed.Policy)
    (sourcePolicy : PeTTa.EagerDFS.Destination.Policy) :
    CodeProgram sampleProgram ∧ CodeRel sampleProgram ["x"] (.var "x") ∧
      (∀ packet, observedTuples frame.bindings packet = solutionTuples before.control.bindings packet) ∧
      (∃ results,
        AtomRel (equationSpace sampleProgram) noForeign HE.Spec.Eval.Completed.rawLookup [] ["x"] (.var "x")
          Atom.undefinedType frame results (policy := policy) ∧
        results.map (fun result => result.1.erase) = [.symbol "A"]) ∧
      Source.Step sourcePolicy sampleProgram before (.silent middle) ∧
      Source.Step sourcePolicy sampleProgram middle (.silent after) ∧
      Source.Step sourcePolicy sampleProgram after (.finish (.value call completedBindings,after)) ∧
      (PeTTa.EagerDFS.Destination.machine sourcePolicy sampleProgram).run 3 before =
        ([],.finished (.value call completedBindings,after)) ∧
      ¬List.Perm [.symbol "A"] [call] := by
  obtain ⟨results,closed,answers,_safe⟩ := PureConstructor.RecursiveTransport.he_evaluation source program_code rfl
    policy [] ["x"] frame callValue call_code
    (by simp only [callValue,call,Entry.Value.erase,List.map_cons,List.map_nil,Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  have readCall : frame.read policy callValue = callValue := call_code.read_closed policy frame
  have readVar : frame.read policy (.var "x") = callValue := by
    simp [Frame.read,Entry.Value.substitute,Entry.Value.resolve,frame,environment,List.lookup]
  have opened : AtomRel (equationSpace sampleProgram) noForeign HE.Spec.Eval.Completed.rawLookup [] ["x"] (.var "x")
      Atom.undefinedType frame results (policy := policy) :=
    closed.input_read_eq (readCall.trans readVar.symm)
  obtain ⟨first,second,returned⟩ := source_steps sourcePolicy
  refine ⟨program_code,.variable (by simp),initial_agreement,⟨results,opened,answers⟩,
    first,second,returned,?_,?_⟩
  · rw [(PeTTa.EagerDFS.Destination.machine sourcePolicy sampleProgram).run_succ_silent first.execution,
      (PeTTa.EagerDFS.Destination.machine sourcePolicy sampleProgram).run_succ_silent second.execution,
      (PeTTa.EagerDFS.Destination.machine sourcePolicy sampleProgram).run_succ_finish returned.execution]
  · intro paired
    have impossible : Atom.symbol "A" = call := List.mem_singleton.mp (paired.mem_iff.mp (by simp))
    cases impossible

end ActiveBindingControls

end Mettapedia.Languages.MeTTa.Translation.OpenContinuation
