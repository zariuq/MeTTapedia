import Mettapedia.Languages.Metamath.SourceGSLTState
import Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
import Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding
import Mettapedia.Languages.Metamath.InferenceDummyAllocation

/-!
# Source-admissible realization of optional dummy declarations

[MM §4.2.7] extended frames were reconciled semantically by
`SourceGSLTSpecGrounding.extendFloat(s)` and the dummy-allocation theorem.
That layer manufactures *semantic* frame extensions; this module supplies
their *source-admissible* counterpart: an optional dummy is realized by a
`$v` declaration followed by a fresh-labeled `$f` statement, both passing
through the source GSLT's own accepted operations
(`declareVariables?` / `declareFloating?`, gated by `acceptUpdate`).
Nothing here re-derives admissibility: every theorem is conditioned on
the operations having been *accepted* by those gates, exactly as the
acceptance facts will be supplied by the parser lane in the full
composition.

Main results:

* `declareDummy?_callerFrame` — one accepted dummy declaration extends
  the operational caller frame by exactly one optional floating
  hypothesis: the source transition realizes `extendFloat`.
* `declareDummies?_callerFrame` — an accepted sequence realizes
  `extendFloats`, declaration by declaration, in order.
* `supported_transport_sourceRealized` — a frame-supported derivation
  over a source state's caller frame remains supported over the caller
  frame of any accepted dummy-realization successor.
* `declareDummy?_accepts` / `supplyPlan_accepts` — the
  acceptance-**existence** tier: globally fresh striped names and
  labels with declared typecodes make the real gates accept, end to
  end.
* `supplyPlan_spec_optionalSequence` — the accepted plan's spec image
  is semantically fresh: `OptionalFresh` is derived from the same
  length striping that made the gates accept.
* `witness_toSupported_sourceAccepted` — the step-2 capstone: from any
  valid, ready, bound-short source state, a finite-support witness over
  the caller frame with declared support typecodes and base-supported
  conclusion yields a constructed plan, its gate acceptance, and
  `SupportedProvable` over the successor's caller frame.
* `provable_toSupported_sourceAccepted` — the Provable-form corollary:
  the typed extraction `Provable.exists_finiteSupport_typed` bounds
  every support-leaf typecode by the conclusion's typecode or a
  database axiom-premise typecode, so the declared-typecode hypothesis
  reduces to two facts the raw-source composition owns — the
  database's axiom-premise typecodes and the conclusion's typecode are
  declared constants.

Universal realization *without* the declared-typecode condition is
false by design: `declareFloating?` stores the typecode into the active
hypothesis' formula, and prefix validity requires every hypothesis
formula's symbols to respect the declarations, so a never-declared
typecode cannot be accepted (negative fixtures below).
-/

namespace Mettapedia.Languages.Metamath.InferenceSourceDummyRealization

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
open Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding

/-! ## One accepted dummy declaration -/

/-- Declare one optional dummy: a `$v` for the variable, then a fresh
`$f` binding it to its typecode.  Both steps are the source GSLT's own
accepted operations. -/
def declareDummy? (state : SourceState)
    (label typecode variableName : String) : Option SourceState :=
  match declareVariables? state [variableName] with
  | none => none
  | some afterVariable =>
      declareFloating? afterVariable label typecode variableName

/-- Acceptance-conditioned shape: the successor state appends exactly the
new variable, the new label, and the new floating hypothesis, leaving
constants, assertions, distinctness data, and scope structure
untouched. -/
theorem declareDummy?_shape {state after : SourceState}
    {label typecode variableName : String}
    (hfresh : variableName ∉ state.declaredVariables)
    (h : declareDummy? state label typecode variableName = some after) :
    after =
      { state with
        declaredVariables := state.declaredVariables ++ [variableName]
        usedLabels := state.usedLabels ++ [label]
        activeHypotheses := state.activeHypotheses ++
          [HypothesisView.floating label typecode variableName] } := by
  unfold declareDummy? at h
  cases hvar : declareVariables? state [variableName] with
  | none =>
      rw [hvar] at h
      exact (Option.some_ne_none after
        (show some after = none from h.symm)).elim
  | some s₁ =>
      rw [hvar] at h
      obtain ⟨-, -, hs₁⟩ := declareVariables?_singleton_inv hvar
      obtain ⟨-, -, hs₂⟩ := declareFloating?_inv h
      subst hs₁
      rw [hs₂, if_neg hfresh]

/-- Typecode availability survives a dummy declaration. -/
theorem declareDummy?_declaredConstants {state after : SourceState}
    {label typecode variableName : String}
    (hfresh : variableName ∉ state.declaredVariables)
    (h : declareDummy? state label typecode variableName = some after) :
    after.declaredConstants = state.declaredConstants := by
  rw [declareDummy?_shape hfresh h]

/-- Fresh dummies never occur in stored distinctness data, so the
proof-facing distinct pairs are untouched. -/
theorem proofDistinct_extend {state : SourceState}
    {label typecode variableName : String}
    (hvalid : sourceStateValid state = true)
    (hfresh : variableName ∉ state.declaredVariables) :
    ({ state with
        declaredVariables := state.declaredVariables ++ [variableName]
        usedLabels := state.usedLabels ++ [label]
        activeHypotheses := state.activeHypotheses ++
          [HypothesisView.floating label typecode variableName] } :
      SourceState).proofDistinctVariables =
      state.proofDistinctVariables := by
  have hpairs : ∀ pair ∈ state.activeDistinctVariables,
      pair.1 ∈ state.declaredVariables ∧
        pair.2 ∈ state.declaredVariables := by
    intro pair hmem
    unfold sourceStateValid at hvalid
    simp only [Bool.and_eq_true, List.all_eq_true] at hvalid
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hdv⟩, -⟩ := hvalid
    have := hdv pair hmem
    simp only [decide_eq_true_eq, List.contains_iff_mem] at this
    exact ⟨this.1.2, this.2⟩
  have hfloats :
      ({ state with
          declaredVariables := state.declaredVariables ++ [variableName]
          usedLabels := state.usedLabels ++ [label]
          activeHypotheses := state.activeHypotheses ++
            [HypothesisView.floating label typecode variableName] } :
        SourceState).activeFloatingVariables =
        state.activeFloatingVariables ++ [variableName] := by
    simp [SourceState.activeFloatingVariables, floatingVariableNames,
      List.filterMap_append, HypothesisView.floatingVariable?]
  unfold SourceState.proofDistinctVariables
  apply List.filter_congr
  intro pair hmem
  obtain ⟨h1, h2⟩ := hpairs pair hmem
  have hne1 : pair.1 ≠ variableName := fun heq => hfresh (heq ▸ h1)
  have hne2 : pair.2 ≠ variableName := fun heq => hfresh (heq ▸ h2)
  rw [hfloats]
  simp [hne1, hne2]

/-- **One accepted dummy declaration realizes one optional frame
extension**: the operational caller frame of the successor is exactly
`extendFloat` of the predecessor's. -/
theorem declareDummy?_callerFrame {state after : SourceState}
    {label typecode variableName : String}
    (hvalid : sourceStateValid state = true)
    (hfresh : variableName ∉ state.declaredVariables)
    (h : declareDummy? state label typecode variableName = some after) :
    sourceOperationalCallerFrame after.toSourcePrefix =
      SourceGSLTSpecGrounding.extendFloat
        (sourceOperationalCallerFrame state.toSourcePrefix)
        ⟨typecode⟩ ⟨variableName⟩ := by
  rw [declareDummy?_shape hfresh h]
  unfold sourceOperationalCallerFrame sourceOperationalFrame
    operationalFrame SourceGSLTSpecGrounding.extendFloat
  congr 1
  · -- hypotheses: map distributes over the appended floating hypothesis
    simp [SourceState.toSourcePrefix, List.map_append, operationalHyp]
  · -- distinctness: the proof-facing pairs are unchanged
    have hdj := proofDistinct_extend
      (label := label) (typecode := typecode)
      (variableName := variableName) hvalid hfresh
    simp only [SourceState.toSourcePrefix, SourceState.callerFrame,
      SourceFrame.toRuntime]
    rw [hdj]

/-! ## Accepted sequences of dummy declarations -/

/-- A dummy-declaration plan: label, typecode, and variable name per
optional hypothesis, in order. -/
structure DummyDecl where
  label : String
  typecode : String
  variableName : String
deriving DecidableEq, Repr

/-- Fold a plan through the accepted single-step operation. -/
def declareDummies? : SourceState → List DummyDecl → Option SourceState
  | state, [] => some state
  | state, decl :: rest =>
      match declareDummy? state decl.label decl.typecode
          decl.variableName with
      | none => none
      | some next => declareDummies? next rest

/-- Spec-level image of a plan. -/
def DummyDecl.spec (decl : DummyDecl) :
    Metamath.Spec.Constant × Metamath.Spec.Variable :=
  (⟨decl.typecode⟩, ⟨decl.variableName⟩)

/-- Stepwise freshness of a plan's variables against the growing
declaration set (the acceptance-level counterpart of
`OptionalFloatSequence`).  Validity of each accepted successor is a
consequence of acceptance and is therefore not re-stated. -/
inductive DummyDeclSequence : SourceState → List DummyDecl → Prop
  | nil (state) : DummyDeclSequence state []
  | cons {state : SourceState} {decl : DummyDecl} {rest : List DummyDecl}
      {next : SourceState}
      (hfresh : decl.variableName ∉ state.declaredVariables)
      (haccept : declareDummy? state decl.label decl.typecode
        decl.variableName = some next)
      (htail : DummyDeclSequence next rest) :
      DummyDeclSequence state (decl :: rest)

theorem DummyDeclSequence.accepts {state : SourceState}
    {decls : List DummyDecl} (hseq : DummyDeclSequence state decls) :
    ∃ after, declareDummies? state decls = some after := by
  induction hseq with
  | nil state => exact ⟨state, rfl⟩
  | @cons state decl rest next hfresh haccept htail ih =>
      obtain ⟨after, hafter⟩ := ih
      refine ⟨after, ?_⟩
      unfold declareDummies?
      rw [haccept]
      exact hafter

/-- Acceptance preserves state validity (the gate guards it). -/
theorem declareDummy?_valid {state after : SourceState}
    {label typecode variableName : String}
    (h : declareDummy? state label typecode variableName = some after) :
    sourceStateValid after = true := by
  unfold declareDummy? at h
  cases hvar : declareVariables? state [variableName] with
  | none =>
      rw [hvar] at h
      exact (Option.some_ne_none after
        (show some after = none from h.symm)).elim
  | some s₁ =>
      rw [hvar] at h
      exact (declareFloating?_inv h).2.1

theorem declareDummy?_valid_before {state after : SourceState}
    {label typecode variableName : String}
    (h : declareDummy? state label typecode variableName = some after) :
    sourceStateValid state = true := by
  unfold declareDummy? at h
  cases hvar : declareVariables? state [variableName] with
  | none =>
      rw [hvar] at h
      exact (Option.some_ne_none after
        (show some after = none from h.symm)).elim
  | some s₁ =>
      exact (declareVariables?_singleton_inv hvar).1

/-- **An accepted plan realizes the batch frame extension**: folding
accepted dummy declarations computes exactly `extendFloats` of the
spec-level plan on the operational caller frame. -/
theorem declareDummies?_callerFrame :
    ∀ {state after : SourceState} {decls : List DummyDecl},
      DummyDeclSequence state decls →
      declareDummies? state decls = some after →
      sourceOperationalCallerFrame after.toSourcePrefix =
        SourceGSLTSpecGrounding.extendFloats
          (sourceOperationalCallerFrame state.toSourcePrefix)
          (decls.map DummyDecl.spec)
  | state, after, [], _, h => by
      cases h
      rfl
  | state, after, decl :: rest, hseq, h => by
      cases hseq with
      | cons hfresh haccept htail =>
          unfold declareDummies? at h
          rw [haccept] at h
          have hstep := declareDummy?_callerFrame
            (declareDummy?_valid_before haccept) hfresh haccept
          have hrest := declareDummies?_callerFrame htail h
          rw [hrest, hstep, List.map_cons]
          simp [SourceGSLTSpecGrounding.extendFloats, DummyDecl.spec]

/-! ## The step-2 keystone -/

open Metamath.Spec.Equivalence in
/-- A frame-supported derivation over a source state's caller frame
remains supported over the caller frame of any accepted dummy-plan
successor, provided the plan's spec image is an optional-float sequence
(the semantic freshness side, dischargeable from acceptance-level
freshness in the supply tier). -/
theorem supported_transport_sourceRealized
    {Γ : Metamath.Spec.Database} {state after : SourceState}
    {decls : List DummyDecl}
    (hseq : DummyDeclSequence state decls)
    (haccept : declareDummies? state decls = some after)
    (hopt : OptionalFloatSequence
      (sourceOperationalCallerFrame state.toSourcePrefix)
      (decls.map DummyDecl.spec))
    {formula : Metamath.Spec.Bridge.MarioFormula}
    (hsupported : SupportedProvable Γ
      (sourceOperationalCallerFrame state.toSourcePrefix) formula) :
    SupportedProvable Γ
      (sourceOperationalCallerFrame after.toSourcePrefix) formula := by
  rw [declareDummies?_callerFrame hseq haccept]
  exact SupportedProvable.extendFloats hopt hsupported

/-! ## Calibration -/

/-- The one-constant calibration state. -/
def calibrationState : SourceState :=
  { initialState with declaredConstants := ["wff"] }

/-- Positive: the constant declaration from the empty state is accepted
with exactly this successor. -/
example :
    declareConstants? initialState ["wff"] = some calibrationState := by
  decide

/-- Positive: one dummy declaration is accepted from the calibration
state, and the operational caller frame gains exactly the optional
float. -/
example :
    (declareDummy? calibrationState "d0" "wff" "x").map
        (fun after => sourceOperationalCallerFrame after.toSourcePrefix) =
      some (SourceGSLTSpecGrounding.extendFloat
        (sourceOperationalCallerFrame calibrationState.toSourcePrefix)
        ⟨"wff"⟩ ⟨"x"⟩) := by
  decide

/-- Negative: a dummy whose typecode was never declared is not accepted —
the prefix-validity gate rejects the floating hypothesis' formula. -/
example :
    declareDummy? initialState "d0" "wff" "x" = none := by decide

/-- Negative: redeclaring an existing variable name is outside this
realization discipline (the plan sequence requires stepwise freshness).
Pinned from the calibration state, where the first step is genuinely
accepted, so the failure isolated here is exactly the second step's
freshness. -/
example :
    ¬ DummyDeclSequence calibrationState
      [⟨"d0", "wff", "x"⟩, ⟨"d1", "wff", "x"⟩] := by
  intro hseq
  cases hseq with
  | cons hfresh haccept htail =>
      cases htail with
      | cons hfresh' haccept' htail' =>
          revert hfresh'
          have hshape := declareDummy?_shape (by decide) haccept
          rw [hshape]
          intro hfresh'
          exact hfresh' (by simp)


/-! ## Acceptance existence for one dummy -/

/-- Every active floating variable is declared (validity forces each
floating hypothesis' formula to respect the declarations). -/
theorem activeFloating_subset_declared {state : SourceState}
    (hvalid : sourceStateValid state = true) :
    ∀ v ∈ state.activeFloatingVariables, v ∈ state.declaredVariables := by
  intro v hv
  unfold sourceStateValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have hprefix := hvalid.1.1.1.1.1.1.1
  unfold sourcePrefixValid at hprefix
  simp only [Bool.and_eq_true] at hprefix
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hhyps⟩, -⟩, -⟩ := hprefix
  simp only [SourceState.toSourcePrefix, List.all_eq_true,
    Function.comp] at hhyps
  simp only [SourceState.activeFloatingVariables,
    floatingVariableNames] at hv
  rcases List.mem_filterMap.mp hv with ⟨hyp, hmem, hval⟩
  cases hyp with
  | essential l f => exact nomatch hval
  | floating l t w =>
      have hw : w = v := Option.some.inj hval
      subst hw
      have := hhyps _ hmem
      simp only [HypothesisView.formula,
        formulaSymbolsRespectDeclarations, Bool.and_eq_true,
        List.all_eq_true] at this
      have := this.2 (.var w) (by simp)
      simpa [List.contains_iff_mem] using this

/-- One dummy declaration is **accepted** whenever the variable and label
are globally fresh and distinct, the label is well-formed, and the
typecode is declared. -/
theorem declareDummy?_accepts (state : SourceState)
    (label typecode variableName : String)
    (hvalid : sourceStateValid state = true)
    (hready : state.pendingBlockCompletions = 0)
    (hvarFresh : variableName ∉ state.objectNames)
    (hlabelFresh : label ∉ state.objectNames)
    (hne : label ≠ variableName)
    (hlabelNonempty : label ≠ "")
    (hlabelPrefix : ¬ label.startsWith
      Mettapedia.Languages.Metamath.InferenceSideConditions.reservedRulePrefix = true)
    (htype : typecode ∈ state.declaredConstants) :
    declareDummy? state label typecode variableName =
      some { state with
        declaredVariables := state.declaredVariables ++ [variableName]
        usedLabels := state.usedLabels ++ [label]
        activeHypotheses := state.activeHypotheses ++
          [HypothesisView.floating label typecode variableName] } := by
  have hstep₁ := declareVariables?_accepts state variableName hvalid
    hready hvarFresh
  have hvalid₁ := (declareVariables?_singleton_inv hstep₁).2.1
  have hlabelFresh₁ : label ∉
      ({ state with declaredVariables :=
          state.declaredVariables ++ [variableName] } :
        SourceState).objectNames := by
    intro h
    apply hlabelFresh
    simp only [SourceState.objectNames] at h ⊢
    rcases List.mem_append.mp h with hcv | hl
    · rcases List.mem_append.mp hcv with hc | hvx
      · exact List.mem_append_left _ (List.mem_append_left _ hc)
      · rcases List.mem_append.mp hvx with hv | hx
        · exact List.mem_append_left _ (List.mem_append_right _ hv)
        · exact absurd (List.mem_singleton.mp hx) hne
    · exact List.mem_append_right _ hl
  have hnofloat : variableName ∉
      state.activeFloatingVariables := fun h =>
    (fun hv => hvarFresh (by
        simp [SourceState.objectNames, hv]))
      (activeFloating_subset_declared hvalid _ h)
  have hstep₂ := declareFloating?_accepts
    { state with declaredVariables :=
        state.declaredVariables ++ [variableName] }
    label typecode variableName hvalid₁ hready hlabelFresh₁
    hlabelNonempty hlabelPrefix
    (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    (by simpa [SourceState.activeFloatingVariables] using hnofloat)
    htype
  unfold declareDummy?
  rw [hstep₁]
  exact hstep₂


/-! ## The fresh supply

Names and labels manufactured by length striping: every string strictly
longer than every used string is unused, odd/even striping keeps names
and labels apart, and lengths grow along the plan so freshness survives
each accepted step. -/

def supplyName (bound i : Nat) : String :=
  String.ofList (List.replicate (bound + 1 + 2 * i) 'v')

def supplyLabel (bound i : Nat) : String :=
  String.ofList (List.replicate (bound + 2 + 2 * i) 'l')

theorem supplyName_length (bound i : Nat) :
    (supplyName bound i).length = bound + 1 + 2 * i := by
  simp [supplyName]

theorem supplyLabel_length (bound i : Nat) :
    (supplyLabel bound i).length = bound + 2 + 2 * i := by
  simp [supplyLabel]

theorem supplyLabel_ne_empty (bound i : Nat) :
    supplyLabel bound i ≠ "" := by
  intro h
  have := supplyLabel_length bound i
  rw [h, show ("" : String).length = 0 from rfl] at this
  omega

theorem supplyLabel_ne_name (bound i : Nat) :
    supplyLabel bound i ≠ supplyName bound i := by
  intro h
  have h1 := supplyLabel_length bound i
  rw [h, supplyName_length] at h1
  omega

theorem supplyLabel_not_reserved (bound i : Nat) :
    ¬ (supplyLabel bound i).startsWith
      Mettapedia.Languages.Metamath.InferenceSideConditions.reservedRulePrefix
        = true := by
  intro h
  have hpref : List.IsPrefix
      (Mettapedia.Languages.Metamath.InferenceSideConditions.reservedRulePrefix.toList)
      ((supplyLabel bound i).toList) := by
    exact String.startsWith_string_iff.mp h
  have hlist : (supplyLabel bound i).toList =
      'l' :: List.replicate (bound + 1 + 2 * i) 'l' := by
    simp [supplyLabel,
      show bound + 2 + 2 * i = (bound + 1 + 2 * i) + 1 by omega,
      List.replicate_succ]
  rw [hlist] at hpref
  obtain ⟨t, ht⟩ := hpref
  have hres :
      Mettapedia.Languages.Metamath.InferenceSideConditions.reservedRulePrefix =
        "$mm." := rfl
  rw [hres] at ht
  have : ("$mm.".toList ++ t) = 'l' :: List.replicate (bound + 1 + 2 * i)
      'l' := ht
  rw [show "$mm.".toList = '$' :: "mm.".toList from rfl] at this
  injection this with h1 _
  exact absurd h1 (by decide)

/-- Names introduced by one accepted dummy declaration: exactly the old
namespace plus the new variable and label. -/
theorem declareDummy?_mem_objectNames {state after : SourceState}
    {label typecode variableName : String}
    (hfresh : variableName ∉ state.declaredVariables)
    (h : declareDummy? state label typecode variableName = some after) :
    ∀ s, s ∈ after.objectNames ↔
      s ∈ state.objectNames ∨ s = variableName ∨ s = label := by
  intro s
  rw [declareDummy?_shape hfresh h]
  constructor
  · intro hs
    simp only [SourceState.objectNames] at hs
    rcases List.mem_append.mp hs with hcv | hl
    · rcases List.mem_append.mp hcv with hc | hvx
      · exact Or.inl (by
          simp only [SourceState.objectNames]
          exact List.mem_append_left _ (List.mem_append_left _ hc))
      · rcases List.mem_append.mp hvx with hv | hx
        · exact Or.inl (by
            simp only [SourceState.objectNames]
            exact List.mem_append_left _ (List.mem_append_right _ hv))
        · exact Or.inr (Or.inl (List.mem_singleton.mp hx))
    · rcases List.mem_append.mp hl with hlab | hx
      · exact Or.inl (by
          simp only [SourceState.objectNames]
          exact List.mem_append_right _ hlab)
      · exact Or.inr (Or.inr (List.mem_singleton.mp hx))
  · intro hs
    simp only [SourceState.objectNames] at hs ⊢
    rcases hs with hold | rfl | rfl
    · rcases List.mem_append.mp hold with hcv | hl
      · rcases List.mem_append.mp hcv with hc | hv
        · exact List.mem_append_left _ (List.mem_append_left _ hc)
        · exact List.mem_append_left _
            (List.mem_append_right _ (List.mem_append_left _ hv))
      · exact List.mem_append_right _ (List.mem_append_left _ hl)
    · exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    · exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- The per-state length bound that keeps the striped supply fresh. -/
def StateBounded (state : SourceState) (bound i : Nat) : Prop :=
  ∀ s ∈ state.objectNames, s.length < bound + 1 + 2 * i

theorem stateBounded_name_fresh {state : SourceState} {bound i : Nat}
    (h : StateBounded state bound i) :
    supplyName bound i ∉ state.objectNames := by
  intro hmem
  have := h _ hmem
  rw [supplyName_length] at this
  omega

theorem stateBounded_label_fresh {state : SourceState} {bound i : Nat}
    (h : StateBounded state bound i) :
    supplyLabel bound i ∉ state.objectNames := by
  intro hmem
  have := h _ hmem
  rw [supplyLabel_length] at this
  omega

theorem stateBounded_name_notVar {state : SourceState} {bound i : Nat}
    (h : StateBounded state bound i) :
    supplyName bound i ∉ state.declaredVariables := fun hv =>
  stateBounded_name_fresh h (by
    simp only [SourceState.objectNames]
    exact List.mem_append_left _ (List.mem_append_right _ hv))

/-- One accepted supply step preserves the bound at the next index. -/
theorem stateBounded_step {state after : SourceState} {bound i : Nat}
    {typecode : String}
    (hbound : StateBounded state bound i)
    (h : declareDummy? state (supplyLabel bound i) typecode
      (supplyName bound i) = some after) :
    StateBounded after bound (i + 1) := by
  intro s hs
  rcases (declareDummy?_mem_objectNames
    (stateBounded_name_notVar hbound) h s).mp hs with hold | rfl | rfl
  · have := hbound _ hold
    omega
  · rw [supplyName_length]
    omega
  · rw [supplyLabel_length]
    omega

/-- The supply plan for a support list: positionally typed, freshly
named and labeled. -/
def supplyPlan (bound : Nat) :
    List Metamath.Spec.Bridge.MarioVR → Nat → List DummyDecl
  | [], _ => []
  | v :: rest, i =>
      ⟨supplyLabel bound i, Metamath.VR.type v, supplyName bound i⟩ ::
        supplyPlan bound rest (i + 1)

/-- **Supply acceptance**: from any valid, ready source state whose
declared constants cover the support typecodes, the striped supply plan
is accepted end to end. -/
theorem supplyPlan_accepts (bound : Nat) :
    ∀ (support : List Metamath.Spec.Bridge.MarioVR)
      (state : SourceState) (i : Nat),
      sourceStateValid state = true →
      state.pendingBlockCompletions = 0 →
      StateBounded state bound i →
      (∀ v ∈ support, Metamath.VR.type v ∈ state.declaredConstants) →
      DummyDeclSequence state (supplyPlan bound support i) ∧
        ∃ after, declareDummies? state (supplyPlan bound support i) =
          some after
  | [], state, i, _, _, _, _ =>
      ⟨.nil state, state, rfl⟩
  | v :: rest, state, i, hvalid, hready, hbound, htypes => by
      have hnotVar := stateBounded_name_notVar hbound
      have haccept := declareDummy?_accepts state
        (supplyLabel bound i) (Metamath.VR.type v) (supplyName bound i)
        hvalid hready
        (stateBounded_name_fresh hbound)
        (stateBounded_label_fresh hbound)
        (supplyLabel_ne_name bound i)
        (supplyLabel_ne_empty bound i)
        (supplyLabel_not_reserved bound i)
        (htypes v (List.Mem.head _))
      have hvalid' := declareDummy?_valid haccept
      have hbound' := stateBounded_step hbound haccept
      obtain ⟨hseqRest, after, hafter⟩ :=
        supplyPlan_accepts bound rest _ (i + 1) hvalid' hready hbound'
          (fun w hw => htypes w (List.Mem.tail _ hw))
      refine ⟨.cons hnotVar haccept hseqRest, after, ?_⟩
      show (match declareDummy? state (supplyLabel bound i)
          (Metamath.VR.type v) (supplyName bound i) with
        | none => none
        | some next =>
            declareDummies? next (supplyPlan bound rest (i + 1))) =
          some after
      rw [haccept]
      exact hafter

/-! ## The semantic image of the supply plan

The accepted supply plan's spec image is an `OptionalFloatSequence`: the
semantic freshness conditions are *derived* from the same length
striping that made the gates accept.  The base frame's obstruction
strings — floating-variable names and essential-hypothesis symbols — all
live in the source state's namespace (validity forces the former into
`declaredVariables` and the latter into the declarations), so every one
of them is shorter than every supplied name. -/

open Mettapedia.Languages.Metamath.InferenceDummyAllocation
open Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport

/-- The supply plan is positionally typed along its support. -/
theorem supplyPlan_typedAlong (bound : Nat) :
    ∀ (support : List Metamath.Spec.Bridge.MarioVR) (i : Nat),
      TypedAlong support ((supplyPlan bound support i).map DummyDecl.spec)
  | [], _ => .nil
  | _ :: rest, i => .cons rfl (supplyPlan_typedAlong bound rest (i + 1))

/-- The supply plan's spec image is an optional-float sequence from any
frame whose variable names are either bound-short or earlier supply
names, and whose essential symbols are all bound-short. -/
theorem supplyPlan_spec_optionalSequence (bound : Nat) :
    ∀ (support : List Metamath.Spec.Bridge.MarioVR) (i : Nat)
      (fr : Metamath.Spec.Frame),
      (∀ w ∈ fr.vars, w.v.length ≤ bound ∨
        ∃ j, j < i ∧ w.v = supplyName bound j) →
      (∀ e, Metamath.Spec.Hyp.essential e ∈ fr.hyps →
        ∀ s ∈ e.syms, s.length ≤ bound) →
      SourceGSLTSpecGrounding.OptionalFloatSequence fr
        ((supplyPlan bound support i).map DummyDecl.spec)
  | [], _, fr, _, _ => .nil fr
  | v :: rest, i, fr, hvars, hess => by
      refine SourceGSLTSpecGrounding.OptionalFloatSequence.cons
        ⟨?_, ?_⟩ ?_
      · -- the supplied name is not a frame variable
        intro hmem
        rcases hvars _ hmem with hle | ⟨j, hj, heq⟩
        · have hlen : (supplyName bound i).length ≤ bound := hle
          rw [supplyName_length] at hlen
          omega
        · have hlen : (supplyName bound i).length =
              (supplyName bound j).length := congrArg String.length heq
          rw [supplyName_length, supplyName_length] at hlen
          omega
      · -- the supplied name occurs in no essential hypothesis
        intro e hmem hsym
        have hlen := hess e hmem _ hsym
        rw [supplyName_length] at hlen
        omega
      · -- tail: the extended frame keeps the invariant at the next index
        refine supplyPlan_spec_optionalSequence bound rest (i + 1)
          (SourceGSLTSpecGrounding.extendFloat fr
            ⟨Metamath.VR.type v⟩ ⟨supplyName bound i⟩) ?_ ?_
        · intro w hw
          rw [SourceGSLTSpecGrounding.frameVars_extendFloat] at hw
          rcases List.mem_append.mp hw with hold | hnew
          · rcases hvars _ hold with hle | ⟨j, hj, hje⟩
            · exact Or.inl hle
            · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hje⟩
          · rcases List.mem_singleton.mp hnew with rfl
            exact Or.inr ⟨i, Nat.lt_succ_self i, rfl⟩
        · intro e hmem s hs
          exact hess e (essential_mem_extendFloat hmem) s hs

/-- Every variable of the operational caller frame is bound-short
whenever the state's object names are: frame variables are exactly the
active floating variables, which validity places among the declared
variables. -/
theorem callerFrame_vars_bounded {state : SourceState} {bound : Nat}
    (hvalid : sourceStateValid state = true)
    (hbound : ∀ s ∈ state.objectNames, s.length ≤ bound) :
    ∀ w ∈ (sourceOperationalCallerFrame state.toSourcePrefix).vars,
      w.v.length ≤ bound := by
  intro w hw
  have hw' : w ∈ (floatingVariableNames state.activeHypotheses).map
      Metamath.Spec.Variable.mk := by
    simpa [sourceOperationalCallerFrame, sourceOperationalFrame,
      SourceState.toSourcePrefix, operationalFrame_vars] using hw
  rcases List.mem_map.mp hw' with ⟨name, hname, rfl⟩
  have hdecl : name ∈ state.declaredVariables :=
    activeFloating_subset_declared hvalid name hname
  exact hbound name (by
    simp only [SourceState.objectNames]
    exact List.mem_append_left _ (List.mem_append_right _ hdecl))

/-- Every essential-hypothesis symbol of the operational caller frame is
bound-short whenever the state's object names are: validity forces every
active hypothesis' formula to respect the declarations, and the
operational image's symbols are exactly the formula's symbol values. -/
theorem callerFrame_essential_bounded {state : SourceState} {bound : Nat}
    (hvalid : sourceStateValid state = true)
    (hbound : ∀ s ∈ state.objectNames, s.length ≤ bound) :
    ∀ e, Metamath.Spec.Hyp.essential e ∈
        (sourceOperationalCallerFrame state.toSourcePrefix).hyps →
      ∀ s ∈ e.syms, s.length ≤ bound := by
  intro e hmem s hs
  have hmem' : Metamath.Spec.Hyp.essential e ∈
      state.activeHypotheses.map operationalHyp := by
    simpa [sourceOperationalCallerFrame, sourceOperationalFrame,
      operationalFrame, SourceState.toSourcePrefix] using hmem
  rcases List.mem_map.mp hmem' with ⟨hyp, hhyp, himg⟩
  unfold sourceStateValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have hprefix := hvalid.1.1.1.1.1.1.1
  unfold sourcePrefixValid at hprefix
  simp only [Bool.and_eq_true] at hprefix
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hhyps⟩, -⟩, -⟩ := hprefix
  simp only [SourceState.toSourcePrefix, List.all_eq_true,
    Function.comp] at hhyps
  have hrespect := hhyps _ hhyp
  cases hyp with
  | floating l t x => exact nomatch himg
  | essential l f =>
      have hef : operationalExpr f = e := by
        simpa [operationalHyp] using himg
      rw [← hef, operationalExpr_syms] at hs
      rcases List.mem_map.mp hs with ⟨sym, hsym, rfl⟩
      simp only [formulaSymbolsRespectDeclarations, Bool.and_eq_true,
        List.all_eq_true, HypothesisView.formula] at hrespect
      have hsymOk := hrespect.2 sym hsym
      cases sym with
      | const c =>
          have hc : c ∈ state.declaredConstants := by
            simpa [List.contains_iff_mem] using hsymOk
          exact hbound _ (by
            simp only [SourceState.objectNames]
            exact List.mem_append_left _ (List.mem_append_left _ hc))
      | var x =>
          have hx : x ∈ state.declaredVariables := by
            simpa [List.contains_iff_mem] using hsymOk
          exact hbound _ (by
            simp only [SourceState.objectNames]
            exact List.mem_append_left _ (List.mem_append_right _ hx))

/-! ## The step-2 capstone: source-accepted supported reconciliation -/

open Metamath.Spec.Equivalence in
/-- **Source-accepted reconciliation.**  From any valid, ready source
state with bound-short object names, every finite-support witness over
the operational caller frame whose support typecodes are declared and
whose conclusion mentions only frame variables yields a **constructed,
accepted** dummy-declaration plan whose successor's caller frame supports
the derivation.  The plan is the striped supply; its acceptance, its
semantic freshness, and its positional typing are all derived — nothing
is inferred from the semantic allocator.  (Witness-parameterized on
purpose: extracting a witness with typecode provenance from a bare
`Metamath.Provable` derivation is the raw-source composition's
obligation, per the module docstring.) -/
theorem witness_toSupported_sourceAccepted
    {Γ : Metamath.Spec.Database} {state : SourceState} {bound : Nat}
    (hvalid : sourceStateValid state = true)
    (hready : state.pendingBlockCompletions = 0)
    (hbound : ∀ s ∈ state.objectNames, s.length ≤ bound)
    {support : List Metamath.Spec.Bridge.MarioVR}
    {formula : Metamath.Spec.Bridge.MarioFormula}
    (hwitness : FiniteSupportWitness (Γ := Γ)
      (source := frameToContext
        (sourceOperationalCallerFrame state.toSourcePrefix))
      (formula := formula) support)
    (htypes : ∀ v ∈ support,
      Metamath.VR.type v ∈ state.declaredConstants)
    (hconcl : ∀ vr, Metamath.Sym.var vr ∈ formula.2 →
      ∃ w, findVar (varMapOfFrame
        (sourceOperationalCallerFrame state.toSourcePrefix)) vr =
          some w) :
    ∃ plan after,
      DummyDeclSequence state plan ∧
      declareDummies? state plan = some after ∧
      SupportedProvable Γ
        (sourceOperationalCallerFrame after.toSourcePrefix) formula := by
  obtain ⟨hseq, after, hafter⟩ := supplyPlan_accepts bound support state 0
    hvalid hready
    (fun s hs => by
      have := hbound s hs
      omega)
    htypes
  have hopt : SourceGSLTSpecGrounding.OptionalFloatSequence
      (sourceOperationalCallerFrame state.toSourcePrefix)
      ((supplyPlan bound support 0).map DummyDecl.spec) :=
    supplyPlan_spec_optionalSequence bound support 0 _
      (fun w hw => Or.inl (callerFrame_vars_bounded hvalid hbound w hw))
      (callerFrame_essential_bounded hvalid hbound)
  have hsup := witness_toSupported_typedPlan hwitness hconcl
    (supplyPlan_typedAlong bound support 0) hopt
  refine ⟨supplyPlan bound support 0, after, hseq, hafter, ?_⟩
  rw [declareDummies?_callerFrame hseq hafter]
  exact hsup

open Metamath.Spec.Equivalence in
/-- **Provable-form source-accepted reconciliation.**  The typed
extraction discharges the support-typecode hypothesis: from a bare
canonical derivation over the caller frame, a plan and its accepted
successor are constructed whenever the database's axiom-premise
typecodes and the conclusion's typecode are declared constants — the
two facts the raw-source composition owns. -/
theorem provable_toSupported_sourceAccepted
    {Γ : Metamath.Spec.Database} {state : SourceState} {bound : Nat}
    (hvalid : sourceStateValid state = true)
    (hready : state.pendingBlockCompletions = 0)
    (hbound : ∀ s ∈ state.objectNames, s.length ≤ bound)
    {formula : Metamath.Spec.Bridge.MarioFormula}
    (hdbTypes : ∀ t, AxiomPremiseTypecode Γ t →
      t ∈ state.declaredConstants)
    (hconclType : formula.1 ∈ state.declaredConstants)
    (hconcl : ∀ vr, Metamath.Sym.var vr ∈ formula.2 →
      ∃ w, findVar (varMapOfFrame
        (sourceOperationalCallerFrame state.toSourcePrefix)) vr =
          some w)
    (h : Metamath.Provable (dbToAxioms Γ)
      (frameToContext (sourceOperationalCallerFrame state.toSourcePrefix))
      formula) :
    ∃ plan after,
      DummyDeclSequence state plan ∧
      declareDummies? state plan = some after ∧
      SupportedProvable Γ
        (sourceOperationalCallerFrame after.toSourcePrefix) formula := by
  obtain ⟨support, hwitness, htyped⟩ :=
    Provable.exists_finiteSupport_typed h
  exact witness_toSupported_sourceAccepted hvalid hready hbound hwitness
    (fun v hv => by
      rcases htyped v hv with heq | haxt
      · rw [heq]
        exact hconclType
      · exact hdbTypes _ haxt)
    hconcl

/-! ## Supply-tier calibration -/

/-- The supplied strings are the expected literals. -/
example : supplyName 3 0 = "vvvv" := by decide
example : supplyLabel 3 0 = "lllll" := by decide

/-- The plan construction itself reduces to its literal shape. -/
example : supplyPlan 3 [⟨"wff", 0⟩] 0 = [⟨"lllll", "wff", "vvvv"⟩] := by
  decide

/-- One-character-constant calibration state for the accepted-path
fixture.  Engineering note for posterity: core `String.startsWith`
kernel-reduces only while the candidate is shorter than the queried
prefix (the byte-comparison loop it otherwise enters is kernel-opaque),
so the reserved-prefix gate `validRuleLabel` is kernel-checkable exactly
for labels under four bytes.  A one-character constant gives bound `1`
and supply label `"lll"`, keeping the whole accepted run inside the
kernel-reducible fragment.  The theorems above are universal and do not
depend on this boundary. -/
def supplyCalibrationState : SourceState :=
  { initialState with declaredConstants := ["w"] }

example :
    declareConstants? initialState ["w"] = some supplyCalibrationState := by
  decide

/-- Positive (kernel-checked): the striped one-leaf supply plan is
accepted end to end, with the exact successor (supplied name `"vv"`,
label `"lll"`). -/
example :
    declareDummies? supplyCalibrationState (supplyPlan 1 [⟨"w", 0⟩] 0) =
      some { supplyCalibrationState with
        declaredVariables := [supplyName 1 0]
        usedLabels := [supplyLabel 1 0]
        activeHypotheses :=
          [HypothesisView.floating (supplyLabel 1 0) "w"
            (supplyName 1 0)] } := by
  decide

/-- Negative (kernel-checked): the same plan is rejected from the empty
state — the typecode was never declared, so the acceptance hypotheses of
the supply tier are not vacuous. -/
example :
    declareDummies? initialState (supplyPlan 3 [⟨"wff", 0⟩] 0) =
      none := by
  decide

/-- Richer calibration state: an existing float, an essential
hypothesis referencing it, and a stored `$d` pair — every name one
character, so accepted runs over it stay kernel-reducible. -/
def richCalibrationState : SourceState :=
  { initialState with
    declaredConstants := ["w"]
    declaredVariables := ["x", "y"]
    usedLabels := ["f", "e"]
    activeHypotheses :=
      [HypothesisView.floating "f" "w" "x",
       HypothesisView.essential "e" ⟨"w", [.var "x"]⟩]
    activeDistinctVariables := [("x", "y")] }

/-- The rich state is reached from the empty state by accepted
operations only. -/
example :
    (do
      let s₁ ← declareConstants? initialState ["w"]
      let s₂ ← declareVariables? s₁ ["x", "y"]
      let s₃ ← declareFloating? s₂ "f" "w" "x"
      let s₄ ← declareEssential? s₃ "e" ⟨"w", [.var "x"]⟩
      declareDisjoint? s₄ ["x", "y"]) = some richCalibrationState := by
  decide

/-- Positive (kernel-checked): one striped supply step is accepted over
existing floats, essentials, and distinctness data, and the operational
caller frame image is exactly the optional `extendFloat`; the stored
`$d` pair's proof-facing status is untouched. -/
example :
    (declareDummy? richCalibrationState (supplyLabel 1 0) "w"
        (supplyName 1 0)).map
        (fun after => sourceOperationalCallerFrame after.toSourcePrefix) =
      some (SourceGSLTSpecGrounding.extendFloat
        (sourceOperationalCallerFrame richCalibrationState.toSourcePrefix)
        ⟨"w"⟩ ⟨supplyName 1 0⟩) := by
  decide

/-- Positive (kernel-checked): the one-leaf supply plan is accepted end
to end over the rich state, with the exact successor. -/
example :
    declareDummies? richCalibrationState (supplyPlan 1 [⟨"w", 0⟩] 0) =
      some { richCalibrationState with
        declaredVariables := ["x", "y", supplyName 1 0]
        usedLabels := ["f", "e", supplyLabel 1 0]
        activeHypotheses := richCalibrationState.activeHypotheses ++
          [HypothesisView.floating (supplyLabel 1 0) "w"
            (supplyName 1 0)] } := by
  decide

end Mettapedia.Languages.Metamath.InferenceSourceDummyRealization
