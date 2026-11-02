import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelSteps
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedDriverReading

/-!
# ρ's runtime model: the normalized profile agrees with the front door

The normalized ρ profile (`Instances.Normalized.RhoProfile`) steps by the plan's firings between terms equal in its
model. The model language (`RhoModel.language`) authors that model; its equivalence is the profile's equality
(`RhoModel.same_iff`) and its steps are the plan's firings (`RhoModel.licensed_step`, `RhoModel.step_receipt`).

- **The moves of the model keep scoping** (`Move.scoped_eq`), and the law steps keep sealing by quotations, which the
  name equation keeps read forwards (`lawStep_safe_eq`, `quoteDropStep_safe`). So the normal form of a process of
  ρ's carrier is in the carrier (`form_carrier`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (LawStep)
open Mettapedia.OSLF.MeTTaIL.QuoteDrop (QuoteDropStep)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Instances.Normalized
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (HashSetFree)

/-! ## Scoping -/

theorem scopedList_iff {depth : ℕ} {patterns : List Pattern} :
    Pattern.isWellScopedListAt depth patterns = true ↔ ∀ pattern ∈ patterns, pattern.isWellScopedAt depth = true :=
  ScopedPattern.isWellScopedListAt_eq_true_iff depth patterns

theorem scopedList_replace {depth : ℕ} {before after : List Pattern} {left right : Pattern}
    (same : left.isWellScopedAt depth = right.isWellScopedAt depth) :
    Pattern.isWellScopedListAt depth (before ++ left :: after) =
      Pattern.isWellScopedListAt depth (before ++ right :: after) := by
  apply Bool.eq_iff_iff.mpr
  simp only [scopedList_iff, List.mem_append, List.mem_cons]
  constructor
  · rintro each x (inBefore | rfl | inAfter)
    · exact each x (.inl inBefore)
    · exact same ▸ each _ (.inr (.inl rfl))
    · exact each x (.inr (.inr inAfter))
  · rintro each x (inBefore | rfl | inAfter)
    · exact each x (.inl inBefore)
    · exact same.symm ▸ each _ (.inr (.inl rfl))
    · exact each x (.inr (.inr inAfter))

theorem lawStep_scoped_eq {left right : Pattern} (step : LawStep laws left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction step with
  | permute _ permutation =>
    intro depth
    apply Bool.eq_iff_iff.mpr
    simp only [Pattern.isWellScopedAt, scopedList_iff]
    exact ⟨fun each x member => each x (permutation.symm.subset member),
      fun each x member => each x (permutation.subset member)⟩
  | members same =>
    intro depth
    apply Bool.eq_iff_iff.mpr
    simp only [Pattern.isWellScopedAt, scopedList_iff]
    exact ⟨fun each x member => each x ((same x).mpr member), fun each x member => each x ((same x).mp member)⟩
  | flatten _ =>
    intro depth
    apply Bool.eq_iff_iff.mpr
    simp only [Pattern.isWellScopedAt, scopedList_iff, List.forall_mem_append, List.forall_mem_cons]
    tauto
  | unit _ _ =>
    intro depth
    apply Bool.eq_iff_iff.mpr
    simp only [Pattern.isWellScopedAt, scopedList_iff, List.forall_mem_append, List.forall_mem_cons]
    simp
  | apply _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact scopedList_replace (ih depth)
  | lambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | multiLambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | substBody _ ih => intro depth; simp only [Pattern.isWellScopedAt]; rw [ih]
  | substReplacement _ ih => intro depth; simp only [Pattern.isWellScopedAt]; rw [ih]
  | element _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact scopedList_replace (ih depth)

theorem quoteDropStep_scoped_eq {left right : Pattern} (step : QuoteDropStep presentation left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction step with
  | collapse name => intro depth; simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | apply _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact scopedList_replace (ih depth)
  | lambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | multiLambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | substBody _ ih => intro depth; simp only [Pattern.isWellScopedAt]; rw [ih]
  | substReplacement _ ih => intro depth; simp only [Pattern.isWellScopedAt]; rw [ih]
  | element _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact scopedList_replace (ih depth)

theorem Move.scoped_eq {left right : Pattern} (move : Move left right) (depth : ℕ) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  rcases move with law | quoteDrop
  · exact lawStep_scoped_eq law depth
  · exact quoteDropStep_scoped_eq quoteDrop depth

/-! ## Sealing by quotations -/

/-- Sealing at a binder depth. -/
abbrev Safe (depth : ℕ) (pattern : Pattern) : Prop := ScopedPattern.binderSafeAt "NQuote" depth pattern = true

theorem safeList_iff {depth : ℕ} : ∀ {patterns : List Pattern},
    ScopedPattern.binderSafeListAt "NQuote" depth patterns = true ↔ ∀ pattern ∈ patterns, Safe depth pattern
  | [] => by simp [ScopedPattern.binderSafeListAt]
  | pattern :: patterns => by simp [ScopedPattern.binderSafeListAt, safeList_iff]

theorem safe_collection_iff {kind : CollType} {elements : List Pattern} {rest : Option String} {depth : ℕ} :
    Safe depth (.collection kind elements rest) ↔ ∀ element ∈ elements, Safe depth element := by
  simp only [Safe, ScopedPattern.binderSafeAt]
  exact safeList_iff

/-- The depth a constructor's arguments are read at: none inside a quotation. -/
def argumentDepth (constructor : String) (arguments : List Pattern) (depth : ℕ) : ℕ :=
  if constructor = "NQuote" ∧ arguments.length = 1 then 0 else depth

theorem safe_apply_iff {constructor : String} {depth : ℕ} : ∀ {arguments : List Pattern},
    Safe depth (.apply constructor arguments) ↔
      ∀ argument ∈ arguments, Safe (argumentDepth constructor arguments depth) argument
  | [] => by simp [Safe, ScopedPattern.binderSafeAt, ScopedPattern.binderSafeListAt]
  | [argument] => by
    by_cases quote : constructor = "NQuote"
    · subst quote
      simp [Safe, ScopedPattern.binderSafeAt, argumentDepth]
    · simp [Safe, ScopedPattern.binderSafeAt, ScopedPattern.binderSafeListAt, argumentDepth, quote]
  | first :: second :: more => by
    simp only [Safe, ScopedPattern.binderSafeAt, argumentDepth, List.length_cons]
    rw [if_neg (by omega)]
    exact safeList_iff

theorem replace_forall {P : Pattern → Prop} {before after : List Pattern} {left right : Pattern}
    (moved : P left → P right) (each : ∀ x ∈ before ++ left :: after, P x) : ∀ x ∈ before ++ right :: after, P x := by
  simp only [List.mem_append, List.mem_cons] at each ⊢
  rintro x (inBefore | rfl | inAfter)
  · exact each x (.inl inBefore)
  · exact moved (each _ (.inr (.inl rfl)))
  · exact each x (.inr (.inr inAfter))

theorem safe_apply_replace {constructor : String} {before after : List Pattern} {left right : Pattern}
    (moved : ∀ depth, Safe depth left → Safe depth right) (depth : ℕ)
    (safe : Safe depth (.apply constructor (before ++ left :: after))) :
    Safe depth (.apply constructor (before ++ right :: after)) := by
  rw [safe_apply_iff] at safe ⊢
  have lengths : (before ++ right :: after).length = (before ++ left :: after).length := by simp
  simp only [argumentDepth, lengths] at safe ⊢
  exact replace_forall (moved _) safe

theorem safe_element_replace {kind : CollType} {before after : List Pattern} {left right : Pattern}
    {rest : Option String} (moved : ∀ depth, Safe depth left → Safe depth right) (depth : ℕ)
    (safe : Safe depth (.collection kind (before ++ left :: after) rest)) :
    Safe depth (.collection kind (before ++ right :: after) rest) := by
  rw [safe_collection_iff] at safe ⊢
  exact replace_forall (moved depth) safe

/-- **A law step keeps sealing, both ways.** -/
theorem lawStep_safe_iff {left right : Pattern} (step : LawStep laws left right) :
    ∀ depth, Safe depth left ↔ Safe depth right := by
  induction step with
  | permute _ permutation =>
    intro depth
    rw [safe_collection_iff, safe_collection_iff]
    exact ⟨fun each x member => each x (permutation.symm.subset member),
      fun each x member => each x (permutation.subset member)⟩
  | members same =>
    intro depth
    rw [safe_collection_iff, safe_collection_iff]
    exact ⟨fun each x member => each x ((same x).mpr member), fun each x member => each x ((same x).mp member)⟩
  | flatten _ =>
    intro depth
    simp only [safe_collection_iff, List.forall_mem_append, List.forall_mem_cons]
    tauto
  | unit _ _ =>
    intro depth
    simp only [safe_collection_iff, List.forall_mem_append, List.forall_mem_cons]
    have zero : Safe depth (.apply "PZero" []) := by simp [Safe, ScopedPattern.binderSafeAt,
      ScopedPattern.binderSafeListAt]
    tauto
  | apply _ ih =>
    intro depth
    exact ⟨safe_apply_replace (fun d => (ih d).mp) depth, safe_apply_replace (fun d => (ih d).mpr) depth⟩
  | lambda _ ih => intro depth; simpa [Safe, ScopedPattern.binderSafeAt] using ih (depth + 1)
  | multiLambda _ ih => intro depth; simpa [Safe, ScopedPattern.binderSafeAt] using ih _
  | substBody _ ih =>
    intro depth
    simp only [Safe, ScopedPattern.binderSafeAt, Bool.and_eq_true]
    exact and_congr (ih (depth + 1)) Iff.rfl
  | substReplacement _ ih =>
    intro depth
    simp only [Safe, ScopedPattern.binderSafeAt, Bool.and_eq_true]
    exact and_congr Iff.rfl (ih depth)
  | element _ ih =>
    intro depth
    exact ⟨safe_element_replace (fun d => (ih d).mp) depth, safe_element_replace (fun d => (ih d).mpr) depth⟩

/-- **A use of the name equation, read forwards, keeps sealing.** -/
theorem quoteDropStep_safe {left right : Pattern} (step : QuoteDropStep presentation left right) :
    ∀ depth, Safe depth left → Safe depth right := by
  induction step with
  | collapse name =>
    intro depth safe
    have quote : presentation.quoteConstructor = "NQuote" := rfl
    have drop : presentation.dropConstructor = "PDrop" := rfl
    have inner : Safe 0 name := by
      simpa [Safe, ScopedPattern.binderSafeAt, ScopedPattern.binderSafeListAt, quote, drop] using safe
    exact ScopedPattern.binderSafeAt_mono "NQuote" inner (Nat.zero_le _)
  | apply _ ih => exact safe_apply_replace ih
  | lambda _ ih => intro depth safe; simpa [Safe, ScopedPattern.binderSafeAt] using ih (depth + 1) safe
  | multiLambda _ ih => intro depth safe; simpa [Safe, ScopedPattern.binderSafeAt] using ih _ safe
  | substBody _ ih =>
    intro depth safe
    simp only [Safe, ScopedPattern.binderSafeAt, Bool.and_eq_true] at safe ⊢
    exact ⟨ih _ safe.1, safe.2⟩
  | substReplacement _ ih =>
    intro depth safe
    simp only [Safe, ScopedPattern.binderSafeAt, Bool.and_eq_true] at safe ⊢
    exact ⟨safe.1, ih _ safe.2⟩
  | element _ ih => exact safe_element_replace ih

/-- **The normal form of a process sealed by its quotations is sealed.** -/
theorem form_sealed {source : Pattern} (safe : sealed source = true) : sealed (RhoProfile.form source) = true := by
  have forward : ∀ {target : Pattern}, QuoteDrop.QuoteDropForward presentation source target → Safe 0 target := by
    intro target chain
    induction chain with
    | refl => exact safe
    | tail _ step ih => exact quoteDropStep_safe step 0 ih
  have quoteDrops := forward (QuoteDrop.quoteDrop_forward (declaration := presentation) source)
  have lawChain := CanonicalBags.to_lawNormal laws (QuoteDrop.normal presentation source)
  show Safe 0 (CanonicalBags.lawNormal laws (QuoteDrop.normal presentation source))
  have along : ∀ {a b : Pattern}, Relation.EqvGen (LawStep RhoModel.laws) a b → (Safe 0 a ↔ Safe 0 b) := by
    intro a b related
    induction related with
    | rel _ _ step => exact lawStep_safe_iff step 0
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  exact (along lawChain).mp quoteDrops

/-- **The normal form of a process of ρ's carrier is in ρ's carrier.** -/
theorem form_carrier {source : Pattern} (admitted : carrier source = true) : carrier (RhoProfile.form source) = true := by
  obtain ⟨sortedSource, safe⟩ := Bool.and_eq_true_iff.mp admitted
  simp only [carrier, Bool.and_eq_true]
  exact ⟨sorted_iff.mpr (RhoProfile.normal_admitted source (sorted_iff.mp sortedSource)), form_sealed safe⟩


/-! ## The region: the class of ρ's carrier -/

/-- **Where the profile is read**: states without sets equal in the model to a process of ρ's carrier. -/
def Region (term : Pattern) : Prop :=
  IsState term ∧ HashSetFree term ∧ ∃ origin, carrier origin = true ∧ ModelEquiv origin term

theorem carrier_state {term : Pattern} (admitted : carrier term = true) : IsState term ∧ HashSetFree term := by
  have typed := sorted_iff.mp (Bool.and_eq_true_iff.mp admitted).1
  exact ⟨⟨typed.2.2.2, typed.2.2.1⟩, Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary.rhoProcWellSorted_hashSetFree
    (Complete.RhoReference.procWellSorted_of_sorted ((GeneralPlanEnvironment.typing_iff plan [] proc _).mpr typed))⟩

theorem carrier_region {term : Pattern} (admitted : carrier term = true) : Region term :=
  ⟨(carrier_state admitted).1, (carrier_state admitted).2, term, admitted, .refl _⟩

/-- **The model's equality keeps states without sets so**, both ways. -/
theorem modelEquiv_state {first second : Pattern} (equal : ModelEquiv first second) :
    (IsState first ∧ HashSetFree first) ↔ (IsState second ∧ HashSetFree second) := by
  have moves := modelEquiv_iff.mp equal
  clear equal
  induction moves with
  | rel _ _ move =>
    unfold IsState IsObject
    rw [move.scoped_eq 0, move.object_eq, move.pure_iff]
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem modelEquiv_trans {first second third : Pattern} (one : ModelEquiv first second) (two : ModelEquiv second third) :
    ModelEquiv first third :=
  .trans _ _ _ one two

theorem moves_modelEquiv {first second : Pattern} (moves : Relation.EqvGen Move first second) :
    ModelEquiv first second :=
  modelEquiv_iff.mpr moves

/-- The profile's steps: a firing of the plan between terms equal in the model. -/
theorem profile_step_iff (source target : Pattern) :
    RhoProfile.profile.system.Step source target ↔
      ∃ representative receipt, ModelEquiv source representative ∧
        GeneralOccurrenceSemantics.Primitive plan [] proc representative receipt ∧ ModelEquiv receipt.target target := by
  rw [Profile.step_iff_source]
  show (∃ representative receipt,
      Relation.EqvGen (Complete.QuoteDropCoherence.ModelEquation RhoProfile.generated.plan [] proc presentation)
        source representative ∧
      GeneralOccurrenceSemantics.Primitive RhoProfile.generated.plan [] proc representative receipt ∧
      Relation.EqvGen (Complete.QuoteDropCoherence.ModelEquation RhoProfile.generated.plan [] proc presentation)
        receipt.target target) ↔ _
  rw [RhoProfile.generated_plan]

theorem form_modelEquiv (term : Pattern) : ModelEquiv term (RhoProfile.form term) :=
  RhoProfile.normalizer.sound term

theorem form_eq {first second : Pattern} (equal : ModelEquiv first second) :
    RhoProfile.form first = RhoProfile.form second :=
  RhoProfile.normalizer.eqvGen_eq equal

/-- **A step of the profile from the class of a process of ρ's carrier is a step of the model** from that process's
normal form, which is in the carrier, to a process of the carrier equal in the model to the step's target. -/
theorem profile_step_witness {origin source target : Pattern} (admitted : carrier origin = true)
    (equal : ModelEquiv origin source) (step : RhoProfile.profile.system.Step source target) :
    ∃ contractum fuel, Step fuel (RhoProfile.form origin) contractum ∧ carrier contractum = true ∧
      ModelEquiv contractum target := by
  obtain ⟨representative, receipt, before, fired, after⟩ := (profile_step_iff source target).mp step
  obtain ⟨next, nextFired, related⟩ := RhoProfile.primitive_form fired
  have sameForm : RhoProfile.form representative = RhoProfile.form origin :=
    (form_eq (modelEquiv_trans equal before)).symm
  rw [sameForm] at nextFired
  obtain ⟨⟨_, licensed⟩, firing, _, filled, _⟩ := nextFired
  simp only [GeneralPlanEnvironment.environmentWith_empty] at firing
  have formAdmitted := form_carrier admitted
  obtain ⟨contractum, fuel, modelStep, moved⟩ := licensed_step licensed rfl rfl formAdmitted firing
  rw [← filled] at moved
  exact ⟨contractum, fuel, modelStep, step_carrier formAdmitted modelStep,
    modelEquiv_trans (moves_modelEquiv moved) (modelEquiv_trans (.symm _ _ related) after)⟩

variable (relEnv : RelationEnv)

/-- **The normalized ρ profile agrees with the front door** on the class of ρ's carrier: its steps are the model
language's steps, it does not leave the class, and its equality is the model language's identification. -/
theorem agreement : NormalizedReading.Agreement RhoProfile.profile relEnv language reading Region where
  object _ inside := inside.1.2
  steps source inside target := by
    obtain ⟨sourceState, sourcePure, origin, admitted, equal⟩ := inside
    constructor
    · rintro ⟨_, targetState, redex, contractum, witness, placed, _, ⟨_, fuel, modelStep⟩, _, after, _⟩
      obtain ⟨receipt, fired, related⟩ := step_receipt fuel modelStep
      exact (profile_step_iff source target).mpr ⟨redex, receipt, modelEquiv_of_objectEquivalent placed, fired,
        modelEquiv_trans (moves_modelEquiv related) (modelEquiv_of_objectEquivalent after)⟩
    · intro step
      obtain ⟨contractum, fuel, modelStep, contractumAdmitted, toTarget⟩ := profile_step_witness admitted equal step
      have contractumState := carrier_state contractumAdmitted
      have targetState := (modelEquiv_state toTarget).mp contractumState
      have formState := carrier_state (form_carrier admitted)
      refine ⟨sourceState, targetState.1, RhoProfile.form origin, contractum, .base [], ?_, formState.1,
        ⟨rfl, fuel, modelStep⟩, contractumState.1, same_of_modelEquiv toTarget contractumState.1.2 contractumState.2,
        rfl⟩
      exact same_of_modelEquiv (modelEquiv_trans (.symm _ _ equal) (form_modelEquiv origin)) sourceState.2 sourcePure
  closed source target inside step := by
    obtain ⟨_, _, origin, admitted, equal⟩ := inside
    obtain ⟨contractum, _, _, contractumAdmitted, toTarget⟩ := profile_step_witness admitted equal step
    have targetState := (modelEquiv_state toTarget).mp (carrier_state contractumAdmitted)
    exact ⟨targetState.1, targetState.2, contractum, contractumAdmitted, toTarget⟩
  equal first second firstInside secondInside := by
    refine (same_iff (relEnv := relEnv) firstInside.1.2 firstInside.2.1).trans ⟨form_eq, fun sameForm => ?_⟩
    have formSame : RhoProfile.form first = RhoProfile.form second := sameForm
    exact modelEquiv_trans (form_modelEquiv first)
      (formSame ▸ (.symm _ _ (form_modelEquiv second) : ModelEquiv (RhoProfile.form second) second))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel
