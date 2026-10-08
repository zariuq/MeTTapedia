import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaSelection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerNumbers

/-!
# Natural-number checking from an authored equation table

The two source entries are the actual recursor equations. Metavariable slots
are reconstructed by the generic matcher, including the dependent motive and
both methods. The resulting instances are computation steps of the already
constructed cumulative natural-number model. All formation and preservation
obligations therefore come from that computing model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableTowerSchemaNumbers

open Mettapedia.TypeTheory.UniverseLevel
open TowerNumbersModel AlgebraicSchema ExecutableSchemaSelection

def zeroLeft : Tm Tower.Head 3 :=
  recApp numRec [.var 0, .var 1, .var 2] (.const zero)

def zeroRight : Tm Tower.Head 3 := .var 1

def succLeft : Tm Tower.Head 4 :=
  recApp numRec [.var 0, .var 1, .var 2] (.app (.const succ) (.var 3))

def succRight : Tm Tower.Head 4 :=
  .app (.app (.var 2) (.var 3)) (recApp numRec [.var 0, .var 1, .var 2] (.var 3))

def program : SchemaTable Tower.Head :=
  [⟨3, zeroLeft, zeroRight⟩, ⟨4, succLeft, succRight⟩]

theorem program_admitted : Admitted program := by
  rw [program, admitted_cons, admitted_cons]
  exact ⟨by unfold GoodEntry; decide +kernel, by unfold GoodEntry; decide +kernel,
    fun entry impossible => False.elim (List.not_mem_nil impossible)⟩

/-- Every computed source entry means an actual dependent recursor step. -/
theorem source_step (level : LevelExpr Nat) {ambient : Nat} {source target : Tm Tower.Head ambient}
    (step : (SchemaFamily.computation program.family).step source target) :
    (rules level).computation.step source target := by
  cases step with
  | instantiate listed substitution =>
      change (⟨_, (_, _)⟩ : Entry Tower.Head) ∈ program at listed
      simp only [program, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with first | second
      · cases first
        exact ⟨substitution 0, [substitution 1, substitution 2], 0, zero, [], [], substitution 1,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases second
        exact ⟨substitution 0, [substitution 1, substitution 2], 1, succ, [.recursive],
          [substitution 3], substitution 2, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (level : LevelExpr Nat)

/-- The model's root evaluator is obtained from actual authored-table
selection. No root-rule or typing witness is supplied by its caller. -/
def root : ExecutableReduction.RootEvaluator (rules level) := fun {_} source =>
  match first program source with
  | .fired receipt _ => some ⟨receipt.target, source_step level receipt.semantic_step⟩
  | .unassigned _ _ | .missed => none

@[simp] theorem root_zero {ambient : Nat} (motive base step : Tm Tower.Head ambient) :
    (root level (recApp numRec [motive, base, step] (.const zero))).map Subtype.val =
      some base := by
  simp [-Order.lt_one_iff, -add_pos_iff,
    root, first, program, zeroLeft, zeroRight, recApp, appSpine,
    ExecutableSchemaMatching.run, ExecutableSchemaMatching.bindSlot,
    ExecutableSchemaMatching.RightAssigned, variableMultiplicity,
    MatchedEntry.target, ExecutableSchemaMatching.materialize, Presentation.subst,
    Fin.forall_fin_succ, Function.update]

@[simp] theorem root_succ {ambient : Nat} (motive base step child : Tm Tower.Head ambient) :
    (root level (recApp numRec [motive, base, step] (.app (.const succ) child))).map Subtype.val =
      some (.app (.app step child) (recApp numRec [motive, base, step] child)) := by
  simp [-Order.lt_one_iff, -Order.lt_two_iff, -add_pos_iff, -Nat.ofNat_pos,
    root, first, program, zeroLeft, succLeft, succRight, recApp, appSpine,
    ExecutableSchemaMatching.run, ExecutableSchemaMatching.bindSlot,
    ExecutableSchemaMatching.RightAssigned, variableMultiplicity,
    MatchedEntry.target, MatchedEntry.prepend, Outcome.prepend,
    ExecutableSchemaMatching.materialize, Presentation.subst, Fin.forall_fin_succ, Function.update]

theorem root_exists_iff_schema_step {ambient : Nat} (source : Tm Tower.Head ambient) :
    (first program source).target?.isSome = true ↔
      ∃ target, (SchemaFamily.computation program.family).step source target :=
  first_has_target_iff_step program_admitted source

def reducer : ExecutableReduction.Reducer (rules level) :=
  ExecutableReduction.normalize (rules level) (root level)

def accepts {ambient : Nat} (budget : Nat) (context : Ctx Tower.Head ambient)
    (source expected : Tm Tower.Head ambient) : Bool :=
  ExecutableChecking.accepts (rules level) (ExecutableTowerNumbers.choices level)
    (reducer level) budget context source expected

/-- Source-derived execution and declaration formation meet in the genuine
computing model, for arbitrary contexts, terms, types and level expressions. -/
theorem accepts_sound {ambient budget : Nat} {context : Ctx Tower.Head ambient}
    {source expected : Tm Tower.Head ambient}
    (accepted : accepts level budget context source expected = true) :
    Typed (rules level) context source expected :=
  ExecutableChecking.accepts_sound (S := setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) accepted

def acceptsSource {ambient : Nat} (budget : Nat)
    (context : ExecutableWrittenChecking.SourceContext Tower.Head ambient)
    (source expected : ATm Tower.Head ambient) : Bool :=
  ExecutableWrittenChecking.acceptsSource (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) budget context source expected

theorem acceptsSource_sound {ambient budget : Nat}
    {context : ExecutableWrittenChecking.SourceContext Tower.Head ambient}
    {source expected : ATm Tower.Head ambient}
    (accepted : acceptsSource level budget context source expected = true) :
    ATyped (rules level) context.erase source expected.erase :=
  ExecutableWrittenChecking.acceptsSource_sound (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) accepted

end TypedEquality.Normalization.ExecutableTowerSchemaNumbers
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
