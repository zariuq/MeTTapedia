import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionSettling

/-!
# Publication with a retained declared typing

An output retains a judged source value and its requested type. Its license
compares those formed types under the information's solutions. It does not
forget the source annotation and search for another typing of the raw code.
The comparison descends through agreement, using the existing conversion
theorems. The realized value keeps the substituted source code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head : Type} {rules : Rules Head}

/-- The original judged value is data of the publication, including its type. -/
structure Output (Γ : Context rules) where
  value : TotalTerm Γ
  expected : TypeOver Γ

namespace Output

variable {Γ Δ Θ : Context rules} (output : Output Γ)

def raw : DependentFull.Make Γ := ⟨output.expected, output.value.2.code⟩

def At (substitution : Δ ⟶ Γ) : Prop :=
  Below rules Δ.raw (output.value.1.reindex substitution).code
    (output.expected.reindex substitution).code

/-- A licensed value has its requested type and the source code after substitution. -/
def realize (substitution : Δ ⟶ Γ) (licensed : output.At substitution) :
    Term Δ (output.expected.reindex substitution) :=
  ⟨subst substitution.substitution output.value.2.code,
    Derivable.sub (output.value.2.typed.substitute substitution.typed) licensed⟩

theorem realize_code (substitution : Δ ⟶ Γ) (licensed : output.At substitution) :
    (output.realize substitution licensed).code = subst substitution.substitution output.value.2.code := rfl

theorem raw_typed (substitution : Δ ⟶ Γ) (licensed : output.At substitution) :
    (output.raw.reindex substitution).WellTyped := (output.realize substitution licensed).typed

def reindex (substitution : Δ ⟶ Γ) : Output Δ :=
  ⟨output.value.reindex substitution, output.expected.reindex substitution⟩

theorem reindex_id : output.reindex (𝟙 Γ) = output := by
  cases output with
  | mk value expected =>
      simp only [reindex, ContextualDependentEta.reindex_id, TypeOver.reindex_id]

theorem reindex_comp (first : Δ ⟶ Γ) (second : Θ ⟶ Δ) :
    (output.reindex first).reindex second = output.reindex (second ≫ first) := by
  cases output with
  | mk value expected =>
      simp only [reindex, ← ContextualDependentEta.reindex_comp, ← TypeOver.reindex_comp]

theorem at_reindex_iff (first : Δ ⟶ Γ) (second : Θ ⟶ Δ) :
    (output.reindex first).At second ↔ output.At (second ≫ first) := by
  unfold At reindex
  change Below rules Θ.raw ((output.value.1.reindex first).reindex second).code
      ((output.expected.reindex first).reindex second).code ↔ _
  rw [← TypeOver.reindex_comp, ← TypeOver.reindex_comp]

theorem At.precompose {substitution : Δ ⟶ Γ} (licensed : output.At substitution)
    (further : Θ ⟶ Δ) : output.At (further ≫ substitution) := by
  rw [← output.at_reindex_iff substitution further]
  exact NativeTypesOnTheStep.below_substitute licensed further.typed

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- The retained typing makes the license an agreement-invariant observation. -/
theorem at_agree {first second : Δ ⟶ Γ}
    (agree : UnificationWithLevels.Agree (frames levels) first second) :
    output.At first ↔ output.At second :=
  ⟨NativeTypesOnTheStep.below_of_agree levels agree.symm output.value.1 output.expected,
    NativeTypesOnTheStep.below_of_agree levels agree output.value.1 output.expected⟩

/-- Source meaning: the declared typing converts at every solution. -/
def Uniform (information : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ (Δ : Context rules) (substitution : Δ ⟶ Γ),
    (frames levels).Models substitution information → output.At substitution

theorem uniform_iff_at_principal {information : EquationStore (TotalTerm Γ)}
    {answer : Δ ⟶ Γ} (principal : (frames levels).Principal information answer) :
    output.Uniform levels information ↔ output.At answer := by
  constructor
  · intro licensed
    exact licensed Δ answer principal.sound
  · intro licensed target substitution solved
    have all := (NativeTypesOnTheStep.conversion_iff_of_principal levels principal
      output.raw output.value.1).mp licensed
    exact all (op target) solved

theorem uniform_types_every_solution {information : EquationStore (TotalTerm Γ)}
    (licensed : output.Uniform levels information) :
    NativeTypesOnTheStep.TypedAfterMatch levels information output.raw := by
  apply (NativeTypesOnTheStep.typedAfterMatch_iff levels information output.raw).mpr
  intro target substitution solved
  exact output.raw_typed substitution (licensed target substitution solved)

/-- A check using the retained annotation is independent of which principal
representative is supplied, even when the answer contexts differ. -/
theorem principal_choice_independent {information : EquationStore (TotalTerm Γ)}
    {first : Δ ⟶ Γ} {second : Θ ⟶ Γ}
    (firstPrincipal : (frames levels).Principal information first)
    (secondPrincipal : (frames levels).Principal information second) :
    output.At first ↔ output.At second :=
  (output.uniform_iff_at_principal levels firstPrincipal).symm.trans
    (output.uniform_iff_at_principal levels secondPrincipal)

/-- The requested typed values agree, while their raw substituted codes need
not be identical. The declared source value supplies the equality to transport. -/
theorem realized_values_agree {first second : Δ ⟶ Γ}
    (agree : UnificationWithLevels.Agree (frames levels) first second)
    (firstLicense : output.At first) (secondLicense : output.At second) :
    (frames levels).E
      (⟨output.expected.reindex first, output.realize first firstLicense⟩ : TotalTerm Δ)
      (⟨output.expected.reindex second, output.realize second secondLicense⟩ : TotalTerm Δ) := by
  refine ⟨NativeTypesOnTheStep.typeEq_of_agree levels agree output.expected, ?_⟩
  exact Derivable.subEq (agree output.value).2 firstLicense

/-- The source's own typing is an everywhere-licensed ordinary output. -/
def unchanged (value : TotalTerm Γ) : Output Γ := ⟨value, value.1⟩

theorem unchanged_uniform (value : TotalTerm Γ) (information : EquationStore (TotalTerm Γ)) :
    (unchanged value).Uniform levels information := by
  intro target substitution _
  exact NativeTypesOnTheStep.below_refl_of_isType (value.1.reindex substitution).isType

end Output

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Output.at_agree
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Output.uniform_iff_at_principal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Output.uniform_types_every_solution
