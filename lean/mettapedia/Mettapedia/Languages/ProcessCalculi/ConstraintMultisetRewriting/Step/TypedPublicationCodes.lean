import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOutputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateConversion

/-!
# Source output code with retained typing evidence

A value output retains its whole declared typing. A template output retains
the existing typed template and its variable-filling checks, so applications
whose function types are learned by matching are expressible too. An explicit
environment preserves the template's original scope under later refinement.
The two source forms are data; no existential retyping of erased code occurs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}

inductive Code (context : Context rules) : Type where
  | value (output : Output context)
  | template (origin : Context rules) (row : Make origin)
      (typing : NativeTypesOnTheStep.Template row) (environment : context ⟶ origin)

instance {context : Context rules} : Coe (Output context) (Code context) := ⟨Code.value⟩

namespace Code

variable {Γ Δ Θ : Context rules}

def raw : Code Γ → Make Γ
  | .value output => output.raw
  | .template _ row _ environment => row.reindex environment

def At : Code Γ → (Δ ⟶ Γ) → Prop
  | .value output, substitution => output.At substitution
  | .template _ _ typing environment, substitution => typing.Holds (substitution ≫ environment)

def reindex : Code Γ → (Δ ⟶ Γ) → Code Δ
  | .value output, substitution => .value (output.reindex substitution)
  | .template origin row typing environment, substitution =>
      .template origin row typing (substitution ≫ environment)

theorem reindex_id (code : Code Γ) : code.reindex (𝟙 Γ) = code := by
  cases code with
  | value output => simp only [reindex, Output.reindex_id]
  | template origin row typing environment => simp only [reindex, Category.id_comp]

theorem reindex_comp (code : Code Γ) (first : Δ ⟶ Γ) (second : Θ ⟶ Δ) :
    (code.reindex first).reindex second = code.reindex (second ≫ first) := by
  cases code with
  | value output => simp only [reindex, Output.reindex_comp]
  | template origin row typing environment => simp only [reindex, Category.assoc]

theorem make_reindex_comp (row : Make Γ) (first : Δ ⟶ Γ) (second : Θ ⟶ Δ) :
    (row.reindex first).reindex second = row.reindex (second ≫ first) :=
  NativeTypesOnTheStep.make_ext (row.type.reindex_comp second first).symm
    (subst_subComp second.substitution first.substitution row.code)

theorem reindex_raw (code : Code Γ) (substitution : Δ ⟶ Γ) :
    (code.reindex substitution).raw = code.raw.reindex substitution := by
  cases code with
  | value output => rfl
  | template origin row typing environment => exact (make_reindex_comp row environment substitution).symm

theorem at_reindex_iff (code : Code Γ) (first : Δ ⟶ Γ) (second : Θ ⟶ Δ) :
    (code.reindex first).At second ↔ code.At (second ≫ first) := by
  cases code with
  | value output => exact output.at_reindex_iff first second
  | template origin row typing environment =>
      change typing.Holds (second ≫ (first ≫ environment)) ↔ typing.Holds ((second ≫ first) ≫ environment)
      rw [Category.assoc]

theorem at_precompose (code : Code Γ) {first : Δ ⟶ Γ} (licensed : code.At first)
    (second : Θ ⟶ Δ) : code.At (second ≫ first) := by
  cases code with
  | value output => exact Output.At.precompose output licensed second
  | template origin row typing environment =>
      simpa only [At, Category.assoc] using typing.holds_comp licensed second

theorem raw_typed (code : Code Γ) (substitution : Δ ⟶ Γ) (licensed : code.At substitution) :
    (code.raw.reindex substitution).WellTyped := by
  cases code with
  | value output => exact output.raw_typed substitution licensed
  | template origin row typing environment =>
      change ((row.reindex environment).reindex substitution).WellTyped
      rw [make_reindex_comp]
      exact typing.typed_of_holds licensed

def realize (code : Code Γ) (substitution : Δ ⟶ Γ) (licensed : code.At substitution) :
    Term Δ (code.raw.type.reindex substitution) :=
  ⟨subst substitution.substitution code.raw.code, code.raw_typed substitution licensed⟩

def readout (code : Code Γ) (substitution : Δ ⟶ Γ) (licensed : code.At substitution) : TotalTerm Δ :=
  ⟨code.raw.type.reindex substitution, code.realize substitution licensed⟩

theorem readout_precompose (code : Code Γ) (first : Δ ⟶ Γ) (second : Θ ⟶ Δ)
    (licensed : code.At first) :
    (code.readout first licensed).reindex second =
      code.readout (second ≫ first) (code.at_precompose licensed second) :=
  totalTerm_ext (code.raw.type.reindex_comp second first).symm
    (subst_subComp second.substitution first.substitution code.raw.code)

theorem readout_reindex (code : Code Γ) (first : Δ ⟶ Γ) (second : Θ ⟶ Δ)
    (licensed : (code.reindex first).At second) :
    (code.reindex first).readout second licensed =
      code.readout (second ≫ first) ((code.at_reindex_iff first second).mp licensed) := by
  apply totalTerm_ext
  · change ((code.reindex first).raw.type.reindex second) = code.raw.type.reindex (second ≫ first)
    rw [code.reindex_raw]
    exact (code.raw.type.reindex_comp second first).symm
  · change subst second.substitution (code.reindex first).raw.code =
      subst (second ≫ first).substitution code.raw.code
    rw [code.reindex_raw]
    exact subst_subComp second.substitution first.substitution code.raw.code

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

theorem agreement_environment {origin : Context rules} {first second : Δ ⟶ Γ}
    (agree : UnificationWithLevels.Agree (frames levels) first second) (environment : Γ ⟶ origin) :
    UnificationWithLevels.Agree (frames levels) (first ≫ environment) (second ≫ environment) := by
  intro term
  change (frames levels).E (term.reindex (first ≫ environment)) (term.reindex (second ≫ environment))
  rw [ContextualDependentEta.reindex_comp, ContextualDependentEta.reindex_comp]
  exact agree (term.reindex environment)

theorem at_agree (code : Code Γ) {first second : Δ ⟶ Γ}
    (agree : UnificationWithLevels.Agree (frames levels) first second) : code.At first ↔ code.At second := by
  cases code with
  | value output => exact output.at_agree levels agree
  | template origin row typing environment =>
      have transported := agreement_environment levels agree environment
      exact ⟨typing.holds_of_agree levels transported.symm, typing.holds_of_agree levels transported⟩

def Uniform (code : Code Γ) (information : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ (context : Context rules) (substitution : context ⟶ Γ),
    (frames levels).Models substitution information → code.At substitution

theorem uniform_iff_at_principal (code : Code Γ) {information : EquationStore (TotalTerm Γ)}
    {answer : Δ ⟶ Γ} (principal : (frames levels).Principal information answer) :
    code.Uniform levels information ↔ code.At answer :=
  principal.entails_iff (fun _ _ _ agree => code.at_agree levels agree)
    (fun _ further licensed => code.at_precompose licensed further)

theorem uniform_types_every_solution (code : Code Γ) {information : EquationStore (TotalTerm Γ)}
    (licensed : code.Uniform levels information) : NativeTypesOnTheStep.TypedAfterMatch levels information code.raw := by
  apply (NativeTypesOnTheStep.typedAfterMatch_iff levels information code.raw).mpr
  intro context substitution solved
  exact code.raw_typed substitution (licensed context substitution solved)

theorem principal_choice_independent (code : Code Γ) {information : EquationStore (TotalTerm Γ)}
    {first : Δ ⟶ Γ} {second : Θ ⟶ Γ}
    (firstPrincipal : (frames levels).Principal information first)
    (secondPrincipal : (frames levels).Principal information second) :
    code.At first ↔ code.At second :=
  (code.uniform_iff_at_principal levels firstPrincipal).symm.trans
    (code.uniform_iff_at_principal levels secondPrincipal)

omit [UniverseLevel.LevelOrder L] in
theorem template_readout {origin : Context rules} (row : Make origin)
    (typing : NativeTypesOnTheStep.Template row) (environment : Γ ⟶ origin)
    (substitution : Δ ⟶ Γ) (licensed : (Code.template origin row typing environment).At substitution) :
    (Code.template origin row typing environment).readout substitution licensed =
      (row.reindex (substitution ≫ environment)).row (typing.typed_of_holds licensed) :=
  totalTerm_ext (row.type.reindex_comp substitution environment).symm
    (subst_subComp substitution.substitution environment.substitution row.code)

theorem readout_agree (code : Code Γ) {first second : Δ ⟶ Γ}
    (agree : UnificationWithLevels.Agree (frames levels) first second)
    (firstLicense : code.At first) (secondLicense : code.At second) :
    (frames levels).E (code.readout first firstLicense) (code.readout second secondLicense) := by
  cases code with
  | value output => exact output.realized_values_agree levels agree firstLicense secondLicense
  | template origin row typing environment =>
      rw [template_readout, template_readout]
      have transported := agreement_environment levels agree environment
      have substitutionsAgree : SubstEq rules typing.frame.raw Δ.raw
          (typing.along (first ≫ environment)) (typing.along (second ≫ environment)) := by
        refine ⟨typing.substMor firstLicense, fun index => ?_⟩
        obtain ⟨level, universeWitness, formed⟩ := origin.formed.lookup (typing.fill index)
        let value : TotalTerm origin :=
          ⟨⟨Ctx.lookup origin.raw (typing.fill index), level, universeWitness, formed⟩,
            ⟨.var (typing.fill index), Derivable.var _⟩⟩
        exact Derivable.subEq (transported value).2 (firstLicense.1 index)
      refine ⟨NativeTypesOnTheStep.typeEq_of_agree levels transported row.type, ?_⟩
      change Equal rules Δ.raw (subst (first ≫ environment).substitution row.code)
        (subst (second ≫ environment).substitution row.code) (row.type.reindex (first ≫ environment)).code
      rw [typing.filled, subst_rename, subst_rename]
      exact Derivable.subEq (typing.typed.functional substitutionsAgree) firstLicense.2

end Code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Code.uniform_iff_at_principal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Code.uniform_types_every_solution
