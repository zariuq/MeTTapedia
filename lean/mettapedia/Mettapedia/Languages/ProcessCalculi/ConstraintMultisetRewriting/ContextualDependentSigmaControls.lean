import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLiftingControls

/-!
# A computed dependent projection solution

Splitting p : Sigma X:U0. Id U0 X X exposes the first projection to the
actual flexible-variable solver. Its answer sets X to Ground and retains
the independently supplied proof, with its type rewritten accordingly.
The pair roundtrip is eta-equal, but not raw syntactic identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSigma.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentFlex

abbrev setting := Wakeup.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def shape : Shape (empty Tower.rules) where
  domain := Wakeup.universeType
  codomain := LiftingControls.laterType
  whole :=
    ⟨.sigma (.head (.sort Tower.zero)) (.id (.head (.sort Tower.zero)) (.var 0) (.var 0)),
      .sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sort _,
      .sigmaForm Wakeup.universeType.formed Wakeup.universeType.universeWitness
        LiftingControls.laterType.formed LiftingControls.laterType.universeWitness (.sorts _ _)⟩
  code := rfl

def packedFirst : TotalTerm shape.packed :=
  ⟨shape.domain.reindex (projectionHom _ shape.whole),
    shape.first (projectionHom _ shape.whole) (newest _ shape.whole)⟩
def packedGround : TotalTerm shape.packed :=
  ⟨shape.domain.reindex (projectionHom _ shape.whole), ⟨.head .legacyGround, .headType .legacyGround⟩⟩
def problem : EquationStore (TotalTerm shape.packed) := [(packedFirst, packedGround)]
def splitUpdate := shape.update setting.levels problem

def prefixUpdate := stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
  ConversionControls.reducer 16 Wakeup.unknownType Wakeup.ground []

def lifted := prefixUpdate.lift shape.codomain

def splitUnknown : TotalTerm shape.split :=
  TotalTerm.reindex (⟨Wakeup.viewedUniverse, Wakeup.unknownType⟩ : TotalTerm Wakeup.frame)
    (projectionHom _ shape.codomain)
def splitGround : TotalTerm shape.split :=
  TotalTerm.reindex (⟨Wakeup.viewedUniverse, Wakeup.ground⟩ : TotalTerm Wakeup.frame)
    (projectionHom _ shape.codomain)

theorem first_projection_computes :
    (frames setting.levels).E (packedFirst.reindex shape.pack) splitUnknown := by
  refine ⟨(shape.domain.reindex shape.splitBase).isType.refl, ?_⟩
  have equality := shape.first_beta shape.splitBase shape.splitFirst shape.splitSecond
  change Equal Tower.rules shape.split.raw (.fst (.pair shape.splitFirst.code shape.splitSecond.code))
    shape.splitFirst.code (.head (.sort Tower.zero)) at equality
  rw [shape.splitFirst_code, shape.splitSecond_code] at equality
  change Equal Tower.rules shape.split.raw (.fst (shape.pack.substitution 0)) (.var 1)
    (.head (.sort Tower.zero))
  rw [shape.pack_zero]
  exact equality

theorem ground_projection_stays : packedGround.reindex shape.pack = splitGround := by rfl'

theorem split_problem_equivalent :
    (frames setting.levels).Equivalent splitUpdate.remaining [(splitUnknown, splitGround)] := by
  intro Δ solution
  have firsts := (frames setting.levels).preserves solution first_projection_computes
  have grounds := congrArg (fun term => term.reindex solution) ground_projection_stays
  constructor
  · intro solved entry member
    obtain rfl := List.mem_singleton.mp member
    have equation := solved _ (List.mem_singleton_self _)
    change (frames setting.levels).E ((packedFirst.reindex shape.pack).reindex solution)
      ((packedGround.reindex shape.pack).reindex solution) at equation
    rw [grounds] at equation
    exact ((frames setting.levels).equivalence Δ).trans
      (((frames setting.levels).equivalence Δ).symm firsts) equation
  · intro solved entry member
    change entry ∈ [(packedFirst.reindex shape.pack, packedGround.reindex shape.pack)] at member
    obtain rfl := List.mem_singleton.mp member
    have equation := solved _ (List.mem_singleton_self _)
    change (frames setting.levels).E ((packedFirst.reindex shape.pack).reindex solution)
      ((packedGround.reindex shape.pack).reindex solution)
    rw [grounds]
    exact ((frames setting.levels).equivalence Δ).trans firsts equation

def solveSplit : Update setting.levels splitUpdate.remaining := lifted.rephrase split_problem_equivalent
def computed := splitUpdate.then solveSplit

theorem actual_projection_problem_finishes : computed.remaining = [] := by decide +kernel

theorem actual_projection_answer_principal :
    (frames setting.levels).Principal problem computed.answer :=
  computed.completed actual_projection_problem_finishes

theorem target_retains_dependent_proof :
    computed.target = extend (empty Tower.rules) LiftingControls.collapsedType := by rfl'

theorem answer_retains_proof_value :
    computed.answer.substitution 0 = .pair (.head .legacyGround)
      (.var ⟨0, by rw [target_retains_dependent_proof]; decide⟩) := by rfl'

theorem eta_roundtrip_not_raw_identity : shape.unpack ≫ shape.pack ≠ 𝟙 shape.packed := by
  intro same
  have codes := congrArg (fun morphism : shape.packed ⟶ shape.packed => morphism.substitution 0) same
  change subst shape.unpack.substitution (shape.pack.substitution 0) = .var 0 at codes
  rw [shape.pack_zero] at codes
  cases codes

theorem eta_roundtrip_is_typed_identity :
    homTypedEquality Tower.rules (𝟙 shape.packed) (shape.unpack ≫ shape.pack) := shape.packed_roundtrip

theorem dependency_cannot_be_erased :
    ¬ TypeEq Tower.rules shape.split.raw
      (.id (.head (.sort Tower.zero)) (.var 1) (.var 1))
      (.id (.head (.sort Tower.zero)) (.head .legacyGround) (.head .legacyGround)) := by
  intro same
  have endpoints := (TypeEq.id_injective TowerModel.facts same shape.split.formed).2.1
  have types : TypeEq Tower.rules shape.split.raw (.var 1) (.head .legacyGround) :=
    ⟨.sort Tower.zero, .sort _, endpoints⟩
  exact (TypeEq.neutral_form TowerModel.facts types shape.split.formed (.var 1)
    (.inl ⟨.legacyGround, rfl⟩)).not_former.1 .legacyGround rfl

theorem closed_solutions_preserved :
    (∃ solution : empty Tower.rules ⟶ shape.packed, (frames setting.levels).Models solution problem) ↔
      ∃ residual : empty Tower.rules ⟶ computed.target,
        (frames setting.levels).Models residual computed.remaining :=
  computed.fixed_point_solutions_iff (empty Tower.rules)

end ContextualDependentSigma.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
