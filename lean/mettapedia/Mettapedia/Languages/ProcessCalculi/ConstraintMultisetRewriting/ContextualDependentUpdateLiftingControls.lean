import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexWakeup
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInversion

/-!
# Solving an older type variable beneath a dependent proof declaration

The computed X := Ground update is lifted beneath p : Id U0 X X. Its target
retains p, now typed at Id U0 Ground Ground. A separate equation on p remains
residual, and a second computed rule solves it. The composed update is
principal for the original three-equation problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUpdate.LiftingControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentFlex

abbrev setting := Wakeup.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def laterType : TypeOver Wakeup.frame :=
  ⟨.id (.head (.sort Tower.zero)) (.var 0) (.var 0),
    .sort (.succ Tower.zero), .sort _,
    .idForm (.headType (.sort _)) (.sort _) (.var 0) (.var 0)⟩

abbrev sourceFrame := extend Wakeup.frame laterType
def lifted := Wakeup.computed.lift laterType

def collapsedType : TypeOver (empty Tower.rules) :=
  ⟨.id (.head (.sort Tower.zero)) (.head .legacyGround) (.head .legacyGround),
    .sort (.succ Tower.zero), .sort _,
    .idForm (.headType (.sort _)) (.sort _) (.headType .legacyGround) (.headType .legacyGround)⟩

theorem dependent_type_rewritten : lifted.target = extend (empty Tower.rules) collapsedType := by rfl'

theorem later_value_not_chosen :
    lifted.answer.substitution 0 = .var (0 : Fin (Wakeup.computed.target.arity + 1)) :=
  Wakeup.computed.lift_answer_newest laterType

theorem lifted_prefix_finishes : lifted.remaining = [] := by decide +kernel

theorem lifted_prefix_principal :
    (frames setting.levels).Principal
      ((frames setting.levels).applyStore (projectionHom Wakeup.frame laterType)
        (equation Wakeup.unknownType Wakeup.ground :: [Wakeup.pending])) lifted.answer :=
  lifted.completed lifted_prefix_finishes

/-- The original annotation cannot be copied into an empty prefix. Its
dependence on X must actually be substituted. -/
theorem original_type_has_no_closed_raw_preimage :
    ¬ ∃ type : Tower.Tm 0, rename (Fin.elim0 : Ren 0 1) type = laterType.code := by
  apply (ContextualDependentInversion.invert_eq_none_iff Fin.elim0
    (ContextualDependentInversion.lookup (Fin.elim0 : Ren 0 1))
    (ContextualDependentInversion.lookup_exact Fin.elim0 (fun index => index.elim0)) laterType.code).mp
  decide +kernel

def laterValue : Term sourceFrame (laterType.reindex (projectionHom Wakeup.frame laterType)) :=
  newest Wakeup.frame laterType

def fixedProofType : TypeOver sourceFrame := collapsedType.reindex (toEmpty sourceFrame)
def fixedProof : Term sourceFrame fixedProofType :=
  ⟨.refl (.head .legacyGround), .reflIntro (.headType .legacyGround)⟩

def extra : Equation (TotalTerm sourceFrame) := (⟨_, laterValue⟩, ⟨_, fixedProof⟩)
def first := lifted.keepLeft [extra]

theorem later_equation_remains : first.remaining.length = 1 := by decide +kernel

def laterTypeAfter : TypeOver Wakeup.computed.target := laterType.reindex Wakeup.computed.answer
def readyLeft : Term first.target (laterTypeAfter.reindex (projectionHom _ laterTypeAfter)) :=
  newest _ laterTypeAfter

theorem ready_type_code : (laterTypeAfter.reindex (projectionHom _ laterTypeAfter)).code =
    .id (.head (.sort Tower.zero)) (.head .legacyGround) (.head .legacyGround) := by rfl'

set_option backward.isDefEq.respectTransparency false in
def readyRight : Term first.target (laterTypeAfter.reindex (projectionHom _ laterTypeAfter)) := by
  refine ⟨.refl (.head .legacyGround), ?_⟩
  rw [ready_type_code]
  exact Derivable.reflIntro (R := Tower.rules) (Derivable.headType LevelTower.HeadTyping.legacyGround)

theorem residual_is_ready : first.remaining = [equation readyLeft readyRight] := by rfl'

def second : Update setting.levels first.remaining :=
  (stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer 16 readyLeft readyRight []).rephrase (by
      intro Δ solution
      rw [residual_is_ready])

def combined := first.then second

theorem both_assignments_finish : combined.remaining = [] := by decide +kernel

theorem computed_dependent_chain_principal :
    (frames setting.levels).Principal
      (extra :: (frames setting.levels).applyStore (projectionHom Wakeup.frame laterType)
        (equation Wakeup.unknownType Wakeup.ground :: [Wakeup.pending])) combined.answer :=
  combined.completed both_assignments_finish

end ContextualDependentUpdate.LiftingControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
