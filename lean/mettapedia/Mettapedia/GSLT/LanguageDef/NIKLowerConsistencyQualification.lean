import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.OSLF.Framework.InitialityConsistencySeparation

/-!
# Model qualification implies lower-level consistency

NIK distinguishes the claim that an authored calculus has a sound model from
the claim that the calculus is syntactically consistent.  This module gives
those two claims an explicit semantics for OSLF rule systems and proves the
one-way consequence between them.

The checker for derivations remains profile-blind.  A model qualification is
additional semantic evidence: every authored rule preserves an independently
supplied meaning predicate, and that predicate rejects bottom.  Such evidence
implies consistency at the same strictly lower target level.  Exact replay
alone does not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKLowerConsistencyQualification

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.Logic
open Mettapedia.OSLF.Framework.InitialityConsistencySeparation

abbrev RuleSystem : Type :=
  List OSLFFormula → OSLFFormula → Prop

/-- Every bootstrap level discusses OSLF rule systems.  The level index says
which authority is the subject; it does not alter the rule carrier. -/
def Statement : Nat → Type := fun _targetLevel => RuleSystem

/-- A lower-level assertion that an independently supplied interpretation
validates every rule and rejects bottom. -/
def modelSoundClaim {hostLevel : Nat} (targetLevel : Fin hostLevel)
    (rules : RuleSystem) : LowerContract Statement hostLevel where
  targetLevel := targetLevel
  kind := .modelSound
  statement := rules

/-- A lower-level assertion that bottom is not derivable from the authored
rules. -/
def lowerConsistencyClaim {hostLevel : Nat} (targetLevel : Fin hostLevel)
    (rules : RuleSystem) : LowerContract Statement hostLevel where
  targetLevel := targetLevel
  kind := .lowerConsistency
  statement := rules

/-- Independent semantics for the two selected bootstrap contract kinds.
Unsupported kinds have no meaning in this profile. -/
def Meaning {hostLevel : Nat}
    (claim : LowerContract Statement hostLevel) : Prop :=
  match claim.kind with
  | .modelSound => Nonempty (ModelQualification claim.statement)
  | .lowerConsistency => Consistent claim.statement
  | _ => False

@[simp] theorem modelSoundClaim_kind {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (rules : RuleSystem) :
    (modelSoundClaim targetLevel rules).kind = .modelSound :=
  rfl

@[simp] theorem lowerConsistencyClaim_kind {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (rules : RuleSystem) :
    (lowerConsistencyClaim targetLevel rules).kind = .lowerConsistency :=
  rfl

@[simp] theorem modelSoundClaim_meaning_iff {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (rules : RuleSystem) :
    Meaning (modelSoundClaim targetLevel rules) ↔
      Nonempty (ModelQualification rules) :=
  Iff.rfl

@[simp] theorem lowerConsistencyClaim_meaning_iff {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (rules : RuleSystem) :
    Meaning (lowerConsistencyClaim targetLevel rules) ↔ Consistent rules :=
  Iff.rfl

/-- Model soundness at a strictly lower target yields consistency at that same
target.  The theorem changes only the contract kind; it neither changes the
target level nor asks the replay checker to inspect a semantic model. -/
theorem modelSound_entails_lowerConsistency {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (rules : RuleSystem)
    (modelSound : Meaning (modelSoundClaim targetLevel rules)) :
    Meaning (lowerConsistencyClaim targetLevel rules) := by
  obtain ⟨qualification⟩ := modelSound
  exact qualification.consistent

/-- Both related contracts retain the same strictly lower subject. -/
theorem consequence_preserves_target {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (rules : RuleSystem) :
    (modelSoundClaim targetLevel rules).targetLevel =
      (lowerConsistencyClaim targetLevel rules).targetLevel :=
  rfl

/-! ## Positive and adversarial controls -/

/-- The empty calculus has genuine model-soundness evidence. -/
theorem emptyRules_modelSound {hostLevel : Nat}
    (targetLevel : Fin hostLevel) :
    Meaning (modelSoundClaim targetLevel emptyRules) :=
  ⟨emptyRulesQualification⟩

/-- The consequence theorem derives the corresponding lower-consistency
claim for the empty calculus. -/
theorem emptyRules_lowerConsistency {hostLevel : Nat}
    (targetLevel : Fin hostLevel) :
    Meaning (lowerConsistencyClaim targetLevel emptyRules) :=
  modelSound_entails_lowerConsistency targetLevel emptyRules
    (emptyRules_modelSound targetLevel)

/-- The direct-bottom calculus has no model-soundness meaning. -/
theorem bottomRules_not_modelSound {hostLevel : Nat}
    (targetLevel : Fin hostLevel) :
    ¬ Meaning (modelSoundClaim targetLevel bottomRules) :=
  bottomRules_has_no_modelQualification

/-- The direct-bottom calculus also fails the lower-consistency claim. -/
theorem bottomRules_not_lowerConsistent {hostLevel : Nat}
    (targetLevel : Fin hostLevel) :
    ¬ Meaning (lowerConsistencyClaim targetLevel bottomRules) :=
  bottomRules_inconsistent

/-- Adversarial control: an exact derivation checker can coexist with failure
of the corresponding lower-consistency claim. -/
theorem exact_replay_does_not_supply_lowerConsistency {hostLevel : Nat}
    (targetLevel : Fin hostLevel) :
    bottomChecker.Authority (Derives bottomRules) ∧
      ¬ Meaning (lowerConsistencyClaim targetLevel bottomRules) :=
  ⟨bottomChecker_exact, bottomRules_not_lowerConsistent targetLevel⟩

#print axioms modelSound_entails_lowerConsistency
#print axioms consequence_preserves_target
#print axioms emptyRules_modelSound
#print axioms emptyRules_lowerConsistency
#print axioms bottomRules_not_modelSound
#print axioms bottomRules_not_lowerConsistent
#print axioms exact_replay_does_not_supply_lowerConsistency

end Mettapedia.GSLT.LanguageDef.NIKLowerConsistencyQualification
