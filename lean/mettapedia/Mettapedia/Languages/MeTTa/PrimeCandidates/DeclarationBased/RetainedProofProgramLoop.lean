import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.GSLTFormationCheckedTelescopePrograms

/-!
# A dependent proof-return program with retained checking evidence

The four parameters are a type, two values, and evidence of their native
identity. The source term returns that evidence. General formed-telescope
laws supply its typing, actual beta execution, and certificate re-entry.

The positive instance uses concrete raw proof trees for actual universes and
reflexivity, not proof existence or an independently manufactured conclusion.
The negative controls reject invalid evidence and exhibit a regular universe
policy under which a formed open judgment cannot acquire its closed product.
Neither counterexample changes the installed cumulative rules.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace RetainedProofProgramLoop

open Presentation
open Presentation.FormationSensitive
open Presentation.TelescopeAbstraction
open Presentation.TelescopeArgumentChecking
open Presentation.FormationCheckedTelescopePrograms
open CheckedTelescopeInstantiation
open Mettapedia.GSLT.LanguageDef.InferenceChecker

def zero : LevelExpr Nat := .const 0
def one : LevelExpr Nat := .succ zero
def two : LevelExpr Nat := .succ one

/-- Oldest-first: A : U, x : A, y : A, e : Id A x y. -/
def proofContext (level : LevelExpr Nat) : Tower.Ctx 4 :=
  .snoc (.snoc (identityContext level) (.var 1))
    (.id (.var 2) (.var 1) (.var 0))

/-- The program is a genuine four-binder lambda abstraction. -/
def proofProgram (level : LevelExpr Nat) : Tower.Tm 0 :=
  closeTerm (proofContext level) (.var 0)

theorem proof_context_formed (level : LevelExpr Nat) :
    ContextFormation Tower.rules (proofContext level) := by
  have contextPrefix : ContextFormation Tower.rules (identityContext level) :=
    .snoc (.snoc .nil (.headType (.sort level)) (.sort (.succ level)))
      (.var 0) (.sort level)
  have withY : ContextFormation Tower.rules
      (.snoc (identityContext level) (.var 1)) :=
    .snoc contextPrefix (.var 1) (.sort level)
  exact .snoc withY (.idForm (.var 2) (.sort level) (.var 1) (.var 0)) (.sort level)

def proofAssignment : Sub Tower.Head 4 0 :=
  consSub (.refl (sortTm zero)) (consSub (sortTm zero) (assignment zero))

def proofCertificates : Fin 4 → RawProof :=
  Fin.cases
    (DeclarationAwareStructuralTyping.reflRaw .nil (sortTm zero) (sortTm one)
      (DeclarationAwareStructuralTyping.sortRaw .nil zero))
    (Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil zero) (certificates zero))

theorem proof_arguments_accepted :
    checkArguments (checkArgument .nil) (proofContext two)
      proofAssignment proofCertificates = true := by
  have earlier : checkArguments (checkArgument .nil) (identityContext two)
      (assignment zero) (certificates zero) = true := arguments_accepted zero
  have withY : checkArguments (checkArgument .nil)
      (.snoc (identityContext two) (.var 1))
      (consSub (sortTm zero) (assignment zero))
      (Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil zero) (certificates zero))
        = true := by
    rw [checkArguments_cons]
    have newest : checkArgument .nil (sortTm zero)
        (subst (assignment zero) (.var 1))
        (DeclarationAwareStructuralTyping.sortRaw .nil zero) = true := by
      convert (DeclarationAwareStructuralTyping.StructuralTyping.sort .nil zero).canonicalTreeRaw_accepted
        using 1
      rfl
    simp only [earlier, newest, Bool.and_true]
  unfold proofContext proofAssignment proofCertificates
  rw [checkArguments_cons]
  have newest : checkArgument .nil (.refl (sortTm zero))
      (subst (consSub (sortTm zero) (assignment zero))
        (.id (.var 2) (.var 1) (.var 0)))
      (DeclarationAwareStructuralTyping.reflRaw .nil (sortTm zero) (sortTm one)
        (DeclarationAwareStructuralTyping.sortRaw .nil zero)) = true := by
    convert (DeclarationAwareStructuralTyping.StructuralTyping.reflIntro
      (DeclarationAwareStructuralTyping.StructuralTyping.sort .nil zero)).canonicalTreeRaw_accepted
      using 1
    rfl
  simp only [withY, newest, Bool.and_true]

def returnedType : Tower.Tm 0 := .id (sortTm one) (sortTm zero) (sortTm zero)

def appliedProgram : Tower.Tm 0 :=
  applyClosed (proofContext two) proofAssignment (liftClosed (proofProgram two))

def relayedProgram : Tower.Tm 0 :=
  applyClosed (proofContext two)
    (consSub appliedProgram (consSub (sortTm zero) (assignment zero)))
    (liftClosed (proofProgram two))

/-- One retained proof tree certifies the value before and after the actual
program execution. This is a formed judgment, not raw subject typing alone. -/
theorem proof_return_loop :
    Judgment Tower.rules .nil appliedProgram returnedType ∧
      Judgment Tower.rules .nil (.refl (sortTm zero)) returnedType ∧
      BetaSteps appliedProgram (.refl (sortTm zero)) ∧
      checkArgument .nil (.refl (sortTm zero)) returnedType (proofCertificates 0) = true := by
  convert (checked_projection_loop towerUniverseRegularity tower_joins
    (proof_context_formed two) (.nil : ContextFormation Tower.rules .nil)
    (checkArgument .nil) (checkArgument_regular .nil) proof_arguments_accepted (0 : Fin 4))
      using 1 <;> rfl

/-- The returned proof is consumed by a second actual dependent invocation;
the directed paths compose and the original output certificate still checks. -/
theorem proof_relay_loop :
    Judgment Tower.rules .nil relayedProgram returnedType ∧
      BetaSteps relayedProgram (.refl (sortTm zero)) ∧
      checkArgument .nil (.refl (sortTm zero)) returnedType (proofCertificates 0) = true := by
  convert (checked_return_then_consume towerUniverseRegularity tower_joins
    (proof_context_formed two) (.nil : ContextFormation Tower.rules .nil)
    (checkArgument .nil) (checkArgument_regular .nil) proof_arguments_accepted)
      using 1 <;> rfl

def invalidCertificates : Fin 4 → RawProof :=
  Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil zero)
    (Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil zero) (certificates zero))

/-- A proof of U0 : U1 is not a proof of Refl U0 : Id U1 U0 U0. -/
theorem invalid_return_certificate_rejected :
    checkArguments (checkArgument .nil) (proofContext two)
      proofAssignment invalidCertificates = false := by
  decide +kernel

/-- The rejected certificate does not refute the returned proposition or
the typing of its actual native reflexivity witness. -/
theorem returned_witness_formed :
    Judgment Tower.rules .nil (.refl (sortTm zero)) returnedType :=
  proof_return_loop.2.1

/-! ## Universe joins are needed, even with regularity and formed contexts -/

def noJoinRules : Rules Tower.Head :=
  { Tower.rules with join := fun _ _ _ => False }

theorem noJoin_regular : UniverseRegularity noJoinRules where
  head_target := towerUniverseRegularity.head_target
  join_target := by
    intro u v w impossible
    exact False.elim impossible
  cumulative_target := towerUniverseRegularity.cumulative_target
  universe_typed := towerUniverseRegularity.universe_typed

def noJoinContext : Tower.Ctx 1 := .snoc .nil (sortTm zero)

theorem noJoin_open_formed :
    Judgment noJoinRules noJoinContext (.var 0) (sortTm zero) :=
  ⟨.snoc .nil (.headType (.sort zero)) (.sort one), .var 0⟩

/-- Thus regularity and source formation cannot replace the join capability
used by the general abstraction theorem. -/
theorem noJoin_closed_type_unformed (type : Tower.Tm 0) :
    ¬ Typing noJoinRules .nil (closeType noJoinContext (sortTm zero)) type := by
  intro formed
  obtain ⟨_, _, _, _, _, _, _, impossible⟩ := formed.piFormation
  exact impossible

#print axioms proof_context_formed
#print axioms proof_arguments_accepted
#print axioms proof_return_loop
#print axioms proof_relay_loop
#print axioms invalid_return_certificate_rejected
#print axioms returned_witness_formed
#print axioms noJoin_regular
#print axioms noJoin_open_formed
#print axioms noJoin_closed_type_unformed

end RetainedProofProgramLoop
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
