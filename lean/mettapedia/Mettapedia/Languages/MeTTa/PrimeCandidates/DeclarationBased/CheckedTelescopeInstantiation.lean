import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeArgumentChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.Telescopes
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareStructuralTyping

/-!
# Checked evidence for actual dependent telescope instances

The argument-checking fold is instantiated with the existing canonical raw
proof checker, not an assumed typed substitution. Its accepted certificates
construct that substitution through the independently interpreted structural
typing rules. The actual dependent identity then checks and executes through
the established closed abstraction.

The primitive checker covers its advertised structural fragment only. Rejecting
a supplied certificate does not refute the typing proposition. The examples
retain concrete raw proofs; no choice operation manufactures compiler output.
These results do not verify the C rule loader or assert declaration formation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace CheckedTelescopeInstantiation

open Presentation
open Presentation.TelescopeAbstraction
open Presentation.TelescopeArgumentChecking
open Mettapedia.GSLT.LanguageDef.InferenceChecker

variable {n m : Nat}

/-- The supplied proof is checked against the computed dependent domain in
the actual target context. This Boolean concerns certificate acceptance. -/
def checkArgument (target : Tower.Ctx m) (argument domain : Tower.Tm m)
    (proof : RawProof) : Bool :=
  DeclarationAwareStructuralTyping.checkCanonicalRaw
    (DeclarationAwareStructuralTyping.claimPattern target argument domain) proof

/-- Static reflection uses the same raw tree and independently authored rule
semantics. It does not create a runtime proof from mere existence. -/
theorem checkArgument_reflects {target : Tower.Ctx m}
    {argument domain : Tower.Tm m} {proof : RawProof}
    (accepted : checkArgument target argument domain proof = true) :
    Nonempty (DeclarationAwareStructuralTyping.StructuralTyping target argument domain) := by
  obtain ⟨derivation, _erases⟩ :=
    Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw_sound accepted
  exact ⟨DeclarationAwareStructuralTyping.structuralSemantics.interpret
    derivation.toDerivation
    { arity := m, context := target, subject := argument, type := domain } rfl⟩

theorem checkArgument_sound (target : Tower.Ctx m)
    (argument domain : Tower.Tm m) (proof : RawProof)
    (accepted : checkArgument target argument domain proof = true) :
    Tower.HasType target argument domain := by
  obtain ⟨evidence⟩ := checkArgument_reflects accepted
  exact evidence.toHasType

/-- An inspectable structural proof for each actual argument compiles to raw
certificates accepted at the same dependent domains. This covers arbitrary
telescopes and assignments within the primitive checker's supported fragment. -/
theorem structural_arguments_compile
    (context : Tower.Ctx n) (target : Tower.Ctx m) (sigma : Sub Tower.Head n m)
    (proofs : ∀ index,
      DeclarationAwareStructuralTyping.StructuralTyping target (sigma index)
        (subst sigma (Ctx.lookup context index))) :
    checkArguments (checkArgument target) context sigma
      (fun index => (proofs index).raw) = true := by
  apply (checkArguments_eq_true_iff _ _ _ _).2
  intro index
  exact (proofs index).canonicalTreeRaw_accepted

/-- Native variable indices are newest-first; application order is oldest-first. -/
def assignment (level : LevelExpr Nat) : Sub Tower.Head 2 0 :=
  consSub (sortTm level)
    (consSub (sortTm (.succ level)) (renSub Fin.elim0))

/-- Concrete proof syntax for both actual arguments. -/
def certificates (level : LevelExpr Nat) : Fin 2 → RawProof :=
  Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil level)
    (Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil (.succ level)) Fin.elim0)

/-- The second domain is the value of the first argument, not its universe. -/
theorem arguments_accepted (level : LevelExpr Nat) :
    checkArguments (checkArgument .nil)
      (identityContext (.succ (.succ level)))
      (assignment level) (certificates level) = true := by
  have older : checkArgument .nil (sortTm (.succ level))
      (sortTm (.succ (.succ level)))
      (DeclarationAwareStructuralTyping.sortRaw .nil (.succ level)) = true :=
    (DeclarationAwareStructuralTyping.StructuralTyping.sort .nil (.succ level)).canonicalTreeRaw_accepted
  have newest : checkArgument .nil (sortTm level) (sortTm (.succ level))
      (DeclarationAwareStructuralTyping.sortRaw .nil level) = true :=
    (DeclarationAwareStructuralTyping.StructuralTyping.sort .nil level).canonicalTreeRaw_accepted
  change ((true && checkArgument .nil (sortTm (.succ level))
      (sortTm (.succ (.succ level)))
      (DeclarationAwareStructuralTyping.sortRaw .nil (.succ level))) &&
    checkArgument .nil (sortTm level) (sortTm (.succ level))
      (DeclarationAwareStructuralTyping.sortRaw .nil level)) = true
  simp only [older, newest, Bool.and_self]

/-- This typed substitution is earned by the executable evidence fold. -/
theorem assignment_typed (level : LevelExpr Nat) :
    Presentation.CtxMor Tower.rules
      (identityContext (.succ (.succ level))) .nil (assignment level) :=
  checkArguments_sound (checkArgument .nil) (checkArgument_sound .nil)
    (arguments_accepted level)

/-- One accepted argument sequence supplies typing, its actual result, and
the directed beta execution of the same dependent program. -/
theorem identity_application_checked (level : LevelExpr Nat) :
    Tower.HasType .nil
      (.app (.app (identityTerm (.succ (.succ level))) (sortTm (.succ level)))
        (sortTm level)) (sortTm (.succ level)) ∧
      Tower.HasType .nil (sortTm level) (sortTm (.succ level)) ∧
      BetaSteps
        (.app (.app (identityTerm (.succ (.succ level))) (sortTm (.succ level)))
          (sortTm level)) (sortTm level) := by
  have bodyTyped : Tower.HasType (identityContext (.succ (.succ level)))
      (.var 0) (.var 1) := by
    exact .var 0
  convert (checked_application_beta (checkArgument .nil) (checkArgument_sound .nil)
    bodyTyped (arguments_accepted level)) using 1 <;> rfl

private def zero : LevelExpr Nat := .const 0
private def one : LevelExpr Nat := .succ zero
private def two : LevelExpr Nat := .succ one

/-- A valid sort proof at U2 cannot certify that U1 inhabits itself. -/
theorem universe_self_certificate_rejected (proof : RawProof) :
    checkArgument .nil (sortTm one) (sortTm one) proof = false := by
  cases result : checkArgument .nil (sortTm one) (sortTm one) proof with
  | false => rfl
  | true =>
      obtain ⟨evidence⟩ := checkArgument_reflects result
      cases evidence

def wrongAssignment : Sub Tower.Head 2 0 :=
  consSub (sortTm one) (consSub (sortTm one) (renSub Fin.elim0))

/-- Scope-correct raw arguments still cannot pass without dependent typing.
This rejection holds for every attempted pair of structural certificates. -/
theorem wrong_arguments_rejected (proofs : Fin 2 → RawProof) :
    checkArguments (checkArgument .nil) (identityContext two)
      wrongAssignment proofs = false := by
  change ((true && checkArgument .nil (sortTm one) (sortTm two) (proofs 1)) &&
    checkArgument .nil (sortTm one) (sortTm one) (proofs 0)) = false
  simp only [universe_self_certificate_rejected, Bool.and_false]

/-- Invalid evidence for an otherwise inhabited typing claim is not accepted. -/
def wrongCertificates : Fin 2 → RawProof :=
  Fin.cases (DeclarationAwareStructuralTyping.legacyGroundRaw .nil)
    (Fin.cases (DeclarationAwareStructuralTyping.sortRaw .nil one) Fin.elim0)

theorem invalid_evidence_rejected :
    checkArguments (checkArgument .nil) (identityContext two)
      (assignment zero) wrongCertificates = false := by
  decide +kernel

theorem rejected_evidence_does_not_refute_typing :
    Tower.HasType .nil (sortTm zero) (sortTm one) :=
  .headType (.sort zero)

#print axioms checkArgument_reflects
#print axioms checkArgument_sound
#print axioms structural_arguments_compile
#print axioms arguments_accepted
#print axioms assignment_typed
#print axioms identity_application_checked
#print axioms universe_self_certificate_rejected
#print axioms wrong_arguments_rejected
#print axioms invalid_evidence_rejected
#print axioms rejected_evidence_does_not_refute_typing

end CheckedTelescopeInstantiation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
