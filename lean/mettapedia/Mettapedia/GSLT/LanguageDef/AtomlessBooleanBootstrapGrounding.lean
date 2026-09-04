import Mettapedia.GSLT.LanguageDef.AtomlessBooleanMSOSemanticBridge

/-!
# A non-vacuous atomless semantic ground for selected lower contracts

A direct semantic decision procedure becomes a bootstrap authority only after
an explicit encoding says what lower-level contracts mean in its claim
language.  This file makes that extra edge proof-relevant and uses the
atomless Boolean first-order decision procedure to ground exactly one NIK
contract kind: `modelSound`.

The resulting level-one layer is non-vacuous.  It accepts a genuine
atomlessness claim and rejects the same statement at every unsupported
contract kind.  Its boundary evidence is intentionally thin (`Unit`): this
is direct semantic decision, not a proof-trace replay shield.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanBootstrapGrounding

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanMSOSemanticBridge
open Mettapedia.Logic.Metaphysics
open Mettapedia.Foundations.Gunk

universe uGround uStatement

/-! ## The explicit grounding edge -/

/-- Evidence that a direct semantic decision procedure exactly interprets a
nonempty family of strictly-lower contracts.  `nonvacuous` rules out obtaining
a bootstrap result merely because level zero has no lower claims. -/
structure ExactSemanticGrounding
    {GroundClaim : Type uGround} {GroundMeaning : GroundClaim -> Prop}
    (ground : Checker.DecisionKernel GroundClaim GroundMeaning)
    (Statement : Nat -> Type uStatement) (hostLevel : Nat)
    (TargetMeaning : LowerContract Statement hostLevel -> Prop) where
  encode : LowerContract Statement hostLevel -> GroundClaim
  meaning_iff : forall claim,
    GroundMeaning (encode claim) <-> TargetMeaning claim
  nonvacuous : Nonempty (LowerContract Statement hostLevel)

namespace ExactSemanticGrounding

variable {GroundClaim : Type uGround} {GroundMeaning : GroundClaim -> Prop}
    {ground : Checker.DecisionKernel GroundClaim GroundMeaning}
    {Statement : Nat -> Type uStatement} {hostLevel : Nat}
    {TargetMeaning : LowerContract Statement hostLevel -> Prop}

/-- The host level of a non-vacuous exact grounding cannot be level zero. -/
theorem hostLevel_ne_zero
    (grounding : ExactSemanticGrounding ground Statement hostLevel
      TargetMeaning) :
    hostLevel ≠ 0 := by
  intro hostIsZero
  obtain ⟨claim⟩ := grounding.nonvacuous
  subst hostLevel
  exact LowerContract.levelZero_empty.false claim

/-- Decide a lower contract by translating it into the semantic ground. -/
def lowerDecision
    (grounding : ExactSemanticGrounding ground Statement hostLevel
      TargetMeaning) :
    Checker.DecisionKernel (LowerContract Statement hostLevel)
      TargetMeaning where
  decide := fun claim => ground.decide (grounding.encode claim)
  correct := by
    intro claim
    exact (ground.correct (grounding.encode claim)).trans
      (grounding.meaning_iff claim)

/-- The explicit grounding edge produces an ordinary, exact NIK bootstrap
layer.  Scope and meaning coincide only for this generated layer. -/
def toBootstrapLayer
    (grounding : ExactSemanticGrounding ground Statement hostLevel
      TargetMeaning) :
    BootstrapLayer Statement hostLevel where
  Certificate := Unit
  Scope := TargetMeaning
  Meaning := TargetMeaning
  scope_sound := fun _claim meaningful => meaningful
  checker := grounding.lowerDecision.toChecker
  scopeAuthority := grounding.lowerDecision.authority

@[simp] theorem toBootstrapLayer_check_iff
    (grounding : ExactSemanticGrounding ground Statement hostLevel
      TargetMeaning)
    (claim : LowerContract Statement hostLevel) :
    (grounding.toBootstrapLayer.checker).check claim () = true <->
      TargetMeaning claim :=
  grounding.lowerDecision.correct claim

/-- Direct grounding erases proof identity at the boundary.  This theorem is
not a criticism of the semantic decision procedure; it records why the
induced boundary is not yet an informative trace shield. -/
theorem toBootstrapLayer_certificates_equal
    (grounding : ExactSemanticGrounding ground Statement hostLevel
      TargetMeaning)
    (first second : grounding.toBootstrapLayer.Certificate) :
    first = second :=
  by
    change Unit at first second
    exact Subsingleton.elim first second

end ExactSemanticGrounding

/-! ## Atomless first-order instantiation -/

/-- Every lower level uses the same closed first-order Boolean claim
language.  The level index still records which authority is being discussed. -/
def Statement : Nat -> Type := fun _level => Formula 0

/-- A canonical level-one claim about the level-zero formula language. -/
def lowerClaim (kind : BootstrapContractKind) (formula : Formula 0) :
    LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := kind
  statement := formula

/-- This semantic ground licenses only model-soundness claims. -/
def TargetMeaning (claim : LowerContract Statement 1) : Prop :=
  claim.kind = .modelSound ∧ ColdMeaning claim.statement

/-- Unsupported contract kinds translate to falsity rather than being
silently interpreted as model soundness. -/
def encode (claim : LowerContract Statement 1) : Formula 0 :=
  if claim.kind = .modelSound then claim.statement else .falsum

theorem encode_meaning_iff (claim : LowerContract Statement 1) :
    ColdMeaning (encode claim) <-> TargetMeaning claim := by
  by_cases isModelSound : claim.kind = .modelSound
  · simp [encode, TargetMeaning, isModelSound]
  · simp [encode, TargetMeaning, ColdMeaning, Satisfies, isModelSound]

/-- The atomless decision procedure genuinely grounds a nonempty level-one
NIK layer, rather than a vacuous level-zero interface. -/
def grounding :
    ExactSemanticGrounding decisionKernel Statement 1 TargetMeaning where
  encode := encode
  meaning_iff := encode_meaning_iff
  nonvacuous := ⟨lowerClaim .modelSound gunkSentence⟩

def layer : BootstrapLayer Statement 1 := grounding.toBootstrapLayer

theorem layer_hostLevel_positive : (1 : Nat) ≠ 0 :=
  grounding.hostLevel_ne_zero

/-- Every unsupported contract kind fails closed, independently of the
formula placed in its statement field. -/
theorem unsupported_kind_rejected
    (kind : BootstrapContractKind) (notModelSound : kind ≠ .modelSound)
    (formula : Formula 0) :
    layer.checker.check (lowerClaim kind formula) () = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have meaningful : TargetMeaning (lowerClaim kind formula) :=
    (grounding.toBootstrapLayer_check_iff (lowerClaim kind formula)).mp
      accepted
  exact notModelSound meaningful.1

/-- Positive canary: the decidable atomless sentence is a real accepted
lower-level model-soundness contract. -/
theorem gunk_modelSound_accepted :
    layer.checker.check (lowerClaim .modelSound gunkSentence) () = true := by
  apply (grounding.toBootstrapLayer_check_iff
    (lowerClaim .modelSound gunkSentence)).mpr
  refine ⟨rfl, ?_⟩
  exact (decisionKernel.correct gunkSentence).mp gunkSentence_decides_true

/-- Negative canary: changing only the contract kind to source soundness is
rejected.  Semantic model evidence is not source-calculus evidence. -/
theorem gunk_sourceSound_rejected :
    layer.checker.check (lowerClaim .sourceSound gunkSentence) () = false :=
  unsupported_kind_rejected .sourceSound (by decide) gunkSentence

/-- Acceptance of a model-soundness claim transports to the MSO semantics at
every selected second-order family. -/
theorem accepted_modelSound_has_mso_meaning
    (formula : Formula 0) (family : Set (Set CantorAlgebra))
    (accepted :
      layer.checker.check (lowerClaim .modelSound formula) () = true) :
    SatSentence family (translateFormula formula) := by
  have meaningful : TargetMeaning (lowerClaim .modelSound formula) :=
    (grounding.toBootstrapLayer_check_iff
      (lowerClaim .modelSound formula)).mp accepted
  exact (satSentence_translateFormula_iff family formula).mpr meaningful.2

/-- Even after packaging formulas as lower-level model contracts, the
family-sensitive existential-ultrafilter sentence remains outside the image. -/
theorem no_lowerClaim_represents_existsUFAx :
    ¬ (∃ claim : LowerContract Statement 1,
      ∀ family : Set (Set CantorAlgebra),
        SatSentence family (translateFormula claim.statement) <->
          SatSentence family existsUFAx) := by
  rintro ⟨claim, represents⟩
  exact no_firstOrder_formula_represents_existsUFAx
    ⟨claim.statement, represents⟩

/-- The induced certificate carrier is thin: all boundary receipts are equal. -/
theorem layer_certificates_equal
    (first second : layer.Certificate) : first = second :=
  grounding.toBootstrapLayer_certificates_equal first second

#print axioms ExactSemanticGrounding.hostLevel_ne_zero
#print axioms ExactSemanticGrounding.lowerDecision
#print axioms ExactSemanticGrounding.toBootstrapLayer
#print axioms encode_meaning_iff
#print axioms grounding
#print axioms unsupported_kind_rejected
#print axioms gunk_modelSound_accepted
#print axioms gunk_sourceSound_rejected
#print axioms accepted_modelSound_has_mso_meaning
#print axioms no_lowerClaim_represents_existsUFAx
#print axioms layer_certificates_equal

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanBootstrapGrounding
