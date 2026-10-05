import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.TypeTheory.PresheafDependentIdentity

/-!
# Native dependent functions on authored certificate families

The actual goal-and-ledger observation of an authored proof calculus is
a dependent type in presheaf slice semantics. Abstraction and application
through the generic dependent adjunction return the supplied derivation,
including its exact ordered premise-use list.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Bridges.TypeTheory.CertificateDependentProducts

open CategoryTheory Limits
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.TypeTheory.PresheafDependentAdjunction
open Mettapedia.TypeTheory.PresheafDependentIdentity

/-- Evaluate the native dependent identity function at an actual authored
proof answer, through the slice product's abstraction and application. -/
noncomputable def applyProofIdentity
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : (derivationTotalFace definition).obj (Opposite.op context)) :
    (derivationTotalFace definition).obj (Opposite.op context) :=
  let f := derivationToGoalLedger definition
  (pullback.fst f f).app (Opposite.op context)
    ((evaluation f ((Over.pullback f).obj (Over.mk f))).left.app (Opposite.op context)
      (((Over.pullback f).map (identityFunction f)).left.app (Opposite.op context)
        ((argumentMap f).app (Opposite.op context) answer)))

/-- The dependent function returns the same proof, not a new proof
chosen from mere inhabitation of its native predicate. -/
theorem applyProofIdentity_eq
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : (derivationTotalFace definition).obj (Opposite.op context)) :
    applyProofIdentity definition context answer = answer :=
  identity_retains_value (derivationToGoalLedger definition) (Opposite.op context) answer

/-- Application preserves the exact ordered occurrence ledger carried by
the proof. No permutation or duplicate removal is performed. -/
theorem applyProofIdentity_ledger
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : (derivationTotalFace definition).obj (Opposite.op context)) :
    (derivationToLedger definition).app (Opposite.op context)
        (applyProofIdentity definition context answer) =
      OpenSearchMachine.holeOccurrences answer.2 := by
  rw [applyProofIdentity_eq]
  rfl

/-- Distinct authored proof answers remain distinct after dependent
abstraction and application, even if their observed goal is the same. -/
theorem applyProofIdentity_injective
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) :
    Function.Injective (applyProofIdentity definition context) := by
  intro first second same
  simpa only [applyProofIdentity_eq] using same

/-- Equal-labeled assumptions at different premise positions give
different answers after actual dependent abstraction/application. -/
theorem duplicatePremises_remain_distinct
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    applyProofIdentity definition ⟨[goal, goal]⟩
        ⟨goal, OpenDerivation.assumption (definition := definition)
          (context := [goal, goal]) (0 : Fin 2)⟩ ≠
      applyProofIdentity definition ⟨[goal, goal]⟩
        ⟨goal, OpenDerivation.assumption (definition := definition)
          (context := [goal, goal]) (1 : Fin 2)⟩ := by
  intro same
  have proofs := applyProofIdentity_injective definition ⟨[goal, goal]⟩ same
  have ledgers := congrArg
    ((derivationToLedger definition).app (Opposite.op ⟨[goal, goal]⟩)) proofs
  change [(0 : Fin 2)] = [(1 : Fin 2)] at ledgers
  exact Fin.zero_ne_one (List.singleton_injective ledgers)

/-- Observing only a goal cannot implement the proof-retaining dependent
function: the two equal-labeled premise positions would be identified. -/
theorem goal_observation_cannot_recover_function
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    ¬ ∃ restore : Pattern →
        (derivationTotalFace definition).obj
          (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition)),
      ∀ answer, restore ((derivationToGoal definition).app _ answer) =
        applyProofIdentity definition ⟨[goal, goal]⟩ answer := by
  rintro ⟨restore, recovers⟩
  let first : (derivationTotalFace definition).obj
      (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition)) :=
    ⟨goal, OpenDerivation.assumption (definition := definition)
      (context := [goal, goal]) (0 : Fin 2)⟩
  let second : (derivationTotalFace definition).obj
      (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition)) :=
    ⟨goal, OpenDerivation.assumption (definition := definition)
      (context := [goal, goal]) (1 : Fin 2)⟩
  exact duplicatePremises_remain_distinct definition goal
    ((recovers first).symm.trans (recovers second))

end Mettapedia.GSLT.Bridges.TypeTheory.CertificateDependentProducts
