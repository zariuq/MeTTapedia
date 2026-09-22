import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BoundedConversion
import Mettapedia.TypeTheory.BudgetedTraversal

/-!
# Typed, heterogeneous normalization batches

The generic one-allowance traversal is instantiated with the actual typed
beta normalizer. Queries may have different contexts and result types. Each
returned receipt retains the normal form, typed reduction path, and normality
proof. Budget conservation and stability are proved, not requested from an
unimplemented normalization capability.

This reference counts stepper calls. It does not verify declaration admission
in C, or turn normalization failure into an obstruction to typing.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BudgetedBatch

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BoundedConversion
open Mettapedia.TypeTheory.BudgetedTraversal

abbrev Query := Σ context : List Ty, Σ type : Ty, Term context type
abbrev Evidence (query : Query) := Mettapedia.Logic.Relation.NormalizationResult BetaStep query.2.2

def check : Checker Query Evidence := fun fuel query => normalizeWithin fuel query.2.2

theorem check_conserves (fuel : Nat) (query : Query)
    (evidence : Evidence query) (remaining : Nat)
    (completed : check fuel query = some (evidence, remaining)) : remaining ≤ fuel :=
  Nat.le_of_lt (normalizeWithin_remaining_lt completed)

theorem check_stable (fuel : Nat) (query : Query)
    (evidence : Evidence query) (remaining : Nat)
    (completed : check fuel query = some (evidence, remaining)) (extra : Nat) :
    check (fuel + extra) query = some (evidence, remaining + extra) :=
  normalizeWithin_add completed extra

theorem batches_compose
    {fuel middle remaining : Nat} {first second : List Query}
    {left : EvidenceList Evidence first} {right : EvidenceList Evidence second}
    (leftRan : traverseWithin check fuel first = some (left, middle))
    (rightRan : traverseWithin check middle second = some (right, remaining)) :
    (fuel - middle) + (middle - remaining) = fuel - remaining ∧
      traverseWithin check fuel (first ++ second) =
        some (left.append right, remaining) :=
  completed_batches_spent_add check check_conserves leftRan rightRan

theorem larger_allowance_retains_evidence
    {fuel remaining : Nat} {queries : List Query}
    {evidence : EvidenceList Evidence queries}
    (completed : traverseWithin check fuel queries = some (evidence, remaining))
    (extra : Nat) :
    traverseWithin check (fuel + extra) queries = some (evidence, remaining + extra) :=
  traverseWithin_add check check_stable completed extra

/-- Strong normalization of the actual simple fragment supplies eventual
completion for arbitrary finite batches of differently scoped typed terms. -/
theorem batch_eventually (queries : List Query) :
    ∃ fuel evidence remaining,
      traverseWithin check fuel queries = some (evidence, remaining) :=
  traverseWithin_eventually check check_stable
    (fun query => normalizeWithin_eventually query.2.2) queries

def redexQuery : Query := ⟨[], .arr .atom .atom, redex⟩
def identityQuery : Query := ⟨[], .arr .atom .atom, identity⟩
def openQuery : Query := ⟨[.atom], .atom, .var .zero⟩

/-- All three checks complete individually at two calls. Their batch cannot
complete at two: the first result does not replenish the shared allowance. -/
theorem individual_success_does_not_admit_batch :
    (check 2 redexQuery).isSome = true ∧
      (check 2 identityQuery).isSome = true ∧
      (check 2 openQuery).isSome = true ∧
      (traverseWithin check 2 [redexQuery, identityQuery, openQuery]).isSome = false := by
  decide

/-- The same closed and open queries complete together with exactly the sum
of their individual work: two calls for the redex, one for each normal term. -/
theorem heterogeneous_batch_completes :
    ((traverseWithin check 4 [redexQuery, identityQuery, openQuery]).map Prod.snd) =
      some 0 := by
  decide

/-- Extract the actual computation's receipts, without choosing witnesses
from a theorem asserting that a normal form exists. -/
def completedBatch : EvidenceList Evidence [redexQuery, identityQuery, openQuery] × Nat :=
  (traverseWithin check 4 [redexQuery, identityQuery, openQuery]).get (by decide)

/-- The third receipt can be consumed at its original open context and atom
type; no coercion through either closed function query is needed. -/
def openReceipt : Mettapedia.Logic.Relation.NormalizationResult BetaStep (openQuery.2.2) :=
  completedBatch.1.get ⟨2, by decide⟩

theorem consumed_open_normal_form : openReceipt.normalForm = (.var .zero) := by
  rfl

#print axioms check_conserves
#print axioms batches_compose
#print axioms larger_allowance_retains_evidence
#print axioms batch_eventually
#print axioms individual_success_does_not_admit_batch
#print axioms heterogeneous_batch_completes
#print axioms completedBatch
#print axioms consumed_open_normal_form

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BudgetedBatch
