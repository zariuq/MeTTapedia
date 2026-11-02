import Mettapedia.GSLT.Readers.HOL.LoadWorld
import Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins

/-!
# Accepted HOL records derive from the actual admissions

The loader's earlier soundness theorem reaches the rule board at acceptance,
which includes previously promoted claims. Here the kernel-run conservativity
invariant removes those intermediate rules. Only successful admission
occurrences remain as root rules, with cited terms as explicit hypotheses.

The theorem is independent of corpus size and the runner's fuel. It does not
assert loader completeness or adequacy of the admitted HOL presentation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.HOL.Load

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins
open Mettapedia.Logic.TierZero.Adequacy.HOL

/-- Successful rule admissions observed during the loader's exact run. -/
def admissionBasis (fuel : ℕ) (program : LState) : List (String × Rule) :=
  (observeProgram fuel (actsOf program)).1

theorem observeProgram_world (fuel : ℕ) (actions : List (ClientAct String)) :
    (observeProgram fuel actions).2 = runProgram fuel actions := by
  exact foldObserved_world fuel actions ([], World.empty)

theorem actsOf_noLocals (program : LState) (claim : Claim String)
    (sent : ClientAct.sendClaim claim ∈ actsOf program) : claim.locals = [] := by
  have included : claim ∈ sentOf (actsOf program) := by
    simp only [sentOf, List.mem_filterMap]
    exact ⟨.sendClaim claim, sent, rfl⟩
  obtain ⟨source, _, rfl⟩ := sentOf_actsOf program claim included
  rfl

theorem program_reduces_to_admissions (fuel : ℕ) (program : LState) :
    ReducesTo (runProgram fuel (actsOf program)).env (admissionBasis fuel program) := by
  have accounted := observeProgram_accounted fuel (actsOf program) (actsOf_noLocals program)
  simpa only [admissionBasis, observeProgram_world] using accounted.reduction

/-- Every accepted record states the loader's encoded HOL sequent and is
derivable from the successful admission occurrences alone. Previously
promoted claims have been eliminated by cut; no local-dummy hypotheses remain. -/
theorem load_accepted_from_admissions (steps : Array (Option PTStep))
    (theorems : Array (Option (List SourceTerm × SourceTerm))) (named : ℕ → Bool)
    (profile : List (String × SourceTerm)) (fuel : ℕ) :
    ∀ id ∈ (runProgram fuel (actsOf (load steps theorems named profile))).T,
      ∃ (record : ℕ) (hypotheses : List SourceTerm) (conclusion : SourceTerm),
        id = "hol:r." ++ toString record ∧
        theorems[record]? = some (some (hypotheses, conclusion)) ∧
        ∃ givens : List Tm, (∀ given ∈ givens, IsGiven given) ∧
          Derivable
            (basisPres (admissionBasis fuel (load steps theorems named profile)) ⟨0, []⟩)
            givens (thmT hypotheses conclusion) := by
  intro id accepted
  obtain ⟨record, hypotheses, conclusion, namedRecord, recorded,
      earlier, givens, _, earlierRules, given, derivation⟩ :=
    load_accepted_derivable steps theorems named profile fuel id accepted
  have current : Derivable
      (presOf (runProgram fuel (actsOf (load steps theorems named profile))).env ⟨0, []⟩)
      givens (thmT hypotheses conclusion) :=
    derivable_rules_prefix earlierRules derivation
  obtain ⟨extra, extraGiven, reduced⟩ :=
    program_reduces_to_admissions fuel (load steps theorems named profile)
      ⟨0, []⟩ givens (thmT hypotheses conclusion) current
  refine ⟨record, hypotheses, conclusion, namedRecord, recorded, givens ++ extra, ?_, reduced⟩
  intro term member
  rcases List.mem_append.mp member with initial | additional
  · exact given term initial
  · exact extraGiven term additional

end Mettapedia.GSLT.Readers.HOL.Load
