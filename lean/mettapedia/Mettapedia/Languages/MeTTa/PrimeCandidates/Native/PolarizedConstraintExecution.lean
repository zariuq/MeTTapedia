import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedConstraintEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# First-class source computation with persistent open equation effects

The authored computations, captured lambdas/thunks, Need cells, forcing rules
and natural evaluation are the existing PolarizedNeed owners. This explicit
profile reads their effect occurrences as logical tells and admits an actual
machine successor only when the joint persistent equation store remains
consistent. The checker acts during execution; it is not unused metadata.

The source meaning is an independently defined natural evaluation whose final
tells have one joint solution. The comparison derives validity of every
intermediate store from persistent refinement and preserves the exact full
world/outcome. Finite ordered machine observations also agree after filtering,
including all surviving duplicate occurrences.

There are no asks, named crossing elaboration or irreversible host effects in
this profile. Native symbols carrying open terms in examples are explicitly
interpreted symbolic data, not a new native conversion or formation policy.
-/

open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedConstraintExecution

open Presentation NeedReference
open PolarizedNeedMachine PolarizedNeedNaturalSemantics
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {T S Head Operation StableFault NativeFault : Type} {m : Nat}

def initial (closure : Closure Head Operation (Equation T) m)
    (world : NeedWorld Head Operation (Equation T) StableFault NativeFault m) :
    NeedMachine Head Operation (Equation T) StableFault NativeFault m :=
  ⟨world, .run (.evaluate closure .done) [], {}⟩

def machine
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (store : EquationStore T) (check : EquationStore T → Bool) :=
  NeedConstraintEffects.checkedCore (extension primitive) store check

/-- Preservation and no invention connect independently authored natural
evaluation to the actual machine restricted by the consistency algorithm. -/
theorem source_iff_checked_execution (action : SubstitutionAction T S)
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (store : EquationStore T) (check : EquationStore T → Bool)
    (checkLaw : ∀ equations, check equations = true ↔ action.Consistent equations)
    (closure : Closure Head Operation (Equation T) m)
    (world final : NeedWorld Head Operation (Equation T) StableFault NativeFault m)
    (outcome : Outcome Head Operation (Equation T) StableFault NativeFault m) :
    (Nonempty (Eval primitive closure world outcome final) ∧
      action.Consistent (store ++ final.receipts.effects)) ↔
      ∃ fuel work,
        (⟨final, .halted outcome, work⟩ : NeedMachine Head Operation (Equation T) StableFault NativeFault m)
          ∈ (machine primitive store check).answerOccurrences fuel (initial closure world) := by
  constructor
  · rintro ⟨⟨evaluation⟩, consistent⟩
    obtain ⟨length, work, path⟩ := evaluation.halts {}
    refine ⟨length, work, ?_⟩
    apply (NeedConstraintEffects.checked_occurrence_iff action (extension primitive)
      store check checkLaw length _ _).mpr
    exact ⟨⟨length, Nat.le_refl _, path, rfl⟩, consistent⟩
  · rintro ⟨fuel, work, accepted⟩
    obtain ⟨⟨length, _, path, _⟩, consistent⟩ :=
      (NeedConstraintEffects.checked_occurrence_iff action (extension primitive)
        store check checkLaw fuel _ _).mp accepted
    exact ⟨Reflection.eval_of_steps path, consistent⟩

/-- This stronger bounded statement retains the entire ordered list of
completed machine states; it does not collapse equal answers or aliases. -/
theorem ordered_occurrences_exact (action : SubstitutionAction T S)
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (store : EquationStore T) (check : EquationStore T → Bool)
    (checkLaw : ∀ equations, check equations = true ↔ action.Consistent equations)
    (fuel : Nat) (closure : Closure Head Operation (Equation T) m)
    (world : NeedWorld Head Operation (Equation T) StableFault NativeFault m) :
    (machine primitive store check).answerOccurrences fuel (initial closure world) =
      ((NeedConstraintEffects.rawCore (extension primitive)).answerOccurrences fuel
        (initial closure world)).filter
          (fun final => check (store ++ final.world.receipts.effects)) :=
  NeedConstraintEffects.checked_occurrences_exact action (extension primitive) store check checkLaw fuel _

namespace FirstOrderProfile

open Mettapedia.Logic.LP

variable (signature : LPSignature)
  [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

/-- The existing total occurs-checked unifier supplies the executable test.
No unifier is selected as a global source interpretation. -/
def check (store : EquationStore (Term signature)) : Bool := (unifyTotal store).isSome

theorem check_exact (store : EquationStore (Term signature)) :
    check signature store = true ↔ (FirstOrder.action signature).Consistent store := by
  rw [← FirstOrder.accepted_iff_consistent]
  exact Option.isSome_iff_exists

end FirstOrderProfile

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedConstraintExecution
