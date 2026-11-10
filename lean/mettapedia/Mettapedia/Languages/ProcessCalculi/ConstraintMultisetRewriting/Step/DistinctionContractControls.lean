import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionContracts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionControls

/-!
# Scope changes and contextual observation controls

An old exact view can become inadequate after adding a new reading, with
the dynamics unchanged. There is no observer-refinement witness licensing
that invalid transport. A context that swaps two bits similarly reveals the
bit that the original reading ignored; saturation retains both distinctions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver.Controls
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.Cybernetics.DistinctionCalculus
open DistinctionFinite

def swapping : ContextMonoid Bool (Bool × Bool) where
  act c s := if c then (s.2, s.1) else s
  unit := false
  mul := Bool.xor
  act_unit _ := rfl
  act_mul c d s := by cases c <;> cases d <;> rfl

theorem contextual_read_keeps_both (s t : Bool × Bool) :
    contextRead swapping Prod.fst s = contextRead swapping Prod.fst t ↔ s = t := by
  constructor
  · intro same
    exact Prod.ext (congrFun same false) (congrFun same true)
  · rintro rfl
    rfl

theorem plain_read_is_insufficient :
    (false, false).1 = (false, true).1 ∧
      contextRead swapping Prod.fst (false, false) ≠ contextRead swapping Prod.fst (false, true) := by
  refine ⟨rfl, ?_⟩
  intro same
  have impossible := (contextual_read_keeps_both _ _).mp same
  cases impossible

def machine : Machine (Bool × Bool) Unit Bool := ⟨Prod.fst, fun s _ => [s]⟩
def encode (s : Nat × (Bool × Bool)) : Bool := s.2.1

def views (revision : Bool) : System (Race.Generic.gslt machine.step.toStep Machine.offers) :=
  tests machine.step.toStep Machine.offers (fun s => if revision then s.2.2 else s.2.1)

theorem old_certificate : Certificate views false encode := by
  have checked : machine.checkEncoding Prod.fst = true := by decide
  have exactView := (machine.exactEncoding_iff_transform Prod.fst).mp
    ((machine.checkEncoding_exact Prod.fst).mp checked)
  exact (tests_bisimulation_iff machine.step.toStep Machine.offers _ _).mpr
    ((exact_iff_kernel_bisimulation machine.step.toStep Machine.offers _ _).mp exactView)

theorem changed_query_refuses_old_encoding : ¬ Certificate views true encode := by
  intro certificate
  have distinguishes := certificate.2.2
    (show encode (0, false, false) = encode (0, false, true) from rfl)
    (fun b => b = true)
  have impossible : false = true := distinguishes.mpr rfl
  cases impossible

/-- The missing transport cannot be supplied by a generic rename or status cast. -/
theorem no_refinement_to_new_query : ¬ Nonempty (ObserverRefinement (views true) (views false)) := by
  rintro ⟨refinement⟩
  exact changed_query_refuses_old_encoding (certificate_forget views refinement old_certificate)

/-- Coarsening the state encoding is different from weakening the protected tests. -/
theorem merging_exact_codes_can_fail :
    DistinctionFinite.Controls.eight.checkEncoding DistinctionFinite.Controls.keepAB = true ∧
      DistinctionFinite.Controls.eight.checkEncoding (Prod.fst ∘ DistinctionFinite.Controls.keepAB) = false := by
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver.Controls
