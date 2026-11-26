import Mettapedia.Machines.TIsa.StoreInstructions.PackedResolution
import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicFiringCode

/-!
# Residual knowledge in a packed snapshot

Resolution can interpret the original equations, but its
temporary agenda is not the knowledge of the next world.
The original chains can be kept as segments: newest first
inside a segment, chronological across segments. No
substitution into source terms is involved in adding one.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedSymbolicKnowledge

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Derivation.SymbolicFiring (LiveWorld Rules act Attempt problem)
open PackedOccurrences (Codes)
open PackedEquations (Arena)

abbrev Chain := Word

structure Tape where
  storage : Arena
  segments : List Chain

def Tape.extend (known : Tape) (head : Chain) : Tape :=
  ⟨known.storage, known.segments ++ [head]⟩

def Tape.read {T : Type*} (codes : Codes T) (known : Tape) : Option (List (T × T)) :=
  (known.segments.mapM (fun head => (PackedEquations.read codes known.storage head).map List.reverse)).map List.flatten

theorem Tape.extend_read {T : Type*} (codes : Codes T) (known : Tape) (head : Chain) :
    (known.extend head).read codes =
      (known.read codes).bind fun prior =>
        (PackedEquations.read codes known.storage head).map (fun newer => prior ++ newer.reverse) := by
  unfold Tape.read Tape.extend
  simp only [List.mapM_append]
  cases all : List.mapM (fun h => Option.map List.reverse (PackedEquations.read codes known.storage h)) known.segments
  · rfl
  · cases localRead : PackedEquations.read codes known.storage head
    · simp [List.mapM_cons, localRead]
    · simp [List.mapM_cons, localRead, List.flatten_append]

universe u p
variable {σ : LPSignature.{u,u,p,u}} {rules : Rules σ} {before : LiveWorld σ}

theorem commit_problem (trial : Attempt rules before)
    (reserved : trial.seed.firing.selection.made = before.reserve 0 trial.seed.firing.selection.made.length) :
    (before.commit trial.seed.firing reserved).state.knowledge = problem trial.seed := rfl

/-- The packed successor can reuse prior knowledge and append
the original local equations selected by MATCH and TELL.
The result is independent of how the solver represented its answer. -/
theorem selected_knowledge (trial : Attempt rules before)
    (reserved : trial.seed.firing.selection.made = before.reserve 0 trial.seed.firing.selection.made.length)
    (codes : Codes (Term σ)) (known : Tape) (head : Chain)
    (prior : known.read codes = some before.state.knowledge)
    (entry : PackedEquations.read codes known.storage head =
      some (SymbolicFiringCode.beforeSolve trial).bindings.newer) :
    (known.extend head).read codes = some (before.commit trial.seed.firing reserved).state.knowledge := by
  rw [Tape.extend_read, prior, Option.bind_some, entry, Option.map_some, commit_problem]
  exact congrArg some (SymbolicFiringCode.beforeSolve_problem trial)

namespace Examples

private def codes : Codes Word := ⟨some, some, fun known => known.symm⟩
private def bank : Arena := #[⟨0, 9, 1⟩, ⟨0, 4, 9⟩, ⟨2, 8, 4⟩]
private def known : Tape := ⟨bank, [1]⟩

theorem extends_without_replacing_an_old_equation :
    (known.extend 3).read codes = some [(9, 1), (4, 9), (8, 4)] := by decide +kernel

theorem a_new_segment_does_not_authorize_skipping_a_missing_chain :
    ((⟨bank, [4]⟩ : Tape).extend 3).read codes = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedSymbolicKnowledge
