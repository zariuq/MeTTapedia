import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.ProgramComposition

/-!
# The program-extension/frontier composite on concrete source programs

The query calls `(g)`. Its program answers `d`; a neighbouring `(g a)`
equation cannot match that call, so the composite keeps the reachable bags.
Adding the matching `(g)` equation to an empty program fails that same
separation contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.ProgramComposition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Composition Hosting.Alternatives
open SourceLanguage.Elaboration
open Hosting.Composition.Controls (D N Q P0 rowProgram gaT q q_unopened eg supply sp separate_instance not_separate)

theorem union_plain : PlainProgram (Q.union (rowProgram gaT)) := by
  intro equation member
  have cases' : equation = eg ∨ equation = ⟨[301], gaT, .fail⟩ := by
    simpa [Program.union, Q, rowProgram] using member
  rcases cases' with rfl | rfl <;> trivial

theorem actual_composed_answer_bags (bag : Multiset (Set (Term MSig [] ()))) :
    (∃ after, (Divergence.sourceSystem D Q supply).MultiStep (Config.initial sp q) after ∧
      after.answers (D := D) = bag) ↔
      ∃ frontier, (FrontierConfig.target (D := D) (Q.union (rowProgram gaT)) N q).MultiStep ⟨{[]}, 0⟩ frontier ∧
        Frontier.answers (FinishedClass (D := D) N (Q.union (rowProgram gaT)) q)
          (classAnswer (D := D) N (Q.union (rowProgram gaT)) q) frontier = bag :=
  Bridges.ProgramComposition.reachable_bags_iff N separate_instance union_plain (by trivial) q_unopened bag

theorem matching_extension_fails_the_contract : ¬ SeparateFrom D P0 Q supply sp q :=
  not_separate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.ProgramComposition

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.ProgramComposition.actual_composed_answer_bags
