import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Unions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Readouts

/-!
# A separated source extension followed by whole-frontier hosting

The first arrow is the existing source-program union correspondence. The
second is the independently defined named frontier controller. Their actual
intermediate system agrees, and the composite preserves reachable answer
bags. The separation premise concerns calls along the source runs; consistency
of a neighbour's knowledge alone is not substituted for it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.ProgramComposition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Composition Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  {D : Discipline S Γ star} {P Q : SourceLanguage.Program κ Γ star D.Ty}
  (N : Nodes S Γ star) {supply : Nat → Term S Γ star}
  {spaces : Term S Γ star → Multiset (Row κ Γ star)} {q : Comp κ Γ star D.Ty}

def composed (separate : SeparateFrom D P Q supply spaces q)
    (plainUnion : PlainProgram (P.union Q)) :
    OperationalCorrespondence (Divergence.sourceSystem D P supply)
      (FrontierConfig.target (P.union Q) N q) :=
  (unionCorrespondence separate).comp
    (FrontierConfig.correspondence (P.union Q) N q supply plainUnion)

def observesSource (bag : Multiset (Set (Term S Γ star))) (configuration : Config κ Γ star D.Ty) : Prop :=
  configuration.answers (D := D) = bag

def observesTarget (bag : Multiset (Set (Term S Γ star))) (frontier : FrontierConfig.TargetState) : Prop :=
  Frontier.answers (FinishedClass N (P.union Q) q) (classAnswer N (P.union Q) q) frontier = bag

theorem union_delivery (separate : SeparateFrom D P Q supply spaces q) :
    Readouts.Delivery (unionCorrespondence separate) (observesSource (D := D)) (observesSource (D := D)) := by
  apply Readouts.Delivery.of_exact
  intro before after related bag
  exact congrArg (fun values => values = bag) (answers_withDead related.2).symm |>.to_iff

theorem frontier_delivery (plainUnion : PlainProgram (P.union Q)) :
    Readouts.Delivery (FrontierConfig.correspondence (P.union Q) N q supply plainUnion)
      (observesSource (D := D)) (observesTarget (P := P) (Q := Q) N (q := q)) := by
  apply Readouts.Delivery.of_exact
  intro before after related bag
  exact congrArg (fun values => values = bag) (FrontierConfig.answers_eq (P.union Q) N q related) |>.to_iff

theorem composed_delivery (separate : SeparateFrom D P Q supply spaces q)
    (plainUnion : PlainProgram (P.union Q)) :
    Readouts.Delivery (composed N separate plainUnion) (observesSource (D := D))
      (observesTarget (P := P) (Q := Q) N (q := q)) :=
  (union_delivery separate).comp (frontier_delivery N plainUnion)

theorem initial (separate : SeparateFrom D P Q supply spaces q)
    (plainUnion : PlainProgram (P.union Q)) (plainQuery : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = []) :
    (composed N separate plainUnion).related (Config.initial spaces q) ⟨{[]}, 0⟩ := by
  refine ⟨Config.initial spaces q, ⟨.refl, rfl, 0, ?_, ?_⟩,
    FrontierConfig.initial (P.union Q) N q spaces plainQuery unopened⟩
  · exact (add_zero _).symm
  · intro branch member
    cases member

theorem reachable_bags_iff (separate : SeparateFrom D P Q supply spaces q)
    (plainUnion : PlainProgram (P.union Q)) (plainQuery : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = [])
    (bag : Multiset (Set (Term S Γ star))) :
    (∃ after, (Divergence.sourceSystem D P supply).MultiStep (Config.initial spaces q) after ∧
      after.answers (D := D) = bag) ↔
      ∃ frontier, (FrontierConfig.target (P.union Q) N q).MultiStep ⟨{[]}, 0⟩ frontier ∧
        Frontier.answers (FinishedClass N (P.union Q) q) (classAnswer N (P.union Q) q) frontier = bag :=
  (composed_delivery N separate plainUnion).reachable_iff
    (initial N separate plainUnion plainQuery unopened) bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.ProgramComposition

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.ProgramComposition.composed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.ProgramComposition.reachable_bags_iff
