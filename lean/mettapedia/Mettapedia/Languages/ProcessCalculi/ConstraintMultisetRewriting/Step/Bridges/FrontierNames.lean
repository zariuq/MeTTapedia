import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Frontier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedEvents

/-!
# Finite named fibres and their frontier unfolding

A source program has four control names and one name per equation ordinal.
The enabled source and hosted-history choices are subsets of that finite name
set. This proves finiteness without enumerating fresh frames, unifiers or raw
firings. The resulting frontier correspondence keeps duplicate equation
origins and the bag of finished answers.

This component unfolds independent alternatives. The full source Config has a
shared scope counter; its connection is a separate representation obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star} (P : SourceLanguage.Program κ Γ star D.Ty)

def names : Finset RuleName :=
  { .ret, .unmatched, .left, .right } ∪ (Finset.range P.equations.length).image RuleName.eqn

theorem lookup_bound {α : Type*} {rows : List α} {index : Nat} {row : α}
    (found : rows[index]? = some row) : index < rows.length := by
  by_contra beyond
  rw [List.getElem?_eq_none (Nat.le_of_not_gt beyond)] at found
  cases found

theorem move_name_mem {world nextWorld : World κ Γ star} {branch nextBranch : Branch κ Γ star D.Ty}
    {name : RuleName} (moved : NamedMove P world branch name nextWorld nextBranch) : name ∈ names P := by
  cases moved with
  | ret => simp [names]
  | unmatched => simp [names]
  | left => simp [names]
  | right => simp [names]
  | eqn _ _ _ _ index equation found _ =>
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨index, Finset.mem_range.mpr (lookup_bound found), rfl⟩)

theorem source_enabled_mem {current : HostedEvents.SourceState (κ := κ) (D := D)} {name : RuleName}
    (enabled : HostedEvents.sourceEnabled P current name) : name ∈ names P := by
  obtain ⟨next, moved, _⟩ := enabled
  exact move_name_mem P moved

instance sourceChoices (current : HostedEvents.SourceState (κ := κ) (D := D)) :
    Fintype ((HostedEvents.sourceSystem (D := D) P).Choice current) := by
  have bounded : Set.Finite {name | HostedEvents.sourceEnabled (D := D) P current name} :=
    (names P).finite_toSet.subset (fun _ enabled => source_enabled_mem P enabled)
  exact bounded.fintype

variable (N : Nodes S Γ star) (q : Comp κ Γ star D.Ty)

theorem rule_name_mem {name : RuleName} {rule : CRule S} (found : ruleNamed N P name = some rule) :
    name ∈ names P := by
  cases name with
  | ret => simp [names]
  | unmatched => simp [names]
  | left => simp [names]
  | right => simp [names]
  | eqn index =>
      obtain ⟨equation, selected, _⟩ := Option.map_eq_some_iff.mp found
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨index, Finset.mem_range.mpr (lookup_bound selected), rfl⟩)

theorem target_enabled_mem {word : List RuleName} {name : RuleName}
    (enabled : HostedEvents.targetEnabled N P q word name) : name ∈ names P := by
  obtain ⟨state, active, history⟩ := enabled
  obtain ⟨before, prior, historyBefore, rule, named, fired⟩ := history.snoc_inv
  exact rule_name_mem P N named

instance targetChoices (word : List RuleName) : Fintype ((HostedEvents.targetSystem (D := D) N P q).Choice word) := by
  have bounded : Set.Finite {name | HostedEvents.targetEnabled N P q word name} :=
    (names P).finite_toSet.subset (fun _ enabled => target_enabled_mem P N q enabled)
  exact bounded.fintype

def source := Frontier.theory (HostedEvents.sourceSystem (D := D) P)
  (fun current => current.2.Finished (D := D))

def target := Frontier.theory (HostedEvents.targetSystem (D := D) N P q) (FinishedClass N P q)

def correspondence (plainP : PlainProgram P) :
    Mettapedia.GSLT.IndexedOperational.OperationalCorrespondence (source P) (target P N q) :=
  Frontier.correspondence (HostedEvents.bisimulation plainP) (fun related => HostedEvents.finished_iff related)

theorem answers_eq {before : Frontier.State (HostedEvents.SourceState (κ := κ) (D := D))}
    {current : Frontier.State (List RuleName)}
    (related : Frontier.Related (HostedEvents.Related N P q) before current) :
    Frontier.answers (fun state => state.2.Finished (D := D)) (fun state => state.2.answer (D := D)) before =
      Frontier.answers (FinishedClass N P q) (classAnswer N P q) current :=
  Frontier.answers_eq (fun pair => HostedEvents.finished_iff pair)
    (fun state => state.2.answer (D := D)) (classAnswer N P q)
    (fun pair finished => (HostedEvents.answer_eq pair finished).symm) related

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNames

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNames.sourceChoices
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNames.targetChoices
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNames.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNames.answers_eq
