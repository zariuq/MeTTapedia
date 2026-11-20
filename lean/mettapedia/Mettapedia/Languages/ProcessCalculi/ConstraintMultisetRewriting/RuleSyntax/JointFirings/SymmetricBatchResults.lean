import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricGivenValues
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchSemantics

/-!
# Actual complete CMR batches have presentation-independent result models

Profile: one first-order occurrence-bag store, ambient rules, finite jointly
fresh bags, guards at each member's own information after tells. Output is a
bag, while the source-mentioned interface and residual models are retained.
No chronology or named-derivation observer is identified by this theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

def outputBag {a : PUnit} {x : (ext (FirstOrder.action signature)).Ext a}
    (members : List (Member O (ext (FirstOrder.action signature)) P x))
    (assignment : Subst signature) : Multiset (Term signature) :=
  ((members.flatMap fun m => (m.firing.opened (frames (FirstOrder.action signature))).produce).map
    assignment.applyTerm : List (Term signature))

theorem emissions_of_assignment (s : State (Terms (Term signature)) O)
    {x : (ext (FirstOrder.action signature)).Ext s.frame}
    (members : List (Member O (ext (FirstOrder.action signature)) P x))
    (source assignment : Subst signature)
    (admitted : ∀ m ∈ members, m.firing.Admits (frames (FirstOrder.action signature)) s)
    (models : ∀ m ∈ members, Unifies assignment (m.firing.information (frames (FirstOrder.action signature)) s))
    (agrees : SourceAgrees s assignment source) :
    Emissions s.label source (members.map fun m => identity.key m.firing) (outputBag members assignment) := by
  induction members with
  | nil => exact .nil
  | cons m rest ih =>
    have model : ResultModel s m.firing source
        ((m.firing.opened (frames (FirstOrder.action signature))).produce.map assignment.applyTerm) :=
      ⟨assignment, models m List.mem_cons_self, agrees, rfl⟩
    have here := ((resultModel_iff s m.firing (admitted m List.mem_cons_self) source _).mp model).2
    have later := ih (fun n inside => admitted n (List.mem_cons_of_mem _ inside))
      (fun n inside => models n (List.mem_cons_of_mem _ inside))
    change Emissions s.label source (identity.key m.firing :: rest.map (fun n => identity.key n.firing)) _
    simpa only [outputBag, List.flatMap_cons, List.map_append, Multiset.coe_add] using
      Emissions.cons (show realizes (identity.key m.firing) s.label source _ from here) later

theorem assignment_of_emissions (s : State (Terms (Term signature)) O)
    {x : (ext (FirstOrder.action signature)).Ext s.frame}
    (members : List (Member O (ext (FirstOrder.action signature)) P x))
    (source : Subst signature) (knowledge : Unifies source s.knowledge)
    (admitted : ∀ m ∈ members, m.firing.Admits (frames (FirstOrder.action signature)) s) :
    ∀ (Q : Subst signature → Prop) (produced : Multiset (Term signature)),
      (∀ assignment, Q assignment → SourceAgrees s assignment source) →
      Realized (frames (FirstOrder.action signature)) PUnit.unit members Q →
      Emissions s.label source (members.map fun m => identity.key m.firing) produced →
      ∃ assignment, Q assignment ∧
        (∀ m ∈ members, Unifies assignment (m.firing.information (frames (FirstOrder.action signature)) s)) ∧
        produced = outputBag members assignment := by
  induction members with
  | nil =>
    intro Q produced _ realized emissions
    cases emissions
    change ∃ assignment : Subst signature, Q assignment at realized
    obtain ⟨assignment, holds⟩ := realized
    exact ⟨assignment, holds, fun _ member => False.elim (List.not_mem_nil member), rfl⟩
  | cons m rest ih =>
    intro Q produced agrees realized emissions
    cases emissions with
    | @cons _ _ _ _ here later =>
      change (presentation m.firing).Realizes s.label source _ at here
      obtain ⟨locals, pairs, tells, output⟩ := here
      have remaining := (realized_cons _ m rest Q).mp realized locals
      obtain ⟨assignment, ⟨holds, localValues⟩, models, after⟩ := ih
        (fun n inside => admitted n (List.mem_cons_of_mem _ inside)) _ _
        (fun assignment both => agrees assignment both.1) remaining later
      have values : ∀ term ∈ m.rule.terms,
          assignment.applyTerm (m.opening.applyTerm term) = locals.applyTerm term := by
        intro term member
        simpa only [frames, Interface.Frames.ofSubstitution, FirstOrder.action] using localValues term member
      obtain ⟨model, made⟩ := realizes_at_given_values s m.firing (admitted m List.mem_cons_self)
        source locals assignment _ knowledge pairs tells output (agrees assignment holds) values
      refine ⟨assignment, holds, ?_, ?_⟩
      · intro n member
        rcases List.mem_cons.mp member with rfl | inside
        · exact model
        · exact models n inside
      · rw [made, after]
        simp only [outputBag, List.flatMap_cons, List.map_append, Multiset.coe_add]

omit [DecidableEq O] in
theorem models_bag_iff (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) (assignment : Subst signature) :
    Unifies assignment (bag.information (frames (FirstOrder.action signature)) s) ↔
      Unifies assignment s.knowledge ∧
        ∀ m ∈ bag.members,
          Unifies assignment (m.firing.information (frames (FirstOrder.action signature)) s) := by
  have known : (frames (FirstOrder.action signature)).applyStore
      ((ext (FirstOrder.action signature)).weaken bag.ext) s.knowledge = s.knowledge :=
    Interface.Frames.applyStore_id s.knowledge
  constructor
  · intro solved
    refine ⟨?_, fun _ member => Bag.models_member _ member (b := PUnit.unit) solved⟩
    intro equation member
    apply solved
    unfold Bag.information
    rw [known]
    exact List.mem_append_left _ member
  · rintro ⟨knowledge, members⟩
    intro equation member
    unfold Bag.information at member
    rw [known] at member
    rcases List.mem_append.mp member with old | added
    · exact knowledge equation old
    · obtain ⟨m, inM, inOwn⟩ := List.mem_flatMap.mp added
      apply members m inM
      rw [Member.information_eq]
      exact List.mem_append_right _ inOwn

def BatchResultModel (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (source : Subst signature) (produced : Multiset (Term signature)) : Prop :=
  ∃ assignment : Subst signature,
    Unifies assignment (bag.result (frames (FirstOrder.action signature)) s).knowledge ∧
      SourceAgrees s assignment source ∧ produced = outputBag bag.members assignment

theorem batchResultModel_iff (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (own : bag.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (source : Subst signature) (produced : Multiset (Term signature)) :
    BatchResultModel s bag source produced ↔
      Unifies source s.knowledge ∧ Emissions s.label source (bag.keysBy identity) produced := by
  have members := fun m inside => Bag.admits_member (frames (FirstOrder.action signature))
    (fun _ _ => ⟨Subst.id signature⟩) own (m := m) inside
  constructor
  · rintro ⟨assignment, solved, agrees, rfl⟩
    obtain ⟨knowledge, memberModels⟩ := (models_bag_iff s bag assignment).mp solved
    refine ⟨?_, emissions_of_assignment s bag.members source assignment members memberModels agrees⟩
    intro equation member
    rw [← agrees equation.1 (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)),
      ← agrees equation.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)))]
    exact knowledge equation member
  · rintro ⟨knowledge, emits⟩
    have realized : Realized (frames (FirstOrder.action signature)) PUnit.unit bag.members
        (fun assignment => SourceAgrees s assignment source) := by
      simpa only [frames, Interface.Frames.ofSubstitution, ext, Extensions.identity, FirstOrder.action,
        Subst.applyTerm_id, SourceAgrees] using own.1.1 PUnit.unit source
    obtain ⟨assignment, agrees, memberModels, output⟩ :=
      assignment_of_emissions s bag.members source knowledge members _ produced (fun _ h => h) realized emits
    refine ⟨assignment, (models_bag_iff s bag assignment).mpr ⟨?_, memberModels⟩, agrees, output⟩
    intro equation member
    rw [agrees equation.1 (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)),
      agrees equation.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)))]
    exact knowledge equation member

theorem complete_batch_result_models (s : State (Terms (Term signature)) O)
    (region : Class signature O → Prop)
    (first second : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (firstComplete : first.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (secondComplete : second.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (source : Subst signature) (produced : Multiset (Term signature)) :
    BatchResultModel s first source produced ↔ BatchResultModel s second source produced := by
  rw [batchResultModel_iff s first firstComplete.1, batchResultModel_iff s second secondComplete.1]
  exact and_congr_right fun _ => emissions_perm_iff
    (firstComplete.keys_perm (fun _ _ => ⟨Subst.id signature⟩) secondComplete) produced

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
