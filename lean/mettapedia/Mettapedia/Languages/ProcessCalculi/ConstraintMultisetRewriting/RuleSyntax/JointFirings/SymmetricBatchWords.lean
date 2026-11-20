import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchResults

/-!
# Correlated output words of a jointly fresh first-order CMR bag

Profile: one occurrence-bag store, ambient programs, guards at each member's
own information after tells. A common source assignment correlates all
members. The member word order is retained here; bag observers may forget it
only through the separate permutation laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

def outputWords {a : PUnit} {x : (ext (FirstOrder.action signature)).Ext a}
    (members : List (Member O (ext (FirstOrder.action signature)) P x))
    (assignment : Subst signature) : List (List (Term signature)) :=
  members.map fun m => (m.firing.opened (frames (FirstOrder.action signature))).produce.map assignment.applyTerm

def WordEmissions (label : O → Term signature) (source : Subst signature)
    (keys : List (Class signature O)) (words : List (List (Term signature))) : Prop :=
  List.Forall₂ (fun key word => realizes key label source word) keys words

theorem words_of_assignment (s : State (Terms (Term signature)) O)
    {x : (ext (FirstOrder.action signature)).Ext s.frame}
    (members : List (Member O (ext (FirstOrder.action signature)) P x))
    (source assignment : Subst signature)
    (admitted : ∀ m ∈ members, m.firing.Admits (frames (FirstOrder.action signature)) s)
    (models : ∀ m ∈ members, Unifies assignment (m.firing.information (frames (FirstOrder.action signature)) s))
    (agrees : SourceAgrees s assignment source) :
    WordEmissions s.label source (members.map fun m => identity.key m.firing) (outputWords members assignment) := by
  unfold WordEmissions outputWords
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro m member
  have model : ResultModel s m.firing source
      ((m.firing.opened (frames (FirstOrder.action signature))).produce.map assignment.applyTerm) :=
    ⟨assignment, models m member, agrees, rfl⟩
  exact ((resultModel_iff s m.firing (admitted m member) source _).mp model).2

theorem assignment_of_words (s : State (Terms (Term signature)) O)
    {x : (ext (FirstOrder.action signature)).Ext s.frame}
    (members : List (Member O (ext (FirstOrder.action signature)) P x))
    (source : Subst signature) (knowledge : Unifies source s.knowledge)
    (admitted : ∀ m ∈ members, m.firing.Admits (frames (FirstOrder.action signature)) s) :
    ∀ (Q : Subst signature → Prop) (words : List (List (Term signature))),
      (∀ assignment, Q assignment → SourceAgrees s assignment source) →
      Realized (frames (FirstOrder.action signature)) PUnit.unit members Q →
      WordEmissions s.label source (members.map fun m => identity.key m.firing) words →
      ∃ assignment, Q assignment ∧
        (∀ m ∈ members, Unifies assignment (m.firing.information (frames (FirstOrder.action signature)) s)) ∧
        words = outputWords members assignment := by
  induction members with
  | nil =>
    intro Q words _ realized emissions
    cases emissions
    change ∃ assignment : Subst signature, Q assignment at realized
    obtain ⟨assignment, holds⟩ := realized
    exact ⟨assignment, holds, fun _ member => False.elim (List.not_mem_nil member), rfl⟩
  | cons m rest ih =>
    intro Q words agrees realized emissions
    cases emissions with
    | @cons _ word _ _ here later =>
      change (presentation m.firing).Realizes s.label source word at here
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
        source locals assignment word knowledge pairs tells output (agrees assignment holds) values
      refine ⟨assignment, holds, ?_, ?_⟩
      · intro n member
        rcases List.mem_cons.mp member with rfl | inside
        · exact model
        · exact models n inside
      · rw [made, after]
        rfl

def WordResultModel (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (source : Subst signature) (words : List (List (Term signature))) : Prop :=
  ∃ assignment : Subst signature,
    Unifies assignment (bag.result (frames (FirstOrder.action signature)) s).knowledge ∧
      SourceAgrees s assignment source ∧ words = outputWords bag.members assignment

theorem wordResultModel_iff (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (own : bag.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (source : Subst signature) (words : List (List (Term signature))) :
    WordResultModel s bag source words ↔
      Unifies source s.knowledge ∧ WordEmissions s.label source (bag.keysBy identity) words := by
  have members := fun m inside => Bag.admits_member (frames (FirstOrder.action signature))
    (fun _ _ => ⟨Subst.id signature⟩) own (m := m) inside
  constructor
  · rintro ⟨assignment, solved, agrees, rfl⟩
    obtain ⟨knowledge, memberModels⟩ := (models_bag_iff s bag assignment).mp solved
    refine ⟨?_, words_of_assignment s bag.members source assignment members memberModels agrees⟩
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
      assignment_of_words s bag.members source knowledge members _ words (fun _ h => h) realized emits
    refine ⟨assignment, (models_bag_iff s bag assignment).mpr ⟨?_, memberModels⟩, agrees, output⟩
    intro equation member
    rw [agrees equation.1 (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)),
      agrees equation.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)))]
    exact knowledge equation member

theorem same_keys_word_models (s : State (Terms (Term signature)) O)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstOwn : first.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (secondOwn : second.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (keys : first.keysBy identity = second.keysBy identity)
    (source : Subst signature) (words : List (List (Term signature))) :
    WordResultModel s first source words ↔ WordResultModel s second source words := by
  rw [wordResultModel_iff s first firstOwn, wordResultModel_iff s second secondOwn, keys]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
