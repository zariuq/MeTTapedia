import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchResults

/-!
# Ambient rule presentations offer the same symmetric CMR matches

Profile: one first-order occurrence-bag store, ambient rule sets, guards after
tells. Renamed copies do not add operational match classes. This does not
erase named rule occurrences or establish an arbitrary raw-code observer law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' Q : Program (Terms (Term signature))}

def offered (P : Program (Terms (Term signature))) (s : State (Terms (Term signature)) O)
    (key : Class signature O) : Prop :=
  ∃ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
    f.Admits (frames (FirstOrder.action signature)) s ∧ identity.key f = key

def reprogram {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a)
    (member : f.rule ∈ P') : Firing O (ext (FirstOrder.action signature)) P' a :=
  ⟨f.rule, member, f.ext, f.opening, f.selection, f.seen⟩

theorem reprogram_admission (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) (member : f.rule ∈ P') :
    (reprogram f member).Admits (frames (FirstOrder.action signature)) s ↔
      f.Admits (frames (FirstOrder.action signature)) s := Iff.rfl

omit [DecidableEq O] in
theorem reprogram_key {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a)
    (member : f.rule ∈ P') : identity.key (reprogram f member) = identity.key f := rfl

theorem offered_union (s : State (Terms (Term signature)) O) (key : Class signature O) :
    offered (P ∪ Q) s key ↔ offered P s key ∨ offered Q s key := by
  constructor
  · rintro ⟨f, admitted, same⟩
    rcases f.member with left | right
    · exact Or.inl ⟨reprogram f left, admitted, same⟩
    · exact Or.inr ⟨reprogram f right, admitted, same⟩
  · rintro (⟨f, admitted, same⟩ | ⟨f, admitted, same⟩)
    · exact ⟨reprogram f (Or.inl f.member), admitted, same⟩
    · exact ⟨reprogram f (Or.inr f.member), admitted, same⟩

def renamedProgram (names : Names signature.vars) (P : Program (Terms (Term signature))) :
    Program (Terms (Term signature)) := (renameRule names.forward) '' P

theorem renamedProgram_member (names : Names signature.vars)
    {rule : Rule (Terms (Term signature))} (member : rule ∈ P) :
    renameRule names.forward rule ∈ renamedProgram names P := ⟨rule, member, rfl⟩

def pullFiring (names : Names signature.vars) {a : PUnit}
    (f : Firing O (ext (FirstOrder.action signature)) P' a)
    (rule : Rule (Terms (Term signature))) (member : rule ∈ P) :
    Firing O (ext (FirstOrder.action signature)) P a :=
  ⟨rule, member, f.ext, fun v => f.opening (names.forward v), f.selection, f.seen⟩

theorem pullFiring_admission (names : Names signature.vars)
    (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (rule : Rule (Terms (Term signature))) (member : rule ∈ P)
    (same : f.rule = renameRule names.forward rule) :
    f.Admits (frames (FirstOrder.action signature)) s ↔
      (pullFiring names f rule member).Admits (frames (FirstOrder.action signature)) s := by
  cases f with
  | mk source sourceMember extension opening selection seen =>
    dsimp at same
    subst source
    exact (RuleOccurrences.renamed_firing (frames (FirstOrder.action signature)) rule
      (fun v => Term.var (names.forward v)) (fun v => Term.var (names.backward v))
      (fun term _ => UnificationRenaming.rename_leftInverse _ _ names.inverse term)
      member sourceMember s extension opening selection seen).1

omit [DecidableEq O] in
theorem pullFiring_key (names : Names signature.vars) {a : PUnit}
    (f : Firing O (ext (FirstOrder.action signature)) P' a)
    (rule : Rule (Terms (Term signature))) (member : rule ∈ P)
    (same : f.rule = renameRule names.forward rule) :
    identity.key f = identity.key (pullFiring names f rule member) := by
  have inTarget : renameRule names.forward rule ∈ P' := by rw [← same]; exact f.member
  have presentations : presentation f =
      presentation (renameFiring names (pullFiring names f rule member) inTarget) := by
    simp only [presentation, renameFiring, pullFiring]
    rw [same]
  rw [show identity.key f = identity.key
      (renameFiring names (pullFiring names f rule member) inTarget) from congrArg Presentation.key presentations]
  exact renameFiring_key names _ inTarget

theorem offered_renamed (names : Names signature.vars) (s : State (Terms (Term signature)) O)
    (key : Class signature O) : offered (renamedProgram names P) s key ↔ offered P s key := by
  constructor
  · rintro ⟨f, admitted, keyEq⟩
    obtain ⟨rule, member, ruleEq⟩ := f.member
    refine ⟨pullFiring names f rule member, (pullFiring_admission names s f rule member ruleEq.symm).mp admitted, ?_⟩
    exact (pullFiring_key names f rule member ruleEq.symm).symm.trans keyEq
  · rintro ⟨f, admitted, keyEq⟩
    have inTarget : renameRule names.forward f.rule ∈ renamedProgram names P := ⟨f.rule, f.member, rfl⟩
    exact ⟨renameFiring names f inTarget, (renameFiring_admission_result names s f inTarget).1.mp admitted,
      (renameFiring_key names f inTarget).trans keyEq⟩

theorem offered_with_renamed_copies (names : Names signature.vars)
    (s : State (Terms (Term signature)) O) (key : Class signature O) :
    offered (P ∪ renamedProgram names P) s key ↔ offered P s key := by
  rw [offered_union, offered_renamed]
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem offered_duplicate (s : State (Terms (Term signature)) O) (key : Class signature O) :
    offered (P ∪ P) s key ↔ offered P s key := by
  rw [offered_union]
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem complete_keys_perm_of_offers (s : State (Terms (Term signature)) O)
    (region : Class signature O → Prop)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstComplete : first.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (secondComplete : second.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (same : ∀ key, offered P s key ↔ offered P' s key) :
    (first.keysBy identity).Perm (second.keysBy identity) := by
  apply (List.perm_ext_iff_of_nodup firstComplete.2.2.1 secondComplete.2.2.1).mpr
  intro key
  constructor
  · intro member
    obtain ⟨m, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨f, admitted, keyEq⟩ := (same _).mp ⟨m.firing,
      Bag.admits_member _ (fun _ _ => ⟨Subst.id signature⟩) firstComplete.1 inside, rfl⟩
    rw [← keyEq]
    exact secondComplete.2.2.2 f (keyEq.symm ▸ firstComplete.2.1 _ member) admitted
  · intro member
    obtain ⟨m, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨f, admitted, keyEq⟩ := (same _).mpr ⟨m.firing,
      Bag.admits_member _ (fun _ _ => ⟨Subst.id signature⟩) secondComplete.1 inside, rfl⟩
    rw [← keyEq]
    exact firstComplete.2.2.2 f (keyEq.symm ▸ secondComplete.2.1 _ member) admitted

theorem complete_results_of_offers (s : State (Terms (Term signature)) O)
    (region : Class signature O → Prop)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstComplete : first.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (secondComplete : second.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (same : ∀ key, offered P s key ↔ offered P' s key)
    (source : Subst signature) (produced : Multiset (Term signature)) :
    BatchResultModel s first source produced ↔ BatchResultModel s second source produced := by
  rw [batchResultModel_iff s first firstComplete.1, batchResultModel_iff s second secondComplete.1]
  exact and_congr_right fun _ => emissions_perm_iff
    (complete_keys_perm_of_offers s region first second firstComplete secondComplete same) produced

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
