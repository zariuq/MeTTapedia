import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.PatternAssignmentOrder

/-!
# Permuting identical-pattern assignments preserves actual CMR admission

Profile: one first-order occurrence-bag store, ambient rules, one-match
admission with guards after tells. The rule, opening, collect claims and made
occurrences stay fixed. Selected occurrences are changed only when the bags
of source-pattern/occurrence pairs are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

def reselect {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a)
    (taken read : List O) : Firing O (ext (FirstOrder.action signature)) P a :=
  ⟨f.rule, f.member, f.ext, f.opening, ⟨taken, read, f.selection.made⟩, f.seen⟩

omit [DecidableEq O] in
theorem reselect_information_perm (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) (taken read : List O)
    (takes : (f.rule.body.take.zip f.selection.taken).Perm (f.rule.body.take.zip taken))
    (reads : (f.rule.body.read.zip f.selection.read).Perm (f.rule.body.read.zip read)) :
    (f.information (frames (FirstOrder.action signature)) s).Perm
      ((reselect f taken read).information (frames (FirstOrder.action signature)) s) := by
  rw [information_eq, information_eq]
  exact (((List.Perm.refl _).append (takes.map _)).append (reads.map _)).append (List.Perm.refl _)

theorem reselect_admitted_iff (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) (taken read : List O)
    (takenPerm : f.selection.taken.Perm taken) (readPerm : f.selection.read.Perm read)
    (takes : (f.rule.body.take.zip f.selection.taken).Perm (f.rule.body.take.zip taken))
    (reads : (f.rule.body.read.zip f.selection.read).Perm (f.rule.body.read.zip read)) :
    f.Admits (frames (FirstOrder.action signature)) s ↔
      (reselect f taken read).Admits (frames (FirstOrder.action signature)) s := by
  have information := reselect_information_perm s f taken read takes reads
  have models : ∀ b (assignment : Subst signature),
      (frames (FirstOrder.action signature)).Models (b := b) assignment
        (f.information (frames (FirstOrder.action signature)) s) ↔
      (frames (FirstOrder.action signature)).Models (b := b) assignment
        ((reselect f taken read).information (frames (FirstOrder.action signature)) s) := by
    intro b assignment
    exact ⟨fun solved e member => solved e (information.mem_iff.mpr member),
      fun solved e member => solved e (information.mem_iff.mp member)⟩
  have shapes : f.Shapes (frames (FirstOrder.action signature)) s ↔
      (reselect f taken read).Shapes (frames (FirstOrder.action signature)) s := by
    change (f.Fresh _ s ∧ f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
      f.rule.body.take.length = f.selection.taken.length ∧ f.rule.body.read.length = f.selection.read.length ∧
      f.rule.body.produce.length = f.selection.made.length ∧ f.rule.collect.length = f.seen.length) ↔
      (f.Fresh _ s ∧ taken.Nodup ∧ f.selection.made.Nodup ∧
      f.rule.body.take.length = taken.length ∧ f.rule.body.read.length = read.length ∧
      f.rule.body.produce.length = f.selection.made.length ∧ f.rule.collect.length = f.seen.length)
    rw [takenPerm.nodup_iff, takenPerm.length_eq, readPerm.length_eq]
  have commit : f.selection.commit (T := Unit) = (reselect f taken read).selection.commit := by
    have takenSet : f.selection.taken.toFinset = taken.toFinset :=
      Finset.ext fun o => by simpa only [List.mem_toFinset] using (takenPerm.mem_iff (a := o))
    have readSet : f.selection.read.toFinset = read.toFinset :=
      Finset.ext fun o => by simpa only [List.mem_toFinset] using (readPerm.mem_iff (a := o))
    unfold Selection.commit
    simp only [reselect, takenSet, readSet]
  unfold Firing.Admits
  rw [shapes, commit]
  constructor
  · rintro ⟨shape, enabled, ⟨b, assignment, solved⟩, guards⟩
    exact ⟨shape, enabled, ⟨b, assignment, (models b assignment).mp solved⟩,
      fun b assignment solved => guards b assignment ((models b assignment).mpr solved)⟩
  · rintro ⟨shape, enabled, ⟨b, assignment, solved⟩, guards⟩
    exact ⟨shape, enabled, ⟨b, assignment, (models b assignment).mpr solved⟩,
      fun b assignment solved => guards b assignment ((models b assignment).mp solved)⟩

omit [DecidableEq O] in
theorem reselect_key {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a)
    (taken read : List O)
    (takes : (f.rule.body.take.zip f.selection.taken).Perm (f.rule.body.take.zip taken))
    (reads : (f.rule.body.read.zip f.selection.read).Perm (f.rule.body.read.zip read)) :
    identity.key f = identity.key (reselect f taken read) :=
  key_eq_of_pair_perms f (reselect f taken read) rfl takes reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
