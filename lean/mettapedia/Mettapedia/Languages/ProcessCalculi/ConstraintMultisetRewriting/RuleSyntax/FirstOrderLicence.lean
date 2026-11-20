import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# The first-order solver licence at actual CMR firing judgments

Profile: one occurrence-bag store, ambient rules, the existing one-match
judgment, guards after its own tells. Only the universal guard/collect clause
is decided here. Shapes, freshness and linear-resource admission are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderLicence

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature}
  [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]
  {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

abbrev action := FirstOrder.action signature

def firingChecks (answer : Subst signature) (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) : Bool :=
  ((f.opened (frames (FirstOrder.action signature))).checks.all
    (ConstraintMultisetRewriting.FirstOrderLicence.check answer
      (f.row (frames (FirstOrder.action signature)) s) s.present)) &&
  (((f.collectOpened (frames (FirstOrder.action signature))).zip f.seen).all fun query =>
    ConstraintMultisetRewriting.FirstOrderLicence.collect answer
      (f.row (frames (FirstOrder.action signature)) s) s.present query.1 query.2)

theorem firingChecks_correct (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (answer : Subst signature)
    (accepted : unifyTotal (f.information (frames (FirstOrder.action signature)) s) = some answer) :
    firingChecks answer s f = true ↔
      (frames (FirstOrder.action signature)).Entails
        (f.information (frames (FirstOrder.action signature)) s)
        (fun b assignment => f.Holds (frames (FirstOrder.action signature)) s (b := b) assignment) := by
  simp only [firingChecks, Bool.and_eq_true, List.all_eq_true,
    ConstraintMultisetRewriting.FirstOrderLicence.check_correct accepted,
    ConstraintMultisetRewriting.FirstOrderLicence.collect_correct accepted]
  constructor
  · rintro ⟨checks, queries⟩ b assignment solved
    refine ⟨?_, ?_⟩
    · intro condition member
      exact (OneFrame.checkHolds_iff (A := FirstOrder.action signature) s.present condition).mpr
        (checks condition member assignment solved)
    · intro query member
      rw [OneFrame.matchesAt_eq]
      exact queries query member assignment solved
  · intro holds
    refine ⟨?_, ?_⟩
    · intro condition member assignment solved
      exact (OneFrame.checkHolds_iff (A := FirstOrder.action signature) s.present condition).mp
        ((holds PUnit.unit assignment solved).1 condition member)
    · intro query member assignment solved
      have collect := (holds PUnit.unit assignment solved).2 query member
      rwa [OneFrame.matchesAt_eq] at collect

theorem admits_iff_checked (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (answer : Subst signature)
    (accepted : unifyTotal (f.information (frames (FirstOrder.action signature)) s) = some answer) :
    f.Admits (frames (FirstOrder.action signature)) s ↔
      f.Shapes (frames (FirstOrder.action signature)) s ∧
        MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) s.present
          (f.selection.commit (T := Unit)) ∧ firingChecks answer s f = true := by
  have solvable : (frames (FirstOrder.action signature)).Solvable
      (f.information (frames (FirstOrder.action signature)) s) :=
    ⟨PUnit.unit, answer, unifyTotal_sound _ _ accepted⟩
  rw [firingChecks_correct s f answer accepted]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩,
    fun h => ⟨h.1, h.2.1, solvable, h.2.2⟩⟩

theorem unsolvable_refuses (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (refused : unifyTotal (f.information (frames (FirstOrder.action signature)) s) = none) :
    ¬ f.Admits (frames (FirstOrder.action signature)) s := by
  intro admitted
  obtain ⟨_, answer, solved⟩ := admitted.2.2.1
  exact (unifyTotal_none_iff_not_unifiable _).mp refused ⟨answer, solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderLicence
