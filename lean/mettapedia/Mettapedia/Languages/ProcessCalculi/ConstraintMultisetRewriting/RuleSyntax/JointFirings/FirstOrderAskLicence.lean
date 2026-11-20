import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderLicence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTiming

/-!
# The first-order solver licence at a bag's declared ask boundary

The same guard code can be checked against the whole bag problem or against
its pre-tell ask problem. Full information must still solve in either case.
Freshness, shapes and resource enabling are retained independently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderAskLicence

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {O : Type} [DecidableEq O] {P : Program (Terms (Term signature))}

abbrev X := frames (FirstOrder.action signature)

def checks (answer : Subst signature) (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) : Bool :=
  bag.members.all fun member => RuleSyntax.FirstOrderLicence.firingChecks answer s member.firing

theorem checks_correct (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (problem : EquationStore (Term signature)) (answer : Subst signature)
    (accepted : unifyTotal problem = some answer) :
    checks answer s bag = true ↔ X.Entails (a := PUnit.unit) problem
      (fun b assignment => bag.Holds X s (b := b) assignment) := by
  simp only [checks, List.all_eq_true, RuleSyntax.FirstOrderLicence.firingChecks,
    Bool.and_eq_true, List.all_eq_true,
    ConstraintMultisetRewriting.FirstOrderLicence.check_correct accepted,
    ConstraintMultisetRewriting.FirstOrderLicence.collect_correct accepted]
  constructor
  · intro checked b assignment solved member inside
    obtain ⟨guards, collects⟩ := checked member inside
    refine ⟨?_, ?_⟩
    · intro guard present
      exact (OneFrame.checkHolds_iff (A := FirstOrder.action signature) s.present guard).mpr
        (guards guard present assignment solved)
    · intro query present
      rw [OneFrame.matchesAt_eq]
      exact collects query present assignment solved
  · intro held member inside
    refine ⟨?_, ?_⟩
    · intro guard present assignment solved
      exact (OneFrame.checkHolds_iff (A := FirstOrder.action signature) s.present guard).mp
        ((held PUnit.unit assignment solved member inside).1 guard present)
    · intro query present assignment solved
      have collect := (held PUnit.unit assignment solved member inside).2 query present
      rwa [OneFrame.matchesAt_eq] at collect

theorem after_tells_iff_checked (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) (answer : Subst signature)
    (accepted : unifyTotal (bag.information X s) = some answer) :
    bag.Admits X s ↔ bag.Fits X s ∧
      MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) s.present (bag.selection.commit (T := Unit)) ∧
      checks answer s bag = true := by
  have solvable : X.Solvable (bag.information X s) := ⟨PUnit.unit, answer, unifyTotal_sound _ _ accepted⟩
  rw [checks_correct s bag _ answer accepted]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact ⟨fun yes => ⟨yes.1, yes.2.1, yes.2.2.2⟩,
    fun yes => ⟨yes.1, yes.2.1, solvable, yes.2.2⟩⟩

theorem before_tells_iff_checked (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) (fullAnswer askAnswer : Subst signature)
    (fullAccepted : unifyTotal (bag.information X s) = some fullAnswer)
    (askAccepted : unifyTotal (bag.askInformation X s) = some askAnswer) :
    bag.AdmitsBeforeTells X s ↔ bag.Fits X s ∧
      MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) s.present (bag.selection.commit (T := Unit)) ∧
      checks askAnswer s bag = true := by
  have solvable : X.Solvable (bag.information X s) := ⟨PUnit.unit, fullAnswer, unifyTotal_sound _ _ fullAccepted⟩
  rw [checks_correct s bag _ askAnswer askAccepted]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact ⟨fun yes => ⟨yes.1, yes.2.1, yes.2.2.2⟩,
    fun yes => ⟨yes.1, yes.2.1, solvable, yes.2.2⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderAskLicence
