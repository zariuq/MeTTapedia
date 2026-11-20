import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicenceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.CanonicalMatches
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricAliases

/-!
# Positive and negative controls for symmetric CMR match identity

Profile: one first-order occurrence-bag store, ambient rules. The controls
retain pattern incidence, variable sharing, access polarity, duplicate resource
identities and repeated reads. Neither solving nor payload equality licenses
additional quotienting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches.Controls

open Mettapedia.Logic.LP
open OneFrame (Terms)
open FirstOrderLicence.Controls (signature c x y)

def rule (takes reads : List (Term signature)) : Rule (Terms (Term signature)) :=
  ⟨PUnit.unit, ⟨takes, reads, [], [], []⟩, []⟩

def pair : Presentation signature Nat :=
  ⟨rule [c 1, c 1] [], [(c 1, 0), (c 1, 1)], 0⟩
def swappedPair : Presentation signature Nat :=
  ⟨rule [c 1, c 1] [], [(c 1, 1), (c 1, 0)], 0⟩

theorem identical_patterns_merge : pair.key = swappedPair.key := by
  have pairs : ([(c 1, 0), (c 1, 1)] : Multiset (Term signature × Nat)) =
      [(c 1, 1), (c 1, 0)] := Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ [])
  unfold pair swappedPair
  rw [pairs]

def differentPatterns : Presentation signature Nat :=
  ⟨rule [x, y] [], [(x, 0), (y, 1)], 0⟩
def exchangedPatterns : Presentation signature Nat :=
  ⟨rule [x, y] [], [(x, 1), (y, 0)], 0⟩

theorem distinct_patterns_do_not_exchange : differentPatterns.key ≠ exchangedPatterns.key := by
  intro same
  have incidence := Same.take_incidence (Quotient.exact same)
  exact (by cbv; decide : takeIncidence differentPatterns ≠ takeIncidence exchangedPatterns) incidence

theorem solving_does_not_authorize_another_quotient :
    (∀ assignment : Subst signature, Unifies assignment [(x, c 1), (y, c 1)] →
      assignment.applyTerm x = assignment.applyTerm y) ∧
      differentPatterns.key ≠ exchangedPatterns.key := by
  refine ⟨?_, distinct_patterns_do_not_exchange⟩
  intro assignment solved
  exact (solved (x, c 1) (by simp)).trans (solved (y, c 1) (by simp)).symm

def shared : Presentation signature Nat :=
  ⟨rule [x, x] [], [(x, 0), (x, 1)], 0⟩

theorem changed_sharing_is_not_renaming : shared.key ≠ differentPatterns.key := by
  intro same
  have sharing := Same.take_pattern_distinct (Quotient.exact same)
  exact (by simp [shared, rule] : ¬ shared.rule.body.take.Nodup)
    (sharing.mpr (by simp [differentPatterns, rule, x, y] : differentPatterns.rule.body.take.Nodup))

def anotherOccurrence : Presentation signature Nat :=
  ⟨rule [c 1, c 1] [], [(c 1, 0), (c 1, 2)], 0⟩

theorem equal_payloads_do_not_erase_occurrences : pair.key ≠ anotherOccurrence.key := by
  intro same
  have occurrences := Same.taken_occurrences (Quotient.exact same)
  exact (by decide : pair.takes.map Prod.snd ≠ anotherOccurrence.takes.map Prod.snd) occurrences

def peekPair : Presentation signature Nat :=
  ⟨rule [] [c 1, c 1], 0, [(c 1, 0), (c 1, 1)]⟩

theorem take_is_not_read : pair.key ≠ peekPair.key := by
  intro same
  have occurrences := Same.taken_occurrences (Quotient.exact same)
  exact (by decide : pair.takes.map Prod.snd ≠ peekPair.takes.map Prod.snd) occurrences

def repeatedRead : Presentation signature Nat :=
  ⟨rule [] [c 1, c 1], 0, [(c 1, 0), (c 1, 0)]⟩
def singleRead : Presentation signature Nat :=
  ⟨rule [] [c 1], 0, [(c 1, 0)]⟩

theorem repeat_read_is_not_single_read : repeatedRead.key ≠ singleRead.key := by
  intro same
  have occurrences := Same.read_occurrences (Quotient.exact same)
  exact (by decide : repeatedRead.reads.map Prod.snd ≠ singleRead.reads.map Prod.snd) occurrences

def shift : Names Nat := ⟨fun v => v + 7, fun v => v - 7, fun v => Nat.add_sub_cancel v 7⟩

theorem consistent_renaming_preserves_key : (differentPatterns.rename shift.forward).key = differentPatterns.key :=
  rename_key shift differentPatterns

def inconsistent : Presentation signature Nat :=
  ⟨renameRule shift.forward differentPatterns.rule, differentPatterns.takes, differentPatterns.reads⟩

theorem renaming_only_the_rule_is_unsound : inconsistent.key ≠ differentPatterns.key := by
  intro same
  have incidence := Same.take_incidence (Quotient.exact same)
  exact (by cbv; decide : takeIncidence inconsistent ≠ takeIncidence differentPatterns) incidence

theorem interleaved_pattern_groups_normalize :
    PatternAssignmentOrder.normalize ([0, 1, 0] : List Nat)
      ([(0, 4), (1, 2), (0, 1)] : Multiset (Nat × Nat)) = some [(0, 1), (1, 2), (0, 4)] := by decide

theorem read_repetition_survives_normalization :
    PatternAssignmentOrder.normalize ([0, 0] : List Nat)
      ([(0, 1), (0, 1)] : Multiset (Nat × Nat)) = some [(0, 1), (0, 1)] ∧
      ¬ PatternAssignmentOrder.StrictlyOrdered ([(0, 1), (0, 1)] : List (Nat × Nat)) := by
  constructor
  · decide
  · simp [PatternAssignmentOrder.StrictlyOrdered]

theorem unsorted_take_is_rejected_by_normal_form :
    ¬ PatternAssignmentOrder.Ordered ([(0, 1), (0, 0)] : List (Nat × Nat)) := by
  simp [PatternAssignmentOrder.Ordered]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches.Controls
