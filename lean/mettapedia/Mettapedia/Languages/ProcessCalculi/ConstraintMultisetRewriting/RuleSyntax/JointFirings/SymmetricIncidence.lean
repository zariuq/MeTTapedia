import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
import Mettapedia.Logic.LP.TermEquality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.PatternAssignmentOrder
import Mathlib.Data.Multiset.Filter

/-!
# Symmetric CMR classes retain source-pattern incidence and sharing

Local renaming preserves the occurrence bag associated with every source
pattern position. Distinct patterns cannot silently exchange selections;
identical patterns may exchange their assignments. The result does not use
equality that happens only after solving the matching equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP

variable {signature : LPSignature} {O : Type}
  [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def rowsFor (pairs : Multiset (Term signature × O)) (pattern : Term signature) : Multiset O :=
  (pairs.filter fun pair => pair.1 = pattern).map Prod.snd

theorem rowsFor_rename (names : Names signature.vars)
    (pairs : Multiset (Term signature × O)) (pattern : Term signature) :
    rowsFor (pairs.map (fun pair => (UnificationRenaming.rename names.forward pair.1, pair.2)))
      (UnificationRenaming.rename names.forward pattern) = rowsFor pairs pattern := by
  have injective := UnificationRenaming.rename_injective names.forward names.backward names.inverse
  induction pairs using Multiset.induction_on with
  | empty => simp [rowsFor]
  | cons pair rest ih =>
    change rowsFor (Multiset.map _ (pair ::ₘ rest)) _ = _
    by_cases same : pair.1 = pattern
    · simp only [rowsFor, Multiset.map_cons, Multiset.filter_cons, same,
        if_pos, Multiset.map_add, Multiset.map_singleton] at ih ⊢
      exact congrArg (fun rest => ({pair.2} : Multiset O) + rest) ih
    · have different : UnificationRenaming.rename names.forward pair.1 ≠
          UnificationRenaming.rename names.forward pattern := fun h => same (injective h)
      simp only [rowsFor, Multiset.map_cons, Multiset.filter_cons, same, different,
        if_false, Multiset.zero_add] at ih ⊢
      exact ih

def takeIncidence (match_ : Presentation signature O) : List (Multiset O) :=
  match_.rule.body.take.map (rowsFor match_.takes)

theorem takeIncidence_rename (names : Names signature.vars) (match_ : Presentation signature O) :
    takeIncidence (match_.rename names.forward) = takeIncidence match_ := by
  simp only [takeIncidence, Presentation.rename, renameRule, RuleInstance.map, List.map_map]
  exact List.map_congr_left fun pattern _ => rowsFor_rename names match_.takes pattern

def readIncidence (match_ : Presentation signature O) : List (Multiset O) :=
  match_.rule.body.read.map (rowsFor match_.reads)

theorem readIncidence_rename (names : Names signature.vars) (match_ : Presentation signature O) :
    readIncidence (match_.rename names.forward) = readIncidence match_ := by
  simp only [readIncidence, Presentation.rename, renameRule, RuleInstance.map, List.map_map]
  exact List.map_congr_left fun pattern _ => rowsFor_rename names match_.reads pattern

theorem Same.read_incidence {first second : Presentation signature O} (same : Same first second) :
    readIncidence first = readIncidence second := by
  induction same with
  | rel first second related =>
    obtain ⟨names, rfl⟩ := related
    exact (readIncidence_rename names first).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

theorem Same.take_incidence {first second : Presentation signature O} (same : Same first second) :
    takeIncidence first = takeIncidence second := by
  induction same with
  | rel first second related =>
    obtain ⟨names, rfl⟩ := related
    exact (takeIncidence_rename names first).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem Same.take_pattern_distinct {first second : Presentation signature O} (same : Same first second) :
    first.rule.body.take.Nodup ↔ second.rule.body.take.Nodup := by
  induction same with
  | rel first second related =>
    obtain ⟨names, rfl⟩ := related
    change first.rule.body.take.Nodup ↔
      (first.rule.body.take.map (UnificationRenaming.rename names.forward)).Nodup
    exact (List.nodup_map_iff
      (UnificationRenaming.rename_injective names.forward names.backward names.inverse)).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
