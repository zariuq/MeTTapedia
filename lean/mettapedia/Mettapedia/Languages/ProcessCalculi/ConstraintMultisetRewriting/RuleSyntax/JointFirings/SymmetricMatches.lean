import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MatchIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.UnificationRenaming
import Mathlib.Logic.Relation

/-!
# Symmetric match classes for first-order CMR

Profile: one occurrence-bag store, ambient rule sets, completeness/uniqueness
over bags admitted by the existing own-information judgment (after tells).
The ordered-key profile remains separate. Local names are quotiented through
lossless coordinate changes; resource occurrence identities are not erased.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type}

/-- A name change with a checked inverse on its image. Unused coordinates
need not be in that image. -/
structure Names (Variable : Type*) where
  forward : Variable → Variable
  backward : Variable → Variable
  inverse : Function.LeftInverse backward forward

def Names.identity (Variable : Type*) : Names Variable := ⟨id, id, fun _ => rfl⟩

def renameRule (names : signature.vars → signature.vars)
    (rule : Rule (Terms (Term signature))) : Rule (Terms (Term signature)) :=
  ⟨rule.locals, rule.body.map (UnificationRenaming.rename names),
    rule.collect.map (UnificationRenaming.rename names)⟩

/-- Source patterns remain paired with the actual resource occurrences.
Take/read polarity and repeated read occurrences are retained. -/
structure Presentation (signature : LPSignature) (O : Type) where
  rule : Rule (Terms (Term signature))
  takes : Multiset (Term signature × O)
  reads : Multiset (Term signature × O)

def Presentation.rename (names : signature.vars → signature.vars)
    (match_ : Presentation signature O) : Presentation signature O :=
  ⟨renameRule names match_.rule,
    match_.takes.map (fun pair => (UnificationRenaming.rename names pair.1, pair.2)),
    match_.reads.map (fun pair => (UnificationRenaming.rename names pair.1, pair.2))⟩

/-- The generators change local names consistently in every position. -/
def Renamed (first second : Presentation signature O) : Prop :=
  ∃ names : Names signature.vars, second = first.rename names.forward

abbrev Same (first second : Presentation signature O) : Prop :=
  Relation.EqvGen Renamed first second

def matchSetoid (signature : LPSignature) (O : Type) : Setoid (Presentation signature O) :=
  Relation.EqvGen.setoid Renamed

abbrev Class (signature : LPSignature) (O : Type) := Quotient (matchSetoid signature O)

def Presentation.key (match_ : Presentation signature O) : Class signature O :=
  Quotient.mk _ match_

theorem key_eq_iff (first second : Presentation signature O) :
    first.key = second.key ↔ Same first second := Quotient.eq

theorem rename_key (names : Names signature.vars) (match_ : Presentation signature O) :
    (match_.rename names.forward).key = match_.key := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨names, rfl⟩)

variable {P : Program (Terms (Term signature))}

def presentation {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a) :
    Presentation signature O :=
  ⟨f.rule, (f.rule.body.take.zip f.selection.taken : List (Term signature × O)),
    (f.rule.body.read.zip f.selection.read : List (Term signature × O))⟩

def identity : MatchIdentity O (ext (FirstOrder.action signature)) P where
  Key := Class signature O
  key f := (presentation f).key

/-- Permuting assignments of identical source patterns preserves their
pair bags, rather than forgetting which different pattern selected a row. -/
theorem key_eq_of_pair_perms {a : PUnit}
    (f g : Firing O (ext (FirstOrder.action signature)) P a)
    (sameRule : f.rule = g.rule)
    (takes : (f.rule.body.take.zip f.selection.taken).Perm
      (g.rule.body.take.zip g.selection.taken))
    (reads : (f.rule.body.read.zip f.selection.read).Perm
      (g.rule.body.read.zip g.selection.read)) :
    identity.key f = identity.key g := by
  apply congrArg Presentation.key
  simp only [presentation, Presentation.mk.injEq]
  exact ⟨sameRule, Multiset.coe_eq_coe.mpr takes, Multiset.coe_eq_coe.mpr reads⟩

/-- Occurrence bags are invariants of local-name changes. This does not
collapse equal-valued resources at different identities. -/
theorem Same.taken_occurrences {first second : Presentation signature O}
    (same : Same first second) : first.takes.map Prod.snd = second.takes.map Prod.snd := by
  induction same with
  | rel first second change =>
    obtain ⟨names, rfl⟩ := change
    simp [Presentation.rename, Multiset.map_map]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem Same.read_occurrences {first second : Presentation signature O}
    (same : Same first second) : first.reads.map Prod.snd = second.reads.map Prod.snd := by
  induction same with
  | rel first second change =>
    obtain ⟨names, rfl⟩ := change
    simp [Presentation.rename, Multiset.map_map]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem Same.production_length {first second : Presentation signature O}
    (same : Same first second) : first.rule.body.produce.length = second.rule.body.produce.length := by
  induction same with
  | rel first second change =>
    obtain ⟨names, rfl⟩ := change
    simp [Presentation.rename, renameRule, RuleInstance.map]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

def taken (key : Class signature O) : Multiset O :=
  Quotient.liftOn key (fun match_ => match_.takes.map Prod.snd)
    (fun _ _ same => Same.taken_occurrences same)

def productionArity (key : Class signature O) : Nat :=
  Quotient.liftOn key (fun match_ => match_.rule.body.produce.length)
    (fun _ _ same => Same.production_length same)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
