import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricTransport

/-!
# Local-coordinate changes of jointly fresh CMR members

Profile: one first-order occurrence-bag store, ambient programs, finite bags,
guards at each member's own information after tells. A coordinate certificate
compares local valuations and opened syntax. Joint freshness, admission and
results are consequences, not fields of the certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type}
  {P P' : Program (Terms (Term signature))} {a : PUnit}
  {x : (ext (FirstOrder.action signature)).Ext a}

def LocalValues (m : Member O (ext (FirstOrder.action signature)) P x)
    (assignment locals : Subst signature) : Prop :=
  ∀ term ∈ m.rule.terms,
    assignment.applyTerm (m.opening.applyTerm term) = locals.applyTerm term

structure MemberCoordinates
    (first : Member O (ext (FirstOrder.action signature)) P x)
    (second : Member O (ext (FirstOrder.action signature)) P' x) where
  selection : first.selection = second.selection
  seen : first.seen = second.seen
  arities : first.rule.body.take.length = second.rule.body.take.length ∧
    first.rule.body.read.length = second.rule.body.read.length ∧
    first.rule.body.produce.length = second.rule.body.produce.length ∧
    first.rule.collect.length = second.rule.collect.length
  opened : first.firing.opened (frames (FirstOrder.action signature)) =
    second.firing.opened (frames (FirstOrder.action signature))
  collect : first.firing.collectOpened (frames (FirstOrder.action signature)) =
    second.firing.collectOpened (frames (FirstOrder.action signature))
  toFirst : Subst signature → Subst signature
  toSecond : Subst signature → Subst signature
  right : ∀ locals assignment, LocalValues first assignment (toFirst locals) →
    LocalValues second assignment locals
  left : ∀ locals assignment, LocalValues second assignment (toSecond locals) →
    LocalValues first assignment locals

def MemberCoordinates.symm
    {first : Member O (ext (FirstOrder.action signature)) P x}
    {second : Member O (ext (FirstOrder.action signature)) P' x}
    (c : MemberCoordinates first second) : MemberCoordinates second first where
  selection := c.selection.symm
  seen := c.seen.symm
  arities := ⟨c.arities.1.symm, c.arities.2.1.symm, c.arities.2.2.1.symm, c.arities.2.2.2.symm⟩
  opened := c.opened.symm
  collect := c.collect.symm
  toFirst := c.toSecond
  toSecond := c.toFirst
  right := c.left
  left := c.right

def coordinates_of_renaming (names : Names signature.vars)
    (first : Member O (ext (FirstOrder.action signature)) P x)
    (second : Member O (ext (FirstOrder.action signature)) P' x)
    (rule : second.rule = renameRule names.forward first.rule)
    (selection : first.selection = second.selection) (seen : first.seen = second.seen)
    (opening : ∀ term ∈ first.rule.terms,
      second.opening.applyTerm (UnificationRenaming.rename names.forward term) =
        first.opening.applyTerm term) : MemberCoordinates first second := by
  let forward : Subst signature := fun v => .var (names.forward v)
  let backward : Subst signature := fun v => .var (names.backward v)
  have terms : second.rule.terms = first.rule.terms.map forward.applyTerm := by
    rw [rule]
    exact RuleOccurrences.terms_renamed (frames (FirstOrder.action signature)) first.rule forward
  have alike := RuleOccurrences.map_congr_terms (frames (FirstOrder.action signature)) first.rule
    (c := PUnit.unit)
    first.opening (second.opening.comp forward)
    (fun term member => by
      change first.opening.applyTerm term = (second.opening.comp forward).applyTerm term
      rw [Subst.applyTerm_comp]
      exact (opening term member).symm)
  have mapped := RuleOccurrences.map_act_comp (frames (FirstOrder.action signature))
    (b := PUnit.unit) (c := PUnit.unit) forward second.opening first.rule.body
  have body : first.firing.opened (frames (FirstOrder.action signature)) =
      second.firing.opened (frames (FirstOrder.action signature)) := by
    change first.rule.body.map first.opening.applyTerm = second.rule.body.map second.opening.applyTerm
    rw [rule]
    exact alike.1.trans mapped.symm
  refine ⟨selection, seen, ?_, body, ?_, fun h => h.comp forward, fun h => h.comp backward, ?_, ?_⟩
  · rw [rule]
    exact ⟨(List.length_map _).symm, (List.length_map _).symm,
      (List.length_map _).symm, (List.length_map _).symm⟩
  · change first.rule.collect.map first.opening.applyTerm = second.rule.collect.map second.opening.applyTerm
    rw [rule]
    change first.rule.collect.map first.opening.applyTerm =
      (first.rule.collect.map forward.applyTerm).map second.opening.applyTerm
    rw [List.map_map]
    apply List.map_congr_left
    intro term member
    exact (opening term (by simp [Rule.terms, member])).symm
  · intro locals assignment values term inside
    rw [terms] at inside
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp inside
    have openOld : second.opening.applyTerm (forward.applyTerm old) = first.opening.applyTerm old :=
      opening old member
    rw [openOld]
    exact (values old member).trans (Subst.applyTerm_comp _ _ _)
  · intro locals assignment values term member
    have inTarget : forward.applyTerm term ∈ second.rule.terms := by
      rw [terms]
      exact List.mem_map.mpr ⟨term, member, rfl⟩
    have value := values (forward.applyTerm term) inTarget
    change assignment.applyTerm (second.opening.applyTerm (forward.applyTerm term)) =
      (locals.comp backward).applyTerm (forward.applyTerm term) at value
    have openTerm : second.opening.applyTerm (forward.applyTerm term) = first.opening.applyTerm term :=
      opening term member
    rw [openTerm, Subst.applyTerm_comp locals backward] at value
    have undo : backward.applyTerm (forward.applyTerm term) = term :=
      UnificationRenaming.rename_leftInverse _ _ names.inverse term
    rwa [undo] at value

theorem realized_coordinates
    {first : List (Member O (ext (FirstOrder.action signature)) P x)}
    {second : List (Member O (ext (FirstOrder.action signature)) P' x)}
    (related : List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) first second)
    (Q : Subst signature → Prop) :
    Realized (frames (FirstOrder.action signature)) PUnit.unit first Q ↔
      Realized (frames (FirstOrder.action signature)) PUnit.unit second Q := by
  induction related generalizing Q with
  | nil => rfl
  | @cons m n rest later relatedHead relatedTail ih =>
    obtain ⟨c⟩ := relatedHead
    constructor
    · intro realized locals
      have h := (ih _).mp (realized (c.toFirst locals))
      exact Realized.mono _ _ (fun assignment both => ⟨both.1, c.right locals assignment both.2⟩) h
    · intro realized locals
      have h := (ih _).mpr (realized (c.toSecond locals))
      exact Realized.mono _ _ (fun assignment both => ⟨both.1, c.left locals assignment both.2⟩) h

def coordinates_rename (names : Names signature.vars)
    (m : Member O (ext (FirstOrder.action signature)) P x)
    (member : renameRule names.forward m.rule ∈ P') :
    MemberCoordinates m (Member.ofFiring (renameFiring names m.firing member)) := by
  let forward : Subst signature := fun v => .var (names.forward v)
  let backward : Subst signature := fun v => .var (names.backward v)
  let newOpening : Subst signature := m.opening.comp backward
  have combined : newOpening.comp forward = m.opening := by
    funext v
    change m.opening (names.backward (names.forward v)) = m.opening v
    rw [names.inverse v]
  have opened : m.firing.opened (frames (FirstOrder.action signature)) =
      (renameFiring names m.firing member).opened (frames (FirstOrder.action signature)) := by
    have mapped := RuleOccurrences.map_act_comp (frames (FirstOrder.action signature))
      (b := PUnit.unit) (c := PUnit.unit) forward newOpening m.rule.body
    change m.rule.body.map m.opening.applyTerm =
      (m.rule.body.map forward.applyTerm).map newOpening.applyTerm
    change (m.rule.body.map forward.applyTerm).map newOpening.applyTerm =
      m.rule.body.map (newOpening.comp forward).applyTerm at mapped
    rw [mapped, combined]
  have terms : (renameRule names.forward m.rule).terms =
      m.rule.terms.map (UnificationRenaming.rename names.forward) :=
    RuleOccurrences.terms_renamed (frames (FirstOrder.action signature)) m.rule
      (fun v => Term.var (names.forward v))
  refine ⟨rfl, rfl, ?_, opened, ?_,
    fun h => h.comp forward, fun h => h.comp backward, ?_, ?_⟩
  · exact ⟨(List.length_map _).symm, (List.length_map _).symm,
      (List.length_map _).symm, (List.length_map _).symm⟩
  · change m.rule.collect.map m.opening.applyTerm =
      (m.rule.collect.map (UnificationRenaming.rename names.forward)).map
        newOpening.applyTerm
    rw [List.map_map]
    apply List.map_congr_left
    intro term _
    change m.opening.applyTerm term = newOpening.applyTerm (forward.applyTerm term)
    rw [← Subst.applyTerm_comp, combined]
  · intro locals assignment values term inside
    change term ∈ (renameRule names.forward m.rule).terms at inside
    rw [terms] at inside
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp inside
    change assignment.applyTerm (newOpening.applyTerm (forward.applyTerm old)) = _
    rw [← Subst.applyTerm_comp newOpening forward old, combined]
    exact (values old member).trans (Subst.applyTerm_comp _ _ _)
  · intro locals assignment values term member
    have inTarget : UnificationRenaming.rename names.forward term ∈
        (renameRule names.forward m.rule).terms := by
      rw [terms]
      exact List.mem_map.mpr ⟨term, member, rfl⟩
    have value := values (UnificationRenaming.rename names.forward term) inTarget
    change assignment.applyTerm (newOpening.applyTerm (forward.applyTerm term)) =
      (locals.comp backward).applyTerm (forward.applyTerm term) at value
    rw [← Subst.applyTerm_comp newOpening forward term, combined] at value
    rw [Subst.applyTerm_comp locals backward] at value
    have undo : backward.applyTerm (forward.applyTerm term) = term :=
      UnificationRenaming.rename_leftInverse _ _ names.inverse term
    rwa [undo] at value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
