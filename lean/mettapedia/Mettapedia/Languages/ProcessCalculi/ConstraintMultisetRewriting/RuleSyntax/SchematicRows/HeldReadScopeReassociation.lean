import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bags

/-!
# Reassociating actual joint freshness across a datum activation

Dropping an arbitrary scope member can be invalid when its local assignments
are uninhabited. Equal local frames provide the required assignment from the
remaining member instead of assuming global inhabitance. After the datum
stage, joint freshness retains every old/data image while assigning the rule
scope independently. The later scope must have a proved two-image span.

The identity-extension firing below is a scope probe, not an admitted runtime
step: its empty resource selection is not claimed to fit the rule's body.
The conclusions use the existing Core freshness judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadScopeReassociation

open Interface (Frames)
open JointFirings

universe uO uT uH uE uOcc uLater
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {a : Obj} {extension : E.Ext a} {b : Obj}

theorem realized_drop_same_frame
    (first second : Member O E P extension) (rest : List (Member O E P extension))
    (same : first.rule.locals = second.rule.locals)
    (condition : Hom (E.target extension) b → Prop)
    (realized : Realized X b (first :: second :: rest) condition) :
    Realized X b (second :: rest) condition := by
  intro secondAssignment
  have firstAssignment : Hom first.rule.locals b := by
    rw [same]
    exact secondAssignment
  exact Realized.mono X rest (fun _ both => ⟨both.1.1, both.2⟩)
    (realized firstAssignment secondAssignment)

theorem datum_fresh (source : RuleSyntax.State Tm O) (extension : E.Ext source.frame)
    (first second : Member O E P extension)
    (same : first.rule.locals = second.rule.locals)
    (joint : (⟨extension, [first, second]⟩ : Bag O E P source.frame).Fresh X source) :
    second.firing.Fresh X source := by
  intro target caller
  exact realized_drop_same_frame X first second [] same _ (joint target caller)

abbrev identityExtensions : Extensions.{uO, uH, 0} Hom := Extensions.identity X

def scopeFiring {U : Type uLater} (member : Member O E P extension) :
    RuleSyntax.Firing U (identityExtensions X) (Set.univ : Program Tm) (E.target extension) where
  rule := member.rule
  member := Set.mem_univ _
  ext := PUnit.unit
  opening := member.opening
  selection := ⟨[], [], []⟩
  seen := []

theorem fresh_after_datum_span {U : Type uLater}
    (source : RuleSyntax.State Tm O) (extension : E.Ext source.frame)
    (first second : Member O E P extension)
    (knowledge : EquationStore (Tm (E.target extension))) (present : Finset U)
    (label : U → Tm (E.target extension))
    (joint : (⟨extension, [first, second]⟩ : Bag O E P source.frame).Fresh X source)
    (span : ∀ term,
      (⟨E.target extension, knowledge, present, label⟩ : RuleSyntax.State Tm U).Mentions term →
      (∃ old, source.Mentions old ∧ term = X.act (E.weaken extension) old) ∨
        (∃ datumTerm, datumTerm ∈ second.rule.terms ∧ term = X.act second.opening datumTerm)) :
    (scopeFiring X (U := U) first).Fresh X
      (⟨E.target extension, knowledge, present, label⟩ : RuleSyntax.State Tm U) := by
  intro target caller ruleAssignment
  obtain ⟨combined, both⟩ := joint target (X.comp caller (E.weaken extension))
    ruleAssignment (X.comp caller second.opening)
  refine ⟨combined, ?_, both.1.2⟩
  intro term mentioned
  change X.E (X.act combined (X.act (X.id (E.target extension)) term)) (X.act caller term)
  rw [X.act_id]
  rcases span term mentioned with ⟨old, oldMentioned, rfl⟩ | ⟨datumTerm, datumMember, rfl⟩
  · simpa only [X.act_comp] using both.1.1 old oldMentioned
  · simpa only [X.act_comp] using both.2 datumTerm datumMember

#print axioms realized_drop_same_frame
#print axioms datum_fresh
#print axioms fresh_after_datum_span

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadScopeReassociation
