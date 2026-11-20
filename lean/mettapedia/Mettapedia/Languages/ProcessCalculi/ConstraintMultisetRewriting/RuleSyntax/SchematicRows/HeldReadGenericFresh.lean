import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

/-!
# The direct scope is exactly the scope needed for both held microsteps

The same two local assignments appear on both sides. Their term lists and
source mentions are transported explicitly. The existing span/reassociation
laws then derive datum and consumer freshness; neither conclusion is assumed,
and no global inhabitance of assignments is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}

theorem schema_scope_terms {a : Obj} (closure : Closure Tm a) :
    (RowUse.scopeRule closure).terms =
      (closure.schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit).terms := by
  have appendParameters (left right : List (Tm closure.schema.locals)) :
      [] ++ [] ++ left ++ right ++ [] ++ closure.schema.value :: closure.schema.params ++ [] =
        ([] ++ [] ++ left ++ right ++ [] ++ [closure.schema.value] ++ []) ++
          (closure.schema.params ++ [] ++ [] ++ [] ++ [] ++ [] ++ []) := by
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append]
  exact appendParameters (closure.schema.knowledge.map Prod.fst) (closure.schema.knowledge.map Prod.snd)

variable (X : Frames Tm Hom) (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  [DecidableEq O] [DecidableEq R] (temporary output : O)

theorem direct_fresh_iff_joint :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Fresh X ↔
      (HeldReadFreshStaging.scopes X
        (datum ordinary rows closures selected extension datumOpening temporary)
        (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output)).Fresh X
          (HeldReadStateScope.scope (hosted ordinary rows closures)) := by
  constructor
  · intro fresh target caller ruleAssignment datumAssignment
    obtain ⟨combined, ⟨kept, ruleTerms⟩, datumTerms⟩ :=
      fresh target caller ruleAssignment datumAssignment
    refine ⟨combined, ⟨?_, ?_⟩, ?_⟩
    · intro term mentioned
      exact kept term ((HeldReadGenericSources.scope_mentions_iff ordinary rows closures term).mpr
        ((HeldReadStateScope.mentions_iff (hosted ordinary rows closures) term).mp mentioned))
    · intro term member
      apply ruleTerms term
      change term ∈ [(closures selected).schema.value, (closures selected).schema.value] at member ⊢
      exact member
    · intro term member
      apply datumTerms term
      change term ∈ (RowUse.scopeRule (closures selected)).terms
      rw [schema_scope_terms]
      change term ∈ (HeldReadFreshStaging.specScope
        ((closures selected).schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit)).terms at member
      rwa [HeldReadFreshStaging.specScope_terms] at member
  · intro joint target caller ruleAssignment datumAssignment
    obtain ⟨combined, ⟨kept, ruleTerms⟩, datumTerms⟩ :=
      joint target caller ruleAssignment datumAssignment
    refine ⟨combined, ⟨?_, ?_⟩, ?_⟩
    · intro term mentioned
      exact kept term ((HeldReadStateScope.mentions_iff (hosted ordinary rows closures) term).mpr
        ((HeldReadGenericSources.scope_mentions_iff ordinary rows closures term).mp mentioned))
    · intro term member
      apply ruleTerms term
      change term ∈ [(closures selected).schema.value, (closures selected).schema.value] at member ⊢
      exact member
    · intro term member
      apply datumTerms term
      change term ∈ (RowUse.scopeRule (closures selected)).terms at member
      rw [schema_scope_terms] at member
      change term ∈ (HeldReadFreshStaging.specScope
        ((closures selected).schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit)).terms
      rwa [HeldReadFreshStaging.specScope_terms]

theorem staged_fresh_of_direct (ambient : Set (HeldReadEncoding.Code Tm))
    (present : selected ∈ rows)
    (fresh : (direct ordinary rows closures selected extension ruleOpening datumOpening output).Fresh X) :
    (datum ordinary rows closures selected extension datumOpening temporary).Fresh X ∧
      (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Fresh X := by
  have joint := (direct_fresh_iff_joint X ordinary rows closures selected extension
    ruleOpening datumOpening temporary output).mp fresh
  refine ⟨HeldReadFreshStaging.datum_fresh X _ _ rfl joint, ?_⟩
  exact HeldReadFreshStaging.consumer_fresh X
    (datum ordinary rows closures selected extension datumOpening temporary)
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output)
    ambient present rfl rfl rfl temporary (closures selected).schema.value rfl rfl rfl joint

#print axioms schema_scope_terms
#print axioms direct_fresh_iff_joint
#print axioms staged_fresh_of_direct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
