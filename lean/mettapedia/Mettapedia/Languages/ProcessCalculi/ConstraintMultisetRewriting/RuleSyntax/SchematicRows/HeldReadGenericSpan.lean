import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericResources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Protection

/-!
# Every old-source and datum image is retained by materialization

These converse span laws inspect the actual returned knowledge, labels and
held arguments. Capture-length agreement ensures that every parameter image
is present in a real capture equation. Together they compose the two actual
freshness judgments back into the direct joint freshness judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}

theorem schema_terms_iff (schema : Schema Tm) (term : Tm schema.locals) :
    term ∈ (schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit).terms ↔
      term ∈ schema.knowledge.map Prod.fst ∨ term ∈ schema.knowledge.map Prod.snd ∨
        term = schema.value ∨ term ∈ schema.params := by
  have membership (left right params : List (Tm schema.locals)) (value : Tm schema.locals) :
      term ∈ ([] ++ [] ++ left ++ right ++ [] ++ [value] ++ []) ++
          (params ++ [] ++ [] ++ [] ++ [] ++ [] ++ []) ↔
        term ∈ left ∨ term ∈ right ∨ term = value ∨ term ∈ params := by
    simp only [List.mem_append, List.not_mem_nil, List.mem_singleton, false_or, or_false, or_assoc]
  exact membership (schema.knowledge.map Prod.fst) (schema.knowledge.map Prod.snd) schema.params schema.value

theorem erase_identity_action (X : Frames Tm Hom) {a b : Obj} (first second : Hom a b) (term : Tm a) :
    X.E (X.act first (X.act (X.id a) term)) (X.act second term) ↔
      X.E (X.act first term) (X.act second term) := by
  rw [X.act_id]

variable (X : Frames Tm Hom) (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  [DecidableEq O] [DecidableEq R] (temporary output : O)

theorem datum_knowledge (equation : Equation (Tm (E.target extension)))
    (member : equation ∈ datumInformation ordinary closures selected extension datumOpening X) :
    equation ∈ ((datum ordinary rows closures selected extension datumOpening temporary).result X).knowledge := by
  have same : ((datum ordinary rows closures selected extension datumOpening temporary).result X).knowledge =
      datumInformation ordinary closures selected extension datumOpening X :=
    datum_information ordinary rows closures selected extension datumOpening X temporary
  exact same.symm ▸ member

theorem datum_old_knowledge (equation : Equation (Tm ordinary.frame)) (member : equation ∈ ordinary.knowledge) :
    (X.act (E.weaken extension) equation.1, X.act (E.weaken extension) equation.2) ∈
      ((datum ordinary rows closures selected extension datumOpening temporary).result X).knowledge := by
  apply datum_knowledge X ordinary rows closures selected extension datumOpening temporary
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem member))

theorem datum_local_knowledge (equation : Equation (Tm (closures selected).schema.locals))
    (member : equation ∈ (closures selected).schema.knowledge) :
    (X.act datumOpening equation.1, X.act datumOpening equation.2) ∈
      ((datum ordinary rows closures selected extension datumOpening temporary).result X).knowledge := by
  apply datum_knowledge X ordinary rows closures selected extension datumOpening temporary
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem member))

theorem datum_capture_knowledge (parameter : Tm (closures selected).schema.locals)
    (argument : Tm ordinary.frame) (paired : (parameter, argument) ∈ (closures selected).schema.params.zip (closures selected).args) :
    (X.act datumOpening parameter, X.act (E.weaken extension) argument) ∈
      ((datum ordinary rows closures selected extension datumOpening temporary).result X).knowledge := by
  apply datum_knowledge X ordinary rows closures selected extension datumOpening temporary
  apply List.mem_append_right
  rw [List.zip_map]
  exact List.mem_map_of_mem paired

theorem datum_source_image (fresh : temporary ∉ ordinary.present) (term : Tm ordinary.frame)
    (mentioned : (hosted ordinary rows closures).Mentions term) :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).Mentions
      (X.act (E.weaken extension) term) := by
  rcases mentioned with (left | right | ⟨o, present, labelled⟩) | ⟨r, present, argument⟩
  · obtain ⟨equation, member, rfl⟩ := List.mem_map.mp left
    exact Or.inl (Or.inl (List.mem_map_of_mem (f := Prod.fst)
      (datum_old_knowledge X ordinary rows closures selected extension datumOpening temporary equation member)))
  · obtain ⟨equation, member, rfl⟩ := List.mem_map.mp right
    exact Or.inl (Or.inr (Or.inl (List.mem_map_of_mem (f := Prod.snd)
      (datum_old_knowledge X ordinary rows closures selected extension datumOpening temporary equation member))))
  · have different : o ≠ temporary := fun same => fresh (same ▸ present)
    refine Or.inl (Or.inr (Or.inr ⟨o, ?_, ?_⟩))
    · exact (datum_present X ordinary rows closures selected extension datumOpening temporary).symm ▸
        Finset.mem_union_left _ present
    · exact (datum_label_other X ordinary rows closures selected extension datumOpening temporary o different).trans
        (congrArg (X.act (E.weaken extension)) labelled)
  · refine Or.inr ⟨r, (datum_rules X ordinary rows closures selected extension datumOpening temporary).symm ▸ present, ?_⟩
    have arguments :
        (((datum ordinary rows closures selected extension datumOpening temporary).result X).held r).args =
          ((hosted ordinary rows closures).held r).args.map (X.act (E.weaken extension)) :=
      congrArg (fun held : Held Tm (HeldReadEncoding.Code Tm) Unit (E.target extension) => held.args)
        (datum_held X ordinary rows closures selected extension datumOpening temporary r)
    exact arguments.symm ▸ List.mem_map_of_mem argument

theorem datum_term_image (wellFormed : (closures selected).WellFormed)
    (term : Tm (closures selected).schema.locals)
    (member : term ∈ ((closures selected).schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit).terms) :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).Mentions
      (X.act datumOpening term) := by
  rcases (schema_terms_iff (closures selected).schema term).mp member with left | right | rfl | parameter
  · obtain ⟨equation, equationKnown, rfl⟩ := List.mem_map.mp left
    exact Or.inl (Or.inl (List.mem_map_of_mem (f := Prod.fst)
      (datum_local_knowledge X ordinary rows closures selected extension datumOpening temporary equation equationKnown)))
  · obtain ⟨equation, equationKnown, rfl⟩ := List.mem_map.mp right
    exact Or.inl (Or.inr (Or.inl (List.mem_map_of_mem (f := Prod.snd)
      (datum_local_knowledge X ordinary rows closures selected extension datumOpening temporary equation equationKnown))))
  · exact Or.inl (Or.inr (Or.inr ⟨temporary,
      (datum_present X ordinary rows closures selected extension datumOpening temporary).symm ▸ Finset.mem_union_right _ (Finset.mem_singleton_self _),
      datum_label X ordinary rows closures selected extension datumOpening temporary⟩))
  · obtain ⟨argument, paired⟩ := exists_zip_of_mem (closures selected).schema.params
      (closures selected).args wellFormed term parameter
    exact Or.inl (Or.inl (List.mem_map_of_mem (f := Prod.fst)
      (datum_capture_knowledge X ordinary rows closures selected extension datumOpening temporary term argument paired)))

theorem direct_fresh_of_stages (fresh : temporary ∉ ordinary.present)
    (wellFormed : (closures selected).WellFormed)
    (datumFresh : (datum ordinary rows closures selected extension datumOpening temporary).Fresh X)
    (consumerFresh : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Fresh X) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Fresh X := by
  apply (direct_fresh_iff_joint X ordinary rows closures selected extension ruleOpening datumOpening temporary output).mpr
  intro target caller ruleAssignment datumAssignment
  obtain ⟨first, old, locals⟩ := datumFresh target caller datumAssignment
  obtain ⟨combined, retained, ruleTerms⟩ := consumerFresh target first ruleAssignment
  have kept : ∀ term,
      ((datum ordinary rows closures selected extension datumOpening temporary).result X).Mentions term →
      X.E (X.act combined term) (X.act first term) := by
    intro term mentioned
    have equality := retained term mentioned
    exact (erase_identity_action X combined first term).mp equality
  refine ⟨combined, ⟨?_, ?_⟩, ?_⟩
  · intro term mentioned
    have sourceMention := (HeldReadStateScope.mentions_iff (hosted ordinary rows closures) term).mp mentioned
    exact (X.equivalence target).trans
      (kept _ (datum_source_image X ordinary rows closures selected extension datumOpening temporary fresh term sourceMention))
      (old term sourceMention)
  · intro term member
    apply ruleTerms term
    change term ∈ [(closures selected).schema.value, (closures selected).schema.value] at member ⊢
    exact member
  · intro term member
    change term ∈ (HeldReadFreshStaging.specScope
      ((closures selected).schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit)).terms at member
    have actualMember := (HeldReadFreshStaging.specScope_terms
      ((closures selected).schema.toSpec : Spec Tm (HeldReadEncoding.Code Tm) Unit)) ▸ member
    exact (X.equivalence target).trans
      (kept _ (datum_term_image X ordinary rows closures selected extension datumOpening temporary wellFormed term actualMember))
      (locals term actualMember)

#print axioms datum_source_image
#print axioms datum_term_image
#print axioms direct_fresh_of_stages

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
