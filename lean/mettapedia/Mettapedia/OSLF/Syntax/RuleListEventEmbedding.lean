import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mettapedia.OSLF.Syntax.FreePresheafEventExtension

/-!
# Transporting retained rule occurrences along an authored rule extension

At a fixed binding signature, metavariable context and equation theory, a
rule-list embedding selects a distinct occurrence of each old rule in a new
list. It induces a natural, endpoint-preserving graph map between the located
event presheaves. Rule indices and structural firing locations survive this
map; only the list of available rules is enlarged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RuleListEventEmbedding

open CategoryTheory
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

variable {S : Signature} {M : List (MetaArity S)}

abbrev RuleList (S : Signature) (M : List (MetaArity S)) :=
  List (UnpositionedRewrite (withMetas S M))

/-- Each old authored rule occurrence has a distinct occurrence in the larger
rule list, with exactly the same rule declaration. -/
structure Embedding (old larger : RuleList S M) where
  index : Fin old.length → Fin larger.length
  index_injective : Function.Injective index
  rule_eq : ∀ i, larger.get (index i) = old.get i

namespace Embedding

@[ext] theorem ext {old larger : RuleList S M}
    {first second : Embedding old larger}
    (agree : first.index = second.index) : first = second := by
  cases first with
  | mk firstIndex firstInjective firstRules =>
      cases second with
      | mk secondIndex secondInjective secondRules =>
          cases agree
          rfl

/-- Every rule occurrence embeds as itself. -/
def id (rules : RuleList S M) : Embedding rules rules where
  index := _root_.id
  index_injective := fun _ _ equal => equal
  rule_eq := fun _ => rfl

/-- Literal rule-preserving occurrence embeddings compose. -/
def comp {first middle last : RuleList S M}
    (earlier : Embedding first middle)
    (later : Embedding middle last) : Embedding first last where
  index := later.index ∘ earlier.index
  index_injective := later.index_injective.comp earlier.index_injective
  rule_eq := by
    intro i
    exact (later.rule_eq (earlier.index i)).trans (earlier.rule_eq i)

theorem id_comp {first later : RuleList S M}
    (embedding : Embedding first later) :
    comp (id first) embedding = embedding := by
  apply ext
  rfl

theorem comp_id {first later : RuleList S M}
    (embedding : Embedding first later) :
    comp embedding (id later) = embedding := by
  apply ext
  rfl

theorem assoc {first middle later last : RuleList S M}
    (f : Embedding first middle) (g : Embedding middle later)
    (h : Embedding later last) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  rfl

end Embedding

/-- A catalogue remembers the ordered authored occurrences of the rules.
The order is used for provenance, not for making a rewrite deterministic. -/
structure Catalogue (S : Signature) (M : List (MetaArity S)) where
  rules : RuleList S M

instance catalogueCategory : Category (Catalogue S M) where
  Hom first later := Embedding first.rules later.rules
  id catalogue := Embedding.id catalogue.rules
  comp earlier later := Embedding.comp earlier later
  id_comp := by
    intro _ _ embedding
    exact Embedding.id_comp embedding
  comp_id := by
    intro _ _ embedding
    exact Embedding.comp_id embedding
  assoc := by
    intro _ _ _ _ f g h
    exact Embedding.assoc f g h

/-- An unconditional presentation with fixed metas and equations, varying
only the list of operational rules. -/
def presentation (E : List (EqAxiom S M)) (R : RuleList S M) :
    UnpositionedPresentation S where
  metas := M
  eqs := E
  rules := R

/-- Keep the root firing and linear context while transporting the authored
rule index to its distinct occurrence in the extended list. -/
def embedEvent {old larger : RuleList S M}
    (embedding : Embedding old larger)
    {E : List (EqAxiom S M)} {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance (presentation E old) Γ sort) :
    PresentationInstance (presentation E larger) Γ sort :=
  ⟨embedding.index event.1, (embedding.rule_eq event.1).symm ▸ event.2⟩

private theorem cast_source {oldRule newRule : UnpositionedRewrite (withMetas S M)}
    {Γ : Ctx S} {sort : S.Srt}
    (same : newRule = oldRule)
    (firing : ContextualLocatedEvents.Instance oldRule Γ sort) :
    (same.symm ▸ firing : ContextualLocatedEvents.Instance newRule Γ sort).source =
      firing.source := by
  cases same
  rfl

private theorem cast_target {oldRule newRule : UnpositionedRewrite (withMetas S M)}
    {Γ : Ctx S} {sort : S.Srt}
    (same : newRule = oldRule)
    (firing : ContextualLocatedEvents.Instance oldRule Γ sort) :
    (same.symm ▸ firing : ContextualLocatedEvents.Instance newRule Γ sort).target =
      firing.target := by
  cases same
  rfl

private theorem cast_map {oldRule newRule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ : Ctx S} {sort : S.Srt}
    (same : newRule = oldRule) (sigma : Sub S Γ Δ)
    (firing : ContextualLocatedEvents.Instance oldRule Γ sort) :
    (same.symm ▸ firing.map sigma :
      ContextualLocatedEvents.Instance newRule Δ sort) =
      (same.symm ▸ firing :
        ContextualLocatedEvents.Instance newRule Γ sort).map sigma := by
  cases same
  rfl

private theorem cast_comp
    {firstRule middleRule lastRule : UnpositionedRewrite (withMetas S M)}
    {Γ : Ctx S} {sort : S.Srt}
    (first : middleRule = firstRule) (later : lastRule = middleRule)
    (firing : ContextualLocatedEvents.Instance firstRule Γ sort) :
    (later.symm ▸ (first.symm ▸ firing) :
      ContextualLocatedEvents.Instance lastRule Γ sort) =
        ((later.trans first).symm ▸ firing :
          ContextualLocatedEvents.Instance lastRule Γ sort) := by
  cases first
  cases later
  rfl

theorem embedEvent_source {old larger : RuleList S M}
    (embedding : Embedding old larger)
    {E : List (EqAxiom S M)} {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance (presentation E old) Γ sort) :
    (embedEvent embedding event).source = event.source := by
  rcases event with ⟨i, firing⟩
  exact cast_source (embedding.rule_eq i) firing

theorem embedEvent_target {old larger : RuleList S M}
    (embedding : Embedding old larger)
    {E : List (EqAxiom S M)} {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance (presentation E old) Γ sort) :
    (embedEvent embedding event).target = event.target := by
  rcases event with ⟨i, firing⟩
  exact cast_target (embedding.rule_eq i) firing

theorem embedEvent_map {old larger : RuleList S M}
    (embedding : Embedding old larger)
    {E : List (EqAxiom S M)} {Γ Δ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ)
    (event : PresentationInstance (presentation E old) Γ sort) :
    embedEvent embedding (PresentationInstance.map sigma event) =
      PresentationInstance.map sigma (embedEvent embedding event) := by
  rcases event with ⟨i, firing⟩
  dsimp [embedEvent, PresentationInstance.map, presentation]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (cast_map (embedding.rule_eq i) sigma firing)

theorem embedEvent_id {E : List (EqAxiom S M)}
    {rules : RuleList S M} {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance (presentation E rules) Γ sort) :
    embedEvent (Embedding.id rules) event = event := by
  rcases event with ⟨i, firing⟩
  rfl

theorem embedEvent_comp {E : List (EqAxiom S M)}
    {first middle last : RuleList S M}
    (earlier : Embedding first middle) (later : Embedding middle last)
    {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance (presentation E first) Γ sort) :
    embedEvent (Embedding.comp earlier later) event =
      embedEvent later (embedEvent earlier event) := by
  rcases event with ⟨i, firing⟩
  dsimp [embedEvent, Embedding.comp, presentation]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (cast_comp (earlier.rule_eq i)
      (later.rule_eq (earlier.index i)) firing).symm

private theorem cast_injective
    {oldRule newRule : UnpositionedRewrite (withMetas S M)}
    {Γ : Ctx S} {sort : S.Srt} (same : newRule = oldRule) :
    Function.Injective (fun firing : ContextualLocatedEvents.Instance oldRule Γ sort =>
      (same.symm ▸ firing : ContextualLocatedEvents.Instance newRule Γ sort)) := by
  cases same
  exact fun _ _ equal => equal

/-- Distinct old authored rule occurrences, and distinct firings of one rule,
remain distinct after extending the rule list. -/
theorem embedEvent_injective {old larger : RuleList S M}
    (embedding : Embedding old larger)
    {E : List (EqAxiom S M)} {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective
      (embedEvent embedding :
        PresentationInstance (presentation E old) Γ sort →
          PresentationInstance (presentation E larger) Γ sort) := by
  rintro ⟨i, first⟩ ⟨j, second⟩ equal
  have index_eq : embedding.index i = embedding.index j :=
    congrArg Sigma.fst equal
  have ij : i = j := embedding.index_injective index_eq
  subst j
  have firing_eq :
      (embedding.rule_eq i).symm ▸ first =
        (embedding.rule_eq i).symm ▸ second := by
    dsimp [embedEvent, presentation] at equal
    have inner := sigma_mk_injective equal
    exact inner
  have original_eq := cast_injective (embedding.rule_eq i) firing_eq
  cases original_eq
  rfl

/-- A natural map of located event presheaves, preserving source and target
classes over the common equation theory. -/
def eventNatural {old larger : RuleList S M}
    (embedding : Embedding old larger)
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    presentationEventPresheaf (presentation E old) sort ⟶
      presentationEventPresheaf (presentation E larger) sort where
  app X := TypeCat.ofHom (embedEvent embedding)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact embedEvent_map embedding f.unop event

/-- The natural event map is injective at every context and sort. -/
theorem eventNatural_injective {old larger : RuleList S M}
    (embedding : Embedding old larger)
    (E : List (EqAxiom S M)) (sort : S.Srt)
    (X : (Syntactic.Ctxt S)ᵒᵖ) :
    Function.Injective ((eventNatural embedding E sort).app X) :=
  embedEvent_injective embedding

theorem eventNatural_source {old larger : RuleList S M}
    (embedding : Embedding old larger)
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    eventNatural embedding E sort ≫
      presentationSourceNatural (presentation E larger) sort =
        presentationSourceNatural (presentation E old) sort := by
  ext X event
  exact congrArg (Quotient.mk _) (embedEvent_source embedding event)

theorem eventNatural_target {old larger : RuleList S M}
    (embedding : Embedding old larger)
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    eventNatural embedding E sort ≫
      presentationTargetNatural (presentation E larger) sort =
        presentationTargetNatural (presentation E old) sort := by
  ext X event
  exact congrArg (Quotient.mk _) (embedEvent_target embedding event)

/-- The event translation is a graph map over the unchanged presheaf of
equation-class states. -/
def graphMap {old larger : RuleList S M}
    (embedding : Embedding old larger)
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    Hom
      { edge := presentationEventPresheaf (presentation E old) sort
        source := presentationSourceNatural (presentation E old) sort
        target := presentationTargetNatural (presentation E old) sort }
      { edge := presentationEventPresheaf (presentation E larger) sort
        source := presentationSourceNatural (presentation E larger) sort
        target := presentationTargetNatural (presentation E larger) sort } where
  edgeMap := eventNatural embedding E sort
  source_comm := eventNatural_source embedding E sort
  target_comm := eventNatural_target embedding E sort

/-- Every old closed step remains a step when the rule list is extended,
including equations on both endpoints. -/
theorem stepModE_of_embedding {old larger : RuleList S M}
    (embedding : Embedding old larger)
    (E : List (EqAxiom S M)) {sort : S.Srt}
    {source target : Term S [] sort}
    (step : (presentation E old).StepModE source target) :
    (presentation E larger).StepModE source target := by
  obtain ⟨event, before, after⟩ :=
    (authored_class_endpoints_iff_stepModE (presentation E old)
      sort source target).mpr step
  dsimp [presentation] at before after
  apply (authored_class_endpoints_iff_stepModE
    (presentation E larger) sort source target).mp
  refine ⟨embedEvent embedding event, ?_, ?_⟩
  · change (Quotient.mk _ (embedEvent embedding event).source : TermQ E [] sort) =
      Quotient.mk _ source
    rw [embedEvent_source]
    exact before
  · change (Quotient.mk _ (embedEvent embedding event).target : TermQ E [] sort) =
      Quotient.mk _ target
    rw [embedEvent_target]
    exact after

/-- At a fixed binding signature and equation theory, a catalogue of rule
occurrences acts functorially on the retained event graph. The graph maps
preserve both endpoints over the unchanged state presheaf. -/
def eventGraphFunctor (E : List (EqAxiom S M)) (sort : S.Srt) :
    Catalogue S M ⥤ Graph (termQPresheaf E sort) where
  obj catalogue :=
    { edge := presentationEventPresheaf (presentation E catalogue.rules) sort
      source := presentationSourceNatural (presentation E catalogue.rules) sort
      target := presentationTargetNatural (presentation E catalogue.rules) sort }
  map embedding := graphMap embedding E sort
  map_id catalogue := by
    apply Hom.ext
    ext X event
    exact embedEvent_id event
  map_comp first later := by
    apply Hom.ext
    ext X event
    exact embedEvent_comp first later event

end Mettapedia.OSLF.Binding.RuleListEventEmbedding
