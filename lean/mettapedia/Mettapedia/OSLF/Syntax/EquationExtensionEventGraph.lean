import Mettapedia.OSLF.Syntax.BindingEquationExtension
import Mettapedia.OSLF.Syntax.RuleListEventEmbedding

/-!
# Equation extension of retained operational event graphs

Adding authored equations quotients the state fibres of a scoped operational
graph. It does not quotient its firing occurrences: their rule indices,
assignments, and locations remain available. The state quotient and identity
event map form a graph morphism. These morphisms compose with successive
equation extensions and commute with literal rule-list embeddings.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EquationExtensionEventGraph

open CategoryTheory
open Mettapedia.OSLF.Binding.BindingEquationExtension
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.RuleListEventEmbedding

variable {S : Signature} {M : List (MetaArity S)}

/-- An equation-class state maps to its class for the larger equation list. -/
def compareClass {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F)
    {Γ : Ctx S} {sort : S.Srt} : TermQ E Γ sort → TermQ F Γ sort :=
  Quotient.lift (fun term => Quotient.mk _ term)
    (fun _ _ same => Quotient.sound
      (eqClosure_of_axiom_inclusion inclusion same))

theorem compareClass_mk {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    compareClass inclusion (Quotient.mk _ term : TermQ E Γ sort) =
      (Quotient.mk _ term : TermQ F Γ sort) := rfl

/-- The presheaf comparison is the state component of equation extension. -/
def compareStates {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F) (sort : S.Srt) :
    termQPresheaf E sort ⟶ termQPresheaf F sort where
  app X := TypeCat.ofHom (compareClass inclusion)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro q
    induction q using Quotient.inductionOn with
    | _ term => rfl

theorem compareStates_mk {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F) (sort : S.Srt)
    (X : (Syntactic.Ctxt S)ᵒᵖ)
    (term : Term S X.unop.vars sort) :
    (compareStates inclusion sort).app X
      (Quotient.mk _ term : TermQ E X.unop.vars sort) =
      (Quotient.mk _ term : TermQ F X.unop.vars sort) :=
  compareClass_mk inclusion term

/-- The presheaf map is the same map obtained from initiality of the free
binding-equation model, on every context and sort. -/
theorem compareStates_eq_comparisonHom {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F) (sort : S.Srt)
    (X : (Syntactic.Ctxt S)ᵒᵖ)
    (q : TermQ E X.unop.vars sort) :
    (compareStates inclusion sort).app X q =
      (comparisonHom inclusion).raw.map q := by
  induction q using Quotient.inductionOn with
  | _ term =>
      rw [compareStates_mk, comparisonHom_mk]

theorem compareStates_id (E : List (EqAxiom S M)) (sort : S.Srt) :
    compareStates (axiomInclusion_refl E) sort =
      𝟙 (termQPresheaf E sort) := by
  ext X q
  induction q using Quotient.inductionOn with
  | _ term => rfl

theorem compareStates_comp {E F G : List (EqAxiom S M)}
    (first : AxiomInclusion E F) (later : AxiomInclusion F G)
    (sort : S.Srt) :
    compareStates (axiomInclusion_trans first later) sort =
      compareStates first sort ≫ compareStates later sort := by
  ext X q
  induction q using Quotient.inductionOn with
  | _ term => rfl

/-- Internal presheaf graphs with variable state object. -/
structure EventGraph (base : Type*) [Category base] where
  vertex : base ⥤ Type
  edge : base ⥤ Type
  source : edge ⟶ vertex
  target : edge ⟶ vertex

/-- An event-graph morphism transports both states and firing occurrences,
and preserves their endpoints. -/
structure EventGraphHom {base : Type*} [Category base]
    (first later : EventGraph base) where
  vertexMap : first.vertex ⟶ later.vertex
  edgeMap : first.edge ⟶ later.edge
  source_comm : edgeMap ≫ later.source = first.source ≫ vertexMap
  target_comm : edgeMap ≫ later.target = first.target ≫ vertexMap

namespace EventGraphHom

@[ext] theorem ext {base : Type*} [Category base]
    {first later : EventGraph base} {f g : EventGraphHom first later}
    (vertexEq : f.vertexMap = g.vertexMap)
    (edgeEq : f.edgeMap = g.edgeMap) : f = g := by
  cases f
  cases g
  congr

def id {base : Type*} [Category base] (graph : EventGraph base) :
    EventGraphHom graph graph where
  vertexMap := 𝟙 graph.vertex
  edgeMap := 𝟙 graph.edge
  source_comm := by simp
  target_comm := by simp

def comp {base : Type*} [Category base]
    {first middle last : EventGraph base}
    (earlier : EventGraphHom first middle)
    (later : EventGraphHom middle last) :
    EventGraphHom first last where
  vertexMap := earlier.vertexMap ≫ later.vertexMap
  edgeMap := earlier.edgeMap ≫ later.edgeMap
  source_comm := by
    rw [Category.assoc, later.source_comm, ← Category.assoc,
      earlier.source_comm, Category.assoc]
  target_comm := by
    rw [Category.assoc, later.target_comm, ← Category.assoc,
      earlier.target_comm, Category.assoc]

end EventGraphHom

instance eventGraphCategory (base : Type*) [Category base] :
    Category (EventGraph base) where
  Hom := EventGraphHom
  id := EventGraphHom.id
  comp := EventGraphHom.comp
  id_comp := by
    intro _ _ f
    apply EventGraphHom.ext <;> simp [EventGraphHom.comp, EventGraphHom.id]
  comp_id := by
    intro _ _ f
    apply EventGraphHom.ext <;> simp [EventGraphHom.comp, EventGraphHom.id]
  assoc := by
    intro _ _ _ _ f g h
    apply EventGraphHom.ext <;> simp [EventGraphHom.comp, Category.assoc]

/-- The retained event graph at a fixed sort, with equation classes as
states and actual located rule firings as edges. -/
def presentedGraph (E : List (EqAxiom S M))
    (rules : RuleList S M) (sort : S.Srt) :
    EventGraph ((Syntactic.Ctxt S)ᵒᵖ) where
  vertex := termQPresheaf E sort
  edge := presentationEventPresheaf (presentation E rules) sort
  source := presentationSourceNatural (presentation E rules) sort
  target := presentationTargetNatural (presentation E rules) sort

private theorem eventPresheaf_equation_independent
    (E F : List (EqAxiom S M)) (rules : RuleList S M) (sort : S.Srt) :
    presentationEventPresheaf (presentation E rules) sort =
      presentationEventPresheaf (presentation F rules) sort := by
  rfl

/-- Adding equations changes each endpoint class, but leaves the witnessed
rule occurrence, its substitution action, and its location intact. -/
def equationGraphMap {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F)
    (rules : RuleList S M) (sort : S.Srt) :
    EventGraphHom (presentedGraph E rules sort)
      (presentedGraph F rules sort) where
  vertexMap := compareStates inclusion sort
  edgeMap := 𝟙 _
  source_comm := by
    ext X event
    rfl
  target_comm := by
    ext X event
    rfl

theorem equationGraphMap_id (E : List (EqAxiom S M))
    (rules : RuleList S M) (sort : S.Srt) :
    equationGraphMap (axiomInclusion_refl E) rules sort =
      𝟙 (presentedGraph E rules sort) := by
  apply EventGraphHom.ext
  · exact compareStates_id E sort
  · rfl

theorem equationGraphMap_comp {E F G : List (EqAxiom S M)}
    (first : AxiomInclusion E F) (later : AxiomInclusion F G)
    (rules : RuleList S M) (sort : S.Srt) :
    equationGraphMap (axiomInclusion_trans first later) rules sort =
      EventGraphHom.comp (equationGraphMap first rules sort)
        (equationGraphMap later rules sort) := by
  apply EventGraphHom.ext
  · exact compareStates_comp first later sort
  · change 𝟙 (presentationEventPresheaf (presentation E rules) sort) =
        𝟙 (presentationEventPresheaf (presentation E rules) sort) ≫
          𝟙 (presentationEventPresheaf (presentation F rules) sort)
    exact (Category.id_comp
      (𝟙 (presentationEventPresheaf (presentation F rules) sort))).symm

/-- Equation catalogues at a fixed signature and metavariable context.
Arrows include every old axiom literally in the later presentation. -/
structure EquationCatalogue (S : Signature) (M : List (MetaArity S)) where
  equations : List (EqAxiom S M)

/-- The arrow retains a proof of literal axiom inclusion. -/
structure EquationInclusion (E F : List (EqAxiom S M)) : Type where
  included : AxiomInclusion E F

instance equationInclusionSubsingleton (E F : List (EqAxiom S M)) :
    Subsingleton (EquationInclusion E F) := by
  constructor
  rintro ⟨first⟩ ⟨later⟩
  rfl

instance equationCatalogueCategory : Category (EquationCatalogue S M) where
  Hom earlier later := EquationInclusion earlier.equations later.equations
  id catalogue := ⟨axiomInclusion_refl catalogue.equations⟩
  comp earlier later :=
    ⟨axiomInclusion_trans earlier.included later.included⟩
  id_comp := by intros; exact Subsingleton.elim _ _
  comp_id := by intros; exact Subsingleton.elim _ _
  assoc := by intros; exact Subsingleton.elim _ _

/-- Equation extension acts functorially on state-and-event graphs. The
event component is the identity; the state component is the canonical map
between the initial binding-equation models. -/
def equationEventGraphFunctor (rules : RuleList S M) (sort : S.Srt) :
    EquationCatalogue S M ⥤ EventGraph ((Syntactic.Ctxt S)ᵒᵖ) where
  obj catalogue := presentedGraph catalogue.equations rules sort
  map inclusion := equationGraphMap inclusion.included rules sort
  map_id catalogue := equationGraphMap_id catalogue.equations rules sort
  map_comp earlier later :=
    equationGraphMap_comp earlier.included later.included rules sort

/-- At fixed equations, a rule-catalogue embedding is a graph map whose
state component is the identity. -/
def ruleGraphMap {E : List (EqAxiom S M)}
    {old larger : RuleList S M} (embedding : Embedding old larger)
    (sort : S.Srt) :
    EventGraphHom (presentedGraph E old sort)
      (presentedGraph E larger sort) where
  vertexMap := 𝟙 _
  edgeMap := eventNatural embedding E sort
  source_comm := by
    change eventNatural embedding E sort ≫
      presentationSourceNatural (presentation E larger) sort =
        presentationSourceNatural (presentation E old) sort ≫ 𝟙 _
    simpa using eventNatural_source embedding E sort
  target_comm := by
    change eventNatural embedding E sort ≫
      presentationTargetNatural (presentation E larger) sort =
        presentationTargetNatural (presentation E old) sort ≫ 𝟙 _
    simpa using eventNatural_target embedding E sort

theorem ruleGraphMap_id (E : List (EqAxiom S M))
    (rules : RuleList S M) (sort : S.Srt) :
    ruleGraphMap (E := E) (Embedding.id rules) sort =
      𝟙 (presentedGraph E rules sort) := by
  apply EventGraphHom.ext
  · rfl
  · ext X event
    exact embedEvent_id event

theorem ruleGraphMap_comp {E : List (EqAxiom S M)}
    {first middle last : RuleList S M}
    (earlier : Embedding first middle)
    (later : Embedding middle last) (sort : S.Srt) :
    ruleGraphMap (E := E) (Embedding.comp earlier later) sort =
      EventGraphHom.comp (ruleGraphMap (E := E) earlier sort)
        (ruleGraphMap (E := E) later sort) := by
  apply EventGraphHom.ext
  · change 𝟙 (termQPresheaf E sort) =
        𝟙 (termQPresheaf E sort) ≫ 𝟙 (termQPresheaf E sort)
    exact (Category.id_comp (𝟙 (termQPresheaf E sort))).symm
  · ext X event
    exact embedEvent_comp earlier later event

/-- Rule extension and equation extension commute on states, retained
firings, and both endpoint maps. -/
theorem rule_equation_square {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F)
    {old larger : RuleList S M} (embedding : Embedding old larger)
    (sort : S.Srt) :
    EventGraphHom.comp (ruleGraphMap (E := E) embedding sort)
        (equationGraphMap inclusion larger sort) =
      EventGraphHom.comp (equationGraphMap inclusion old sort)
        (ruleGraphMap (E := F) embedding sort) := by
  apply EventGraphHom.ext
  · change 𝟙 (termQPresheaf E sort) ≫ compareStates inclusion sort =
        compareStates inclusion sort ≫ 𝟙 (termQPresheaf F sort)
    simp
  · ext X event
    rfl

/-- A concrete step modulo the earlier equations remains a step modulo the
larger equation theory. The same authored event witnesses it; only the two
endpoint equality proofs are transported. -/
theorem stepModE_of_equation_inclusion {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F) (rules : RuleList S M)
    {sort : S.Srt} {source target : Term S [] sort}
    (step : (presentation E rules).StepModE source target) :
    (presentation F rules).StepModE source target := by
  obtain ⟨event, before, after⟩ :=
    (authored_class_endpoints_iff_stepModE
      (presentation E rules) sort source target).mpr step
  apply (authored_class_endpoints_iff_stepModE
    (presentation F rules) sort source target).mp
  refine ⟨event, ?_, ?_⟩
  · exact congrArg (compareClass inclusion) before
  · exact congrArg (compareClass inclusion) after

/-- The fixed-signature, fixed-metavariable fragment of the authored
`(Σ,E,R)` ladder is a two-variable functor. Its arrows preserve literal
equations and individual rule occurrences; state quotienting and rule
extension commute by `rule_equation_square`. -/
def presentationGraphBifunctor (sort : S.Srt) :
    (EquationCatalogue S M × Catalogue S M) ⥤
      EventGraph ((Syntactic.Ctxt S)ᵒᵖ) where
  obj item := presentedGraph item.1.equations item.2.rules sort
  map := fun {first later} morphism =>
    EventGraphHom.comp
      (equationGraphMap morphism.1.included first.2.rules sort)
      (ruleGraphMap (E := later.1.equations) morphism.2 sort)
  map_id item := by
    apply EventGraphHom.ext
    · exact compareStates_id item.1.equations sort
    · ext X event
      exact embedEvent_id event
  map_comp first later := by
    apply EventGraphHom.ext
    · exact compareStates_comp first.1.included later.1.included sort
    · ext X event
      exact embedEvent_comp first.2 later.2 event

end Mettapedia.OSLF.Binding.EquationExtensionEventGraph
