import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRuleUniversal
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryInterpretationControls
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension

/-!
# Passive premises, repeated edge occurrences and rejected firing endpoints

Two independently authored rules have genuinely different premise objects:
a passive program and a pair of complete edges. The actual generated firing
arrows return their independently supplied functions. Both repeated edge
weights are retained, including equal supplied occurrences. A well-typed
firing function with an incorrect target is rejected by full admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RuleControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation
open Controls CategoryControls

abbrev original := Presentation.signature vertex
abbrev categoryMap := SignatureMap.identity original
abbrev meanings := CategoryInterpretation.assignment vertex base weighted
abbrev realized := CategoryInterpretation.realization vertex base weighted
  weighted_endpoint_laws weighted_category_laws
abbrev originalFunctor := Interpretation.functor meanings realized

abbrev program := NativeCategory.vertexObject vertex categoryMap
abbrev edge := NativeCategory.edgeObject vertex categoryMap

inductive Origin where
  | passive
  | repeated

def firstEdge : RawHom (product edge edge) edge :=
  ⟨.first edge.code edge.code,⟨.first edge.formed.some edge.formed.some⟩⟩

def secondEdge : RawHom (product edge edge) edge :=
  ⟨.second edge.code edge.code,⟨.second edge.formed.some edge.formed.some⟩⟩

def declarations : Origin → RulePresentation.Declaration vertex categoryMap
  | .passive => ⟨program,RawHom.identity program,RawHom.identity program⟩
  | .repeated => ⟨product edge edge,
      firstEdge.compose (NativeCategory.source vertex categoryMap),
      secondEdge.compose (NativeCategory.target vertex categoryMap)⟩

theorem different_premise_presentations : (declarations .passive).domain.code ≠
    (declarations .repeated).domain.code := by
  intro same
  cases same

def firing : ∀ origin, RuleInterpretation.premise vertex categoryMap declarations meanings realized origin ⟶
    RuleInterpretation.edges vertex categoryMap meanings realized
  | .passive => TypeCat.ofHom (fun state => (state,state,11))
  | .repeated => TypeCat.ofHom (fun pair => (pair.1.1,pair.2.2.1,pair.1.2.2 + pair.2.2.2))

theorem source_function : originalFunctor.map (classOf (NativeCategory.source vertex categoryMap)) = graph.source := by
  have complete := functor_complete_readout meanings realized (NativeCategory.source vertex categoryMap)
  have supplied : meanings.evaluateArrow (NativeCategory.source vertex categoryMap).code =
      some (⟨Evidence,Bool,graph.source⟩ : ArrowValue Type) := rfl
  exact ArrowValue.arrow_injective (Option.some.inj (complete.symm.trans supplied))

theorem target_function : originalFunctor.map (classOf (NativeCategory.target vertex categoryMap)) = graph.target := by
  have complete := functor_complete_readout meanings realized (NativeCategory.target vertex categoryMap)
  have supplied : meanings.evaluateArrow (NativeCategory.target vertex categoryMap).code =
      some (⟨Evidence,Bool,graph.target⟩ : ArrowValue Type) := rfl
  exact ArrowValue.arrow_injective (Option.some.inj (complete.symm.trans supplied))

theorem first_function : originalFunctor.map (classOf firstEdge) =
    TypeCat.ofHom (Prod.fst : Evidence × Evidence → Evidence) := by
  have complete := functor_complete_readout meanings realized firstEdge
  have supplied : meanings.evaluateArrow firstEdge.code = some
      (⟨Evidence × Evidence,Evidence,TypeCat.ofHom Prod.fst⟩ : ArrowValue Type) := rfl
  exact ArrowValue.arrow_injective (Option.some.inj (complete.symm.trans supplied))

theorem second_function : originalFunctor.map (classOf secondEdge) =
    TypeCat.ofHom (Prod.snd : Evidence × Evidence → Evidence) := by
  have complete := functor_complete_readout meanings realized secondEdge
  have supplied : meanings.evaluateArrow secondEdge.code = some
      (⟨Evidence × Evidence,Evidence,TypeCat.ofHom Prod.snd⟩ : ArrowValue Type) := rfl
  exact ArrowValue.arrow_injective (Option.some.inj (complete.symm.trans supplied))

theorem local_laws : RuleInterpretation.LocalLaws vertex categoryMap declarations meanings realized firing where
  source origin := by
    cases origin with
    | passive =>
        change firing .passive ≫ originalFunctor.map (classOf (NativeCategory.source vertex categoryMap)) =
          originalFunctor.map (𝟙 program)
        rw [source_function,originalFunctor.map_id]
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext state
        rfl
    | repeated =>
        change firing .repeated ≫ originalFunctor.map (classOf (NativeCategory.source vertex categoryMap)) =
          originalFunctor.map (classOf firstEdge ≫ classOf (NativeCategory.source vertex categoryMap))
        rw [originalFunctor.map_comp,source_function,first_function]
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext pair
        rfl
  target origin := by
    cases origin with
    | passive =>
        change firing .passive ≫ originalFunctor.map (classOf (NativeCategory.target vertex categoryMap)) =
          originalFunctor.map (𝟙 program)
        rw [target_function,originalFunctor.map_id]
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext state
        rfl
    | repeated =>
        change firing .repeated ≫ originalFunctor.map (classOf (NativeCategory.target vertex categoryMap)) =
          originalFunctor.map (classOf secondEdge ≫ classOf (NativeCategory.target vertex categoryMap))
        rw [originalFunctor.map_comp,target_function,second_function]
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext pair
        rfl

abbrev interpreted := RuleInterpretation.functor vertex categoryMap declarations meanings realized firing local_laws

def readFire (origin : Origin) : Option
    (RuleInterpretation.premise vertex categoryMap declarations meanings realized origin ⟶ Evidence) :=
  ArrowValue.readAt (some ⟨interpreted.obj (RulePresentation.ruleDomain vertex categoryMap declarations origin),
    interpreted.obj (RulePresentation.edges vertex categoryMap declarations),
    interpreted.map (classOf (RulePresentation.fire vertex categoryMap declarations origin))⟩)
      (RuleInterpretation.premise vertex categoryMap declarations meanings realized origin) Evidence

theorem generated_function (origin : Origin) : readFire origin = some (firing origin) := by
  unfold readFire
  rw [RuleInterpretation.fire_complete_read vertex categoryMap declarations meanings realized firing local_laws]
  exact ArrowValue.readAt_supplied _

theorem whole_passive_firing (state : Bool) :
    (readFire .passive).map (fun operation => operation state) = some ((state,state,11) : Evidence) := by
  rw [generated_function]
  rfl

theorem whole_two_occurrence_firing (first second : Evidence) :
    (readFire .repeated).map (fun operation => operation (first,second)) =
      some ((first.1,second.2.1,first.2.2 + second.2.2) : Evidence) := by
  rw [generated_function]
  rfl

theorem equal_occurrences_both_retained :
    (readFire .repeated).map (fun operation => operation ((false,true,3),(false,true,3))) =
      some ((false,true,6) : Evidence) := by
  exact whole_two_occurrence_firing (false,true,3) (false,true,3)

instance interpreted_lex : PreservesFiniteLimits interpreted := by
  change PreservesFiniteLimits (Interpretation.functor
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing)
    (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing local_laws))
  infer_instance

instance interpreted_closed : MonoidalClosedFunctor interpreted := by
  change MonoidalClosedFunctor (Interpretation.functor
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing)
    (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing local_laws))
  infer_instance

def primitiveImages := CanonicalExtension.images
  (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing)
  (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing local_laws)

theorem primitive_readings : RuleUniversal.LocalReadings vertex categoryMap declarations
    (Presentation.headers vertex) meanings realized firing interpreted primitiveImages where
  original origin := (CanonicalExtension.arrow_images
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing)
    (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing local_laws)
    (RulePresentation.headers vertex categoryMap declarations (Presentation.headers vertex))).arrow (Sum.inl origin)
  firing origin := (CanonicalExtension.arrow_images
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing)
    (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing local_laws)
    (RulePresentation.headers vertex categoryMap declarations (Presentation.headers vertex))).arrow (Sum.inr origin)

abbrev generatedUniqueComparison := RuleUniversal.admittedIsoUnique vertex categoryMap declarations
  (Presentation.headers vertex) meanings realized firing interpreted primitiveImages primitive_readings

theorem whole_original_readback : (RulePresentation.arrowInclusion vertex categoryMap declarations).functor ⋙
    (RulePresentation.equationInclusion vertex categoryMap declarations).functor ⋙ interpreted = originalFunctor :=
  RuleInterpretation.complete_original_restriction vertex categoryMap declarations meanings realized firing local_laws

def incorrectTarget : ∀ origin, RuleInterpretation.premise vertex categoryMap declarations meanings realized origin ⟶
    RuleInterpretation.edges vertex categoryMap meanings realized
  | .passive => TypeCat.ofHom (fun state => (state,!state,11))
  | .repeated => firing .repeated

theorem incorrect_target_well_typed : Realization (RulePresentation.arrowSignature vertex categoryMap declarations)
    (RuleInterpretation.arrowAssignment vertex categoryMap declarations meanings realized incorrectTarget) :=
  RuleInterpretation.arrowRealization vertex categoryMap declarations meanings realized incorrectTarget

theorem incorrect_target_rejected :
    ¬ RuleInterpretation.LocalLaws vertex categoryMap declarations meanings realized incorrectTarget := by
  intro laws
  have target := laws.target .passive
  change incorrectTarget .passive ≫ originalFunctor.map (classOf (NativeCategory.target vertex categoryMap)) =
    originalFunctor.map (𝟙 program) at target
  rw [target_function,originalFunctor.map_id] at target
  have impossible := congrArg (fun operation : Bool ⟶ Bool => operation true) target
  change false = true at impossible
  cases impossible

theorem incorrect_target_not_admitted : ¬ Realization (RulePresentation.signature vertex categoryMap declarations)
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized incorrectTarget) := by
  intro admitted
  exact incorrect_target_rejected
    ((RuleInterpretation.realization_iff vertex categoryMap declarations meanings realized incorrectTarget).mp admitted)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RuleControls
