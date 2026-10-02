import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafSetting
import Mettapedia.OSLF.Syntax.PresheafEventImageComparisonBridge

/-!
# Indexed generic events and their reduction observation

Each context and sort has its own actual representable program and event
presheaves. The endpoint maps are the Yoneda images of the existing generic
event projection and the authored program-context projections. Their reduction
is the endpoint image, while the event presheaf retains individual tree arrows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.GSLT.Topos.ConstructivePresheaf (EventGraph)
open Mettapedia.GSLT.Topos.PresheafEventModalities

universe w uD vD

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-- The source projection uses the full arity of the endpoint programs. -/
def genericEventSourceArrow (Γ : Ctx S) (s : S.Srt) :
    eventObject R equations Γ s ⟶ (programSection R equations).obj ⟨single S Γ s⟩ :=
  toProgram R equations (eventObject R equations Γ s) ≫
    (programSection R equations).map
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (firstProjection S (single S Γ s) (single S Γ s)))

/-- The target projection is distinct from the source projection and
retains the same open program context and sort. -/
def genericEventTargetArrow (Γ : Ctx S) (s : S.Srt) :
    eventObject R equations Γ s ⟶ (programSection R equations).obj ⟨single S Γ s⟩ :=
  toProgram R equations (eventObject R equations Γ s) ≫
    (programSection R equations).map
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (secondProjection S (single S Γ s) (single S Γ s)))

def genericEventSource (Γ : Ctx S) (s : S.Srt) :
    event.{w} R equations Γ s ⟶ program.{w} R equations Γ s :=
  (embedding R equations).map (genericEventSourceArrow R equations Γ s)

def genericEventTarget (Γ : Ctx S) (s : S.Srt) :
    event.{w} R equations Γ s ⟶ program.{w} R equations Γ s :=
  (embedding R equations).map (genericEventTargetArrow R equations Γ s)

/-- The existing modal graph interface is instantiated separately at every
context and sort; no closed-term replacement or combined carrier is used. -/
def genericEventGraph (Γ : Ctx S) (s : S.Srt) :
    EventGraph.{0, 0, w} (Classifier R equations)ᵒᵖ where
  vertex := program R equations Γ s
  edge := event R equations Γ s
  source := genericEventSource R equations Γ s
  target := genericEventTarget R equations Γ s

abbrev genericEndpointMap (Γ : Ctx S) (s : S.Srt) :=
  PresheafEventImageComparison.endpointMap (genericEventGraph.{w} R equations Γ s)

abbrev genericReduction (Γ : Ctx S) (s : S.Srt) :=
  PresheafEventImageComparison.reduction (genericEventGraph.{w} R equations Γ s)

abbrev genericReductionSubobject (Γ : Ctx S) (s : S.Srt) :=
  PresheafEventImageComparison.reductionSubobject (genericEventGraph.{w} R equations Γ s)

theorem generic_source_section (Γ : Ctx S) (s : S.Srt)
    (X : (Classifier R equations)ᵒᵖ) (e : (event.{w} R equations Γ s).obj X) :
    ((genericEventSource R equations Γ s).app X e).down =
      e.down ≫ genericEventSourceArrow R equations Γ s := rfl

theorem generic_target_section (Γ : Ctx S) (s : S.Srt)
    (X : (Classifier R equations)ᵒᵖ) (e : (event.{w} R equations Γ s).obj X) :
    ((genericEventTarget R equations Γ s).app X e).down =
      e.down ≫ genericEventTargetArrow R equations Γ s := rfl

/-- The section-level reduction observation is exactly existence of an
individual arrow to the actual generic event object with these endpoints. -/
theorem mem_genericReduction_iff (Γ : Ctx S) (s : S.Srt)
    (X : (Classifier R equations)ᵒᵖ)
    (pair : (program.{w} R equations Γ s).obj X × (program.{w} R equations Γ s).obj X) :
    pair ∈ (genericReduction R equations Γ s).obj X ↔
      ∃ e : X.unop ⟶ eventObject R equations Γ s,
        e ≫ genericEventSourceArrow R equations Γ s = pair.1.down ∧
        e ≫ genericEventTargetArrow R equations Γ s = pair.2.down := by
  refine (PresheafEventImageComparison.mem_reduction_iff
    (genericEventGraph R equations Γ s) X pair).trans ?_
  constructor
  · rintro ⟨e, source, target⟩
    exact ⟨e.down, congrArg ULift.down source, congrArg ULift.down target⟩
  · rintro ⟨e, source, target⟩
    refine ⟨ULift.up e, ?_, ?_⟩
    · exact ULift.ext _ _ source
    · exact ULift.ext _ _ target

theorem genericReduction_factorization (Γ : Ctx S) (s : S.Srt) :
    Subfunctor.toRange (genericEndpointMap.{w} R equations Γ s) ≫
      (genericReduction R equations Γ s).ι = genericEndpointMap R equations Γ s :=
  PresheafEventImageComparison.reduction_factorization _

theorem genericReduction_eq_image (Γ : Ctx S) (s : S.Srt) :
    genericReductionSubobject.{w} R equations Γ s =
      imageSubobject (genericEndpointMap R equations Γ s) :=
  PresheafEventImageComparison.reductionSubobject_eq_image _

def genericReductionPredicate (Γ : Ctx S) (s : S.Srt) :=
  PresheafEventImageComparison.reductionPredicate (genericEventGraph.{0} R equations Γ s)

theorem generic_diamond_spec (Γ : Ctx S) (s : S.Srt)
    (predicate : Subfunctor (program.{w} R equations Γ s))
    (X : (Classifier R equations)ᵒᵖ) (x : (program R equations Γ s).obj X) :
    x ∈ (diamond (genericEventGraph R equations Γ s) predicate).obj X ↔
      ∃ y, (x, y) ∈ (genericReduction R equations Γ s).obj X ∧ y ∈ predicate.obj X :=
  PresheafEventImageComparison.diamond_reduction_spec _ _ _ _

theorem generic_diamond_box_adjunction (Γ : Ctx S) (s : S.Srt) :
    GaloisConnection (diamond (genericEventGraph.{w} R equations Γ s))
      (box (genericEventGraph R equations Γ s)) :=
  PresheafEventImageComparison.diamond_box_adjunction _

theorem generic_box_spec (Γ : Ctx S) (s : S.Srt)
    (predicate : Subfunctor (program.{w} R equations Γ s))
    (X : (Classifier R equations)ᵒᵖ) (x : (program R equations Γ s).obj X) :
    x ∈ (box (genericEventGraph R equations Γ s) predicate).obj X ↔
      ∀ (Y : (Classifier R equations)ᵒᵖ) (k : X ⟶ Y)
        (y : (program R equations Γ s).obj Y),
        (y, (program R equations Γ s).map k x) ∈
          (genericReduction R equations Γ s).obj Y → y ∈ predicate.obj Y :=
  PresheafEventImageComparison.box_reduction_spec _ _ _ _

section Trees

variable {R equations} {a : Classifier R equations}
variable (j : Judgment (modelAt equations a.base))
variable (first second : Tree R _ (seeds R _ (events R equations a)) j)

/-- Representing a tree retains its identity, including distinct firings
with equal endpoints. -/
theorem rep_injective (same : rep R equations j first = rep R equations j second) :
    first = second := by
  have slots := congr_arg_heq
    (fun h : a ⟶ eventObject R equations j.1 j.2.1 =>
      IntrinsicScopedLocalActedFibres.atSlot R _ h.fiber
        (IntrinsicScopedLocalActedFibres.first R
          (pairJudgment equations j.1 j.2.1) (IntrinsicScopedLocalActedFiniteContext.Context.empty R _)))
    same
  exact eq_of_heq ((atSlot_rep R equations j first).symm.trans
    (slots.trans (atSlot_rep R equations j second)))

theorem generic_tree_source_equal :
    rep R equations j first ≫ genericEventSourceArrow R equations j.1 j.2.1 =
      rep R equations j second ≫ genericEventSourceArrow R equations j.1 j.2.1 := by
  simp only [genericEventSourceArrow, ← Category.assoc, rep_toProgram]

theorem generic_tree_target_equal :
    rep R equations j first ≫ genericEventTargetArrow R equations j.1 j.2.1 =
      rep R equations j second ≫ genericEventTargetArrow R equations j.1 j.2.1 := by
  simp only [genericEventTargetArrow, ← Category.assoc, rep_toProgram]

theorem generic_tree_sections_distinct (different : first ≠ second) :
    (ULift.up (rep R equations j first) : (event.{w} R equations j.1 j.2.1).obj (Opposite.op a)) ≠
      ULift.up (rep R equations j second) := by
  intro same
  exact different (rep_injective j first second (congrArg ULift.down same))

/-- Every actual firing-tree arrow witnesses reduction-image membership,
regardless of whether another firing has the same endpoints. -/
theorem generic_tree_reduction_member :
    (ULift.up (rep R equations j first ≫ genericEventSourceArrow R equations j.1 j.2.1),
      ULift.up (rep R equations j first ≫ genericEventTargetArrow R equations j.1 j.2.1)) ∈
        (genericReduction.{w} R equations j.1 j.2.1).obj (Opposite.op a) :=
  (mem_genericReduction_iff R equations j.1 j.2.1 _ _).2 ⟨rep R equations j first, rfl, rfl⟩

end Trees

section Extension

variable {D : Type uD} [Category.{vD} D]
variable (L : Presheaf.{w} R equations ⥤ D)
variable [PreservesColimitsOfShape WalkingParallelPair L]
variable (Γ : Ctx S) (s : S.Srt)
variable [HasImage (L.map (genericEndpointMap R equations Γ s))]

/-- Any cocontinuous extension has this comparison with the image of its
transported event map, even when its action on the generic image is not mono. -/
abbrev genericReductionComparison :=
  PresheafEventImageComparison.transportedImageComparison
    (genericEndpointMap R equations Γ s) L

theorem genericReductionComparison_events :
    L.map (Subfunctor.toRange (genericEndpointMap R equations Γ s)) ≫
      genericReductionComparison R equations L Γ s =
        factorThruImage (L.map (genericEndpointMap R equations Γ s)) :=
  PresheafEventImageComparison.transportedImageComparison_events _ _

theorem genericReductionComparison_endpoint :
    genericReductionComparison R equations L Γ s ≫
      image.ι (L.map (genericEndpointMap R equations Γ s)) =
        L.map (genericReduction R equations Γ s).ι :=
  PresheafEventImageComparison.transportedImageComparison_ι _ _

theorem genericReductionComparison_epi [HasEqualizers D] :
    Epi (genericReductionComparison R equations L Γ s) :=
  PresheafEventImageComparison.transportedImageComparison_epi _ _

theorem genericReductionComparison_isIso
    [hmono : Mono (L.map (genericReduction R equations Γ s).ι)] :
    IsIso (genericReductionComparison R equations L Γ s) := by
  let : Mono (L.map (Subfunctor.range (genericEndpointMap R equations Γ s)).ι) := hmono
  exact PresheafEventImageComparison.transportedImageComparison_isIso _ _

end Extension

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
