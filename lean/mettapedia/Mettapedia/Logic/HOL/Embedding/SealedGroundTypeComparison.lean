import Mettapedia.Logic.HOL.Syntax.Type
import Mettapedia.TypeTheory.RegularDependentConversionDecision

/-!
# Church simple types versus a sealed one-ground dependent calculus

The regular dependent calculus used by the exact-normalization experiment has
one ordinary ground type below an untyped formation marker.  This module
compares that concrete resource with the actual Church-style HOL type syntax.

Forgetting the distinction between HOL's proposition type and its individual
base types gives a canonical map into the one-base simple fragment of the
dependent calculus.  The map is faithful exactly when the HOL vocabulary has
no individual base types.  With even one base type, `prop` and that base type
become the same dependent ground type, and the exact conversion checker
accepts them.

Consequently, the sealed calculus supports a faithful higher-order
propositional type fragment, but it cannot host a property-explicit HOL type
vocabulary without adding distinguishable type codes or ground types.  This
is a comparison of type formation and conversion only; it does not claim an
embedding of HOL terms, axioms, extensionality, choice, or infinity.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.SealedGroundTypeComparison

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.RegularDependentConversionDecision
open Mettapedia.TypeTheory.RegularDependentConversionDecision.SimpleFragment
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

universe u

/-! ## The canonical loss of HOL ground distinctions -/

/-- Forget whether a HOL leaf was the proposition type or an individual base
type, while preserving every arrow node. -/
def forgetGroundDistinctions {Base : Type u} :
    Ty Base → SimpleType
  | .prop => .base
  | .base _ => .base
  | .arr domain codomain =>
      .arrow (forgetGroundDistinctions domain)
        (forgetGroundDistinctions codomain)

/-- If the HOL vocabulary has no individual base types, forgetting ground
distinctions is faithful. -/
theorem forgetGroundDistinctions_injective_of_noBase
    {Base : Type u} (noBase : Base → False) :
    Function.Injective
      (forgetGroundDistinctions : Ty Base → SimpleType) := by
  intro source
  induction source with
  | prop =>
      intro target equalImages
      cases target with
      | prop => rfl
      | base base => exact False.elim (noBase base)
      | arr domain codomain =>
          simp [forgetGroundDistinctions] at equalImages
  | base base => exact False.elim (noBase base)
  | arr sourceDomain sourceCodomain domainIH codomainIH =>
      intro target equalImages
      cases target with
      | prop => cases equalImages
      | base base => exact False.elim (noBase base)
      | arr targetDomain targetCodomain =>
          simp only [forgetGroundDistinctions, SimpleType.arrow.injEq]
            at equalImages
          exact congrArg₂ Ty.arr
            (domainIH equalImages.1) (codomainIH equalImages.2)

/-- Conversely, a faithful forgetful map proves that the HOL vocabulary has
no individual base type. -/
theorem noBase_of_forgetGroundDistinctions_injective
    {Base : Type u}
    (faithful : Function.Injective
      (forgetGroundDistinctions : Ty Base → SimpleType)) :
    Base → False := by
  intro base
  have impossible : (Ty.prop : Ty Base) = .base base := faithful rfl
  cases impossible

/-- Exact characterization: the one-ground encoding is faithful precisely
for Church type vocabularies with no individual base types. -/
theorem forgetGroundDistinctions_injective_iff_noBase
    {Base : Type u} :
    Function.Injective
        (forgetGroundDistinctions : Ty Base → SimpleType) ↔
      (Base → False) :=
  ⟨noBase_of_forgetGroundDistinctions_injective,
    forgetGroundDistinctions_injective_of_noBase⟩

/-! ## Exact conversion after the comparison map -/

/-- Interpret the forgotten Church type in the sealed dependent calculus at
an arbitrary de Bruijn context length. -/
def toRegularType {Base : Type u} (contextLength : Nat) (type : Ty Base) :=
  embed contextLength (forgetGroundDistinctions type)

/-- Dependent conversion after the comparison is exactly equality of the
ground-forgetting Church type shapes. -/
theorem regularConversion_iff_forgetGroundDistinctions_eq
    {Base : Type u} (contextLength : Nat) (source target : Ty Base) :
    ConstantFreeConv (toRegularType contextLength source)
        (toRegularType contextLength target) ↔
      forgetGroundDistinctions source = forgetGroundDistinctions target :=
  fragmentConversion_iff_eq contextLength _ _

/-- Over a base-free vocabulary, the sealed dependent conversion relation
reflects literal Church-type equality. -/
theorem regularConversion_iff_eq_of_noBase
    {Base : Type u} (noBase : Base → False)
    (contextLength : Nat) (source target : Ty Base) :
    ConstantFreeConv (toRegularType contextLength source)
        (toRegularType contextLength target) ↔
      source = target := by
  rw [regularConversion_iff_forgetGroundDistinctions_eq]
  constructor
  · intro equalImages
    exact (forgetGroundDistinctions_injective_of_noBase noBase) equalImages
  · intro equality
    exact congrArg forgetGroundDistinctions equality

/-- The closed normalization state used by the executable comparison. -/
def closedState {Base : Type u} (type : Ty Base) : State 0 :=
  state RegularCtx.nil (forgetGroundDistinctions type)

/-- The executable dependent conversion decision observes exactly the
ground-forgetting Church type shape. -/
theorem decision_eq_true_iff_forgetGroundDistinctions_eq
    {Base : Type u} (source target : Ty Base) :
    normalizationInvariant.decideConversion 0
        (closedState source) (closedState target) = true ↔
      forgetGroundDistinctions source = forgetGroundDistinctions target :=
  decision_eq_true_iff_type_eq .nil _ _

/-- Hence the same executable decision is exact for Church types with no
individual base vocabulary. -/
theorem decision_eq_true_iff_eq_of_noBase
    {Base : Type u} (noBase : Base → False) (source target : Ty Base) :
    normalizationInvariant.decideConversion 0
        (closedState source) (closedState target) = true ↔
      source = target := by
  rw [decision_eq_true_iff_forgetGroundDistinctions_eq]
  constructor
  · intro equalImages
    exact (forgetGroundDistinctions_injective_of_noBase noBase) equalImages
  · intro equality
    exact congrArg forgetGroundDistinctions equality

/-! ## Positive and negative canaries -/

/-- Positive control: the base-free higher-order propositional fragment is
checked faithfully by the sealed dependent normalizer. -/
theorem propositionArrow_fragment_is_faithful
    (source target : Ty Empty) :
    normalizationInvariant.decideConversion 0
        (closedState source) (closedState target) = true ↔
      source = target :=
  decision_eq_true_iff_eq_of_noBase Empty.elim source target

/-- With one individual base type, the comparison identifies it with the HOL
proposition type. -/
theorem proposition_base_collision :
    forgetGroundDistinctions (Ty.prop : Ty Unit) =
      forgetGroundDistinctions (Ty.base () : Ty Unit) :=
  rfl

/-- The colliding source HOL types are nevertheless syntactically distinct. -/
theorem proposition_ne_base :
    (Ty.prop : Ty Unit) ≠ Ty.base () := by
  intro equality
  cases equality

/-- Negative control: exact dependent normalization accepts the two
distinct HOL types after the lossy one-ground comparison. -/
theorem decision_accepts_proposition_base_collision :
    normalizationInvariant.decideConversion 0
        (closedState (Ty.prop : Ty Unit))
        (closedState (Ty.base () : Ty Unit)) = true :=
  (decision_eq_true_iff_forgetGroundDistinctions_eq _ _).2 rfl

/-- Therefore the one-ground comparison cannot be a conversion-reflecting
encoding for a HOL vocabulary containing an individual base type. -/
theorem oneGround_comparison_not_conversion_reflecting :
    ¬ ∀ source target : Ty Unit,
      normalizationInvariant.decideConversion 0
          (closedState source) (closedState target) = true ↔
        source = target := by
  intro reflects
  exact proposition_ne_base
    ((reflects .prop (.base ())).1
      decision_accepts_proposition_base_collision)

/-! ## Axiom audit -/

#print axioms forgetGroundDistinctions_injective_iff_noBase
#print axioms regularConversion_iff_forgetGroundDistinctions_eq
#print axioms regularConversion_iff_eq_of_noBase
#print axioms decision_eq_true_iff_forgetGroundDistinctions_eq
#print axioms decision_eq_true_iff_eq_of_noBase
#print axioms propositionArrow_fragment_is_faithful
#print axioms proposition_ne_base
#print axioms decision_accepts_proposition_base_collision
#print axioms oneGround_comparison_not_conversion_reflecting

end Mettapedia.Logic.HOL.Embedding.SealedGroundTypeComparison
