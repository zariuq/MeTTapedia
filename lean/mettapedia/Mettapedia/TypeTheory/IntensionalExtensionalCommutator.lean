import Mettapedia.TypeTheory.IndexedUniverseAdequacy

/-!
# The intensional--extensional code commutator

For any interpretation `denote : Code → Host`, quotienting codes by equality of
denotation is equivalent to the essential image of the interpretation.  This is
the exact reversible part of an intensional-to-extensional semantics:

```
Code  -->  Code / same-denotation  ≃  EssentialImage denote  -->  Host.
```

The original map may identify different intensional codes, and the ambient
host may contain objects with no native code at all.  The quotient
repairs the first issue but cannot repair the second.  Paired finite controls
exhibit both boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IntensionalExtensionalCommutator

universe uCode uHost

variable {Code : Type uCode} {Host : Type uHost}

/-! ## Semantic quotient and essential image -/

/-- Codes are semantically equivalent exactly when they have equal
denotations. -/
def denotationSetoid (denote : Code → Host) : Setoid Code where
  r left right := denote left = denote right
  iseqv := ⟨fun _ => rfl, fun equal => equal.symm,
    fun first second => first.trans second⟩

/-- Intensional codes quotiented by the selected extensional equality. -/
abbrev SemanticQuotient (denote : Code → Host) :=
  Quotient (denotationSetoid denote)

/-- The semantic class of one intensional code. -/
def classOf (denote : Code → Host) (code : Code) :
    SemanticQuotient denote :=
  Quotient.mk _ code

/-- Denotation factors through semantic equivalence. -/
def quotientDenote (denote : Code → Host) :
    SemanticQuotient denote → Host :=
  Quotient.lift denote (fun _ _ equal => equal)

@[simp]
theorem quotientDenote_classOf (denote : Code → Host) (code : Code) :
    quotientDenote denote (classOf denote code) = denote code :=
  rfl

/-- Extensionalization becomes faithful after quotienting by exactly the
equality observed by the host. -/
theorem quotientDenote_injective (denote : Code → Host) :
    Function.Injective (quotientDenote denote) := by
  intro left right equal
  revert equal
  refine Quotient.inductionOn₂ left right ?_
  intro leftCode rightCode equal
  exact Quotient.sound equal

/-- Host objects carrying at least one intensional code. -/
def EssentialImage (denote : Code → Host) :=
  {host : Host // ∃ code : Code, denote code = host}

/-- A semantic code class determines a host object in the essential image. -/
def quotientToEssentialImage (denote : Code → Host) :
    SemanticQuotient denote → EssentialImage denote :=
  Quotient.lift
    (fun code => ⟨denote code, ⟨code, rfl⟩⟩)
    (by
      intro left right equal
      exact Subtype.ext equal)

/-- The essential-image map has the same underlying host denotation as the
factored interpretation. -/
@[simp]
theorem quotientToEssentialImage_value (denote : Code → Host)
    (semanticCode : SemanticQuotient denote) :
    (quotientToEssentialImage denote semanticCode).1 =
      quotientDenote denote semanticCode := by
  refine Quotient.inductionOn semanticCode ?_
  intro code
  rfl

/-- The quotient-to-image map is injective. -/
theorem quotientToEssentialImage_injective (denote : Code → Host) :
    Function.Injective (quotientToEssentialImage denote) := by
  intro left right equal
  apply quotientDenote_injective denote
  have valueEqual := congrArg Subtype.val equal
  simpa only [quotientToEssentialImage_value] using valueEqual

/-- Every object in the essential image is reached by a semantic code class. -/
theorem quotientToEssentialImage_surjective (denote : Code → Host) :
    Function.Surjective (quotientToEssentialImage denote) := by
  rintro ⟨host, code, equal⟩
  subst host
  exact ⟨classOf denote code, rfl⟩

/-- The semantic quotient is exactly equivalent to the coded essential
image.  Lean's construction of an inverse from surjectivity uses its standard
classical choice principle; the forward map and its injectivity do not. -/
noncomputable def quotientEquivEssentialImage (denote : Code → Host) :
    SemanticQuotient denote ≃ EssentialImage denote :=
  Equiv.ofBijective (quotientToEssentialImage denote)
    ⟨quotientToEssentialImage_injective denote,
      quotientToEssentialImage_surjective denote⟩

/-! ## Exact reverse-direction boundaries -/

/-- A host object is representable when some intensional code denotes it. -/
def Representable (denote : Code → Host) (host : Host) : Prop :=
  ∃ code : Code, denote code = host

/-- The intensional codes denoting one fixed host object. -/
def CodeFibre (denote : Code → Host) (host : Host) :=
  {code : Code // denote code = host}

/-- A left-inverse reifier would force the original intensional interpretation
to be faithful. -/
theorem no_intensional_recovery_of_noninjective
    (denote : Code → Host) (notInjective : ¬ Function.Injective denote) :
    ¬ ∃ reify : Host → Code, Function.LeftInverse reify denote := by
  rintro ⟨reify, leftInverse⟩
  exact notInjective leftInverse.injective

/-- A section of denotation would make every host object representable. -/
theorem no_total_section_of_unrepresentable
    (denote : Code → Host) {host : Host}
    (notRepresentable : ¬ Representable denote host) :
    ¬ ∃ reify : Host → Code, Function.RightInverse reify denote := by
  rintro ⟨reify, rightInverse⟩
  exact notRepresentable ⟨reify host, rightInverse host⟩

/-- Quotienting removes intensional multiplicity but does not manufacture
codes for extensional-only host objects. -/
theorem quotientDenote_surjective_iff (denote : Code → Host) :
    Function.Surjective (quotientDenote denote) ↔
      Function.Surjective denote := by
  constructor
  · intro quotientSurjective host
    rcases quotientSurjective host with ⟨semanticCode, equal⟩
    obtain ⟨code, representative⟩ := Quotient.exists_rep semanticCode
    subst semanticCode
    exact ⟨code, equal⟩
  · intro denoteSurjective host
    rcases denoteSurjective host with ⟨code, equal⟩
    exact ⟨classOf denote code, equal⟩

/-- The quotient interpretation is a host equivalence exactly when the
original interpretation reaches every host object. -/
theorem quotientDenote_bijective_iff_surjective (denote : Code → Host) :
    Function.Bijective (quotientDenote denote) ↔
      Function.Surjective denote := by
  constructor
  · intro bijective
    exact (quotientDenote_surjective_iff denote).1 bijective.2
  · intro surjective
    exact ⟨quotientDenote_injective denote,
      (quotientDenote_surjective_iff denote).2 surjective⟩

/-! ## Application to family-universe adequacy -/

open Mettapedia.TypeTheory.IndexedUniverseAdequacy
open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe uElement uObject

/-- The faithful semantic quotient attached to an existing family-universe
adequacy interpretation. -/
abbrev adequacySemanticQuotient
    {A : Type uElement} {B : A → Type uElement}
    {envelope : ClosedTarskiUniverseOver.{uCode, uElement} A B}
    {host : ExtensionalUniverseAlgebra.{uObject, uElement}}
    (adequacy : FamilyUniverseAdequacy envelope host) :=
  SemanticQuotient adequacy.denote

/-- The host objects actually denoted by an existing family-universe
adequacy interpretation. -/
abbrev adequacyEssentialImage
    {A : Type uElement} {B : A → Type uElement}
    {envelope : ClosedTarskiUniverseOver.{uCode, uElement} A B}
    {host : ExtensionalUniverseAlgebra.{uObject, uElement}}
    (adequacy : FamilyUniverseAdequacy envelope host) :=
  EssentialImage adequacy.denote

/-- Every family-universe adequacy map has an exact equivalence between its
semantic code quotient and its coded host image. -/
noncomputable def adequacyQuotientEquivEssentialImage
    {A : Type uElement} {B : A → Type uElement}
    {envelope : ClosedTarskiUniverseOver.{uCode, uElement} A B}
    {host : ExtensionalUniverseAlgebra.{uObject, uElement}}
    (adequacy : FamilyUniverseAdequacy envelope host) :
    adequacySemanticQuotient adequacy ≃
      adequacyEssentialImage adequacy :=
  quotientEquivEssentialImage adequacy.denote

/-! ## Positive and negative controls -/

namespace Canary

/-- Erase an intensional Boolean code tag. -/
def taggedDenote : Bool × Nat → Nat := Prod.snd

theorem taggedDenote_surjective : Function.Surjective taggedDenote := by
  intro value
  exact ⟨(false, value), rfl⟩

theorem taggedDenote_not_injective : ¬ Function.Injective taggedDenote := by
  intro injective
  have equalCodes : (false, 0) = (true, 0) := injective rfl
  have equalTags := congrArg Prod.fst equalCodes
  exact Bool.false_ne_true equalTags

/-- One extensional natural has two genuinely distinct codes. -/
theorem tagged_zero_has_multiple_codes :
    ∃ left right : CodeFibre taggedDenote 0, left ≠ right := by
  let left : CodeFibre taggedDenote 0 := ⟨(false, 0), rfl⟩
  let right : CodeFibre taggedDenote 0 := ⟨(true, 0), rfl⟩
  refine ⟨left, right, ?_⟩
  intro equal
  have equalCodes := congrArg (fun value => value.1.1) equal
  exact Bool.false_ne_true equalCodes

/-- After semantic quotienting, the tagged encoding is exactly equivalent
to the extensional natural-number host. -/
noncomputable def taggedQuotientEquivNat : SemanticQuotient taggedDenote ≃ Nat :=
  Equiv.ofBijective (quotientDenote taggedDenote)
    ⟨quotientDenote_injective taggedDenote,
      (quotientDenote_surjective_iff taggedDenote).2 taggedDenote_surjective⟩

/-- An injective encoding with two codes and an infinite extensional host. -/
def partialDenote : Bool → Nat
  | false => 0
  | true => 1

theorem partialDenote_injective : Function.Injective partialDenote := by
  intro left right equal
  cases left <;> cases right <;> simp [partialDenote] at equal ⊢

/-- The extensional object `2` has no native code. -/
theorem two_not_representable : ¬ Representable partialDenote 2 := by
  rintro ⟨code, equal⟩
  cases code <;> simp [partialDenote] at equal

/-- Semantic quotienting cannot turn the partial encoding into a total
encoding of all naturals. -/
theorem partialQuotient_not_surjective :
    ¬ Function.Surjective (quotientDenote partialDenote) := by
  rw [quotientDenote_surjective_iff partialDenote]
  intro surjective
  rcases surjective 2 with ⟨code, equal⟩
  exact two_not_representable ⟨code, equal⟩

end Canary

#print axioms quotientDenote_injective
#print axioms quotientEquivEssentialImage
#print axioms no_intensional_recovery_of_noninjective
#print axioms no_total_section_of_unrepresentable
#print axioms quotientDenote_surjective_iff
#print axioms adequacyQuotientEquivEssentialImage
#print axioms Canary.tagged_zero_has_multiple_codes
#print axioms Canary.taggedQuotientEquivNat
#print axioms Canary.two_not_representable
#print axioms Canary.partialQuotient_not_surjective

end Mettapedia.TypeTheory.IntensionalExtensionalCommutator
