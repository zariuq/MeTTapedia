import Mettapedia.OSLF.Syntax.DeterministicGSOSFinitePresentation

/-!
# The finite-premise correspondence modulo rule equivalence

Consistent independently authored rule presentations are identified by
their complete successful target readouts, not by clause identity. Their
quotient is equivalent to precisely the natural laws whose successful
readouts have finite observation support. An image-finite presentation
instead corresponds to a uniform finite observation bound. These bounds
are distinguished even when the action alphabet is infinite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- Authored finite-premise rules satisfying local deterministic consistency. -/
abbrev ConsistentPresentation :=
  {presentation : FinitePresentation Actions // FinitePresentation.Consistent Actions presentation}

namespace ConsistentPresentation

/-- Only the complete successful readouts determine denotational equivalence. -/
def setoid : Setoid (ConsistentPresentation Actions) where
  r first second := FinitePresentation.Equivalent Actions first.val second.val
  iseqv := by
    constructor
    · intro presentation sort operator action guard target
      rfl
    · intro first second equivalent sort operator action guard target
      exact (equivalent sort operator action guard target).symm
    · intro first second third earlier later sort operator action guard target
      exact (earlier sort operator action guard target).trans
        (later sort operator action guard target)

/-- Ordinary finite-premise rule presentations modulo denotational equivalence. -/
abbrev Denotations := Quotient (setoid Actions)

/-- The natural laws characterized by ordinary finite-premise presentations. -/
abbrev ObservedLaws :=
  {law : Law S Actions // FiniteSuccessfulObservation Actions (fromLaw Actions law)}

/-- A rule presentation constructs its actual finitely observed natural law. -/
noncomputable def law (presentation : ConsistentPresentation Actions) : ObservedLaws Actions :=
  ⟨FinitePresentation.toLaw Actions presentation.val,
    (FinitePresentation.toLaw_denotes Actions presentation.val presentation.property).finiteSuccessfulObservation
      Actions⟩

theorem law_equal_iff (first second : ConsistentPresentation Actions) :
    law Actions first = law Actions second ↔
      FinitePresentation.Equivalent Actions first.val second.val := by
  constructor
  · intro equal
    exact (FinitePresentation.equivalent_iff_law_equal Actions first.val second.val
      first.property second.property).mpr (congrArg Subtype.val equal)
  · intro equivalent
    apply Subtype.ext
    exact (FinitePresentation.equivalent_iff_law_equal Actions first.val second.val
      first.property second.property).mp equivalent

/-- Reconstruct rules by the independently proved finite-success support theorem. -/
noncomputable def presentation (law : ObservedLaws Actions) : ConsistentPresentation Actions :=
  ⟨soundFinitePresentation Actions (fromLaw Actions law.val),
    FinitePresentation.consistent_of_denotes Actions
      (finiteSuccessfulObservation_denotes Actions law.property)⟩

theorem law_presentation (candidate : ObservedLaws Actions) :
    law Actions (presentation Actions candidate) = candidate := by
  apply Subtype.ext
  exact FinitePresentation.law_roundtrip Actions candidate.val candidate.property

/-- Interpret equivalence classes by their actual natural laws. -/
noncomputable def quotientLaw : Denotations Actions → ObservedLaws Actions :=
  Quotient.lift (law Actions) (fun first second equivalent =>
    (law_equal_iff Actions first second).mpr equivalent)

/-- Construct the equivalence class of the recovered finite-premise rules. -/
noncomputable def lawQuotient (candidate : ObservedLaws Actions) : Denotations Actions :=
  Quotient.mk (setoid Actions) (presentation Actions candidate)

theorem quotientLaw_lawQuotient (candidate : ObservedLaws Actions) :
    quotientLaw Actions (lawQuotient Actions candidate) = candidate :=
  law_presentation Actions candidate

theorem lawQuotient_quotientLaw (denotation : Denotations Actions) :
    lawQuotient Actions (quotientLaw Actions denotation) = denotation := by
  refine Quotient.inductionOn denotation ?_
  intro authored
  apply Quotient.sound
  exact (law_equal_iff Actions (presentation Actions (law Actions authored)) authored).mp
    (law_presentation Actions (law Actions authored))

/-- The corrected finite-premise GSOS theorem, with its exact observation boundary. -/
noncomputable def equivalence : Denotations Actions ≃ ObservedLaws Actions where
  toFun := quotientLaw Actions
  invFun := lawQuotient Actions
  left_inv := lawQuotient_quotientLaw Actions
  right_inv := quotientLaw_lawQuotient Actions

end ConsistentPresentation

/-- Independently authored image-finite consistent rules. -/
abbrev ConsistentImageFinitePresentation :=
  {presentation : ConsistentPresentation Actions // ImageFinite Actions presentation.val}

namespace ConsistentImageFinitePresentation

def setoid : Setoid (ConsistentImageFinitePresentation Actions) where
  r first second := FinitePresentation.Equivalent Actions first.val.val second.val.val
  iseqv := by
    constructor
    · intro presentation sort operator action guard target
      rfl
    · intro first second equivalent sort operator action guard target
      exact (equivalent sort operator action guard target).symm
    · intro first second third earlier later sort operator action guard target
      exact (earlier sort operator action guard target).trans
        (later sort operator action guard target)

abbrev Denotations := Quotient (setoid Actions)

/-- Uniform finite observation bounds, including unsuccessful input guards. -/
abbrev ObservedLaws :=
  {law : Law S Actions // UniformFiniteObservation Actions (fromLaw Actions law)}

noncomputable def law (presentation : ConsistentImageFinitePresentation Actions) : ObservedLaws Actions :=
  ⟨FinitePresentation.toLaw Actions presentation.val.val,
    presentation.property.uniformObservation Actions
      (FinitePresentation.toLaw_denotes Actions presentation.val.val presentation.val.property)⟩

theorem law_equal_iff (first second : ConsistentImageFinitePresentation Actions) :
    law Actions first = law Actions second ↔
      FinitePresentation.Equivalent Actions first.val.val second.val.val := by
  constructor
  · intro equal
    exact (FinitePresentation.equivalent_iff_law_equal Actions first.val.val second.val.val
      first.val.property second.val.property).mpr (congrArg Subtype.val equal)
  · intro equivalent
    apply Subtype.ext
    exact (FinitePresentation.equivalent_iff_law_equal Actions first.val.val second.val.val
      first.val.property second.val.property).mp equivalent

noncomputable def presentation (candidate : ObservedLaws Actions) :
    ConsistentImageFinitePresentation Actions := by
  let recovered := (imageFinite_iff_uniformFiniteObservation Actions
    (fromLaw Actions candidate.val)).mpr candidate.property
  exact ⟨⟨recovered.choose, FinitePresentation.consistent_of_denotes Actions recovered.choose_spec.2⟩,
    recovered.choose_spec.1⟩

theorem presentation_denotes (candidate : ObservedLaws Actions) :
    Denotes Actions (presentation Actions candidate).val.val (fromLaw Actions candidate.val) := by
  exact ((imageFinite_iff_uniformFiniteObservation Actions
    (fromLaw Actions candidate.val)).mpr candidate.property).choose_spec.2

theorem law_presentation (candidate : ObservedLaws Actions) :
    law Actions (presentation Actions candidate) = candidate := by
  apply Subtype.ext
  exact (FinitePresentation.law_unique Actions (presentation Actions candidate).val.val
    (presentation Actions candidate).val.property candidate.val
    (presentation_denotes Actions candidate)).symm

noncomputable def quotientLaw : Denotations Actions → ObservedLaws Actions :=
  Quotient.lift (law Actions) (fun first second equivalent =>
    (law_equal_iff Actions first second).mpr equivalent)

noncomputable def lawQuotient (candidate : ObservedLaws Actions) : Denotations Actions :=
  Quotient.mk (setoid Actions) (presentation Actions candidate)

theorem quotientLaw_lawQuotient (candidate : ObservedLaws Actions) :
    quotientLaw Actions (lawQuotient Actions candidate) = candidate :=
  law_presentation Actions candidate

theorem lawQuotient_quotientLaw (denotation : Denotations Actions) :
    lawQuotient Actions (quotientLaw Actions denotation) = denotation := by
  refine Quotient.inductionOn denotation ?_
  intro authored
  apply Quotient.sound
  exact (law_equal_iff Actions (presentation Actions (law Actions authored)) authored).mp
    (law_presentation Actions (law Actions authored))

/-- Image-finite GSOS classes correspond exactly to uniformly finitely observed laws. -/
noncomputable def equivalence : Denotations Actions ≃ ObservedLaws Actions where
  toFun := quotientLaw Actions
  invFun := lawQuotient Actions
  left_inv := lawQuotient_quotientLaw Actions
  right_inv := quotientLaw_lawQuotient Actions

/-- With finite actions every natural law has the required uniform observation bound. -/
noncomputable def finiteActionsObservedLawEquiv [∀ sort, Finite (Actions sort)] :
    ObservedLaws Actions ≃ Law S Actions where
  toFun := Subtype.val
  invFun candidate := ⟨candidate, finiteActions_uniform Actions (fromLaw Actions candidate)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The finite-action theorem classifies every law by image-finite rule equivalence classes. -/
noncomputable def finiteActionsEquivalence [∀ sort, Finite (Actions sort)] :
    Denotations Actions ≃ Law S Actions :=
  (equivalence Actions).trans (finiteActionsObservedLawEquiv Actions)

end ConsistentImageFinitePresentation

end Mettapedia.OSLF.DeterministicGSOS
