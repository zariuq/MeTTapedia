import Mettapedia.Languages.Agda.Structural.AdministrativeCompatiblePreservation
import Mettapedia.Languages.Agda.Structural.AdministrativeRegularityControls

/-!
# Controls for native administrative preservation

Actual conversion-wrapped trees exercise empty and nested elimination, both
append roots, and compatible positions. Changing an argument changes its
dependent result code, so the right action must retain native conversion.
Different computational occurrences retain their distinct step evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.PreservationControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Controls
open Statics (RawTm RawTy RawContext)

def expandedUniverse {n : Nat} : RawTy n :=
  el (set (levelClosed 2)) (eliminate (Statics.universeTerm 1) nil)

noncomputable def universeConversion {n : Nat} {Γ : RawContext n}
    (context : CoreDerivation (Statics.context Γ)) :
    CoreDerivation (Statics.typeEqual Γ expandedUniverse (Statics.universeType n 1).code) :=
  Derivation.core (.typeEquality Γ 2 (eliminate (Statics.universeTerm 1) nil) (Statics.universeTerm 1))
    (consEvidence CoreDerivation
      (Derivation.emptyElimination (Derivation.core (.sort Γ 1)
        (consEvidence CoreDerivation context (noEvidence CoreDerivation))))
      (noEvidence CoreDerivation))

noncomputable def administrativeArgument : CoreDerivation
    (Statics.typed empty (eliminate contracted nil) domain.code) :=
  Derivation.elimination contractedTyped (Derivation.nil empty _)

noncomputable def convertedEmptySource : CoreDerivation
    (Statics.typed empty (eliminate contracted nil) expandedUniverse) :=
  Derivation.core (.conversion empty (eliminate contracted nil) domain.code expandedUniverse)
    (consEvidence CoreDerivation administrativeArgument
      (consEvidence CoreDerivation
        (universeConversion (includeCanonical Statics.Derivation.empty)).typeSymmetry
        (noEvidence CoreDerivation)))

/-- The result retains the converted annotation, rather than reverting to the head's first type. -/
noncomputable def convertedEmptyTarget : CoreDerivation (Statics.typed empty contracted expandedUniverse) :=
  (Preservation.eliminateEmpty contracted).typing convertedEmptySource

noncomputable def convertedEmptyEquality :=
  (Preservation.eliminateEmpty contracted).equality empty expandedUniverse convertedEmptySource

theorem converted_annotation_changes_raw_code : expandedUniverse (n := 0) ≠ domain.code := by
  intro same
  cases same

noncomputable def convertedNestedSource : CoreDerivation
    (Statics.typed SpineStatics.Controls.functionContext
      (eliminate (eliminate (.var .zero) SpineStatics.Controls.firstSpine) SpineStatics.Controls.secondSpine)
      expandedUniverse) :=
  Derivation.core (.conversion SpineStatics.Controls.functionContext _ SpineStatics.Controls.domain.code expandedUniverse)
    (consEvidence CoreDerivation (includePrior SpineStatics.Controls.nestedEliminationTyping)
      (consEvidence CoreDerivation
        (universeConversion (includeCanonical SpineStatics.Controls.functionContextFormed)).typeSymmetry
        (noEvidence CoreDerivation)))

noncomputable def convertedNestedTarget : CoreDerivation
    (Statics.typed SpineStatics.Controls.functionContext
      (eliminate (.var .zero) (append SpineStatics.Controls.firstSpine SpineStatics.Controls.secondSpine))
      expandedUniverse) :=
  (Preservation.eliminateAppend (n := 1) (.var .zero) SpineStatics.Controls.firstSpine SpineStatics.Controls.secondSpine).typing
    convertedNestedSource

/-- Generation also handles an inherited application constructor, not only general elimination. -/
noncomputable def canonicalApplicationParts := expandedTyped.eliminationParts

noncomputable def convertedAppendSource : Action SpineStatics.Controls.functionContext
    SpineStatics.Controls.doubleArrow.code (append SpineStatics.Controls.firstSpine SpineStatics.Controls.secondSpine)
    expandedUniverse :=
  Derivation.inputConversion (CoreDerivation.typingFormation functionTyped).typeReflexivity
    (Derivation.outputConversion (Derivation.append firstAction secondAction)
      (universeConversion (includeCanonical SpineStatics.Controls.functionContextFormed)).typeSymmetry)

noncomputable def convertedAppendTarget : Action SpineStatics.Controls.functionContext
    SpineStatics.Controls.doubleArrow.code
    (cons (apply SpineStatics.Controls.firstArgument) (append nil SpineStatics.Controls.secondSpine))
    expandedUniverse := Preservation.appendConsAction convertedAppendSource

noncomputable def convertedAppendEquality :=
  (Preservation.appendCons (apply SpineStatics.Controls.firstArgument) nil SpineStatics.Controls.secondSpine).equality
    SpineStatics.Controls.functionContext SpineStatics.Controls.doubleArrow.code expandedUniverse convertedAppendSource

/-- Both conversions in this existing action change their boundary's raw code. -/
noncomputable def changedEmptyAppendTarget := Preservation.appendEmptyAction RegularityControls.wrappedEmptyAppend

noncomputable def changedEmptyAppendEquality :=
  (Preservation.appendEmpty (nil : Spine (scope 0))).equality empty _ _ RegularityControls.wrappedEmptyAppend

abbrev family := RegularityControls.family

noncomputable def dependentSource : Action empty (Statics.piType domain family).code
    (cons (apply (eliminate contracted nil)) nil) (family.instantiate (eliminate contracted nil)).code :=
  Derivation.cons administrativeArgument (Derivation.nil empty _)

noncomputable def dependentCertificate := (Preservation.eliminateEmpty contracted).argument nil

noncomputable def dependentEquality : SpineEq empty (Statics.piType domain family).code
    (cons (apply (eliminate contracted nil)) nil) (cons (apply contracted) nil)
    (family.instantiate (eliminate contracted nil)).code :=
  dependentCertificate.equality empty _ _ dependentSource

/-- The contracted argument is typed at the original, genuinely different dependent result. -/
noncomputable def dependentTarget : Action empty (Statics.piType domain family).code
    (cons (apply contracted) nil) (family.instantiate (eliminate contracted nil)).code :=
  dependentCertificate.action dependentSource RegularityControls.inputFormed

theorem dependent_results_differ :
    (family.instantiate (eliminate contracted nil)).code ≠ (family.instantiate contracted).code := by
  intro same
  cases same

/-- A compatible tail contraction passes through the first of two ordered applications. -/
noncomputable def tailSource : Action SpineStatics.Controls.functionContext SpineStatics.Controls.doubleArrow.code
    (cons (apply SpineStatics.Controls.firstArgument) (append nil SpineStatics.Controls.secondSpine))
    SpineStatics.Controls.domain.code :=
  Derivation.cons (A := SpineStatics.Controls.domain) (B := .noBind SpineStatics.Controls.arrow)
    (includePrior SpineStatics.Controls.firstArgumentTyped)
    (Derivation.append (Derivation.nil SpineStatics.Controls.functionContext _) secondAction)

noncomputable def tailCertificate :=
  (Preservation.appendEmpty SpineStatics.Controls.secondSpine).consTail (apply SpineStatics.Controls.firstArgument)

noncomputable def tailTarget : Action SpineStatics.Controls.functionContext SpineStatics.Controls.doubleArrow.code
    SpineStatics.Controls.twoArguments SpineStatics.Controls.domain.code :=
  tailCertificate.action tailSource (CoreDerivation.typingFormation functionTyped)

noncomputable def compatibleEliminationTarget : CoreDerivation
    (Statics.typed SpineStatics.Controls.functionContext
      (eliminate (.var .zero) SpineStatics.Controls.twoArguments) SpineStatics.Controls.domain.code) :=
  (tailCertificate.eliminateSpine (.var .zero)).typing (Derivation.elimination functionTyped tailSource)

noncomputable def appendFirstSource : Action empty domain.code (append (append nil nil) nil) domain.code :=
  Derivation.append (Derivation.append nilAction nilAction) nilAction

noncomputable def appendFirstTarget : Action empty domain.code (append nil nil) domain.code :=
  ((Preservation.appendEmpty (nil : Spine (scope 0))).appendFirst nil).action appendFirstSource domainFormed

noncomputable def appendSecondSource : Action empty domain.code (append nil (append nil nil)) domain.code :=
  Derivation.append nilAction (Derivation.append nilAction nilAction)

noncomputable def appendSecondTarget : Action empty domain.code (append nil nil) domain.code :=
  ((Preservation.appendEmpty (nil : Spine (scope 0))).appendSecond nil).action appendSecondSource domainFormed

noncomputable def overlapSource : CoreDerivation
    (Statics.typed empty (eliminate (eliminate contracted nil) nil) domain.code) :=
  Derivation.elimination administrativeArgument nilAction

noncomputable def outerOccurrence := Preservation.eliminateEmpty (eliminate contracted nil)
noncomputable def innerOccurrence := (Preservation.eliminateEmpty contracted).eliminateHead nil

noncomputable def outerTarget := outerOccurrence.typing overlapSource
noncomputable def innerTarget := innerOccurrence.typing overlapSource

theorem typed_occurrences_remain_distinct : outerOccurrence.step ≠ innerOccurrence.step := by
  intro same
  cases same

/-- A raw administrative step is available even when its projection head has no static action. -/
def projectionAppendStep : Step (append (cons (proj "field") (nil : Spine (scope 0))) nil)
    (cons (proj "field") (append nil nil)) := .root (.appendCons _ _ _)

theorem no_projection_action {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {rest : Spine (scope n)} (tree : Action Γ A (cons (proj "field") rest) B) : False := by
  obtain ⟨u, same⟩ := tree.appliedHead
  cases same

theorem no_projection_append_action {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {rest tail : Spine (scope n)} (tree : Action Γ A (append (cons (proj "field") rest) tail) B) : False :=
  no_projection_action tree.splitAppend.first

noncomputable def unsupportedAppendSource : Action empty unsupportedType (append nil nil) unsupportedType :=
  Derivation.append (Derivation.nil empty _) (Derivation.nil empty _)

/-- Append contraction on actions does not manufacture a typing or formation judgment. -/
noncomputable def unsupportedAppendTarget : Action empty unsupportedType nil unsupportedType :=
  Preservation.appendEmptyAction unsupportedAppendSource

theorem unsupported_head_typing_absent (term : RawTm 0) :
    ¬ Nonempty (CoreDerivation (Statics.typed empty term unsupportedType)) := by
  rintro ⟨tree⟩
  exact unsupported_type_unformed ⟨tree.typingFormation⟩

theorem unsupported_contraction_still_unformed :
    Nonempty (Action empty unsupportedType nil unsupportedType) ∧
      ¬ Nonempty (CoreDerivation (Statics.formed empty unsupportedType)) :=
  ⟨⟨unsupportedAppendTarget⟩, unsupported_type_unformed⟩

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.PreservationControls
