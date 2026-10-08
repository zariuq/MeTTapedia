import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialProducts

/-!
# Complete dependent sections with actual material bodies

The attached literal receipt decoder connects genuine contextual sums
and products to the native adjunctions. Abstraction and application act
on whole compatible sections. Their material readings retain the
ordered argument/result graph, while the literal section equations keep
the stronger receipt information needed by dependent continuations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSections

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : Family base) (body : Family (total domain.native))

def lambdaEquiv : (literal body).sections ≃ (literal (pi domain body)).sections :=
  (sectionDecoder body).trans
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).trans
      (sectionDecoder (pi domain body)).symm)

theorem lambda_future_value (term : (literal body).sections) (point : base.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain.native point).Elements) :
    ((sectionDecoder (pi domain body) (lambdaEquiv domain body term)).val point).val argument =
      (sectionDecoder body term).val ((flatten domain.native).obj
        ((ContextualSmallFamilyTypeFormers.futureArguments domain.native point).obj argument)) := by
  have decoded := (sectionDecoder (pi domain body)).apply_symm_apply
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native) (sectionDecoder body term))
  exact congrArg (fun whole : (nativeProduct domain body).sections => (whole.val point).val argument) decoded

theorem lambda_eta (function : (literal (pi domain body)).sections) :
    lambdaEquiv domain body ((lambdaEquiv domain body).symm function) = function :=
  (lambdaEquiv domain body).apply_symm_apply function

def argumentChange (argument : (literal domain).sections) : NaturalHom base (total domain.native) :=
  ContextualGraphFamilyProducts.argumentSubstitution domain.native (sectionDecoder domain argument)

def substitutedBody (argument : (literal domain).sections) : Family base :=
  substitute body (argumentChange domain argument)

def pullSection {other : D ⥤ Type u} (family : Family base) (change : NaturalHom other base)
    (term : (literal family).sections) : (literal (substitute family change)).sections :=
  (sectionDecoder (substitute family change)).symm
    (ContextualSmallFamilyIdentity.reindexSection change family.native (sectionDecoder family term))

theorem pullSection_decode {other : D ⥤ Type u} (family : Family base) (change : NaturalHom other base)
    (term : (literal family).sections) :
    sectionDecoder (substitute family change) (pullSection family change term) =
      ContextualSmallFamilyIdentity.reindexSection change family.native (sectionDecoder family term) :=
  (sectionDecoder (substitute family change)).apply_symm_apply _

def application (function : (literal (pi domain body)).sections) (argument : (literal domain).sections) :
    (literal (substitutedBody domain body argument)).sections :=
  pullSection body (argumentChange domain argument) ((lambdaEquiv domain body).symm function)

theorem application_beta (term : (literal body).sections) (argument : (literal domain).sections) :
    application domain body (lambdaEquiv domain body term) argument =
      pullSection body (argumentChange domain argument) term := by
  unfold application
  rw [Equiv.symm_apply_apply]

theorem application_decode (function : (literal (pi domain body)).sections) (argument : (literal domain).sections) :
    sectionDecoder (substitutedBody domain body argument) (application domain body function argument) =
      ContextualSmallFamilyIdentity.reindexSection (argumentChange domain argument) body.native
        ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).symm
          (sectionDecoder (pi domain body) function)) := by
  have decoded := (sectionDecoder body).apply_symm_apply
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).symm
      (sectionDecoder (pi domain body) function))
  exact (pullSection_decode body (argumentChange domain argument)
    ((lambdaEquiv domain body).symm function)).trans
      (congrArg (ContextualSmallFamilyIdentity.reindexSection (argumentChange domain argument) body.native) decoded)

theorem native_application_value (function : (nativeProduct domain body).sections)
    (point : base.Elements) (argument : domain.native.obj point) :
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).symm function).val
      ((flatten domain.native).obj ⟨point, argument⟩) =
        evaluated domain body point (function.val point) argument := by
  let indexedLambda := (ContextualAuthoredMaterialCwf.sectionHomEquiv (indexedBody domain.native body.native)).trans
    ((ContextualSmallFamilyNativeAdjunction.smallHomEquiv domain.native
      (indexedBody domain.native body.native) (ContextualAuthoredMaterialCwf.unitNative base.Elements)).trans
      (ContextualAuthoredMaterialCwf.sectionHomEquiv (nativeProduct domain body)).symm)
  have decoded := (bodySectionEquiv domain.native body.native).apply_symm_apply (indexedLambda.symm function)
  exact congrArg (fun whole : (indexedBody domain.native body.native).sections => whole.val ⟨point, argument⟩) decoded

theorem native_lambda_evaluation (term : body.native.sections)
    (point : base.Elements) (argument : domain.native.obj point) :
    evaluated domain body point
        ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native term).val point) argument =
      term.val ((flatten domain.native).obj ⟨point, argument⟩) :=
  (native_application_value domain body
    (ContextualGraphFamilyProducts.nativeLambda domain.native body.native term) point argument).symm.trans
      (congrArg (fun whole : body.native.sections => whole.val ((flatten domain.native).obj ⟨point, argument⟩))
        ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).symm_apply_apply term))

theorem application_value (function : (literal (pi domain body)).sections) (argument : (literal domain).sections)
    (point : base.Elements) :
    termValue (substitutedBody domain body argument) point
      ((sectionDecoder (substitutedBody domain body argument) (application domain body function argument)).val point) =
        resultValue domain body point ((sectionDecoder (pi domain body) function).val point)
          ((sectionDecoder domain argument).val point) := by
  have decoded := congrArg (fun whole : (substitutedBody domain body argument).native.sections => whole.val point)
    (application_decode domain body function argument)
  exact (congrArg (termValue (substitutedBody domain body argument) point) decoded).trans
    (congrArg (termValue body ((flatten domain.native).obj
      ⟨point, (sectionDecoder domain argument).val point⟩))
        (native_application_value domain body (sectionDecoder (pi domain body) function) point
          ((sectionDecoder domain argument).val point)))

def application_material_member (function : (literal (pi domain body)).sections) (argument : (literal domain).sections)
    (point : base.Elements) :
    Member (ContextualGraphOrderedPairs.orderedPair
      (termValue domain point ((sectionDecoder domain argument).val point))
      (termValue (substitutedBody domain body argument) point
        ((sectionDecoder (substitutedBody domain body argument) (application domain body function argument)).val point)))
      (productElement domain body point ((sectionDecoder (pi domain body) function).val point)) :=
  Member.transportChild
    (ContextualGraphOrderedPairs.orderedPairCongr (Equal.refl _)
      (Equal.ofEq (application_value domain body function argument point)).symm)
    (applicationMember domain body point ((sectionDecoder (pi domain body) function).val point)
      ((sectionDecoder domain argument).val point))

def sigmaFirst (term : (literal (sigma domain body)).sections) : (literal domain).sections :=
  (sectionDecoder domain).symm (ContextualGraphFamilyProducts.nativeSigmaFirst domain.native body.native
    (sectionDecoder (sigma domain body) term))

def sigmaSecond (term : (literal (sigma domain body)).sections) :
    (literal (substitutedBody domain body (sigmaFirst domain body term))).sections :=
  (sectionDecoder _).symm (ContextualGraphFamilyProducts.nativeSigmaSecond domain.native body.native
    (sectionDecoder (sigma domain body) term))

def sigmaPair (firstTerm : (literal domain).sections)
    (secondTerm : (literal (substitutedBody domain body firstTerm)).sections) :
    (literal (sigma domain body)).sections :=
  (sectionDecoder (sigma domain body)).symm
    (ContextualGraphFamilyProducts.nativeSigmaPair domain.native body.native
      (sectionDecoder domain firstTerm) (sectionDecoder _ secondTerm))

theorem sigmaFirst_pair (firstTerm : (literal domain).sections)
    (secondTerm : (literal (substitutedBody domain body firstTerm)).sections) :
    sigmaFirst domain body (sigmaPair domain body firstTerm secondTerm) = firstTerm := by
  apply Subtype.ext
  funext point
  exact ContextualGraphFamilyBodies.encode_decode domain.native domain.reading point (firstTerm.val point)

theorem sigma_eta (term : (literal (sigma domain body)).sections) :
    (sectionDecoder (sigma domain body)).symm
      (ContextualGraphFamilyProducts.nativeSigmaPair domain.native body.native
        (ContextualGraphFamilyProducts.nativeSigmaFirst domain.native body.native (sectionDecoder _ term))
        (ContextualGraphFamilyProducts.nativeSigmaSecond domain.native body.native (sectionDecoder _ term))) = term := by
  apply Subtype.ext
  funext point
  exact ContextualGraphFamilyBodies.encode_decode (sigma domain body).native (sigma domain body).reading point
    (term.val point)

def sumMember (point : base.Elements) (term : (sigma domain body).native.obj point) :
    Member (termValue (sigma domain body) point term) ((carrier (sigma domain body)).app point.1 point.2) :=
  ContextualGraphFamilyBodyComparison.memberIntro (sigma domain body).native (sigma domain body).reading
    point _ term (Equal.refl _)

def sumDecode (point : base.Elements) (element : Value D point.1)
    (membership : Member element ((carrier (sigma domain body)).app point.1 point.2)) :
    Σ term : (sigma domain body).native.obj point,
      Equal element (ContextualGraphOrderedPairs.orderedPair (termValue domain point term.1)
        (termValue body ((flatten domain.native).obj ⟨point, term.1⟩) term.2)) :=
  ContextualGraphFamilyBodyComparison.memberDecode (sigma domain body).native (sigma domain body).reading
    point element membership

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSections
