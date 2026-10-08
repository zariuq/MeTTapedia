import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualSumElimination
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalContextualControls

/-!
# External dependent function and pair controls

Generated-equal higher-order family annotations remain different Church
lambda codes, while mixed congruence preserves their complete term classes.
A nonidentity projection changes both a domain parameter and its bound-body
parameter. The dependent pair retains an actual function and its supplied
family witness in separate variable positions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.TypeOperationControls

open _root_.CategoryTheory Contextual ContextualControls
open Contextual.DependentTypes Contextual.QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualTypeOperations

abbrev rightAnnotation := secondFamily.reindex (projectionHom functionContext secondFamily)
def firstIdentity := Products.rawLam (newest functionContext firstFamily)
def secondIdentity := Products.rawLam (newest functionContext secondFamily)

theorem body_annotations_equal : Holds signature (.typeEq witnessContext.raw firstAnnotation.code
    (rightAnnotation.reindex (extensionComparison firstFamily secondFamily annotations_equal).hom).code) := by
  rw [extensionComparison_type_code]
  exact annotations_substituted

theorem mixed_identity_annotations : QTerm.mk firstIdentity = QTerm.mk secondIdentity := by
  apply Products.rawLam_compared _ _ annotations_equal _ _ body_annotations_equal
  rw [extensionComparison_term_code]
  exact termEquality_refl (newest functionContext firstFamily)

theorem distinct_church_identity_codes : firstIdentity.code ≠ secondIdentity.code := by
  intro same
  exact different_annotation_syntax (TermExpr.lam.inj same |>.1)

abbrev qFunctionContext := (quotientProjection signature).obj functionContext
def nativeDomain : QuotientCwf.Ty qFunctionContext := QType.mk firstFamily
noncomputable def nativeBodyType : QuotientCwf.Ty (QuotientCwf.ext qFunctionContext nativeDomain) :=
  QuotientCwf.tySub nativeDomain (QuotientCwf.wk nativeDomain)
noncomputable def nativeIdentity : QuotientCwf.Tm qFunctionContext (Products.pi nativeDomain nativeBodyType) :=
  Products.lam (QuotientCwf.vz nativeDomain)

theorem native_function_recovers_body : Products.uncurry nativeIdentity = QuotientCwf.vz nativeDomain :=
  Products.uncurry_lam _

theorem native_generic_eta : Products.lam
    (Mettapedia.TypeTheory.ContextualPiEta.genericSection (Products.operations signature)
      Products.formation_substitution nativeIdentity) = nativeIdentity := Products.eta nativeIdentity

noncomputable def weakenedIdentity := reindexFunction (Products.operations signature) Products.formation_substitution
  (QuotientCwf.project olderProjection) nativeIdentity

set_option backward.isDefEq.respectTransparency false in
theorem native_function_body_substitution :
    QuotientCwf.tmSub (Products.uncurry nativeIdentity)
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf signature) (QuotientCwf.project olderProjection) nativeDomain) =
      Products.uncurry weakenedIdentity :=
  Products.uncurry_substitution _ _ _
    (reindexFunction_heq (Products.operations signature) Products.formation_substitution
      (QuotientCwf.project olderProjection) nativeIdentity).symm

theorem domain_and_body_shift :
    ((rawPi firstFamily firstAnnotation).reindex olderProjection).code =
      .pi (.family .indexed (fun _ => .var (1 : Fin 2)))
        (.family .indexed (fun _ => .var (2 : Fin 3))) := by
  rw [rawPi_reindex]
  change (TypeExpr.pi firstAnnotation.code
    (firstAnnotation.reindex (rawLift olderProjection firstFamily)).code : TypeExpr symbols 2) = _
  rw [projection_shifts_parameter]
  apply congrArg (TypeExpr.pi (S := symbols) (.family TypeSymbol.indexed (fun _ => .var (1 : Fin 2))))
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero =>
      change ((.var (1 : Fin 2) : TermExpr symbols 2).substitute
        (rawLift olderProjection firstFamily).substitution) = .var (2 : Fin 3)
      rw [rawLift_substitution]
      rfl
  | succ prior => exact Fin.elim0 prior

theorem omitted_body_shift :
    ((rawPi firstFamily firstAnnotation).reindex olderProjection).code ≠
      .pi (.family .indexed (fun _ => .var (1 : Fin 2)))
        (.family .indexed (fun _ => .var (1 : Fin 3))) := by
  rw [domain_and_body_shift]
  intro same
  have bodies := TypeExpr.pi.inj same |>.2
  have arguments := eq_of_heq (TypeExpr.family.inj bodies |>.2)
  exact (by decide : (2 : Fin 3) ≠ 1) (TermExpr.var.inj (congrFun arguments 0))

def functionDomain : TypeOver witnessContext := ⟨functionType 2, function_formed witnessContext.formed⟩
abbrev pairBodyContext := extend witnessContext functionDomain

def genericFunctionArguments : pairBodyContext ⟶ functionContext :=
  ⟨extendSubstitution Fin.elim0 (.var 0), by
    have newestTyped := (newest witnessContext functionDomain).typed
    change Holds signature (.term pairBodyContext.raw (.var 0)
      ((functionType 2).substitute (fun index => .var index.succ))) at newestTyped
    rw [functionType_substitute] at newestTyped
    have nil := conclude (.substitutionNil pairBodyContext.raw) ⟨pairBodyContext.formed.judgment, trivial⟩
    have typed : Holds signature (.term pairBodyContext.raw (.var 0)
        ((functionType 0).substitute (Fin.elim0 : Substitution symbols 0 3))) := by
      rw [functionType_substitute]
      exact newestTyped
    exact conclude (.substitutionExtend pairBodyContext.raw .nil (functionType 0) Fin.elim0 (.var 0))
      ⟨nil, function_formed .nil, typed, trivial⟩⟩

def pairBody : TypeOver pairBodyContext := firstFamily.reindex genericFunctionArguments

def olderFunction : Term witnessContext functionDomain :=
  ⟨.var 1, by
    have typed := termSubstitute olderProjection.admitted supplied_typed
    simpa only [suppliedFunction, olderProjection, projectionHom, TermExpr.substitute,
      functionType_substitute, Fin.succ_zero_eq_one, functionDomain] using typed⟩

theorem pair_body_at_function : pairBody.reindex (nativeSection olderFunction) = firstAnnotation := by
  apply TypeOver.ext
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero =>
      rw [nativeSection_substitution]
      rfl
  | succ prior => exact Fin.elim0 prior

def suppliedPairWitness : Term witnessContext (pairBody.reindex (nativeSection olderFunction)) :=
  witness.cast pair_body_at_function.symm

def dependentPair := Sums.rawPair olderFunction suppliedPairWitness

theorem dependent_pair_first : QTerm.mk (Sums.rawFst dependentPair) = QTerm.mk olderFunction :=
  Sums.rawFstBeta _ _

theorem dependent_pair_second : QTerm.mk (Sums.rawSnd dependentPair) = QTerm.mk witness :=
  (Sums.rawSndBeta _ _).trans (QTerm.mk_cast _ _)

theorem dependent_pair_eta : QTerm.mk
    (Sums.rawPair (Sums.rawFst dependentPair) (Sums.rawSnd dependentPair)) = QTerm.mk dependentPair :=
  Sums.rawEta _

theorem witness_depends_on_older_function : (pairBody.reindex (nativeSection olderFunction)).code =
    .family .indexed (fun _ => .var (1 : Fin 2)) :=
  (congrArg TypeOver.code pair_body_at_function).trans projection_shifts_parameter

theorem replacing_first_by_witness_is_wrong : (pairBody.reindex (nativeSection olderFunction)).code ≠
    .family .indexed (fun _ => .var (0 : Fin 2)) := by
  rw [pair_body_at_function]
  exact omitted_parameter_shift

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.TypeOperationControls
