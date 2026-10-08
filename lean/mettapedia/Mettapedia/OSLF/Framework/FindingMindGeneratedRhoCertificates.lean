import Mettapedia.OSLF.Framework.InterpretedGeneratedModality
import Mettapedia.OSLF.Framework.GeneratedModalityRho
import Mettapedia.OSLF.Framework.GeneratedEventCertificates

/-!
# Dependent generated-modality certificates for reflective rho COMM

The generated rules use rho's declared reflective interpretation. Their
independent postcondition requires a parallel result and retains its exact
component inventory, rest slot and a bounded witness. This postcondition
excludes a bare nil process. Applying the certificate at the closed COMM
bindings supplies the actual reflective contractum, with the original
postcondition witness recovered by elimination.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FindingMindGeneratedRhoCertificates

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality (RelySatisfied)
open Mettapedia.OSLF.Framework.GeneratedModalityRho
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary
open InterpretedGeneratedModality
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

variable {C : Type} [Category C]

/-- A dependent specification of an actual parallel result, with its
component inventory and a witness bounded by that inventory. -/
structure ParallelCertificate (target : Pattern) where
  elements : List Pattern
  rest : Option String
  endpoint : target = .collection .hashBag elements rest
  witness : Fin (elements.length + 1)

/-- Reflective instantiation preserves the outer collection constructor and
reads its actual component and rest inventories. -/
def reflectiveCollectionCertificate (declaration : ReflectivePresentationDecl)
    (bindings : Bindings) (elements : List Pattern) (rest : Option String) :
    ParallelCertificate (applyBindingsReflective declaration bindings
      (.collection .hashBag elements rest)) := by
  unfold applyBindingsReflective
  split
  exact ⟨_, _, rfl, ⟨0, Nat.zero_lt_succ _⟩⟩

/-- The postcondition is nonconstant: bare nil does not have a parallel
component inventory of the specified shape. -/
theorem bare_nil_fails_postcondition :
    ¬ Nonempty (ParallelCertificate (.apply "PZero" [])) := by
  rintro ⟨certificate⟩
  cases certificate.endpoint

def commPostcondition (bindings : Bindings) :
    ParallelCertificate (rhoRuleInterpretation.instantiateRule rhoCalc rhoCommRewrite bindings) := by
  change ParallelCertificate (applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite bindings)
  rw [applyBindingsForRuleUsing, LanguageDefAdequacy.rhoComm_substitutionPresentation_selected]
  exact reflectiveCollectionCertificate _ bindings _ _

/-- M-INTRO covers all admitted bindings with the declared operational
interpretation and the independently defined dependent postcondition. -/
def commCertificate : RelyEvidence rhoRuleInterpretation rhoBasePremises rhoCalc
    rhoCommRewrite rhoCommPos (fun _ _ => True) ParallelCertificate rhoCommFocus :=
  introduce rhoComm_stable rhoComm_focus_eq (fun bindings _ _ => commPostcondition bindings)

theorem commFires : RuleFires rhoRuleInterpretation rhoBasePremises rhoCalc
    rhoCommRewrite commBindings := by
  change RhoStep (applyBindings commBindings rhoCommRewrite.left)
    (applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite commBindings)
  rw [rhoComm_instantiate_left, declared_comm_instantiate]
  exact declared_step

/-- M-STEP executes the actual closed reflective synchronization. -/
theorem comm_step :
    RhoStep (commCertificate commBindings rhoComm_rely commFires).source
      (commCertificate commBindings rhoComm_rely commFires).target :=
  (commCertificate commBindings rhoComm_rely commFires).firing

/-- Both endpoint readouts are pinned to the independently executed COMM. -/
theorem comm_endpoints :
    (commCertificate commBindings rhoComm_rely commFires).source = dropReceiverSource ∧
      (commCertificate commBindings rhoComm_rely commFires).target = declaredContractum :=
  ⟨rhoComm_instantiate_left, declared_comm_instantiate⟩

/-- M-ELIM recovers the same supplied dependent certificate at its actual
target, including the component inventory and bounded witness. -/
theorem comm_result :
    result commCertificate commBindings rhoComm_rely commFires =
      ⟨rhoRuleInterpretation.instantiateRule rhoCalc rhoCommRewrite commBindings,
        commPostcondition commBindings⟩ := rfl

theorem comm_postcondition_support :
    RelyPossibly rhoRuleInterpretation rhoBasePremises rhoCalc rhoCommRewrite
      rhoCommPos (fun _ _ => True) (fun target => Nonempty (ParallelCertificate target)) rhoCommFocus :=
  evidence_support commCertificate

/-- A supplied firing rejects an empty result specification, so the closed
operational example is not obtained from an empty observer obligation. -/
theorem empty_postcondition_rejected :
    ¬ RelyPossibly rhoRuleInterpretation rhoBasePremises rhoCalc rhoCommRewrite
      rhoCommPos (fun _ _ => True) (fun _ => False) rhoCommFocus :=
  not_relyPossibly_empty commBindings rhoComm_rely commFires

/-- Declared and structural substitution supply different primitive
contracta on this source; native evidence cannot silently identify them. -/
theorem structural_profile_cannot_supply_declared_step :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step GSLT.LanguageDef.defaultBasePremises
      rhoCalc dropReceiverSource declaredContractum :=
  syntactic_step_not_declaredContractum

/-- The dependent parallel-result specification is a genuine displayed
family over the generated COMM event interface. -/
def parallelFamily : DisplayedFamily.{0, 0, 0, 0}
    ((GeneratedEventCertificates.presentation rhoRuleInterpretation rhoBasePremises rhoCalc
      rhoCommRewrite rhoCommPos (fun _ _ => True) rhoCommFocus).states (C := C)) where
  obj point := ParallelCertificate point.2
  map {first second} move := TypeCat.ofHom fun certificate =>
    (show first.2 = second.2 from move.property) ▸ certificate
  map_id _ := rfl
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro certificate
    rcases first with ⟨firstWorld, firstTarget⟩
    rcases middle with ⟨middleWorld, middleTarget⟩
    rcases last with ⟨lastWorld, lastTarget⟩
    have firstSame : firstTarget = middleTarget := earlier.property
    have lastSame : middleTarget = lastTarget := later.property
    subst middleTarget
    subst lastTarget
    rfl

/-- The same independently specified COMM certificate is introduced into
the native event sum, with its authored request and actual firing. -/
def nativeCommCertificate (world : Cᵒᵖ) :=
  GeneratedEventCertificates.nativeCertificate parallelFamily world rhoComm_rely commFires
    (commCertificate commBindings rhoComm_rely commFires)

/-- The native receipt's source is the independently formed closed redex. -/
theorem nativeComm_source (world : Cᵒᵖ) :
    (totalProjection (((GeneratedEventCertificates.presentation rhoRuleInterpretation
      rhoBasePremises rhoCalc rhoCommRewrite rhoCommPos (fun _ _ => True)
        rhoCommFocus).eventSpan (C := C)).certificates parallelFamily)).app world
          ⟨_, nativeCommCertificate world⟩ = dropReceiverSource :=
  rhoComm_instantiate_left

/-- Native event elimination retains the supplied binding site of the
actual reflective synchronization. -/
theorem nativeComm_request (world : Cᵒᵖ) :
    ((((GeneratedEventCertificates.presentation rhoRuleInterpretation rhoBasePremises rhoCalc
      rhoCommRewrite rhoCommPos (fun _ _ => True) rhoCommFocus).eventSpan (C := C)).eventReadout
      parallelFamily).app world
        ⟨_, nativeCommCertificate world⟩).2.site = commBindings := rfl

/-- The native result map recovers the same complete target inventory,
rest slot and bounded witness at the independently checked contractum. -/
theorem nativeComm_result (world : Cᵒᵖ) :
    (((GeneratedEventCertificates.presentation rhoRuleInterpretation rhoBasePremises rhoCalc
      rhoCommRewrite rhoCommPos (fun _ _ => True) rhoCommFocus).eventSpan (C := C)).resultReadout
      parallelFamily).app world ⟨_, nativeCommCertificate world⟩ =
        ⟨declaredContractum, commPostcondition commBindings⟩ := rfl

end Mettapedia.OSLF.Framework.FindingMindGeneratedRhoCertificates
