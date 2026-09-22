import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityInputCoherence

/-!
# Retained semantic inputs for the native based eliminator

At one fixed formed context, the observation retains the semantic element
type, left endpoint, typed motive-function class, and typed method class.
The request domain is their exact image over all admitted native tuples.
Its operation descends the actual native eliminator to this image: no
source identifier, representative-selection callback, or eta equation is
part of a request. This is an operation on the admitted image, not total
based elimination for arbitrary semantic motives.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientRetainedIdentity

open _root_.CategoryTheory FormationSensitive QuotientIdentity QuotientCwf
open QuotientIdentityInputCoherence

variable {signature : Declaration.Signature Tower.Head}
variable {context : Context (OpaqueRelatorExtension.rules signature)}

/-- `QTerm` retains both its type class and its value class. In particular,
the submitted motive function is not replaced by its applied body. -/
structure Observation (context : Context (OpaqueRelatorExtension.rules signature)) where
  type : QType context
  left : TermFibre type
  motiveFunction : QTerm context
  method : QTerm context

def observe (input : Based.Admitted context) : Observation context where
  type := QType.mk input.element
  left := TermFibre.mk input.leftTerm
  motiveFunction := QTerm.mk (QuotientIdentityInputCoherence.motiveFunction input)
  method := input.base.val

theorem Observation.ext {first second : Observation context}
    (types : first.type = second.type) (lefts : first.left.val = second.left.val)
    (motives : first.motiveFunction = second.motiveFunction)
    (methods : first.method = second.method) : first = second := by
  cases first
  cases second
  cases types
  cases Subtype.ext lefts
  cases motives
  cases methods
  rfl

noncomputable def Observation.basedContext (observation : Observation context) :
    QContext (OpaqueRelatorExtension.rules signature) :=
  Mettapedia.TypeTheory.ContextualBasedIdentityOperations.basedContext
    (formation (OpaqueRelatorExtension.rules signature))
    (context := (quotientProjection _).obj context) observation.left

theorem observe_basedContext (input : Based.Admitted context) :
    (observe input).basedContext = input.chosenContext := rfl

theorem chosen_context_eq (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm) :
    first.chosenContext = second.chosenContext := by
  have points : HEq (TermFibre.mk first.leftTerm) (TermFibre.mk second.leftTerm) :=
    QuotientComprehensionSyntax.heq_of_value lefts
  have contexts {firstType secondType : QType context}
      (firstPoint : TermFibre firstType) (secondPoint : TermFibre secondType)
      (sameTypes : firstType = secondType) (samePoints : HEq firstPoint secondPoint) :
      Mettapedia.TypeTheory.ContextualBasedIdentityOperations.basedContext
          (formation (OpaqueRelatorExtension.rules signature))
          (context := (quotientProjection _).obj context) firstPoint =
        Mettapedia.TypeTheory.ContextualBasedIdentityOperations.basedContext
          (formation (OpaqueRelatorExtension.rules signature))
          (context := (quotientProjection _).obj context) secondPoint := by
    cases sameTypes
    cases eq_of_heq samePoints
    rfl
  exact contexts _ _ types points

private noncomputable def nativePresentation (input : Based.Admitted context) :
    input.chosenContext.as ≅ input.basedContext :=
  (doubleExtensionComparison (typeRepresentative (QType.mk input.element)) input.element
    (chosenWitness input.element input.leftTerm) (nativeWitness input.element input.leftTerm)
    ((QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk input.element)))
    (chosenWitness_conversion input.element input.leftTerm)).trans
      (eqToIso (QuotientBasedContextRepresentation.input_context_eq input))

private theorem nativePresentation_project (input : Based.Admitted context) :
    (quotientProjection _).mapIso (nativePresentation input) = input.presentation := by
  exact (Functor.mapIso_trans (quotientProjection _) _ _).trans
    (congrArg (fun next => (basedPresentation input.element input.leftTerm).trans next)
      (eqToIso_map (quotientProjection _)
        (QuotientBasedContextRepresentation.input_context_eq input)))

private theorem postcompose_equality_substitution
    {source target other : Context (OpaqueRelatorExtension.rules signature)}
    (same : target = other) (arrow : source ⟶ target) (index : Fin other.arity) :
    (arrow ≫ eqToHom same).substitution index =
      arrow.substitution
        (cast (congrArg (fun next : Context _ => Fin next.arity) same.symm) index) := by
  cases same
  rfl

private theorem precompose_equality_substitution
    {source target other : Context (OpaqueRelatorExtension.rules signature)}
    (same : source = other) (arrow : other ⟶ target) (index : Fin target.arity) :
    (eqToHom same ≫ arrow).substitution index =
      cast (congrArg (fun next : Context _ => Tower.Tm next.arity) same.symm)
        (arrow.substitution index) := by
  cases same
  exact congrFun (subComp_ids_left arrow.substitution) index

private theorem nativePresentation_hom_substitution (input : Based.Admitted context) :
    (nativePresentation input).hom.substitution = ids := by
  funext index
  exact (postcompose_equality_substitution
    (QuotientBasedContextRepresentation.input_context_eq input) _ index).trans (by rfl)

private theorem nativePresentation_inv_substitution (input : Based.Admitted context) :
    (nativePresentation input).inv.substitution = ids := by
  funext index
  exact (precompose_equality_substitution
    (QuotientBasedContextRepresentation.input_context_eq input).symm _ index).trans (by rfl)

private theorem equality_substitution
    {source target : Context (OpaqueRelatorExtension.rules signature)}
    (same : source = target) (index : Fin target.arity) :
    (eqToHom same).substitution index =
      .var (cast (congrArg (fun next : Context _ => Fin next.arity) same.symm) index) := by
  cases same
  rfl

/-- The comparison of equal retained element/endpoint classes is the
equality arrow of their actual chosen context, not merely an arbitrary
context isomorphism. -/
theorem chosenInputMap_eq (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm) :
    chosenInputMap first second types lefts = eqToHom (chosen_context_eq first second types lefts) := by
  let comparison := QuotientBasedJRepresentation.inputComparison first second
    ((QType.mk_eq_iff _ _).mp types) (((QTerm.mk_eq_iff _ _).mp lefts).2)
  let arrow := (nativePresentation first).hom ≫ comparison.hom ≫ (nativePresentation second).inv
  have substitution : arrow.substitution = ids := by
    change subComp (nativePresentation first).hom.substitution
      (subComp comparison.hom.substitution (nativePresentation second).inv.substitution) = ids
    rw [nativePresentation_hom_substitution, nativePresentation_inv_substitution]
    exact (subComp_ids_left _).trans (subComp_ids_left _)
  have raw : arrow = eqToHom
      (congrArg (fun next : QContext _ => next.as) (chosen_context_eq first second types lefts)) := by
    apply Hom.ext
    funext index
    rw [substitution, equality_substitution]
    rfl
  have projected := congrArg (fun map => project map) raw
  have firstProject : project (nativePresentation first).hom = first.presentation.hom :=
    congrArg Iso.hom (nativePresentation_project first)
  have secondProject : project (nativePresentation second).inv = second.presentation.inv :=
    congrArg Iso.inv (nativePresentation_project second)
  change project ((nativePresentation first).hom ≫ comparison.hom ≫
    (nativePresentation second).inv) = _ at projected
  simp only [project, Functor.map_comp, eqToHom_map] at projected
  exact (congrArg (fun pair => pair.1 ≫ project comparison.hom ≫ pair.2)
    (show (first.presentation.hom, second.presentation.inv) =
      (project (nativePresentation first).hom, project (nativePresentation second).inv) from
        Prod.ext firstProject.symm secondProject.symm)).trans projected

private theorem tySub_equality_heq
    {first second : QContext (OpaqueRelatorExtension.rules signature)}
    (same : first = second) (type : Ty second) :
    HEq (tySub type (eqToHom same)) type := by
  cases same
  exact heq_of_eq (tySub_id type)

private theorem tmSub_equality_heq
    {first second : QContext (OpaqueRelatorExtension.rules signature)}
    (same : first = second) {type : Ty second} (value : QuotientCwf.Tm second type) :
    HEq (tmSub value (eqToHom same)) value := by
  cases same
  exact QuotientComprehensionSyntax.heq_of_value (totalSub_id value.val)

/-- Equality of retained observations determines the applied motive in
the actual chosen based context, even when all native parameters differ. -/
theorem chosen_motive_coherent (first second : Based.Admitted context)
    (same : observe first = observe second) :
    HEq (tySub (QType.mk first.motiveType) first.presentation.hom)
      (tySub (QType.mk second.motiveType) second.presentation.hom) := by
  have types := congrArg Observation.type same
  have lefts := congrArg (fun observation => observation.left.val) same
  have motives := congrArg Observation.motiveFunction same
  have transport := chosen_motive_transport first second types lefts motives
  have equality := congrArg
    (tySub (tySub (QType.mk second.motiveType) second.presentation.hom))
    (chosenInputMap_eq first second types lefts)
  exact (heq_of_eq (equality.symm.trans transport).symm).trans
    (tySub_equality_heq (chosen_context_eq first second types lefts) _)

/-- The native chosen output is independent of the admitted representative
of a retained observation. This is stronger than comparison along an
unspecified isomorphism: `chosenInputMap_eq` identifies that comparison. -/
theorem chosen_j_coherent (first second : Based.Admitted context)
    (same : observe first = observe second) : HEq first.chosenJ second.chosenJ := by
  have types := congrArg Observation.type same
  have lefts := congrArg (fun observation => observation.left.val) same
  have motives := congrArg Observation.motiveFunction same
  have methods := congrArg Observation.method same
  have transport := chosen_j_transport_value first second types lefts motives methods
  have equality := congrArg (totalSub second.chosenJ.val)
    (chosenInputMap_eq first second types lefts)
  exact (QuotientComprehensionSyntax.heq_of_value
    (equality.symm.trans transport).symm).trans
      (tmSub_equality_heq (chosen_context_eq first second types lefts) second.chosenJ)

private theorem body_input_ext
    (first second : Mettapedia.TypeTheory.ContextualBasedIdentityScope.Input
      (formation (OpaqueRelatorExtension.rules signature))
      (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature)))
    (contexts : first.context = second.context) (types : HEq first.type second.type)
    (lefts : HEq first.left second.left) (motives : HEq first.motive second.motive)
    (methods : HEq first.base second.base) : first = second := by
  cases first
  cases second
  cases contexts
  cases eq_of_heq types
  cases eq_of_heq lefts
  cases eq_of_heq motives
  cases eq_of_heq methods
  rfl

/-- The separately formed body/method input is a consequence of the
retained observation, not an additional representative-dependent field. -/
theorem semantic_input_coherent (first second : Based.Admitted context)
    (same : observe first = observe second) : semanticInput first = semanticInput second := by
  apply body_input_ext
  · rfl
  · exact heq_of_eq (congrArg Observation.type same)
  · exact QuotientComprehensionSyntax.heq_of_value
      (congrArg (fun observation => observation.left.val) same)
  · exact chosen_motive_coherent first second same
  · exact QuotientComprehensionSyntax.heq_of_value (congrArg Observation.method same)

/-! ## Descent to the exact semantic image -/

/-- Membership is exactly existence of an admitted native tuple with this
observation; it supplies no output and does not discard any admitted tuple. -/
def Request (context : Context (OpaqueRelatorExtension.rules signature)) :=
  {observation : Observation context // ∃ input : Based.Admitted context, observe input = observation}

def requestOf (input : Based.Admitted context) : Request context :=
  ⟨observe input, input, rfl⟩

theorem requestOf_surjective : Function.Surjective (requestOf (context := context)) := by
  intro request
  obtain ⟨input, same⟩ := request.property
  exact ⟨input, Subtype.ext same⟩

theorem requestOf_eq_iff (first second : Based.Admitted context) :
    requestOf first = requestOf second ↔ observe first = observe second :=
  ⟨fun same => congrArg Subtype.val same, fun same => Subtype.ext same⟩

/-- A descended output retains its actual dependent motive annotation. -/
def Result (observation : Observation context) :=
  Σ motive : Ty observation.basedContext, QuotientCwf.Tm observation.basedContext motive

/-- The actual chosen motive and native J, before descent. -/
noncomputable def nativeResult (input : Based.Admitted context) : Result (observe input) :=
  ⟨tySub (QType.mk input.motiveType) input.presentation.hom, input.chosenJ⟩

private theorem result_ext {first second : Observation context}
    (firstResult : Result first) (secondResult : Result second)
    (same : first = second) (motives : HEq firstResult.1 secondResult.1)
    (values : HEq firstResult.2 secondResult.2) : HEq firstResult secondResult := by
  cases same
  cases firstResult
  cases secondResult
  cases eq_of_heq motives
  cases eq_of_heq values
  rfl

private theorem nativeResult_coherent (first second : Based.Admitted context)
    (same : observe first = observe second) : HEq (nativeResult first) (nativeResult second) :=
  result_ext _ _ same (chosen_motive_coherent first second same) (chosen_j_coherent first second same)

private noncomputable def representative (request : Request context) : Based.Admitted context :=
  Classical.choose request.property

private theorem representative_observe (request : Request context) :
    observe (representative request) = request.val := Classical.choose_spec request.property

/-- Selection is only an implementation of quotient descent. The public
representative law below proves agreement with every admitted tuple. -/
noncomputable def result (request : Request context) : Result request.val :=
  cast (congrArg Result (representative_observe request)) (nativeResult (representative request))

theorem result_representative (request : Request context) (input : Based.Admitted context)
    (same : observe input = request.val) : HEq (result request) (nativeResult input) :=
  (cast_heq _ _).trans (nativeResult_coherent (representative request) input
    ((representative_observe request).trans same.symm))

noncomputable def motive (request : Request context) : Ty request.val.basedContext :=
  (result request).1

noncomputable def run (request : Request context) : QuotientCwf.Tm request.val.basedContext
    (motive request) := (result request).2

theorem result_requestOf (input : Based.Admitted context) :
    result (requestOf input) = nativeResult input :=
  eq_of_heq (result_representative (requestOf input) input rfl)

theorem motive_requestOf (input : Based.Admitted context) :
    motive (requestOf input) = tySub (QType.mk input.motiveType) input.presentation.hom :=
  congrArg Sigma.fst (result_requestOf input)

/-- Exact native representative law in the dependent output fibre. -/
theorem run_requestOf (input : Based.Admitted context) :
    HEq (run (requestOf input)) input.chosenJ := by
  have dependent {first second : Result (observe input)} (same : first = second) :
      HEq first.2 second.2 := by
    cases same
    rfl
  exact dependent (result_requestOf input)

/-- Every other dependent operation with the exact native representative
law is this descended operation. Coverage, rather than a chosen source
representative, determines it. -/
theorem result_unique (alternative : (request : Request context) → Result request.val)
    (agrees : ∀ input : Based.Admitted context,
      alternative (requestOf input) = nativeResult input) : alternative = result := by
  funext request
  obtain ⟨input, rfl⟩ := requestOf_surjective request
  exact (agrees input).trans (result_requestOf input).symm

theorem run_requestOf_value (input : Based.Admitted context) :
    (run (requestOf input)).val = input.chosenJ.val :=
  QuotientComprehensionSyntax.heq_value (motive_requestOf input) (run_requestOf input)

theorem run_representative (request : Request context) (input : Based.Admitted context)
    (same : observe input = request.val) : HEq (run request) input.chosenJ := by
  have requests : requestOf input = request := Subtype.ext same
  cases requests
  exact run_requestOf input

/-- The method annotation is derived from the descended motive at the
canonical section; it is not postulated in the image membership predicate. -/
theorem motive_reflexivity (request : Request context) :
    tySub (motive request) (QuotientIdentityGeometry.reflSection request.val.left) =
      request.val.method.type := by
  obtain ⟨input, rfl⟩ := requestOf_surjective request
  exact (congrArg
    (fun type => tySub type (QuotientIdentityGeometry.reflSection (TermFibre.mk input.leftTerm)))
    (motive_requestOf input)).trans
      ((QuotientIdentityGeometry.admitted_motive_reflexivity input).trans input.base.property.symm)

noncomputable def method (request : Request context) : QuotientCwf.Tm
    ((quotientProjection _).obj context)
    (tySub (motive request) (QuotientIdentityGeometry.reflSection request.val.left)) :=
  ⟨request.val.method, (motive_reflexivity request).symm⟩

/-- Beta holds for every image request and returns the retained semantic
method, including when the internal representative is different. -/
theorem beta_value (request : Request context) :
    (tmSub (run request) (QuotientIdentityGeometry.reflSection request.val.left)).val =
      request.val.method := by
  obtain ⟨input, rfl⟩ := requestOf_surjective request
  exact (congrArg
    (fun value => totalSub value
      (QuotientIdentityGeometry.reflSection (TermFibre.mk input.leftTerm)))
    (run_requestOf_value input)).trans (QuotientIdentityGeometry.admitted_beta_value input)

theorem beta (request : Request context) :
    tmSub (run request) (QuotientIdentityGeometry.reflSection request.val.left) = method request :=
  Subtype.ext (beta_value request)

/-- The family-only input is available as an explicit forgetful view of a
retained request; the operation itself does not factor through this view. -/
noncomputable def body (request : Request context) :
    Mettapedia.TypeTheory.ContextualBasedIdentityScope.Input
      (formation (OpaqueRelatorExtension.rules signature))
      (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature)) where
  context := (quotientProjection _).obj context
  type := request.val.type
  left := request.val.left
  motive := motive request
  base := method request

theorem body_requestOf (input : Based.Admitted context) :
    body (requestOf input) = semanticInput input := by
  apply body_input_ext
  · rfl
  · rfl
  · rfl
  · exact heq_of_eq (motive_requestOf input)
  · exact QuotientComprehensionSyntax.heq_of_value rfl

namespace Controls

/-- The mixed wire/list/path workload and its independently admitted,
converted four-parameter version have one semantic request. -/
theorem mixed_request_equal (wire : NativeWireData.Wire) :
    requestOf (QuotientIdentity.Controls.mixedInput wire) =
      requestOf (QuotientBasedJRepresentation.Controls.convertedMixedInput wire) := by
  apply (requestOf_eq_iff _ _).mpr
  obtain ⟨types, lefts, motives, methods⟩ :=
    QuotientIdentityInputCoherence.Controls.mixed_parameter_classes wire
  exact Observation.ext types lefts motives methods

theorem mixed_run_exact (wire : NativeWireData.Wire) :
    HEq (run (requestOf (QuotientIdentity.Controls.mixedInput wire)))
      (QuotientBasedJRepresentation.Controls.convertedMixedInput wire).chosenJ :=
  run_representative _ _ (congrArg Subtype.val (mixed_request_equal wire)).symm

/-- The actual neutral motive function and its eta expansion are retained
as different requests, although their body/method view is identical. -/
theorem eta_requests_distinct :
    requestOf (abstractedInput QuotientIdentityInputCoherence.Controls.variableInput) ≠
      requestOf QuotientIdentityInputCoherence.Controls.variableInput := by
  intro same
  exact QuotientIdentityInputCoherence.Controls.eta_collision_function
    (congrArg (fun request => request.val.motiveFunction) same).symm

theorem eta_bodies_equal :
    body (requestOf (abstractedInput QuotientIdentityInputCoherence.Controls.variableInput)) =
      body (requestOf QuotientIdentityInputCoherence.Controls.variableInput) :=
  (body_requestOf _).trans
    (QuotientIdentityInputCoherence.Controls.eta_collision_semantic_input.trans
      (body_requestOf _).symm)

theorem eta_runs_distinct :
    ¬ HEq (run (requestOf (abstractedInput QuotientIdentityInputCoherence.Controls.variableInput)))
      (run (requestOf QuotientIdentityInputCoherence.Controls.variableInput)) := by
  intro same
  exact QuotientIdentityInputCoherence.Controls.eta_collision_chosen_j_heq
    ((run_requestOf _).symm.trans (same.symm.trans (run_requestOf _)))

end Controls

#print axioms chosenInputMap_eq
#print axioms chosen_motive_coherent
#print axioms chosen_j_coherent
#print axioms semantic_input_coherent
#print axioms requestOf_surjective
#print axioms run_representative
#print axioms beta
#print axioms Controls.mixed_run_exact
#print axioms Controls.eta_runs_distinct

end FormationSensitiveContextual.QuotientRetainedIdentity
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
