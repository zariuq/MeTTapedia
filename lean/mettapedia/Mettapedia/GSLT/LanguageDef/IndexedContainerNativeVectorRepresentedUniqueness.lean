import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedAdmission
import Mettapedia.Logic.HOL.IndexedContainerFieldReadback
import Mettapedia.Logic.HOL.RepresentedConstructorAdmission
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionTransport

/-!
# Whole-domain uniqueness for the represented original constructor

The generated source shape is eliminated at an arbitrary admitted payload.
Its retained payload-field guard supplies direct-image membership, from which
the source embedding recovers that field. Mapping the complete finite payload
down and back therefore fixes every admitted payload. The raw source
constructor law can then recover the original payload and child function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedUniqueness
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorRepresentedAdmission
open FiniteConstructorEncoding MixedConstructorPayloadMaps

variable {Γ Ξ : Ctx Base} {A : Ty Base} {Δ : List (Formula Const Γ)}

def tagMember (predicate : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed predicate length tag shape)) :
    ProofSyntax Const Δ (.app predicate tag) := by
  exact (guards.readEvidence code (parameterMap predicate) (arguments length tag shape) allowed).2.1

theorem tagMember_free (predicate : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed predicate length tag shape))
    (free : allowed.FunctionExtensionalityFree) : (tagMember predicate length tag shape allowed).FunctionExtensionalityFree :=
  (guards.readEvidence_free code (parameterMap predicate) (arguments length tag shape) allowed free).2.1

theorem allowed_subst (predicate : Term Const Γ (E ⇒ .prop)) (images : Subst Const Γ Ξ) :
    HOL.subst images ((constructors predicate).allowed (occurrence predicate)) =
      (constructors (HOL.subst images predicate)).allowed (occurrence (HOL.subst images predicate)) := by
  change HOL.subst images (guards.compile code (parameterMap predicate)) =
    guards.compile code (parameterMap (HOL.subst images predicate))
  rw [guards.compile_subst]
  apply congrArg (guards.compile code)
  funext type index
  cases index with
  | vz => rfl
  | vs impossible => nomatch impossible

theorem leftInverse_subst (encode : Term Const Γ (A ⇒ E)) (decode : Term Const Γ (E ⇒ A))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (ConstructorFieldRepresentation.leftInverse encode decode) =
      ConstructorFieldRepresentation.leftInverse (HOL.subst images encode) (HOL.subst images decode) := by
  simp only [ConstructorFieldRepresentation.leftInverse,HOL.subst,subst_weaken,Subst.lift]

theorem numeral_subst (images : Subst Const Γ Ξ) (number : Nat) :
    HOL.subst images (numeral Γ number) = numeral Ξ number := by
  induction number with
  | zero => exact subst_weakenCtx images original.zero
  | succ number previous =>
      change Term.app (HOL.subst images (weakenCtx Γ original.successor))
        (HOL.subst images (numeral Γ number)) = _
      rw [subst_weakenCtx,previous]
      rfl

theorem constructors_subst (predicate : Term Const Γ (E ⇒ .prop)) (images : Subst Const Γ Ξ) :
    (constructors predicate).subst images = constructors (HOL.subst images predicate) := by
  unfold constructors IndexedContainerPositionTerms.FieldGuards.constructors IndexedConstructorGuards.ConstructorPrograms.subst
  congr 1
  · funext number
    exact numeral_subst images number
  · funext selected
    fin_cases selected
    exact allowed_subst predicate images
  · funext selected
    fin_cases selected
    change HOL.subst images (reading.resultProgram code (parameterMap predicate)) =
      reading.resultProgram code (parameterMap (HOL.subst images predicate))
    rw [reading.resultProgram_subst]
    apply congrArg (reading.resultProgram code)
    funext type index
    cases index with
    | vz => rfl
    | vs impossible => nomatch impossible

theorem admission_subst (signature : RecursiveSpacePredicate.Contextual Const Γ) (images : Subst Const Γ Ξ) :
    HOL.subst images signature.constructorAdmission = (signature.subst images).constructorAdmission :=
  signature.constructorAdmission_subst images

@[irreducible] private def roundtripFromFields {lowerField upperField : Ty Base}
    (lower : Term Const Γ (lowerField ⇒ upperField)) (raise : Term Const Γ (upperField ⇒ lowerField))
    (payload : Term Const Γ (Payload N lowerField)) (length : Term Const Γ N)
    (element : Term Const Γ lowerField) (shape : Term Const Γ N)
    (field : ProofSyntax Const Δ (.eq (.app raise (.app lower element)) element))
    (same : ProofSyntax Const Δ (.eq payload (pack length element shape))) :
    ProofSyntax Const Δ (.eq (mapPayload raise (mapPayload lower payload)) payload) :=
  .eqTrans (mapPayload_congr raise _ _ (mapPayload_congr lower _ _ same))
    (.eqTrans (roundtrip_at lower raise length element shape field) (.eqSymm same))

private theorem roundtripFromFields_free {lowerField upperField : Ty Base}
    (lower : Term Const Γ (lowerField ⇒ upperField)) (raise : Term Const Γ (upperField ⇒ lowerField))
    (payload : Term Const Γ (Payload N lowerField)) (length : Term Const Γ N)
    (element : Term Const Γ lowerField) (shape : Term Const Γ N)
    (field : ProofSyntax Const Δ (.eq (.app raise (.app lower element)) element))
    (same : ProofSyntax Const Δ (.eq payload (pack length element shape)))
    (fieldFree : field.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (roundtripFromFields lower raise payload length element shape field same).FunctionExtensionalityFree := by
  unfold roundtripFromFields
  exact ⟨mapPayload_congr_free raise _ _ _ (mapPayload_congr_free lower _ _ same sameFree),
    roundtrip_at_free lower raise length element shape field fieldFree,sameFree⟩

@[irreducible] def shapeRoundtripCase (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (tag : Term Const Γ N) (payload : Term Const Γ (Payload N E))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (selected : Fin (constructors (given.payload source)).fields.length) :
    FieldCase Δ ((constructors (given.payload source)).fields.get selected)
      ((constructors (given.payload source)).shapeCasePredicate tag payload selected)
      (.eq (mapPayload given.encode (mapPayload given.decode payload)) payload) := by
  have only : selected = ⟨0,by change 0 < 1; decide⟩ := by
    apply Fin.ext
    change selected.val = 0
    have bound := selected.isLt
    change selected.val < 1 at bound
    omega
  cases only
  intro Ξ images fields
  let inventory := (constructors (given.payload source)).subst images
  let localAssumptions := applyArguments [N,E,N]
    (HOL.subst images ((constructors (given.payload source)).shapeCasePredicate tag payload ⟨0,by change 0 < 1; decide⟩)) fields ::
      Δ.map (HOL.subst images)
  have present : ProofSyntax Const localAssumptions
      (applyArguments [N,E,N] (inventory.shapeCasePredicate (HOL.subst images tag) (HOL.subst images payload) ⟨0,by change 0 < 1; decide⟩) fields) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    change applyArguments [N,E,N]
      (HOL.subst images ((constructors (given.payload source)).shapeCasePredicate tag payload ⟨0,by change 0 < 1; decide⟩)) fields = _
    exact congrArg (fun condition : Term Const Ξ (handlerType [N,E,N]) => applyArguments [N,E,N] condition fields)
      ((constructors (given.payload source)).shapeCasePredicate_subst images tag payload ⟨0,by change 0 < 1; decide⟩)
  have parts := inventory.shapeCase_parts (HOL.subst images tag) (HOL.subst images payload) ⟨0,by change 0 < 1; decide⟩ fields present
  have allowed : ProofSyntax Const localAssumptions (sourceAllowed
      (HOL.subst images (given.payload source)) fields.1 fields.2.1 fields.2.2.1) := by
    apply ProofSyntax.castIndices rfl ?_ (.andEL parts)
    change applyArguments [N,E,N] (HOL.subst images ((constructors (given.payload source)).allowed (occurrence (given.payload source)))) fields = _
    rw [allowed_subst]
    rfl
  have member := tagMember (HOL.subst images (given.payload source)) fields.1 fields.2.1 fields.2.2.1 allowed
  have shiftedLaw : ProofSyntax Const localAssumptions
      (ConstructorFieldRepresentation.leftInverse (HOL.subst images given.encode) (HOL.subst images given.decode)) :=
    ProofSyntax.castIndices rfl (leftInverse_subst _ _ images) ((law.subst images).prepend _)
  have field : ProofSyntax Const localAssumptions (.eq
      (.app (HOL.subst images given.encode) (.app (HOL.subst images given.decode) fields.2.1)) fields.2.1) := by
    apply ConstructorPredicateRepresentation.recover (HOL.subst images given.encode) (HOL.subst images given.decode)
      (HOL.subst images source) fields.2.1 shiftedLaw
    apply ProofSyntax.castIndices rfl ?_ member
    exact congrArg (fun predicate => Term.app predicate fields.2.1) (ConstructorPredicateRepresentation.lift_subst images given.encode source)
  have same : ProofSyntax Const localAssumptions (.eq (HOL.subst images payload) (pack fields.1 fields.2.1 fields.2.2.1)) :=
    .andER (.andER parts)
  apply ProofSyntax.castIndices rfl ?_
    (roundtripFromFields (HOL.subst images given.decode) (HOL.subst images given.encode)
      (HOL.subst images payload) fields.1 fields.2.1 fields.2.2.1 field same)
  simp only [HOL.subst,mapPayload_subst]

@[irreducible] def shapeRoundtrip (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (tag : Term Const Γ N) (payload : Term Const Γ (Payload N E))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (shape : ProofSyntax Const Δ (.app (.app (constructors (given.payload source)).shapeProgram tag) payload)) :
    ProofSyntax Const Δ (.eq (mapPayload given.encode (mapPayload given.decode payload)) payload) :=
  (constructors (given.payload source)).shapeProgram_elim tag payload _
    (shapeRoundtripCase given source tag payload law) shape

theorem shapeRoundtripCase_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (tag : Term Const Γ N) (payload : Term Const Γ (Payload N E))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (free : law.FunctionExtensionalityFree)
    (selected : Fin (constructors (given.payload source)).fields.length)
    (images : Subst Const Γ Ξ)
    (fields : Arguments Const Ξ ((constructors (given.payload source)).fields.get selected)) :
    (shapeRoundtripCase given source tag payload law selected images fields).FunctionExtensionalityFree := by
  have only : selected = ⟨0,by change 0 < 1; decide⟩ := by
    apply Fin.ext
    change selected.val = 0
    have bound := selected.isLt
    change selected.val < 1 at bound
    omega
  cases only
  unfold shapeRoundtripCase
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply roundtripFromFields_free
  · apply ConstructorPredicateRepresentation.recover_free
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_subst] using free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply tagMember_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply IndexedConstructorGuards.ConstructorPrograms.shapeCase_parts_free
      exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro
  · apply IndexedConstructorGuards.ConstructorPrograms.shapeCase_parts_free
    exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

theorem shapeRoundtrip_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (tag : Term Const Γ N) (payload : Term Const Γ (Payload N E))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (shape : ProofSyntax Const Δ (.app (.app (constructors (given.payload source)).shapeProgram tag) payload))
    (lawFree : law.FunctionExtensionalityFree) (shapeFree : shape.FunctionExtensionalityFree) :
    (shapeRoundtrip given source tag payload law shape).FunctionExtensionalityFree := by
  unfold shapeRoundtrip
  exact (constructors (given.payload source)).shapeProgram_elim_free tag payload _ _ shape
    (fun selected {_Ξ} images fields => shapeRoundtripCase_free given source tag payload law lawFree selected images fields) shapeFree

@[irreducible] def admittedRoundtrip (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (tag : Term Const Γ N) (payload : Term Const Γ (Payload N E)) (children : Term Const Γ (N ⇒ E))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (admitted : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom) tag payload children)) :
    ProofSyntax Const Δ (.eq (mapPayload given.encode (mapPayload given.decode payload)) payload) :=
  shapeRoundtrip given source tag payload law
    ((IndexedContainerNativeVectorConstructorAdmission.signature (given.payload source) given.construct bottom).admissionShape
      tag payload children admitted)

theorem admittedRoundtrip_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (tag : Term Const Γ N) (payload : Term Const Γ (Payload N E)) (children : Term Const Γ (N ⇒ E))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (admitted : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom) tag payload children))
    (lawFree : law.FunctionExtensionalityFree) (admittedFree : admitted.FunctionExtensionalityFree) :
    (admittedRoundtrip given source bottom tag payload children law admitted).FunctionExtensionalityFree := by
  unfold admittedRoundtrip
  exact shapeRoundtrip_free given source tag payload law _ lawFree
    ((IndexedContainerNativeVectorConstructorAdmission.signature (given.payload source) given.construct bottom).admissionShape_free
      tag payload children admitted admittedFree)

def compareAdmitted (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (firstTag secondTag : Term Const Γ N) (firstPayload secondPayload : Term Const Γ (Payload N E))
    (firstChildren secondChildren : Term Const Γ (N ⇒ E))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (firstAdmitted : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom) firstTag firstPayload firstChildren))
    (secondAdmitted : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom) secondTag secondPayload secondChildren))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply given.construct secondTag secondPayload secondChildren)
      (ConstructorProjections.apply given.construct firstTag firstPayload firstChildren))) :
    ProofSyntax Const Δ (.and (.eq secondPayload firstPayload) (.eq secondChildren firstChildren)) := by
  have parts := ConstructorPayloadTransport.compareLowered given.raw given.decode firstTag secondTag
    firstPayload secondPayload firstChildren secondChildren rawLaw same
  exact .andI (.eqTrans (.eqSymm (admittedRoundtrip given source bottom secondTag secondPayload secondChildren law secondAdmitted))
    (.eqTrans (mapPayload_congr given.encode _ _ (.andEL parts))
      (admittedRoundtrip given source bottom firstTag firstPayload firstChildren law firstAdmitted))) (.andER parts)

@[irreducible] def admissionShapeSubst (predicate : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ IndexedContainerNativeVectorConstructorProgram.RawConstructor) (bottom : Term Const Γ E)
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ N) (payload : Term Const Ξ (Payload N E)) (children : Term Const Ξ (N ⇒ E))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (IndexedContainerNativeVectorConstructorAdmission.domain predicate construct bottom)) tag payload children)) :
    ProofSyntax Const assumptions (.app (.app (HOL.subst images (constructors predicate).shapeProgram) tag) payload) :=
  (IndexedContainerNativeVectorConstructorAdmission.signature predicate construct bottom).admissionShapeSubst
    images tag payload children present

theorem admissionShapeSubst_free (predicate : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ IndexedContainerNativeVectorConstructorProgram.RawConstructor) (bottom : Term Const Γ E)
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ N) (payload : Term Const Ξ (Payload N E)) (children : Term Const Ξ (N ⇒ E))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (IndexedContainerNativeVectorConstructorAdmission.domain predicate construct bottom)) tag payload children))
    (free : present.FunctionExtensionalityFree) :
    (admissionShapeSubst predicate construct bottom images tag payload children present).FunctionExtensionalityFree := by
  unfold admissionShapeSubst
  exact (IndexedContainerNativeVectorConstructorAdmission.signature predicate construct bottom).admissionShapeSubst_free
    images tag payload children present free

private theorem shapeProgram_subst_forInputs (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (constructors (given.payload source)).shapeProgram =
      (constructors ((given.substitute images).payload (HOL.subst images source))).shapeProgram := by
  have first := IndexedConstructorGuards.ConstructorPrograms.shapeProgram_subst
    (constructors (given.payload source)) images
  have second := congr_arg_heq
    (fun inventory : IndexedConstructorGuards.ConstructorPrograms Const Ξ => inventory.shapeProgram)
    (constructors_subst (given.payload source) images)
  have third := congrArg (fun predicate : Term Const Ξ (E ⇒ .prop) =>
    (show Term Const Ξ (N ⇒ Payload N E ⇒ .prop) from (constructors predicate).shapeProgram))
    (given.payload_subst source images)
  exact first.trans ((eq_of_heq second).trans third)

@[irreducible] private def transportProof {first second : Formula Const Γ}
    (same : first = second) (proof : ProofSyntax Const Δ first) : ProofSyntax Const Δ second :=
  proof.castIndices rfl same

private theorem transportProof_free {first second : Formula Const Γ}
    (same : first = second) (proof : ProofSyntax Const Δ first) (free : proof.FunctionExtensionalityFree) :
    (transportProof same proof).FunctionExtensionalityFree := by
  unfold transportProof
  exact (ProofSyntax.functionExtensionalityFree_castIndices rfl same proof).mpr free

@[irreducible] def admittedRoundtripSubst (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ N) (payload : Term Const Ξ (Payload N E)) (children : Term Const Ξ (N ⇒ E))
    (law : ProofSyntax Const assumptions (ConstructorFieldRepresentation.leftInverse
      (HOL.subst images given.encode) (HOL.subst images given.decode)))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom))
      tag payload children)) :
    ProofSyntax Const assumptions (.eq
      (mapPayload (HOL.subst images given.encode) (mapPayload (HOL.subst images given.decode) payload)) payload) := by
  apply ProofSyntax.castIndices rfl ?_ (shapeRoundtrip (given.substitute images) (HOL.subst images source) tag payload
    (ProofSyntax.castIndices rfl (congrArg₂ ConstructorFieldRepresentation.leftInverse
      (given.encode_subst images) (given.decode_subst images)) law)
    (transportProof
      (congrArg (fun program : Term Const Ξ (N ⇒ Payload N E ⇒ .prop) => Term.app (Term.app program tag) payload)
        (shapeProgram_subst_forInputs given source images))
      (admissionShapeSubst (given.payload source) given.construct bottom images tag payload children present)))
  · rw [given.encode_subst,given.decode_subst]

theorem admittedRoundtripSubst_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ N) (payload : Term Const Ξ (Payload N E)) (children : Term Const Ξ (N ⇒ E))
    (law : ProofSyntax Const assumptions (ConstructorFieldRepresentation.leftInverse
      (HOL.subst images given.encode) (HOL.subst images given.decode)))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom))
      tag payload children)) (lawFree : law.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (admittedRoundtripSubst given source bottom images tag payload children law present).FunctionExtensionalityFree := by
  unfold admittedRoundtripSubst
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply shapeRoundtrip_free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr lawFree
  · apply transportProof_free
    exact admissionShapeSubst_free (given.payload source) given.construct bottom images tag payload children present presentFree

def fieldInjective (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective given.construct
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom)) := by
  apply RepresentedConstructorAdmission.fieldInjective given.raw given.decode given.encode _ rawLaw
  intro Ξ images assumptions transport tag payload children present
  apply admittedRoundtripSubst given source bottom images tag payload children _ present
  exact ProofSyntax.castIndices rfl (leftInverse_subst _ _ images) ((law.subst images).mono transport)

theorem fieldInjective_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (rawFree : rawLaw.FunctionExtensionalityFree) (lawFree : law.FunctionExtensionalityFree) :
    (fieldInjective given source bottom rawLaw law).FunctionExtensionalityFree := by
  unfold fieldInjective
  apply RepresentedConstructorAdmission.fieldInjective_free
  · exact rawFree
  · intro Ξ images assumptions transport tag payload children present presentFree
    apply admittedRoundtripSubst_free
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_subst] using lawFree
    · exact presentFree

def fromSource (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective given.construct
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom)) :=
  fieldInjective given source bottom (given.fieldInjectivity sourceLaw) (given.roundtrip payloadChoice fieldChoice sourceLaw)

theorem fromSource_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (sourceFree : sourceLaw.FunctionExtensionalityFree) :
    (fromSource given source bottom payloadChoice fieldChoice sourceLaw).FunctionExtensionalityFree :=
  fieldInjective_free given source bottom _ _ (given.fieldInjectivity_free sourceLaw sourceFree)
    (given.roundtrip_free payloadChoice fieldChoice sourceLaw payloadFree fieldFree sourceFree)

#print axioms tagMember
#print axioms shapeRoundtrip
#print axioms fieldInjective
#print axioms fromSource_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedUniqueness
