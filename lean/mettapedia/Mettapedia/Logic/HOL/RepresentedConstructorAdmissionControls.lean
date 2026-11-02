import Mettapedia.Logic.HOL.RepresentedConstructorAdmission
import Mettapedia.Logic.HOL.ConstructorFieldRepresentationControls

/-!
# Recovery-domain controls for represented constructor uniqueness

The canonical retraction domain admits every payload fixed by lowering and
raising. Finite packed payloads enter it through actual field recovery.
This tests the general theorem without claiming that an arbitrary source
predicate supplies the required recovery evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RepresentedConstructorAdmissionControls
open FiniteConstructorEncoding MixedConstructorPayloadMaps
universe u v
section General
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {number source target children carrier : Ty Base} {Δ : List (Formula Const Γ)}

def body (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source)) :
    ArgumentBody Const Γ [number,Payload number source,children] :=
  fun images fields => .eq (mapPayload (HOL.subst images raise) (mapPayload (HOL.subst images lower) fields.2.1)) fields.2.1

theorem body_natural (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source)) :
    NaturalBody (body (number := number) (children := children) lower raise) := by
  intro Ξ Ω first later fields
  simp only [body,HOL.subst,mapPayload_subst,HOL.subst_comp,substituteArguments]
  rfl

def domain (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source)) :
    Term Const Γ (GuardedConstructorProjections.Admission number (Payload number source) children) :=
  abstractArguments [number,Payload number source,children] (body lower raise)

theorem domain_subst (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (domain (number := number) (children := children) lower raise) =
      domain (HOL.subst images lower) (HOL.subst images raise) := by
  rw [domain,abstractArguments_subst _ _ _ (body_natural lower raise)]
  apply congrArg (abstractArguments [number,Payload number source,children])
  funext Ω later fields
  simp only [body,HOL.subst_comp]
  rfl

def atArguments (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (tag : Term Const Γ number) (payload : Term Const Γ (Payload number source)) (branches : Term Const Γ children) :
    ProofSyntax Const Δ (.eq (GuardedConstructorProjections.admitted (domain lower raise) tag payload branches)
      (.eq (mapPayload raise (mapPayload lower payload)) payload)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractArguments_beta [number,Payload number source,children]
    (body lower raise) (body_natural lower raise) (tag,payload,branches,PUnit.unit))
  have identity {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [body,identity]
  rfl

theorem atArguments_free (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (tag : Term Const Γ number) (payload : Term Const Γ (Payload number source)) (branches : Term Const Γ children) :
    (atArguments (Δ := Δ) lower raise tag payload branches).FunctionExtensionalityFree := by
  unfold atArguments
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (abstractArguments_beta_free _ _ _ _)

def recovery (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source)) :
    RepresentedConstructorAdmission.Recovery Δ lower raise (domain (number := number) (children := children) lower raise) := by
  intro Ξ images assumptions _transport tag payload branches present
  apply ProofSyntax.impE (.eqPropEL (atArguments (HOL.subst images lower) (HOL.subst images raise) tag payload branches))
  exact ProofSyntax.castIndices rfl
    (congrArg (fun relation => GuardedConstructorProjections.admitted relation tag payload branches) (domain_subst lower raise images)) present

theorem recovery_free (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source)) :
    RepresentedConstructorAdmission.Recovery.Free
      (recovery (Δ := Δ) (number := number) (children := children) lower raise) := by
  intro Ξ images assumptions _transport tag payload branches present free
  exact ⟨atArguments_free _ _ _ _ _,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free⟩

def admitPacked (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (tag index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number)
    (branches : Term Const Γ children)
    (field : ProofSyntax Const Δ (.eq (.app raise (.app lower element)) element)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.admitted (domain lower raise) tag (pack index element shape) branches) :=
  .impE (.eqPropER (atArguments lower raise tag (pack index element shape) branches)) (roundtrip_at lower raise index element shape field)

def guardedLaw
    (raw : Term Const Γ (ConstructorPayloadTransport.Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective (ConstructorPayloadTransport.constructor raw lower) (domain lower raise)) :=
  RepresentedConstructorAdmission.fieldInjective raw lower raise _ rawLaw (recovery lower raise)

theorem guardedLaw_free
    (raw : Term Const Γ (ConstructorPayloadTransport.Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw)) (free : rawLaw.FunctionExtensionalityFree) :
    (guardedLaw raw lower raise rawLaw).FunctionExtensionalityFree :=
  RepresentedConstructorAdmission.fieldInjective_free _ _ _ _ _ _ free (recovery_free lower raise)

#print axioms guardedLaw_free
end General

namespace BoolSpace
open ConstructorFieldRepresentationControls

def storedPayload : Term Const [A] (Payload N E) :=
  pack (weaken marker) (.app (weaken encode) (.var .vz)) (weaken marker)

def fieldAdmission : Formula Const [A] :=
  GuardedConstructorProjections.admitted (weaken (domain decode encode)) (weaken marker)
    storedPayload (weaken branches)

def allFieldsAdmitted : ProofSyntax Const premises (.all fieldAdmission) := by
  apply ProofSyntax.allI
  have inverse : ProofSyntax Const (weakenHyps (σ := A) premises)
      (ConstructorFieldRepresentation.leftInverse (weaken (σ := A) encode) (weaken (σ := A) decode)) :=
    ProofSyntax.castIndices rfl (ConstructorFieldRepresentation.leftInverse_rename (Rename.weaken (σ := A)) encode decode)
      (recoveryProof.rename (Rename.weaken (σ := A)))
  have field := ConstructorFieldRepresentation.leftInverse_at (weaken encode) (weaken decode) (.var .vz) inverse
  apply ProofSyntax.castIndices rfl ?_
    (admitPacked (weaken decode) (weaken encode) (weaken marker) (weaken marker)
      (.app (weaken encode) (.var .vz)) (weaken marker) (weaken branches) (.eqAppArg (weaken encode) field))
  apply congrArg (fun relation => GuardedConstructorProjections.admitted relation (weaken marker)
    (pack (weaken marker) (.app (weaken encode) (.var .vz)) (weaken marker)) (weaken branches))
  symm
  simpa only [subst_ofRename,weaken] using
    (domain_subst (number := N) (children := N ⇒ E) decode encode (Subst.ofRename (Rename.weaken (σ := A))))

theorem all_fields_admitted : (model.denote (.all fieldAdmission) values).down :=
  Soundness.extDerivation_sound allFieldsAdmitted.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem two_fields_admitted :
    (model.denote fieldAdmission (model.extend (σ := A) values (ULift.up true : Element))).down ∧
    (model.denote fieldAdmission (model.extend (σ := A) values (ULift.up false : Element))).down :=
  ⟨all_fields_admitted (ULift.up true : Element) (full A _),
    all_fields_admitted (ULift.up false : Element) (full A _)⟩

abbrev StoredPayloadValue := (Number → Space → Number → ULift.{1,0} Prop) → ULift.{1,0} Prop

noncomputable def packedValue (field : Element) : StoredPayloadValue :=
  fun handler => handler (ULift.up 0) (model.denote encode values field) (ULift.up 0)

theorem stored_payload_meaning (field : Element) :
    model.denote storedPayload (model.extend (σ := A) values field) = packedValue field := by rfl

theorem packed_fields_distinct : packedValue (ULift.up true) ≠ packedValue (ULift.up false) := by
  intro same
  let observer : Number → Space → Number → ULift.{1,0} Prop :=
    fun _ stored _ => ULift.up (stored = model.denote encode values (ULift.up true))
  have observed := congrArg (fun payload : StoredPayloadValue => (payload observer).down) same
  change (model.denote encode values (ULift.up true) = model.denote encode values (ULift.up true)) =
    (model.denote encode values (ULift.up false) = model.denote encode values (ULift.up true)) at observed
  exact distinct_fields_remain_distinct (Eq.mp observed rfl).symm

theorem admitted_payloads_distinct :
    model.denote storedPayload (model.extend (σ := A) values (ULift.up true : Element)) ≠
      model.denote storedPayload (model.extend (σ := A) values (ULift.up false : Element)) := by
  rw [stored_payload_meaning,stored_payload_meaning]
  exact packed_fields_distinct

def representedLaw : ProofSyntax Const premises (GuardedConstructorProjections.fieldInjective
    (ConstructorPayloadTransport.constructor raw decode) (domain decode encode)) :=
  guardedLaw raw decode encode (.hyp ⟨2,by simp [premises]⟩)

theorem represented_law_holds : (model.denote (GuardedConstructorProjections.fieldInjective
    (ConstructorPayloadTransport.constructor raw decode) (domain decode encode)) values).down :=
  Soundness.extDerivation_sound representedLaw.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem recovery_on_the_entire_carrier_refused : ¬ ∀ stored : Space,
    model.denote encode values (model.denote decode values stored) = stored := global_reverse_roundtrip_refused

#print axioms two_fields_admitted
#print axioms packed_fields_distinct
#print axioms admitted_payloads_distinct
#print axioms represented_law_holds
#print axioms recovery_on_the_entire_carrier_refused
end BoolSpace
end Mettapedia.Logic.HOL.RepresentedConstructorAdmissionControls
