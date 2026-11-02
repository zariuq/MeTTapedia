import Mettapedia.Logic.HOL.ConstructorArgumentMap
import Mettapedia.Logic.HOL.ConstructorPredicateRepresentationSemantics
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionSemantics

/-!
# Two admitted arguments are necessary for reflected constructor equality

Lowering observes a Boolean function at false. Raising produces a constant
function, and admission is its actual image. Thus lowering is noninjective
on the ambient function space but recovers every admitted payload. The raw
constructor pairs the lowered bit with its child bit. The generic retained
reflection theorem applies to two admitted inputs; retaining only the first
admission admits an explicit collision with the identity function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.ConstructorArgumentMapControls
open CurriedPredicates FiniteConstructorEncoding

inductive Base where | bit | pair
abbrev B : Ty Base := .base .bit
abbrev S : Ty Base := B ⇒ B
abbrev R : Ty Base := .base .pair
abbrev Bit := ULift.{1} Bool
abbrev Payload := Bit → Bit

inductive Const : Ty Base → Type where
  | raw : Const (B ⇒ B ⇒ B ⇒ R)
  | bit (value : Bool) : Const B

def carriers : Base → Type 1
  | .bit => Bit
  | .pair => ULift.{1} (Bool × Bool)
def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carriers type
  | _,.raw => fun _ payload children => .up (payload.down,children.down)
  | _,.bit value => .up value
def model : HenkinModel.{0,0,0} Base Const := .standard carriers meaning
def values : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def raw {Γ : Ctx Base} : Term Const Γ (B ⇒ B ⇒ B ⇒ R) := .const .raw
def lower {Γ : Ctx Base} : Term Const Γ (S ⇒ B) := .lam (.app (.var .vz) (.const (.bit false)))
def raise {Γ : Ctx Base} : Term Const Γ (B ⇒ S) := .lam (.lam (.var (.vs .vz)))
def allBits {Γ : Ctx Base} : Term Const Γ (B ⇒ .prop) := .lam .top
def image {Γ : Ctx Base} : Term Const Γ (S ⇒ .prop) := ConstructorPredicateRepresentation.lift raise allBits

theorem lower_subst {Γ Ξ : Ctx Base} (images : Subst Const Γ Ξ) : subst images lower = lower := rfl
theorem raise_subst {Γ Ξ : Ctx Base} (images : Subst Const Γ Ξ) : subst images raise = raise := rfl
theorem image_subst {Γ Ξ : Ctx Base} (images : Subst Const Γ Ξ) : subst images image = image := by
  rw [image,ConstructorPredicateRepresentation.lift_subst,raise_subst]
  rfl

private def domainBody {Γ : Ctx Base} (guard : Term Const Γ (S ⇒ .prop)) :
    FieldBody Const Γ [B,S,B] .prop := fun images arguments => .app (subst images guard) arguments.2.1
private theorem domainBody_natural {Γ : Ctx Base} (guard : Term Const Γ (S ⇒ .prop)) :
    NaturalFieldBody (domainBody guard) := by
  intro Ξ Ω earlier later arguments
  simp only [domainBody,HOL.subst,HOL.subst_comp]
  rfl
private def domainOf {Γ : Ctx Base} (guard : Term Const Γ (S ⇒ .prop)) :
    Term Const Γ (GuardedConstructorProjections.Admission B S B) := abstractFields [B,S,B] (domainBody guard)
private theorem domainOf_subst {Γ Ξ : Ctx Base} (guard : Term Const Γ (S ⇒ .prop)) (images : Subst Const Γ Ξ) :
    subst images (domainOf guard) = domainOf (subst images guard) := by
  rw [domainOf,abstractFields_subst _ _ _ (domainBody_natural guard)]
  apply congrArg (abstractFields [B,S,B])
  funext Ω later arguments
  simp only [domainBody,HOL.subst_comp]
  rfl

def domain {Γ : Ctx Base} : Term Const Γ (GuardedConstructorProjections.Admission B S B) := domainOf image
theorem domain_subst {Γ Ξ : Ctx Base} (images : Subst Const Γ Ξ) : subst images domain = domain := by
  rw [domain,domainOf_subst,image_subst]
  rfl

private def domain_beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (tag : Term Const Γ B) (payload : Term Const Γ S) (children : Term Const Γ B) :
    ProofSyntax Const Δ (.eq (GuardedConstructorProjections.admitted domain tag payload children) (.app image payload)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [B,S,B] (domainBody image)
    (domainBody_natural image) (tag,payload,children,PUnit.unit))
  simp only [domainBody]
  rfl

private def lower_beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (function : Term Const Γ S) :
    ProofSyntax Const Δ (.eq (.app lower function) (.app function (.const (.bit false)))) :=
  .beta function (.app (.var .vz) (.const (.bit false)))
private def raise_beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (bit : Term Const Γ B) :
    ProofSyntax Const Δ (.eq (.app raise bit) (.lam (weaken bit))) :=
  .beta bit (.lam (.var (.vs .vz)))

def leafRoundtrip {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (bit : Term Const Γ B) :
    ProofSyntax Const Δ (.eq (.app lower (.app raise bit)) bit) :=
  .eqTrans (lower_beta (.app raise bit))
    (.eqTrans (.eqApp (.const (.bit false)) (raise_beta bit))
      (ProofSyntax.castIndices rfl (congrArg (Term.eq _) (instantiate_weaken (.const (.bit false)) bit))
        (.beta (.const (.bit false)) (weaken bit))))

def leafLaw {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
    ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse raise lower) :=
  .allI (leafRoundtrip (.var .vz))

theorem leafLaw_free {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
    (leafLaw (Γ := Γ) (Δ := Δ)).FunctionExtensionalityFree := by
  change (leafRoundtrip (Δ := weakenHyps Δ) (.var .vz)).FunctionExtensionalityFree
  exact ⟨True.intro,True.intro,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

private theorem domain_beta_free {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (tag : Term Const Γ B) (payload : Term Const Γ S) (children : Term Const Γ B) :
    (domain_beta (Δ := Δ) tag payload children).FunctionExtensionalityFree := by
  unfold domain_beta
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    (abstractFields_beta_free [B,S,B] (domainBody image) (domainBody_natural image) (tag,payload,children,PUnit.unit))

def recovery {Γ : Ctx Base} (Δ : List (Formula Const Γ)) : ConstructorArgumentMap.Recovery Δ lower raise domain := by
  intro Ξ images assumptions _transport tag payload children present
  have current : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted domain tag payload children) := by
    apply ProofSyntax.castIndices rfl ?_ present
    rw [domain_subst]
  have admitted : ProofSyntax Const assumptions (.app image payload) := .impE (.eqPropEL (domain_beta tag payload children)) current
  have recovered := ConstructorPredicateRepresentation.recover raise lower allBits payload leafLaw admitted
  apply ProofSyntax.castIndices rfl ?_ recovered
  rw [lower_subst,raise_subst]

theorem recovery_free {Γ : Ctx Base} (Δ : List (Formula Const Γ)) : ConstructorArgumentMap.Recovery.Free (recovery Δ) := by
  intro Ξ images assumptions transport tag payload children present presentFree
  unfold recovery
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ConstructorPredicateRepresentation.recover_free
  · exact leafLaw_free
  · exact ⟨domain_beta_free _ _ _,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr presentFree⟩

def premises : List (ClosedFormula Const) := [ConstructorProjections.fieldInjective raw]
def reflectedProof : ProofSyntax Const premises (GuardedConstructorProjections.fieldInjective
    (ConstructorArgumentMap.constructor raw lower) domain) :=
  ConstructorArgumentMap.fieldInjective raw lower raise domain (.hyp ⟨0,by simp [premises]⟩) (recovery premises)

theorem reflectedProof_free : reflectedProof.FunctionExtensionalityFree :=
  ConstructorArgumentMap.fieldInjective_free _ _ _ _ _ _ True.intro (recovery_free premises)

theorem raw_separates : model.models (ConstructorProjections.fieldInjective (raw : ClosedTerm Const _)) := by
  intro _tag _ payload _ children _ _otherTag _ otherPayload _ otherChildren _ same
  change model.Eqv B otherPayload payload ∧ model.Eqv B otherChildren children
  have pairSame : (otherPayload.down,otherChildren.down) = (payload.down,children.down) := congrArg ULift.down same
  exact ⟨congrArg ULift.up (congrArg Prod.fst pairSame),congrArg ULift.up (congrArg Prod.snd pairSame)⟩

theorem premises_realizable : Soundness.SatisfiesHyps model values premises := by
  intro formula present
  have same : formula = ConstructorProjections.fieldInjective raw := by simpa only [premises,List.mem_singleton] using present
  cases same
  exact (model.models_iff_denote_closed _ values).mp raw_separates

theorem reflected_holds : (model.denote (GuardedConstructorProjections.fieldInjective
    (ConstructorArgumentMap.constructor raw lower) domain) values).down :=
  Soundness.extDerivation_sound reflectedProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) premises_realizable

theorem two_admission_reflection (tag : Bit) (payload : Payload) (children : Bit)
    (admitted : (model.denote domain values tag payload children).down)
    (otherTag : Bit) (otherPayload : Payload) (otherChildren : Bit)
    (otherAdmitted : (model.denote domain values otherTag otherPayload otherChildren).down)
    (same : model.denote (ConstructorArgumentMap.constructor raw lower) values otherTag otherPayload otherChildren =
      model.denote (ConstructorArgumentMap.constructor raw lower) values tag payload children) :
    otherPayload = payload ∧ otherChildren = children :=
  (GuardedConstructorProjections.fieldInjective_denote_full model full _ domain values).mp reflected_holds
    tag payload children admitted otherTag otherPayload otherChildren otherAdmitted same

def falsePayload : Payload := fun _ => .up false
def truePayload : Payload := fun _ => .up true
def identityPayload : Payload := id

theorem false_admitted (tag children : Bit) : (model.denote domain values tag falsePayload children).down := by
  change (model.denote image values falsePayload).down
  exact (ConstructorPredicateRepresentation.lift_denote_full model full raise allBits values falsePayload).mpr ⟨.up false,True.intro,rfl⟩

theorem true_admitted (tag children : Bit) : (model.denote domain values tag truePayload children).down := by
  change (model.denote image values truePayload).down
  exact (ConstructorPredicateRepresentation.lift_denote_full model full raise allBits values truePayload).mpr ⟨.up true,True.intro,rfl⟩

theorem admitted_payloads_nontrivial : ∃ first second : Payload, first ≠ second ∧
    (model.denote domain values (.up false) first (.up false)).down ∧
    (model.denote domain values (.up false) second (.up false)).down := by
  refine ⟨falsePayload,truePayload,?_,false_admitted _ _,true_admitted _ _⟩
  intro same
  exact Bool.noConfusion (congrArg ULift.down (congrFun same (.up false)))

theorem payloads_distinct : identityPayload ≠ falsePayload := by
  intro same
  exact Bool.noConfusion (congrArg ULift.down (congrFun same (.up true)))

theorem identity_not_admitted (tag children : Bit) : ¬ (model.denote domain values tag identityPayload children).down := by
  intro present
  change (model.denote image values identityPayload).down at present
  obtain ⟨bit,_,same⟩ := (ConstructorPredicateRepresentation.lift_denote_full model full raise allBits values identityPayload).mp present
  have atFalse : bit = ULift.up false := congrFun same (.up false)
  have atTrue : bit = ULift.up true := congrFun same (.up true)
  exact Bool.noConfusion (congrArg ULift.down (atTrue.symm.trans atFalse))

theorem lower_noninjective : ¬ Function.Injective (model.denote (lower : ClosedTerm Const _) values) := by
  intro injective
  exact payloads_distinct (injective (show model.denote lower values identityPayload = model.denote lower values falsePayload from rfl))

theorem admitted_recovery (tag : Bit) (payload : Payload) (children : Bit)
    (present : (model.denote domain values tag payload children).down) :
    model.denote raise values (model.denote lower values payload) = payload := by
  change (model.denote image values payload).down at present
  obtain ⟨bit,_,same⟩ := (ConstructorPredicateRepresentation.lift_denote_full model full raise allBits values payload).mp present
  rw [← same]
  rfl

theorem one_admission_counterexample :
    (model.denote domain values (.up false) falsePayload (.up false)).down ∧
    ¬ (model.denote domain values (.up false) identityPayload (.up false)).down ∧
    model.denote (ConstructorArgumentMap.constructor raw lower) values (.up false) identityPayload (.up false) =
      model.denote (ConstructorArgumentMap.constructor raw lower) values (.up false) falsePayload (.up false) ∧
    identityPayload ≠ falsePayload :=
  ⟨false_admitted _ _,identity_not_admitted _ _,rfl,payloads_distinct⟩

theorem one_admission_reflection_refused : ¬ ∀ tag payload children,
    (model.denote domain values tag payload children).down →
      ∀ otherTag otherPayload otherChildren,
        model.denote (ConstructorArgumentMap.constructor raw lower) values otherTag otherPayload otherChildren =
          model.denote (ConstructorArgumentMap.constructor raw lower) values tag payload children →
        otherPayload = payload ∧ otherChildren = children := by
  intro claimed
  exact payloads_distinct (claimed (.up false) falsePayload (.up false) (false_admitted _ _)
    (.up false) identityPayload (.up false) rfl).1

theorem raw_payload_nontrivial :
    model.denote (raw : ClosedTerm Const _) values (.up false) (.up true) (.up false) ≠
      model.denote raw values (.up false) (.up false) (.up false) := by
  intro same
  exact Bool.noConfusion (congrArg (fun value => value.down.1) same)
theorem raw_children_nontrivial :
    model.denote (raw : ClosedTerm Const _) values (.up false) (.up false) (.up true) ≠
      model.denote raw values (.up false) (.up false) (.up false) := by
  intro same
  exact Bool.noConfusion (congrArg (fun value => value.down.2) same)

#print axioms leafLaw
#print axioms leafLaw_free
#print axioms reflectedProof
#print axioms reflectedProof_free
#print axioms premises_realizable
#print axioms two_admission_reflection
#print axioms one_admission_reflection_refused
end Mettapedia.Logic.HOL.ConstructorArgumentMapControls
