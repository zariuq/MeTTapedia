import Mettapedia.Logic.HOL.IndexedContainerGuardElimination
import Mettapedia.Logic.HOL.PredicateContextInstantiation

/-!
# Predicate contexts generated from original payload fields

Data fields extend the index environment. Registered shape fields introduce
their actual guard without extending that environment. Recursive fields stay
in the separate child condition, matching the existing payload layout.
The generated variable assignment retains the original payload field order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms.FieldGuards

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open FiniteConstructorEncoding PredicateContexts
universe u v w
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
    {Const : Ty Base → Type w} {parameters : Nat} {reading : Reading I registry Const}
    {Γ Ξ : Ctx Base}

def payloadScope : {context : List I.SortCode} → Code I registry parameters context → Ctx Base → Ctx Base
  | _, .result _, ambient => ambient
  | _, .data sort rest, ambient => payloadScope rest (reading.indices.sort sort :: ambient)
  | _, .recursive _ rest, ambient => payloadScope rest ambient
  | _, .nested name entry registered _ _ rest, ambient =>
      payloadScope rest (reading.shapeType name entry registered :: ambient)

def payloadEmbedding : {context : List I.SortCode} → (code : Code I registry parameters context) →
    (ambient : Ctx Base) → Rename Base ambient (payloadScope (reading := reading) code ambient)
  | _, .result _, _, _, index => index
  | _, .data _ rest, _, _, index => payloadEmbedding rest _ (.vs index)
  | _, .recursive _ rest, _, _, index => payloadEmbedding rest _ index
  | _, .nested _ _ _ _ _ rest, _, _, index => payloadEmbedding rest _ (.vs index)

def payloadVariables : {context : List I.SortCode} → (code : Code I registry parameters context) →
    (ambient : Ctx Base) → Arguments Const (payloadScope (reading := reading) code ambient) (reading.fields code)
  | _, .result _, _ => PUnit.unit
  | _, .data _ rest, _ => (.var (payloadEmbedding rest _ .vz), payloadVariables rest _)
  | _, .recursive _ rest, ambient => payloadVariables rest ambient
  | _, .nested _ _ _ _ _ rest, _ => (.var (payloadEmbedding rest _ .vz), payloadVariables rest _)

def payloadAssignment : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {ambient target : Ctx Base} → Subst Const ambient target → Arguments Const target (reading.fields code) →
    Subst Const (payloadScope (reading := reading) code ambient) target
  | _, .result _, _, _, images, _ => images
  | _, .data _ rest, _, _, images, arguments => payloadAssignment rest (Subst.cons arguments.1 images) arguments.2
  | _, .recursive _ rest, _, _, images, arguments => payloadAssignment rest images arguments
  | _, .nested _ _ _ _ _ rest, _, _, images, arguments => payloadAssignment rest (Subst.cons arguments.1 images) arguments.2

def payloadTelescope (guards : FieldGuards reading) :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    {ambient : Ctx Base} → Telescope Const ambient →
    Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) ambient →
    Telescope Const (payloadScope (reading := reading) code ambient)
  | _, .result _, _, base, _ => base
  | context, .data sort rest, _, base, rho =>
      guards.payloadTelescope rest
        (base.snoc (subst (reading.parameterSubst (context := context) rho) (guards.value sort))) (Subst.lift rho)
  | _, .recursive _ rest, _, base, rho => guards.payloadTelescope rest base rho
  | _, .nested name entry registered output _ rest, _, base, rho =>
      guards.payloadTelescope rest (base.snoc (subst rho (guards.shape name entry registered output)))
        (fun index => weaken (rho index))

theorem payloadScope_eq {context : List I.SortCode} (code : Code I registry parameters context)
    (ambient : Ctx Base) : payloadScope (reading := reading) code ambient = (reading.fields code).reverse ++ ambient := by
  induction code generalizing ambient with
  | result _ => rfl
  | data _ _ previous => simpa only [payloadScope, Reading.fields, List.reverse_cons, List.append_assoc, List.singleton_append] using previous (_ :: ambient)
  | recursive _ _ previous => exact previous ambient
  | nested _ _ _ _ _ _ previous => simpa only [payloadScope, Reading.fields, List.reverse_cons, List.append_assoc, List.singleton_append] using previous (_ :: ambient)

theorem payloadAssignment_ambient {context : List I.SortCode} (code : Code I registry parameters context)
    (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ (reading.fields code))
    {type : Ty Base} (index : Var Γ type) :
    payloadAssignment code images arguments (payloadEmbedding code Γ index) = images index := by
  induction code generalizing Γ with
  | result _ => rfl
  | data _ _ previous => exact previous (Subst.cons arguments.1 images) arguments.2 (.vs index)
  | recursive _ _ previous => exact previous images arguments index
  | nested _ _ _ _ _ _ previous => exact previous (Subst.cons arguments.1 images) arguments.2 (.vs index)

theorem payloadVariables_instantiate {context : List I.SortCode} (code : Code I registry parameters context)
    (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ (reading.fields code)) :
    substituteArguments (payloadAssignment code images arguments) (reading.fields code) (payloadVariables code Γ) = arguments := by
  induction code generalizing Γ with
  | result _ => cases arguments; rfl
  | data _ rest previous =>
      apply Prod.ext
      · exact payloadAssignment_ambient rest (Subst.cons arguments.1 images) arguments.2 .vz
      · exact previous (Subst.cons arguments.1 images) arguments.2
  | recursive _ _ previous => exact previous images arguments
  | nested _ _ _ _ _ rest previous =>
      apply Prod.ext
      · exact payloadAssignment_ambient rest (Subst.cons arguments.1 images) arguments.2 .vz
      · exact previous (Subst.cons arguments.1 images) arguments.2

private theorem subst_cons_weaken {domain result : Ty Base}
    (argument : Term Const Ξ domain) (images : Subst Const Γ Ξ) (term : Term Const Γ result) :
    subst (Subst.cons argument images) (weaken term) = subst images term := by
  rw [weaken, subst_rename]
  rfl

private theorem cons_comp_lift {domain : Ty Base} {Ω : Ctx Base}
    (argument : Term Const Ξ domain) (images : Subst Const Γ Ξ) (rho : Subst Const Ω Γ) :
    @Eq (Subst Const (domain :: Ω) Ξ)
      (Subst.comp (Subst.cons argument images) (Subst.lift rho))
      (Subst.cons argument (Subst.comp images rho)) := by
  funext type index
  cases index with
  | vz => rfl
  | vs prior => exact subst_cons_weaken argument images (rho prior)

private theorem cons_comp_weaken {domain : Ty Base} {Ω : Ctx Base}
    (argument : Term Const Ξ domain) (images : Subst Const Γ Ξ) (rho : Subst Const Ω Γ) :
    @Eq (Subst Const Ω Ξ)
      (Subst.comp (Subst.cons argument images) (fun index => weaken (rho index)))
      (Subst.comp images rho) := by
  funext type index
  exact subst_cons_weaken argument images (rho index)

def castEvidence (guards : FieldGuards reading) {context : List I.SortCode}
    (code : Code I registry parameters context) {hypotheses : List (Formula Const Ξ)}
    {first second : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Ξ}
    (same : @Eq (Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Ξ) first second)
    (arguments : Arguments Const Ξ (reading.fields code))
    (evidence : guards.Evidence hypotheses code first arguments) : guards.Evidence hypotheses code second arguments :=
  same ▸ evidence

theorem castEvidence_free (guards : FieldGuards reading) {context : List I.SortCode}
    (code : Code I registry parameters context) {hypotheses : List (Formula Const Ξ)}
    {first second : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Ξ}
    (same : @Eq (Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Ξ) first second)
    (arguments : Arguments Const Ξ (reading.fields code))
    (evidence : guards.Evidence hypotheses code first arguments)
    (free : guards.EvidenceFree hypotheses code first arguments evidence) :
    guards.EvidenceFree hypotheses code second arguments (castEvidence guards code same arguments evidence) := by
  exact Eq.recOn (motive := fun (assigned : Subst Const
      (context.map reading.indices.sort ++ reading.indices.parameters) Ξ) equality =>
    guards.EvidenceFree hypotheses code assigned arguments (castEvidence guards code equality arguments evidence)) same free

private theorem dataPredicate_subst (guards : FieldGuards reading) {context : List I.SortCode}
    (sort : I.SortCode) (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (images : Subst Const Γ Ξ) :
    subst images (subst (reading.parameterSubst rho) (guards.value sort)) =
      subst (reading.parameterSubst (Subst.comp images rho)) (guards.value sort) := by
  rw [subst_comp]
  rfl

variable {hypotheses : List (Formula Const Ξ)}

def realizePayload (guards : FieldGuards reading) :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    {ambient : Ctx Base} → (base : Telescope Const ambient) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) ambient) →
    (images : Subst Const ambient Ξ) → (arguments : Arguments Const Ξ (reading.fields code)) →
    base.Realizes images hypotheses → guards.Evidence hypotheses code (Subst.comp images rho) arguments →
    (guards.payloadTelescope code base rho).Realizes (payloadAssignment code images arguments) hypotheses
  | _, .result _, _, _, _, _, _, baseRealizer, _ => baseRealizer
  | context, .data sort rest, ambient, base, rho, images, arguments, baseRealizer, evidence => by
      let predicate := subst (reading.parameterSubst (context := context) rho) (guards.value sort)
      let head : ProofSyntax Const hypotheses (.app (subst images predicate) arguments.1) :=
        ProofSyntax.castIndices rfl
          (congrArg (fun code => Term.app code arguments.1) (dataPredicate_subst guards sort rho images).symm) evidence.1
      let next : (base.snoc predicate).Realizes (Subst.cons arguments.1 images) hypotheses :=
        Telescope.Realizes.cons baseRealizer predicate arguments.1 head
      let tail := castEvidence guards rest (cons_comp_lift arguments.1 images rho).symm arguments.2 evidence.2
      exact guards.realizePayload rest (base.snoc predicate) (Subst.lift rho)
        (Subst.cons arguments.1 images) arguments.2 next tail
  | _, .recursive _ rest, _, base, rho, images, arguments, baseRealizer, evidence =>
      guards.realizePayload rest base rho images arguments baseRealizer evidence
  | _, .nested name entry registered output _ rest, _, base, rho, images, arguments, baseRealizer, evidence => by
      let predicate := subst rho (guards.shape name entry registered output)
      let head : ProofSyntax Const hypotheses (.app (subst images predicate) arguments.1) :=
        ProofSyntax.castIndices rfl
          (congrArg (fun code => Term.app code arguments.1) (subst_comp images rho _).symm) evidence.1
      let next : (base.snoc predicate).Realizes (Subst.cons arguments.1 images) hypotheses :=
        Telescope.Realizes.cons baseRealizer predicate arguments.1 head
      let tail := castEvidence guards rest (cons_comp_weaken arguments.1 images rho).symm arguments.2 evidence.2
      exact guards.realizePayload rest (base.snoc predicate) (fun value => weaken (rho value))
        (Subst.cons arguments.1 images) arguments.2 next tail

private def headEvidence {domain : Ty Base} {base : Telescope Const Γ}
    (predicate : Term Const Γ (domain ⇒ .prop)) (images : Subst Const Γ Ξ) (argument : Term Const Ξ domain)
    (realizer : (base.snoc predicate).Realizes (Subst.cons argument images) hypotheses) :
    ProofSyntax Const hypotheses (.app (subst images predicate) argument) :=
  ProofSyntax.castIndices rfl (by
    simp only [Telescope.guard, Telescope.domain, subst, Subst.cons, subst_cons_weaken]) (realizer .vz)

private def tailEvidence {domain : Ty Base} {base : Telescope Const Γ}
    (predicate : Term Const Γ (domain ⇒ .prop)) (images : Subst Const Γ Ξ) (argument : Term Const Ξ domain)
    (realizer : (base.snoc predicate).Realizes (Subst.cons argument images) hypotheses) :
    base.Realizes images hypotheses := fun index =>
  ProofSyntax.castIndices rfl (by
    simp only [Telescope.guard, Telescope.domain, subst, Subst.cons, subst_cons_weaken]) (realizer (.vs index))

def unpackPayload (guards : FieldGuards reading) :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    {ambient : Ctx Base} → (base : Telescope Const ambient) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) ambient) →
    (images : Subst Const ambient Ξ) → (arguments : Arguments Const Ξ (reading.fields code)) →
    (guards.payloadTelescope code base rho).Realizes (payloadAssignment code images arguments) hypotheses →
    base.Realizes images hypotheses × guards.Evidence hypotheses code (Subst.comp images rho) arguments
  | _, .result _, _, _, _, _, _, realizer => ⟨realizer, PUnit.unit⟩
  | context, .data sort rest, _, base, rho, images, arguments, realizer => by
      let predicate := subst (reading.parameterSubst (context := context) rho) (guards.value sort)
      let current := guards.unpackPayload rest (base.snoc predicate) (Subst.lift rho)
        (Subst.cons arguments.1 images) arguments.2 realizer
      let head : ProofSyntax Const hypotheses
          (.app (subst (reading.parameterSubst (Subst.comp images rho)) (guards.value sort)) arguments.1) :=
        ProofSyntax.castIndices rfl (congrArg (fun code => Term.app code arguments.1)
          (dataPredicate_subst guards sort rho images)) (headEvidence predicate images arguments.1 current.1)
      let tail := castEvidence guards rest (cons_comp_lift arguments.1 images rho) arguments.2 current.2
      exact ⟨tailEvidence predicate images arguments.1 current.1, head, tail⟩
  | _, .recursive _ rest, _, base, rho, images, arguments, realizer =>
      guards.unpackPayload rest base rho images arguments realizer
  | _, .nested name entry registered output _ rest, _, base, rho, images, arguments, realizer => by
      let predicate := subst rho (guards.shape name entry registered output)
      let current := guards.unpackPayload rest (base.snoc predicate) (fun value => weaken (rho value))
        (Subst.cons arguments.1 images) arguments.2 realizer
      let head : ProofSyntax Const hypotheses
          (.app (subst (Subst.comp images rho) (guards.shape name entry registered output)) arguments.1) :=
        ProofSyntax.castIndices rfl (congrArg (fun code => Term.app code arguments.1)
          (subst_comp images rho _)) (headEvidence predicate images arguments.1 current.1)
      let tail := castEvidence guards rest (cons_comp_weaken arguments.1 images rho) arguments.2 current.2
      exact ⟨tailEvidence predicate images arguments.1 current.1, head, tail⟩

theorem payload_realizable_iff (guards : FieldGuards reading) {context : List I.SortCode}
    (code : Code I registry parameters context) (base : Telescope Const Γ)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ (reading.fields code)) :
    Nonempty ((guards.payloadTelescope code base rho).Realizes (payloadAssignment code images arguments) hypotheses) ↔
      Nonempty (base.Realizes images hypotheses × guards.Evidence hypotheses code (Subst.comp images rho) arguments) := by
  constructor
  · rintro ⟨realizer⟩
    exact ⟨guards.unpackPayload code base rho images arguments realizer⟩
  · rintro ⟨baseRealizer, evidence⟩
    exact ⟨guards.realizePayload code base rho images arguments baseRealizer evidence⟩

theorem realizePayload_free (guards : FieldGuards reading) {context : List I.SortCode}
    (code : Code I registry parameters context) (base : Telescope Const Γ)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ (reading.fields code))
    (baseRealizer : base.Realizes images hypotheses)
    (evidence : guards.Evidence hypotheses code (Subst.comp images rho) arguments)
    (baseFree : ∀ {type} (index : Var Γ type), (baseRealizer index).FunctionExtensionalityFree)
    (evidenceFree : guards.EvidenceFree hypotheses code (Subst.comp images rho) arguments evidence) :
    ∀ {type} (index : Var (payloadScope (reading := reading) code Γ) type),
      (guards.realizePayload code base rho images arguments baseRealizer evidence index).FunctionExtensionalityFree := by
  induction code generalizing Γ with
  | result _ => exact baseFree
  | data sort rest previous =>
      unfold realizePayload
      apply previous
      · apply Telescope.Realizes.cons_free
        · exact baseFree
        · simpa only [ProofSyntax.functionExtensionalityFree_castIndices] using evidenceFree.1
      · exact castEvidence_free guards rest _ _ evidence.2 evidenceFree.2
  | recursive _ _ previous => exact previous base rho images arguments baseRealizer evidence baseFree evidenceFree
  | nested _ _ _ _ _ _ previous =>
      unfold realizePayload
      apply previous
      · apply Telescope.Realizes.cons_free
        · exact baseFree
        · simpa only [ProofSyntax.functionExtensionalityFree_castIndices] using evidenceFree.1
      · exact castEvidence_free guards _ _ _ evidence.2 evidenceFree.2

private theorem headEvidence_free {domain : Ty Base} {base : Telescope Const Γ}
    (predicate : Term Const Γ (domain ⇒ .prop)) (images : Subst Const Γ Ξ) (argument : Term Const Ξ domain)
    (realizer : (base.snoc predicate).Realizes (Subst.cons argument images) hypotheses)
    (free : ∀ {type} (index : Var (domain :: Γ) type), (realizer index).FunctionExtensionalityFree) :
    (headEvidence predicate images argument realizer).FunctionExtensionalityFree := by
  simpa only [headEvidence, ProofSyntax.functionExtensionalityFree_castIndices] using free .vz

private theorem tailEvidence_free {domain : Ty Base} {base : Telescope Const Γ}
    (predicate : Term Const Γ (domain ⇒ .prop)) (images : Subst Const Γ Ξ) (argument : Term Const Ξ domain)
    (realizer : (base.snoc predicate).Realizes (Subst.cons argument images) hypotheses)
    (free : ∀ {type} (index : Var (domain :: Γ) type), (realizer index).FunctionExtensionalityFree) :
    ∀ {type} (index : Var Γ type), (tailEvidence predicate images argument realizer index).FunctionExtensionalityFree := by
  intro type index
  simpa only [tailEvidence, ProofSyntax.functionExtensionalityFree_castIndices] using free (.vs index)

theorem unpackPayload_free (guards : FieldGuards reading) {context : List I.SortCode}
    (code : Code I registry parameters context) (base : Telescope Const Γ)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ (reading.fields code))
    (realizer : (guards.payloadTelescope code base rho).Realizes (payloadAssignment code images arguments) hypotheses)
    (free : ∀ {type} (index : Var (payloadScope (reading := reading) code Γ) type),
      (realizer index).FunctionExtensionalityFree) :
    (∀ {type} (index : Var Γ type),
      ((guards.unpackPayload code base rho images arguments realizer).1 index).FunctionExtensionalityFree) ∧
      guards.EvidenceFree hypotheses code (Subst.comp images rho) arguments
        (guards.unpackPayload code base rho images arguments realizer).2 := by
  induction code generalizing Γ with
  | result _ => exact ⟨free, True.intro⟩
  | data sort rest previous =>
      let predicate := subst (reading.parameterSubst rho) (guards.value sort)
      have inherited := previous (base.snoc predicate) (Subst.lift rho)
        (Subst.cons arguments.1 images) arguments.2 realizer free
      constructor
      · exact tailEvidence_free _ _ _ _ inherited.1
      · constructor
        · simpa only [unpackPayload, ProofSyntax.functionExtensionalityFree_castIndices] using
            headEvidence_free _ _ _ _ inherited.1
        · exact castEvidence_free guards rest _ _ _ inherited.2
  | recursive _ _ previous => exact previous base rho images arguments realizer free
  | nested name entry registered output _ rest previous =>
      let predicate := subst rho (guards.shape name entry registered output)
      have inherited := previous (base.snoc predicate) (fun value => weaken (rho value))
        (Subst.cons arguments.1 images) arguments.2 realizer free
      constructor
      · exact tailEvidence_free _ _ _ _ inherited.1
      · constructor
        · simpa only [unpackPayload, ProofSyntax.functionExtensionalityFree_castIndices] using
            headEvidence_free _ _ _ _ inherited.1
        · exact castEvidence_free guards rest _ _ _ inherited.2

#print axioms payloadVariables_instantiate
#print axioms realizePayload
#print axioms unpackPayload
#print axioms payload_realizable_iff
#print axioms realizePayload_free
#print axioms unpackPayload_free

end Mettapedia.Logic.HOL.IndexedContainerPositionTerms.FieldGuards
