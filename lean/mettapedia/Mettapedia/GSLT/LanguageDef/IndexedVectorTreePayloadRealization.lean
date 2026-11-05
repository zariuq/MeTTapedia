import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorPayloadLowering
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuards
import Mettapedia.Logic.HOL.ConstructorPredicateRepresentationSemantics

/-!
# Model-relative represented payloads for the parsed Vector inventory

The semantic payload carrier is the original predicate's subtype at an
explicit model and parameter valuation. Its encoding is the retained HOL
field program. Primitive image recognition follows from the program's direct
image predicate. Natural data retain the complete natural-number carrier;
the numeric guard must therefore recognize every represented natural.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreePayloadRealization

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedPositiveContainer IndexedContainerPositionTerms

universe u v w x
variable {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base} {N A E : Ty Base}

def emptyValues (model : HenkinModel.{v,w,x} Base Const) : model.Valuation [] :=
  fun impossible => nomatch impossible

structure Numbers (model : HenkinModel.{v,w,x} Base Const)
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) where
  equivalence : Nat ≃ Ty.denote model.Carrier N
  zero_correct : model.denote zero (emptyValues model) = equivalence 0
  successor_correct : ∀ n, model.denote successor (emptyValues model) (equivalence n) = equivalence (n+1)

def Payload (model : HenkinModel.{v,w,x} Base Const) (source : Term Const Γ (A ⇒ .prop))
    (values : model.Valuation Γ) :=
  {field : Ty.denote model.Carrier A // (model.denote source values field).down}

def indices (Carrier : Type u) (Const : Ty Base → Type w) (Γ : Ctx Base) (N E : Ty Base) :
    IndexedConstructorTerms.Reading (VectorPayload.interface Carrier) Const where
  sort := IndexedVectorTreeStoredFieldGuards.dataType N E
  index := .prop
  parameters := Γ
  term _ := .top

theorem registered_entry {Carrier : Type u} {name : String}
    {entry : Entry (VectorPayload.interface Carrier)}
    (found : (VectorPayload.registry Carrier).lookup name = some entry) :
    entry = VectorPayload.entry Carrier := by
  by_cases same : name = "Vector"
  · simpa [VectorPayload.registry,same] using found.symm
  · simp [VectorPayload.registry,same] at found

theorem registered_name {Carrier : Type u} {name : String}
    {entry : Entry (VectorPayload.interface Carrier)}
    (found : (VectorPayload.registry Carrier).lookup name = some entry) : name = "Vector" := by
  by_contra different
  simp [VectorPayload.registry,different] at found

def reading (Carrier : Type u) (zero : ClosedTerm Const N)
    (successor : ClosedTerm Const (N ⇒ N)) :
    Reading (VectorPayload.interface Carrier) (VectorPayload.registry Carrier) Const where
  indices := indices Carrier Const Γ N E
  number := N
  one := .app successor zero
  shapeType _ _ _ := N
  count := by
    intro context name entry found output
    obtain rfl := registered_entry found
    exact .lam (weaken (.var (IndexedVectorTreeStoredFieldGuards.lengthVariable output)))

def guards (Carrier : Type u) (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) :
    FieldGuards (reading (Γ := Γ) (E := E) Carrier zero successor) where
  value
    | .length => numbers
    | .payload => given.predicate source
  shape := fun {context} _ _ _ _ => IndexedVectorTreeStoredFieldGuards.shapePredicate zero (context.map (IndexedVectorTreeStoredFieldGuards.dataType N E) ++ Γ)

def encodeValue (model : HenkinModel.{v,w,x} Base Const) (Carrier : Type u)
    (encode : Carrier → Ty.denote model.Carrier E) (numbers : Nat ≃ Ty.denote model.Carrier N) :
    ∀ sort, VectorPayload.value Carrier sort → Ty.denote model.Carrier (IndexedVectorTreeStoredFieldGuards.dataType N E sort)
  | .length, item => numbers item.down
  | .payload, item => encode item

theorem length_denote (model : HenkinModel.{v,w,x} Base Const) (Carrier : Type u)
    (encode : Carrier → Ty.denote model.Carrier E) (numbers : Nat ≃ Ty.denote model.Carrier N)
    (values : model.Valuation Γ) {context : List VectorControl.DataSort}
    (expression : VectorControl.LengthExpr context) (environment : Env (VectorPayload.value Carrier) context) :
    model.denote (.var (IndexedVectorTreeStoredFieldGuards.lengthVariable expression))
      ((indices Carrier Const Γ N E).valuation model (encodeValue model Carrier encode numbers) values environment) =
      numbers (VectorPayload.evalLength Carrier expression environment) := by
  induction expression with
  | here => rfl
  | there prior previous => exact previous environment.2

private theorem closed_denote (model : HenkinModel.{v,w,x} Base Const)
    {type : Ty Base} (term : ClosedTerm Const type) (values : model.Valuation []) :
    model.denote term values = model.denote term (emptyValues model) := by
  apply congrArg (model.denote term)
  funext type impossible
  exact nomatch impossible

def realization (model : HenkinModel.{v,w,x} Base Const)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (values : model.Valuation Γ)
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (numbers : Numbers model zero successor) :
    Realization (reading (Γ := Γ) (E := E) (Payload model source values) zero successor)
      (VectorPayload.orderedFinitary (Payload model source values)) model where
  numbers := numbers.equivalence
  value := encodeValue model (Payload model source values)
    (fun item => model.denote given.encode values item.val) numbers.equivalence
  index _ := .up True
  shape _ _ _ _ _ := numbers.equivalence 0
  parameterValues := values
  index_correct := by intros; rfl
  one_correct := by
    intro valuation
    change model.denote successor valuation (model.denote zero valuation) = numbers.equivalence 1
    rw [closed_denote model zero,closed_denote model successor,numbers.zero_correct]
    exact numbers.successor_correct 0
  count_correct := by
    intro context name entry found output environment shape
    obtain rfl := registered_name found
    obtain rfl := registered_entry found
    change model.denote (.var (IndexedVectorTreeStoredFieldGuards.lengthVariable output))
      ((indices (Payload model source values) Const Γ N E).valuation model
        (encodeValue model (Payload model source values)
          (fun item => model.denote given.encode values item.val) numbers.equivalence) values environment) =
        numbers.equivalence (List.ofFn (id : Fin (VectorPayload.evalLength _ output environment) → _)).length
    simpa only [List.length_ofFn] using length_denote model (Payload model source values)
      (fun item => model.denote given.encode values item.val) numbers.equivalence values output environment

theorem fieldImages (model : HenkinModel.{v,w,x} Base Const) (full : model.FullDomains)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numberGuard : Term Const Γ (N ⇒ .prop))
    (values : model.Valuation Γ) (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (numbers : Numbers model zero successor)
    (guard_on_numbers : ∀ n, (model.denote numberGuard values (numbers.equivalence n)).down) :
    FieldImages (realization model given source values zero successor numbers)
      (guards (Payload model source values) given source numberGuard zero successor) where
  value_correct := by
    intro sort target
    cases sort with
    | length =>
        constructor
        · intro _
          exact ⟨⟨numbers.equivalence.symm target⟩,numbers.equivalence.apply_symm_apply target⟩
        · rintro ⟨item,same⟩
          exact same ▸ guard_on_numbers item.down
    | payload => exact ConstructorPredicateRepresentation.value_image model full given.encode source values target
  shape_correct := by
    intro context name entry found output environment target
    obtain rfl := registered_name found
    obtain rfl := registered_entry found
    change model.Eqv N target (model.denote (weakenCtx _ zero)
      (model.extend ((indices (Payload model source values) Const Γ N E).valuation model
        (encodeValue model (Payload model source values)
          (fun item => model.denote given.encode values item.val) numbers.equivalence) values environment) target)) ↔ _
    rw [model.denote_weakenCtx]
    change model.Eqv N target (model.denote zero (emptyValues model)) ↔
      ∃ _shape : Unit, numbers.equivalence 0 = target
    rw [model.eqv_iff_eq_of_fullDomains full,numbers.zero_correct]
    exact ⟨fun same => ⟨(),same.symm⟩,fun ⟨_,same⟩ => same.symm⟩

theorem guard_on_numbers_of_images (model : HenkinModel.{v,w,x} Base Const)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numberGuard : Term Const Γ (N ⇒ .prop))
    (values : model.Valuation Γ) (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (numbers : Numbers model zero successor)
    (images : FieldImages (realization model given source values zero successor numbers)
      (guards (Payload model source values) given source numberGuard zero successor)) (n : Nat) :
    (model.denote numberGuard values (numbers.equivalence n)).down :=
  (images.value_correct .length (numbers.equivalence n)).mpr ⟨⟨n⟩,rfl⟩

theorem fieldImages_iff_number_guard (model : HenkinModel.{v,w,x} Base Const) (full : model.FullDomains)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numberGuard : Term Const Γ (N ⇒ .prop))
    (values : model.Valuation Γ) (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (numbers : Numbers model zero successor) :
    Nonempty (FieldImages (realization model given source values zero successor numbers)
      (guards (Payload model source values) given source numberGuard zero successor)) ↔
      ∀ n, (model.denote numberGuard values (numbers.equivalence n)).down :=
  ⟨fun ⟨images⟩ => guard_on_numbers_of_images model given source numberGuard values zero successor numbers images,
    fun guard => ⟨fieldImages model full given source numberGuard values zero successor numbers guard⟩⟩

theorem injections (model : HenkinModel.{v,w,x} Base Const) (full : model.FullDomains)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (values : model.Valuation Γ)
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (numbers : Numbers model zero successor) {assumptions : List (Formula Const Γ)}
    (payloadChoice : ProofSyntax Const assumptions (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const assumptions (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const assumptions (ConstructorProjections.fieldInjective given.raw))
    (satisfied : Soundness.SatisfiesHyps model values assumptions) :
    FieldInjective (realization model given source values zero successor numbers) where
  value := by
    intro sort first second same
    cases sort with
    | length =>
        have down := numbers.equivalence.injective same
        cases first; cases second
        cases down
        rfl
    | payload =>
        let comparison := ConstructorPredicateRepresentation.subtypeEquivOfProof model full
          given.encode given.decode source values (given.roundtripLaw payloadChoice fieldChoice rawLaw) satisfied
        apply comparison.injective
        exact Subtype.ext same
  shape := by
    intro name entry found output first second _
    obtain rfl := registered_entry found
    change Unit at first second
    exact Subsingleton.elim first second

theorem index_injective (model : HenkinModel.{v,w,x} Base Const)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (values : model.Valuation Γ)
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (numbers : Numbers model zero successor) :
    Function.Injective (realization model given source values zero successor numbers).index :=
  by
    intro first second _
    change ULift Unit at first second
    cases first with | up first =>
      cases second with | up second =>
        cases first; cases second; rfl

def codes (Carrier : Type u) := ModuleSource.IndexedPositiveVectorLowering.Controls.family.codesWithPayload Carrier

theorem fields_source (Carrier : Type u) (zero : ClosedTerm Const N)
    (successor : ClosedTerm Const (N ⇒ N)) :
    (codes Carrier).map (reading (Γ := Γ) (E := E) Carrier zero successor).fields =
      VectorTreeFieldEmbedding.storedSignature N E := rfl

theorem fields_erasure (Carrier : Type u) (zero : ClosedTerm Const N)
    (successor : ClosedTerm Const (N ⇒ N)) :
    {context : List VectorControl.DataSort} → {names : List String} →
    (code : ModuleSource.IndexedPositiveVectorLowering.Code context names) →
    (reading (Γ := Γ) (E := E) Carrier zero successor).fields (code.eraseWithPayload Carrier) =
      (IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) (.app successor zero)).fields code.erase
  | _,_,.result => rfl
  | _,_,.data _ sort _ rest => congrArg (List.cons (IndexedVectorTreeStoredFieldGuards.dataType N E sort))
      (fields_erasure Carrier zero successor rest)
  | _,_,.recursive _ rest => fields_erasure Carrier zero successor rest
  | _,_,.vector _ _ rest => congrArg (List.cons N) (fields_erasure Carrier zero successor rest)

def inventory (Carrier : Type u) (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numberGuard : Term Const Γ (N ⇒ .prop))
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (tags : Nat → Term Const Γ N) : IndexedConstructorGuards.ConstructorPrograms Const Γ :=
  (guards Carrier given source numberGuard zero successor).constructors (codes Carrier) Subst.id tags

theorem inventory_eq_stored (Carrier : Type u) (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numberGuard : Term Const Γ (N ⇒ .prop))
    (zero : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
    (tags : Nat → Term Const Γ N) :
    inventory Carrier given source numberGuard zero successor tags =
      IndexedVectorTreeStoredFieldGuards.inventory given source numberGuard zero (.app successor zero) tags := by
  unfold inventory IndexedVectorTreeStoredFieldGuards.inventory FieldGuards.constructors
  congr 1
  · funext occurrence
    rcases occurrence with ⟨occurrence,bound⟩
    change occurrence < 2 at bound
    match occurrence with
    | 0 => rfl
    | 1 => rfl
    | n+2 => exact False.elim (Nat.not_lt_zero n
        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))
  · funext occurrence
    rcases occurrence with ⟨occurrence,bound⟩
    change occurrence < 2 at bound
    match occurrence with
    | 0 => rfl
    | 1 => rfl
    | n+2 => exact False.elim (Nat.not_lt_zero n
        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

theorem plans_eq_stored (Carrier : Type u) (zero : ClosedTerm Const N)
    (successor : ClosedTerm Const (N ⇒ N))
    (occurrence : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    FieldGuards.plans (reading := reading (Γ := Γ) (E := E) Carrier zero successor)
        (codes Carrier) Subst.id occurrence =
      FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) (.app successor zero))
        IndexedVectorTreeStoredFieldGuards.codes Subst.id occurrence := by
  rcases occurrence with ⟨occurrence,bound⟩
  change occurrence < 2 at bound
  match occurrence with
  | 0 => rfl
  | 1 => rfl
  | n+2 => exact False.elim (Nat.not_lt_zero n
      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

theorem canonical_number_guard (model : HenkinModel.{v,w,x} Base Const)
    (values : model.Valuation Γ) (numbers : Nat ≃ Ty.denote model.Carrier N) (n : Nat) :
    (model.denote (.lam .top : Term Const Γ (N ⇒ .prop)) values (numbers n)).down := True.intro

theorem false_number_guard_refused (model : HenkinModel.{v,w,x} Base Const)
    (values : model.Valuation Γ) (numbers : Nat ≃ Ty.denote model.Carrier N) :
    ¬ (∀ n, (model.denote (.lam .bot : Term Const Γ (N ⇒ .prop)) values (numbers n)).down) :=
  fun supposed => supposed 0

#print axioms realization
#print axioms fieldImages
#print axioms fieldImages_iff_number_guard
#print axioms injections
#print axioms fields_source
#print axioms fields_erasure
#print axioms inventory_eq_stored
#print axioms plans_eq_stored

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreePayloadRealization
