import Mettapedia.TypeTheory.ExtensionalReadout
import Mettapedia.Logic.HOL.Semantics.LogicalRelationModel
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Henkin logical policies on semantic type codes

The native HOL interface declares one universal and one equality operator,
each taking a small type argument. Interpreting their HOL instances does not
yet interpret those polymorphic declarations at every semantic code.

For a carrier-preserving map from HOL types to codes, this module gives the
exact additional condition: admissibility and extensional equality must each
agree whenever codes coincide, after transporting their arguments. The proof
reuses observer descent on the image of the total code-and-value map. It does
not assume full Henkin domains, identify HOL equality with native identity,
or supply a dependent-product or universe interpretation of native syntax.

The controls use one carrier-preserving, arrow-preserving code map that
identifies propositions with Booleans. Both policies descend for the standard
model on those carriers. Neither descends for the existing monotone Boolean
Henkin model. That model is lambda-closed but does not satisfy the additional
`FunctionsRespectEqv` condition of the fixed-base institution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HenkinLogicalCodeDescent

open Mettapedia.Logic HOL
open Mettapedia.TypeTheory.ExtensionalReadout

universe u v w uCode uEl uSource uTarget

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Only a semantic code map and its independently supplied carrier
identifications. No logical policy or native-model law is a field. -/
structure CarrierCoding (Carrier : Base → Type (max (u + 1) w))
    (Code : Type uCode) (El : Code → Type uEl) where
  code : Ty Base → Code
  identify : ∀ type, El (code type) ≃ Ty.denote Carrier type

/-- Transport is along equality of actual codes, not merely equivalence of
their decoded carriers. -/
def transport {Code : Type uCode} {El : Code → Type uEl}
    {left right : Code} (equal : left = right) (value : El left) : El right :=
  cast (congrArg El equal) value

private theorem total_eq_iff {Code : Type uCode} {El : Code → Type uEl}
    {left right : Code} {x : El left} {y : El right} :
    (Sigma.mk left x = Sigma.mk right y) ↔
      ∃ equal : left = right, transport equal x = y := by
  constructor
  · intro equal
    cases equal
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem transport_pair {Code : Type uCode} {El : Code → Type uEl}
    {left right : Code} (equal : left = right) (x y : El left) :
    transport (El := fun code => El code × El code) equal (x, y) =
      (transport equal x, transport equal y) := by
  cases equal
  rfl

/-! ## Reusing observer descent on the actual image -/

private noncomputable def imageReadout {Source : Type uSource} {Target : Type uTarget}
    (observe : Source → Target) : SplitReadout Source (Set.range observe) where
  observe source := ⟨observe source, ⟨source, rfl⟩⟩
  representative target := Classical.choose target.2
  observe_representative target :=
    Subtype.ext (Classical.choose_spec target.2)

/-- A proposition-valued observer can be extended off the image exactly
when it is constant on observation fibres. Values off the image are not
constrained; the existential construction makes the predicate false there. -/
private theorem predicate_extension_iff
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source → Target) (policy : Source → Prop) :
    (∃ extended : Target → Prop, ∀ source,
      extended (observe source) ↔ policy source) ↔
    (∀ left right, observe left = observe right →
      (policy left ↔ policy right)) := by
  constructor
  · rintro ⟨extended, agrees⟩ left right equal
    rw [← agrees left, ← agrees right, equal]
  · intro coherent
    have invariant : (imageReadout observe).FibreInvariant policy := by
      intro left right equal
      exact propext (coherent left right (congrArg Subtype.val equal))
    obtain ⟨onImage, agrees⟩ :=
      ((imageReadout observe).factorsObserver_iff_fibreInvariant policy).mpr invariant
    refine ⟨fun target => ∃ member : target ∈ Set.range observe,
      onImage ⟨target, member⟩, ?_⟩
    intro source
    constructor
    · rintro ⟨member, holds⟩
      change onImage ((imageReadout observe).observe source) at holds
      rwa [agrees source] at holds
    · intro holds
      refine ⟨⟨source, rfl⟩, ?_⟩
      change onImage ((imageReadout observe).observe source)
      rwa [agrees source]

section Policies

variable {Code : Type uCode} {El : Code → Type uEl}
variable (model : HenkinModel.{u, v, w} Base Const)
variable (coding : CarrierCoding model.Carrier Code El)

/-- A global admissibility policy restricts to the actual Henkin domains. -/
def AdmissibilityExtends (admissible : (code : Code) → El code → Prop) : Prop :=
  ∀ type value, admissible (coding.code type) value ↔
    model.adm type (coding.identify type value)

/-- A global logical equality policy restricts to Henkin `Eqv`, without
identifying it with equality of the ambient native values. -/
def EqualityExtends (relation : (code : Code) → El code → El code → Prop) : Prop :=
  ∀ type left right, relation (coding.code type) left right ↔
    model.Eqv type (coding.identify type left) (coding.identify type right)

/-- The exact unary-policy condition at semantic code collisions. -/
def AdmissibilityCoherent : Prop :=
  ∀ left right (equal : coding.code left = coding.code right) value,
    model.adm left (coding.identify left value) ↔
      model.adm right (coding.identify right (transport equal value))

/-- The exact binary-policy condition at semantic code collisions. -/
def EqualityCoherent : Prop :=
  ∀ left right (equal : coding.code left = coding.code right) x y,
    model.Eqv left (coding.identify left x) (coding.identify left y) ↔
      model.Eqv right (coding.identify right (transport equal x))
        (coding.identify right (transport equal y))

/-- Admissibility extends to all codes if and only if it loses no policy
distinction at a code collision. -/
theorem admissibility_extension_iff :
    (∃ admissible, AdmissibilityExtends model coding admissible) ↔
      AdmissibilityCoherent model coding := by
  let observe : (Σ type, El (coding.code type)) → Sigma El :=
    fun point => ⟨coding.code point.1, point.2⟩
  let policy : (Σ type, El (coding.code type)) → Prop :=
    fun point => model.adm point.1 (coding.identify point.1 point.2)
  constructor
  · rintro ⟨admissible, agrees⟩ left right equal value
    have factors : ∃ extended : Sigma El → Prop, ∀ source,
        extended (observe source) ↔ policy source :=
      ⟨fun point => admissible point.1 point.2, fun point => agrees point.1 point.2⟩
    exact (predicate_extension_iff observe policy).mp factors
      ⟨left, value⟩ ⟨right, transport equal value⟩
      (total_eq_iff.mpr ⟨equal, rfl⟩)
  · intro coherent
    have invariant : ∀ left right, observe left = observe right →
        (policy left ↔ policy right) := by
      rintro ⟨left, x⟩ ⟨right, y⟩ equal
      obtain ⟨codeEqual, valueEqual⟩ := total_eq_iff.mp equal
      change transport codeEqual x = y at valueEqual
      change model.adm left (coding.identify left x) ↔
        model.adm right (coding.identify right y)
      rw [← valueEqual]
      exact coherent left right codeEqual x
    obtain ⟨extended, agrees⟩ := (predicate_extension_iff observe policy).mpr invariant
    exact ⟨fun code value => extended ⟨code, value⟩,
      fun type value => agrees ⟨type, value⟩⟩

/-- Extensional logical equality has its own, independent code-collision
condition. Unary-domain descent is not used as an assumption. -/
theorem equality_extension_iff :
    (∃ relation, EqualityExtends model coding relation) ↔
      EqualityCoherent model coding := by
  let observe : (Σ type, El (coding.code type) × El (coding.code type)) →
      (Σ code, El code × El code) := fun point => ⟨coding.code point.1, point.2⟩
  let policy : (Σ type, El (coding.code type) × El (coding.code type)) → Prop :=
    fun point => model.Eqv point.1 (coding.identify point.1 point.2.1)
      (coding.identify point.1 point.2.2)
  constructor
  · rintro ⟨relation, agrees⟩ left right equal x y
    have factors : ∃ extended : (Σ code, El code × El code) → Prop, ∀ source,
        extended (observe source) ↔ policy source :=
      ⟨fun point => relation point.1 point.2.1 point.2.2,
        fun point => agrees point.1 point.2.1 point.2.2⟩
    apply (predicate_extension_iff observe policy).mp factors
      ⟨left, x, y⟩ ⟨right, transport equal x, transport equal y⟩
    exact total_eq_iff.mpr ⟨equal, transport_pair equal x y⟩
  · intro coherent
    have invariant : ∀ left right, observe left = observe right →
        (policy left ↔ policy right) := by
      rintro ⟨left, x, y⟩ ⟨right, x', y'⟩ equal
      obtain ⟨codeEqual, valueEqual⟩ := total_eq_iff.mp equal
      rw [transport_pair] at valueEqual
      obtain ⟨xEqual, yEqual⟩ := Prod.mk.inj valueEqual
      change model.Eqv left (coding.identify left x) (coding.identify left y) ↔
        model.Eqv right (coding.identify right x') (coding.identify right y')
      rw [← xEqual, ← yEqual]
      exact coherent left right codeEqual x y
    obtain ⟨extended, agrees⟩ := (predicate_extension_iff observe policy).mpr invariant
    exact ⟨fun code left right => extended ⟨code, left, right⟩,
      fun type left right => agrees ⟨type, left, right⟩⟩

/-- Both actual logical policies extend precisely when both separate
collision conditions hold. No native Π/universe laws are asserted here. -/
theorem logical_policy_extension_iff :
    (∃ admissible relation,
      AdmissibilityExtends model coding admissible ∧
      EqualityExtends model coding relation) ↔
      AdmissibilityCoherent model coding ∧ EqualityCoherent model coding := by
  constructor
  · rintro ⟨admissible, relation, adm, eqv⟩
    exact ⟨(admissibility_extension_iff model coding).mp ⟨admissible, adm⟩,
      (equality_extension_iff model coding).mp ⟨relation, eqv⟩⟩
  · rintro ⟨adm, eqv⟩
    obtain ⟨admissible, adm⟩ := (admissibility_extension_iff model coding).mpr adm
    obtain ⟨relation, eqv⟩ := (equality_extension_iff model coding).mpr eqv
    exact ⟨admissible, relation, adm, eqv⟩

/-! ## The two global polymorphic logical operations -/

/-- The domain-restricted universal has the actual declaration's shape
`(code : U₀) → (El code → HOLProp) → HOLProp`. -/
def universal (admissible : (code : Code) → El code → Prop)
    (code : Code) (predicate : El code → El (coding.code .prop)) :
    El (coding.code .prop) :=
  (coding.identify .prop).symm
    ⟨∀ value, admissible code value → (coding.identify .prop (predicate value)).down⟩

/-- This declared equality returns the proposition carrier; it is not a
native identity type or a proof of its output proposition. -/
def equality (relation : (code : Code) → El code → El code → Prop)
    (code : Code) (left right : El code) : El (coding.code .prop) :=
  (coding.identify .prop).symm ⟨relation code left right⟩

theorem universal_on_image
    {admissible : (code : Code) → El code → Prop}
    (agrees : AdmissibilityExtends model coding admissible)
    (type : Ty Base) (predicate : El (coding.code type) → El (coding.code .prop)) :
    (coding.identify .prop (universal model coding admissible (coding.code type) predicate)).down ↔
      ∀ value, model.adm type value →
        (coding.identify .prop (predicate ((coding.identify type).symm value))).down := by
  unfold universal
  erw [(coding.identify .prop).apply_symm_apply]
  constructor
  · intro holds value admitted
    exact holds ((coding.identify type).symm value)
      ((agrees type _).mpr (by simpa only [Equiv.apply_symm_apply] using admitted))
  · intro holds value admitted
    simpa only [Equiv.symm_apply_apply] using
      holds (coding.identify type value) ((agrees type value).mp admitted)

theorem equality_on_image
    {relation : (code : Code) → El code → El code → Prop}
    (agrees : EqualityExtends model coding relation)
    (type : Ty Base) (left right : El (coding.code type)) :
    (coding.identify .prop (equality model coding relation (coding.code type) left right)).down ↔
      model.Eqv type (coding.identify type left) (coding.identify type right) := by
  unfold equality
  erw [(coding.identify .prop).apply_symm_apply]
  exact agrees type left right

/-! ## Full domains are a sufficient positive control, not a prerequisite -/

theorem full_domains_admissibility_extension (full : model.FullDomains) :
    AdmissibilityExtends model coding (fun _ _ => True) := by
  intro type value
  exact ⟨fun _ => full type (coding.identify type value), fun _ => True.intro⟩

theorem full_domains_equality_extension (full : model.FullDomains) :
    EqualityExtends model coding (fun _ left right => left = right) := by
  intro type left right
  constructor
  · intro equal
    subst right
    exact model.eqv_refl (full type _)
  · intro equal
    exact (coding.identify type).injective (model.eq_of_eqv_of_fullDomains full equal)

end Policies

/-! ## The same noninjective coding: a positive and a genuine obstruction -/

namespace BooleanCollision

open MonotoneBooleanModel

/-- A deliberate forgetting of the proposition/Boolean type distinction. -/
def code : Ty Unit → Ty Unit
  | .prop => .base ()
  | .base _ => .base ()
  | .arr domain codomain => .arr (code domain) (code codomain)

noncomputable def boolProp : ULift.{1} Bool ≃ ULift.{1} Prop :=
  Equiv.ulift.trans (Equiv.propEquivBool.symm.trans Equiv.ulift.symm)

@[simp] theorem boolProp_down (value : ULift.{1} Bool) :
    (boolProp value).down = (value.down = true) := rfl

/-- The forgetting does preserve ambient carriers, by an actual equivalence
at every HOL type, including higher-order functions. -/
noncomputable def identify : (type : Ty Unit) →
    Ty.denote.{0, 0} model.Carrier (code type) ≃ Ty.denote.{0, 0} model.Carrier type
  | .prop => boolProp
  | .base _ => Equiv.refl _
  | .arr domain codomain => Equiv.arrowCongr (identify domain) (identify codomain)

noncomputable def coding :
    CarrierCoding.{0, 0, 0, 1} model.Carrier (Ty Unit) (Ty.denote.{0, 0} model.Carrier) where
  code := code
  identify := identify

theorem code_preserves_arrow (domain codomain : Ty Unit) :
    code (.arr domain codomain) = .arr (code domain) (code codomain) := rfl

theorem identify_application (domain codomain : Ty Unit)
    (function : Ty.denote.{0, 0} model.Carrier (code (.arr domain codomain)))
    (argument : Ty.denote.{0, 0} model.Carrier (code domain)) :
    identify (.arr domain codomain) function (identify domain argument) =
      identify codomain (function argument) := by
  change identify codomain (function ((identify domain).symm (identify domain argument))) = _
  rw [(identify domain).symm_apply_apply]

theorem code_not_injective : ¬ Function.Injective code := by
  intro injective
  have impossible : (Ty.prop : Ty Unit) = .base () := injective rfl
  cases impossible

/-- Every proposition endomap is admitted in the existing logical-relation
model, whereas Boolean endomaps must be monotone. -/
theorem proposition_endomap_admissible
    (function : Ty.denote.{0, 0} model.Carrier (.arr .prop .prop)) :
    model.adm (.arr .prop .prop) function := by
  intro _ _ _
  trivial

/-- The two arrow codes coincide and have identified carriers, but the
negation value has incompatible admissibility requirements. -/
theorem admissibility_does_not_extend :
    ¬ ∃ admissible, AdmissibilityExtends model coding admissible := by
  intro extension
  have coherent := (admissibility_extension_iff model coding).mp extension
  have agrees := coherent (.arr boolean boolean) (.arr .prop .prop) rfl negation
  apply negation_not_admissible
  apply agrees.mpr
  exact proposition_endomap_admissible _

/-- The binary policy fails independently: the two existing higher-order
observations agree on admitted Boolean maps, but not on all proposition maps. -/
theorem equality_does_not_extend :
    ¬ ∃ relation, EqualityExtends model coding relation := by
  intro extension
  have coherent := (equality_extension_iff model coding).mp extension
  have agrees := coherent endomapObservation (.arr (.arr .prop .prop) .prop)
    rfl atFalse andEndpoints
  have equal := agrees.mp atFalse_eqv_andEndpoints
  have impossible := equal (identify (.arr .prop .prop) negation)
    (proposition_endomap_admissible _)
  change (identify (.arr (.arr .prop .prop) .prop) atFalse
      (identify (.arr .prop .prop) negation)).down ↔
    (identify (.arr (.arr .prop .prop) .prop) andEndpoints
      (identify (.arr .prop .prop) negation)).down at impossible
  erw [identify_application, identify_application] at impossible
  simp [identify, atFalse, andEndpoints, negation] at impossible
  change (true = true) ↔ (false = true) at impossible
  exact Bool.false_ne_true (impossible.mp rfl)

/-- This counterexample is not smuggled into the narrower institution whose
models additionally require extensional argument congruence. -/
theorem nonfull_counterexample_scope :
    ¬ model.FullDomains ∧ ¬ model.FunctionsRespectEqv ∧
      (¬ ∃ admissible, AdmissibilityExtends model coding admissible) ∧
      (¬ ∃ relation, EqualityExtends model coding relation) :=
  ⟨not_fullDomains, not_functionsRespectEqv,
    admissibility_does_not_extend, equality_does_not_extend⟩

/-- Standardizing changes the model's domains, not the ambient code map. -/
def standard : HenkinModel.{0, 0, 0} Unit Constants :=
  HenkinModel.standard model.Carrier model.constDen

/-- The very same noninjective, carrier-preserving code map supports both
policies for a standard model. Code-name injectivity is not necessary. -/
theorem standard_noninjective_positive :
    ¬ Function.Injective coding.code ∧
      AdmissibilityExtends standard coding (fun _ _ => True) ∧
      EqualityExtends standard coding (fun _ left right => left = right) :=
  ⟨code_not_injective,
    full_domains_admissibility_extension standard coding
      (HenkinModel.fullDomains_standard _ _),
    full_domains_equality_extension standard coding
      (HenkinModel.fullDomains_standard _ _)⟩

/-- Passing to that positive control does not preserve arbitrary source
truth: the already exhibited fixed-point sentence changes its meaning. -/
theorem standardization_is_a_model_change :
    model.models fixedPointSentence ∧ ¬ standard.models fixedPointSentence :=
  ⟨models_fixedPointSentence, standard_refutes_fixedPointSentence⟩

end BooleanCollision

#print axioms admissibility_extension_iff
#print axioms equality_extension_iff
#print axioms logical_policy_extension_iff
#print axioms universal_on_image
#print axioms equality_on_image
#print axioms full_domains_admissibility_extension
#print axioms full_domains_equality_extension
#print axioms BooleanCollision.identify_application
#print axioms BooleanCollision.admissibility_does_not_extend
#print axioms BooleanCollision.equality_does_not_extend
#print axioms BooleanCollision.nonfull_counterexample_scope
#print axioms BooleanCollision.standard_noninjective_positive
#print axioms BooleanCollision.standardization_is_a_model_change

end Mettapedia.TypeTheory.HenkinLogicalCodeDescent
