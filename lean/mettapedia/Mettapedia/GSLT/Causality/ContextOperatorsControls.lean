import Mettapedia.GSLT.Causality.ContextBindings
import Mettapedia.GSLT.Causality.WeightedResponseTypes

/-!
# Controls for the context operators

* **Stores** (`Store`).  Terms are stores, a value at every key, and nothing
  steps; an assignment overrides keys.
  * Two interventions on one key do not commute (`same_key_not_commute`).
  * **Explicit `do` reaches beyond derived `do` over infinitely many keys**
    (`explicit_beyond_derived`): the store false everywhere and the store true
    at one key cannot be told apart by any chain of bindings, at rung three,
    under the observation "every key is true", and one assignment of infinitely
    many keys separates them at rung two.
* **Interaction** (`Interaction`).  Two keys and the graded observation "both
  keys are true".  Setting either key alone has passive impact zero, and
  setting both has passive impact one (`passive_impact_not_subadditive`): the
  subadditivity of `ContextOperators.impact_compose_le` needs the outer context
  in the measuring class, and fails for the bottom class.  A class that may
  set the other key sees the first setting's impact (`impact_sees_interaction`).
* **Authority** (`OneShot`).  A model is a law read once on an environment of
  keys.  When the law ignores secret keys as long as guard keys hold their
  masking values, and the region of keys the contexts may bind contains no
  secret and no guard, environments that differ only in secrets are
  indistinguishable by the region's contexts at every rung
  (`masked_noninterference`); in particular a law that reads only the region's
  keys makes environments that agree on the region indistinguishable
  (`region_noninterference`).  The guard is what the region lacks: binding a
  guard, which a global context may do, separates such a pair
  (`region_witness`).
* **Retention on the ladder** (`Retention`), on the response-type GSLT of
  `Hierarchy`.  The rung-3 query "some drawn individual shows `a` treated and
  `b` untreated" reads the twin built from the shared draw (`sat_twinQuery`):
  the pairs of the shared cell (`DemandAgreement.sharedPairSet`).  The two
  rung-2 queries "treated, some individual shows `a`" and "untreated, some
  individual shows `b`" read the experiment, the pairs of the resampled cell
  (`sat_experimentQueries`).  They coincide when the population has at most one
  individual, the condition of `DemandAgreement`
  (`twinSet_eq_experimentSet_of_card_le_one`); the mixed and the fixed
  populations have one experiment and two twins (`mixed_fixed_retention`), and
  a population of helped and always-affected individuals has twin equal to
  experiment with two individuals (`retention_beyond_condition`), so on the
  readout the condition is sufficient and not necessary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ContextOperatorsControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.ContextOperators
open Mettapedia.GSLT.Causality.ContextBindings
open Mettapedia.GSLT.Causality.ContextBindings.OverrideAction

/-! ## Stores -/

namespace Store

variable (Key : Type) (Value : Type)

/-- **Stores**: a value at every key.  Nothing steps. -/
abbrev storeGSLT : GSLT where
  Term := Key → Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- An assignment overrides the keys it assigns. -/
def storeAction : OverrideAction (storeGSLT Key Value) Key Value where
  assign assignment store := fun key => (assignment key).getD (store key)
  assign_none _ := rfl
  assign_override outer inner store := by
    change (fun key => (override outer inner key).getD (store key)) =
      fun key => (outer key).getD ((inner key).getD (store key))
    funext key
    rw [override_apply]
    cases outer key <;> rfl
  assign_resp _ left right equivalent := by
    have equal : left = right := equivalent
    subst equal
    rfl

variable {Key Value} [DecidableEq Key]

theorem bindingPlug_eq (bindings : Bindings Key Value) (store : Key → Value) :
    (storeAction Key Value).bindingPlug bindings store =
      fun key => (lookupValue bindings key).getD (store key) :=
  (storeAction Key Value).bindingPlug_equiv_assign bindings store

/-- **Two interventions on one key do not commute.** -/
theorem same_key_not_commute (key : Key) {first second : Value} (different : first ≠ second) :
    ¬ ContextOperators.Commute (rules := (storeAction Key Value).derivedRules)
      (doBinding key first) (doBinding key second) := by
  intro commute
  have equal := congrFun (commute (fun _ => first)) key
  change (storeAction Key Value).bindingPlug (graft (doBinding key first) (doBinding key second))
      (fun _ => first) key =
    (storeAction Key Value).bindingPlug (graft (doBinding key second) (doBinding key first))
      (fun _ => first) key at equal
  rw [bindingPlug_eq, bindingPlug_eq] at equal
  simp only [lookupValue_graft, doBinding, lookupValue_bind, lookupValue_empty, override_apply,
    single, if_pos] at equal
  exact different (by simpa using equal)

/-! ### Infinitely many keys at once -/

/-- "Every key is true." -/
def everyKeyTrue : ContextualRules.Observations (storeGSLT ℕ Bool) where
  Atom := Unit
  observes _ store := ∀ key, store key = true
  observes_resp _ left right equivalent := by
    have equal : left = right := equivalent
    subst equal
    exact Iff.rfl

/-- False at every key. -/
def allFalse : ℕ → Bool := fun _ => false

/-- True at key zero only. -/
def trueAtZero : ℕ → Bool := fun key => decide (key = 0)

/-- Infinitely many keys are false. -/
def Unfinished (store : ℕ → Bool) : Prop :=
  {key | store key = false}.Infinite

theorem unfinished_allFalse : Unfinished allFalse := by
  simpa [Unfinished, allFalse] using Set.infinite_univ

theorem unfinished_trueAtZero : Unfinished trueAtZero := by
  have sub : {key : ℕ | key ≠ 0} ⊆ {key | trueAtZero key = false} := by
    intro key nonzero
    simpa [trueAtZero] using nonzero
  refine Set.Infinite.mono sub ?_
  have : {key : ℕ | key ≠ 0} = Set.univ \ {0} := by
    ext key
    simp
  rw [this]
  exact Set.infinite_univ.sdiff (Set.finite_singleton 0)

theorem not_everyKeyTrue_of_unfinished {store : ℕ → Bool} (unfinished : Unfinished store) :
    ¬ ∀ key, store key = true := by
  intro all
  obtain ⟨key, false_at⟩ := unfinished.nonempty
  have := all key
  have false_at' : store key = false := false_at
  rw [false_at'] at this
  exact Bool.false_ne_true this

/-- A chain changes finitely many keys, so an unfinished store stays
unfinished. -/
theorem unfinished_bindingPlug (bindings : Bindings ℕ Bool) {store : ℕ → Bool}
    (unfinished : Unfinished store) :
    Unfinished ((storeAction ℕ Bool).bindingPlug bindings store) := by
  rw [bindingPlug_eq]
  have sub : {key | store key = false} \ {key | key ∈ keysOf bindings} ⊆
      {key | (lookupValue bindings key).getD (store key) = false} := by
    rintro key ⟨false_at, unbound⟩
    have false_at' : store key = false := false_at
    have unbound' : key ∉ keysOf bindings := unbound
    show (lookupValue bindings key).getD (store key) = false
    cases found : lookupValue bindings key with
    | none => simpa using false_at'
    | some value =>
        exact absurd (mem_keysOf_of_lookupValue (by rw [found]; rfl)) unbound'
  exact (unfinished.sdiff (List.finite_toSet (keysOf bindings))).mono sub

/-- **No chain of bindings tells the two stores apart, at any rung.** -/
theorem chains_cannot_separate (rung : Rung) :
    Agree ((storeAction ℕ Bool).regionDerived Set.univ) everyKeyTrue rung allFalse trueAtZero := by
  refine agree_of_unwinding _ everyKeyTrue (relation := fun left right => Unfinished left ∧ Unfinished right)
    ⟨⟨fun _ _ impossible => impossible.elim, fun _ _ impossible => impossible.elim⟩, ?_⟩ ?_
    ⟨unfinished_allFalse, unfinished_trueAtZero⟩ rung
  · rintro left right ⟨leftUnfinished, rightUnfinished⟩ _
    exact ⟨fun all => absurd all (not_everyKeyTrue_of_unfinished leftUnfinished),
      fun all => absurd all (not_everyKeyTrue_of_unfinished rightUnfinished)⟩
  · rintro bindings left right _ ⟨leftUnfinished, rightUnfinished⟩
    exact ⟨unfinished_bindingPlug bindings leftUnfinished,
      unfinished_bindingPlug bindings rightUnfinished⟩

/-- Assign true to every key but zero. -/
def allButZero : ℕ → Option Bool := fun key => if key = 0 then none else some true

/-- **One assignment of infinitely many keys separates them, at rung two.** -/
theorem assignment_separates :
    ¬ Agree (⊤ : AdmissibleClass (storeAction ℕ Bool).explicitRules) everyKeyTrue .intervention
      allFalse trueAtZero := by
  intro agree
  obtain ⟨relation, ⟨_, atoms⟩, related⟩ :=
    agree (AdmissibleClass.top_admissible (rules := (storeAction ℕ Bool).explicitRules) allButZero)
  have same := atoms related ()
  have rightHolds : ∀ key, (storeAction ℕ Bool).assign allButZero trueAtZero key = true := by
    intro key
    by_cases zero : key = 0
    · subst zero
      rfl
    · simp [storeAction, allButZero, zero]
  have leftHolds := same.mpr rightHolds 0
  exact Bool.false_ne_true leftHolds

/-- **Explicit `do` over all assignments is strictly finer than derived `do`
when there are infinitely many keys.** -/
theorem explicit_beyond_derived :
    Agree ((storeAction ℕ Bool).regionDerived Set.univ) everyKeyTrue .counterfactual
        allFalse trueAtZero ∧
      ¬ Agree (⊤ : AdmissibleClass (storeAction ℕ Bool).explicitRules) everyKeyTrue .intervention
        allFalse trueAtZero :=
  ⟨chains_cannot_separate .counterfactual, assignment_separates⟩

end Store

/-! ## Interaction -/

namespace Interaction

open Store

/-- Two keys. -/
inductive Pair where
  | first
  | second
  deriving DecidableEq

/-- "Both keys are true", read as one or zero. -/
noncomputable def both : GradedObservations (storeGSLT Pair Bool) where
  Atom := Unit
  value _ store := if store .first = true ∧ store .second = true then 1 else 0
  value_nonneg _ _ := by split_ifs <;> norm_num
  value_le_one _ _ := by split_ifs <;> norm_num
  value_resp _ left right equivalent := by
    have equal : left = right := equivalent
    subst equal
    rfl

variable (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

theorem passiveDistance_eq_zero {left right : Pair → Bool}
    (same : both.value () left = both.value () right) :
    passiveDistance both discount discount_nonneg discount_le_one left right = 0 := by
  apply GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar
  refine ⟨fun first second => both.value () first = both.value () second, ⟨?_, ?_, ?_⟩, same⟩
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · intro _ _ related atom
    cases atom
    exact related

theorem le_passiveDistance (left right : Pair → Bool) :
    |both.value () left - both.value () right| ≤
      passiveDistance both discount discount_nonneg discount_le_one left right :=
  (GradedSystem.stepping (storeGSLT Pair Bool) both discount discount_nonneg
    discount_le_one).abs_eval_sub_le_logicalDistance (.atom ()) left right

/-- Both keys false. -/
def neither : Pair → Bool := fun _ => false

/-- The chain presentation of the two keys. -/
abbrev rules := (storeAction Pair Bool).derivedRules

theorem plug_doBinding (key : Pair) (value : Bool) (store : Pair → Bool) :
    rules.plug (doBinding key value) store = fun other => if other = key then value else store other := by
  change (storeAction Pair Bool).bindingPlug (doBinding key value) store = _
  rw [bindingPlug_eq]
  funext other
  by_cases same : other = key <;>
    simp [doBinding, lookupValue_bind, lookupValue_empty, single, same]

theorem value_set_first : both.value () (rules.plug (doBinding .first true) neither) = 0 := by
  rw [plug_doBinding]
  simp [both, neither]

theorem value_set_second : both.value () (rules.plug (doBinding .second true) neither) = 0 := by
  rw [plug_doBinding]
  simp [both, neither]

theorem value_set_both :
    both.value () (rules.plug (rules.compose (doBinding .second true) (doBinding .first true))
      neither) = 1 := by
  have equal := rules.plug_compose (doBinding .second true) (doBinding .first true) neither
  have equal' : rules.plug (rules.compose (doBinding .second true) (doBinding .first true)) neither =
      rules.plug (doBinding .second true) (rules.plug (doBinding .first true) neither) := equal
  rw [equal', plug_doBinding, plug_doBinding]
  simp [both]

/-- **Passive impact is not subadditive**: each setting alone has passive
impact zero, and the two settings together have passive impact one. -/
theorem passive_impact_not_subadditive :
    impact (⊥ : AdmissibleClass rules) both discount discount_nonneg discount_le_one
        (doBinding .first true) neither = 0 ∧
      impact (⊥ : AdmissibleClass rules) both discount discount_nonneg discount_le_one
        (doBinding .second true) neither = 0 ∧
      1 ≤ impact (⊥ : AdmissibleClass rules) both discount discount_nonneg discount_le_one
        (rules.compose (doBinding .second true) (doBinding .first true)) neither := by
  refine ⟨?_, ?_, ?_⟩
  · exact (impact_bot (rules := rules) both discount discount_nonneg discount_le_one
      (doBinding .first true) neither).trans
      (passiveDistance_eq_zero discount discount_nonneg discount_le_one
        (by rw [value_set_first]; simp [both, neither]))
  · exact (impact_bot (rules := rules) both discount discount_nonneg discount_le_one
      (doBinding .second true) neither).trans
      (passiveDistance_eq_zero discount discount_nonneg discount_le_one
        (by rw [value_set_second]; simp [both, neither]))
  · refine le_of_le_of_eq ?_ (impact_bot (rules := rules) both discount discount_nonneg
      discount_le_one (rules.compose (doBinding .second true) (doBinding .first true)) neither).symm
    refine le_trans ?_ (le_passiveDistance discount discount_nonneg discount_le_one _ _)
    rw [value_set_both]
    simp [both, neither]

/-- **A class that may set the second key sees the first setting's impact.** -/
theorem impact_sees_interaction :
    1 ≤ impact (⊤ : AdmissibleClass rules) both discount discount_nonneg discount_le_one
      (doBinding .first true) neither := by
  refine le_trans ?_ (passiveDistance_plug_le_interventional _ both discount discount_nonneg
    discount_le_one (AdmissibleClass.top_admissible (doBinding .second true)) _ _)
  refine le_trans ?_ (le_passiveDistance discount discount_nonneg discount_le_one _ _)
  have equal : rules.plug (doBinding .second true) (rules.plug (doBinding .first true) neither) =
      rules.plug (rules.compose (doBinding .second true) (doBinding .first true)) neither :=
    (rules.plug_compose (doBinding .second true) (doBinding .first true) neither).symm
  rw [equal, value_set_both, plug_doBinding]
  simp [both, neither]

end Interaction

/-! ## Authority: regions -/

namespace OneShot

variable {Key : Type} {Value : Type}

/-- A model waiting to read its law on an environment, or the value it read. -/
inductive Stage (Key Value : Type) where
  | pending (law : (Key → Value) → Value) (environment : Key → Value)
  | result (value : Value)

/-- The one step: read the law. -/
inductive Fires : Stage Key Value → Stage Key Value → Prop where
  | fire {law : (Key → Value) → Value} {environment : Key → Value} :
      Fires (.pending law environment) (.result (law environment))

variable (Key Value) in
/-- **One-shot models.** -/
abbrev oneShotGSLT : GSLT where
  Term := Stage Key Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Fires
  rewrites_resp_left := by
    intro source source' target equal step
    have same : source = source' := equal
    subst same
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    have same : target = target' := equal
    subst same
    exact step

/-- Override an environment. -/
def assignStage (assignment : Key → Option Value) : Stage Key Value → Stage Key Value
  | .pending law environment => .pending law fun key => (assignment key).getD (environment key)
  | .result value => .result value

variable (Key Value) in
/-- An assignment overrides the environment of a pending model. -/
def oneShotAction : OverrideAction (oneShotGSLT Key Value) Key Value where
  assign := assignStage
  assign_none stage := by cases stage <;> rfl
  assign_override outer inner stage := by
    change assignStage (override outer inner) stage = assignStage outer (assignStage inner stage)
    cases stage with
    | pending law environment =>
        simp only [assignStage]
        congr 1
        funext key
        rw [override_apply]
        cases outer key <;> rfl
    | result value => rfl
  assign_resp _ left right equivalent := by
    have equal : left = right := equivalent
    subst equal
    rfl

variable (Key Value) in
/-- A result shows its value. -/
def shows : ContextualRules.Observations (oneShotGSLT Key Value) where
  Atom := Value
  observes value stage := stage = .result value
  observes_resp _ left right equivalent := by
    have equal : left = right := equivalent
    subst equal
    exact Iff.rfl

variable [DecidableEq Key]

theorem bindingPlug_pending (bindings : Bindings Key Value) (law : (Key → Value) → Value)
    (environment : Key → Value) :
    (oneShotAction Key Value).bindingPlug bindings (.pending law environment) =
      .pending law fun key => (lookupValue bindings key).getD (environment key) :=
  (oneShotAction Key Value).bindingPlug_equiv_assign bindings _

theorem bindingPlug_result (bindings : Bindings Key Value) (value : Value) :
    (oneShotAction Key Value).bindingPlug bindings (.result value) = .result value :=
  (oneShotAction Key Value).bindingPlug_equiv_assign bindings _

/-- **Masked noninterference.**  Let the law ignore the secret keys whenever
the guard keys hold their masking values, and let the region contain no
secret and no guard.  Then environments that differ only in secrets, with the
guards masked, are indistinguishable by the region's contexts at every rung. -/
theorem masked_noninterference (region secrets guards : Set Key) (mask : Key → Value)
    (law : (Key → Value) → Value)
    (masked : ∀ environment environment' : Key → Value,
      (∀ key, key ∉ secrets → environment key = environment' key) →
        (∀ guard ∈ guards, environment guard = mask guard) → law environment = law environment')
    (outside : ∀ key ∈ region, key ∉ secrets ∧ key ∉ guards)
    (guardsPublic : ∀ guard ∈ guards, guard ∉ secrets)
    {environment environment' : Key → Value}
    (agree : ∀ key, key ∉ secrets → environment key = environment' key)
    (guarded : ∀ guard ∈ guards, environment guard = mask guard) (rung : Rung) :
    Agree ((oneShotAction Key Value).regionDerived region) (shows Key Value) rung
      (.pending law environment) (.pending law environment') := by
  let related : Stage Key Value → Stage Key Value → Prop := fun left right =>
    left = right ∨ ∃ first second : Key → Value,
      (∀ key, key ∉ secrets → first key = second key) ∧
        (∀ guard ∈ guards, first guard = mask guard) ∧
          left = .pending law first ∧ right = .pending law second
  have guardedSecond : ∀ {first second : Key → Value},
      (∀ key, key ∉ secrets → first key = second key) →
        (∀ guard ∈ guards, first guard = mask guard) → ∀ guard ∈ guards, second guard = mask guard :=
    fun agreeing masking guard member =>
      (agreeing guard (guardsPublic guard member)).symm.trans (masking guard member)
  refine agree_of_unwinding _ (shows Key Value) (relation := related) ⟨⟨?_, ?_⟩, ?_⟩ ?_
    (Or.inr ⟨environment, environment', agree, guarded, rfl, rfl⟩) rung
  · rintro left right (rfl | ⟨first, second, agreeing, masking, rfl, rfl⟩) left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · have fires : Fires (.pending law first) left' := step
      cases fires
      refine ⟨.result (law second), Fires.fire, Or.inl ?_⟩
      rw [masked first second agreeing masking]
  · rintro left right (rfl | ⟨first, second, agreeing, masking, rfl, rfl⟩) right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · have fires : Fires (.pending law second) right' := step
      cases fires
      refine ⟨.result (law first), Fires.fire, Or.inl ?_⟩
      rw [masked first second agreeing masking]
  · rintro left right (rfl | ⟨first, second, agreeing, masking, rfl, rfl⟩) value
    · exact Iff.rfl
    · change (Stage.pending law first = .result value) ↔ (Stage.pending law second = .result value)
      exact ⟨fun impossible => (nomatch impossible), fun impossible => (nomatch impossible)⟩
  · rintro bindings left right admissible (rfl | ⟨first, second, agreeing, masking, rfl, rfl⟩)
    · exact Or.inl rfl
    · have unbound : ∀ key, key ∈ secrets ∨ key ∈ guards → lookupValue bindings key = none := by
        intro key member
        cases found : lookupValue bindings key with
        | none => rfl
        | some _ =>
            have inRegion := admissible key (mem_keysOf_of_lookupValue (by rw [found]; rfl))
            rcases member with secret | guard
            · exact absurd secret (outside key inRegion).1
            · exact absurd guard (outside key inRegion).2
      refine Or.inr ⟨fun key => (lookupValue bindings key).getD (first key),
        fun key => (lookupValue bindings key).getD (second key), ?_, ?_,
        bindingPlug_pending bindings law first, bindingPlug_pending bindings law second⟩
      · intro key notSecret
        simp only
        rw [agreeing key notSecret]
      · intro guard member
        simp only
        rw [unbound guard (Or.inr member), Option.getD_none]
        exact masking guard member

/-- **Noninterference for a region**: when the law reads only the keys of the
region, environments that agree on the region are indistinguishable by the
region's contexts at every rung. -/
theorem region_noninterference (region : Set Key) (law : (Key → Value) → Value)
    (local_ : ∀ environment environment' : Key → Value,
      (∀ key ∈ region, environment key = environment' key) → law environment = law environment')
    {environment environment' : Key → Value}
    (agree : ∀ key ∈ region, environment key = environment' key) (rung : Rung) :
    Agree ((oneShotAction Key Value).regionDerived region) (shows Key Value) rung
      (.pending law environment) (.pending law environment') :=
  masked_noninterference region regionᶜ ∅ environment law
    (fun first second agreeing _ => local_ first second fun key member =>
      agreeing key (by simpa using member))
    (fun _ member => ⟨by simpa using member, Set.notMem_empty _⟩)
    (fun _ member => absurd member (Set.notMem_empty _))
    (fun key notSecret => agree key (by simpa using notSecret))
    (fun _ member => absurd member (Set.notMem_empty _)) rung

/-! ### The witness -/

/-- Three keys: the region's key, a guard and a secret. -/
inductive Switch where
  | open_
  | guard
  | secret
  deriving DecidableEq

/-- The law reads the secret through the guard. -/
def gatedLaw (environment : Switch → Bool) : Bool :=
  environment .guard && environment .secret

/-- The secret is on, the guard and the region's key off. -/
def secretOn : Switch → Bool
  | .secret => true
  | _ => false

/-- Everything off. -/
def secretOff : Switch → Bool := fun _ => false

/-- **The region cannot separate the two environments, at any rung.** -/
theorem region_cannot_separate (rung : Rung) :
    Agree ((oneShotAction Switch Bool).regionDerived {Switch.open_}) (shows Switch Bool) rung
      (.pending gatedLaw secretOn) (.pending gatedLaw secretOff) :=
  masked_noninterference {Switch.open_} {Switch.secret} {Switch.guard} (fun _ => false) gatedLaw
    (fun first second agreeing masking => by
      have guardOff : first .guard = false := masking .guard rfl
      have guardOff' : second .guard = false :=
        (agreeing .guard (by simp)).symm.trans guardOff
      simp [gatedLaw, guardOff, guardOff'])
    (fun key member => by
      simp only [Set.mem_singleton_iff] at member
      subst member
      simp)
    (fun key member => by
      simp only [Set.mem_singleton_iff] at member
      subst member
      simp)
    (fun key notSecret => by
      cases key
      · rfl
      · rfl
      · simp at notSecret)
    (fun key member => by
      simp only [Set.mem_singleton_iff] at member
      subst member
      rfl)
    rung

/-- **Opening the guard separates them**: a context outside the region tells
them apart at rung two. -/
theorem global_separates :
    ¬ Agree (⊤ : AdmissibleClass (oneShotAction Switch Bool).derivedRules) (shows Switch Bool)
      .intervention (.pending gatedLaw secretOn) (.pending gatedLaw secretOff) := by
  intro agree
  obtain ⟨relation, ⟨⟨forward, _⟩, atoms⟩, related⟩ :=
    agree (AdmissibleClass.top_admissible (rules := (oneShotAction Switch Bool).derivedRules)
      (doBinding Switch.guard true))
  have plugOn : (oneShotAction Switch Bool).derivedRules.plug (doBinding Switch.guard true)
      (.pending gatedLaw secretOn) = .pending gatedLaw (fun key =>
        (lookupValue (doBinding Switch.guard true) key).getD (secretOn key)) :=
    bindingPlug_pending _ _ _
  have plugOff : (oneShotAction Switch Bool).derivedRules.plug (doBinding Switch.guard true)
      (.pending gatedLaw secretOff) = .pending gatedLaw (fun key =>
        (lookupValue (doBinding Switch.guard true) key).getD (secretOff key)) :=
    bindingPlug_pending _ _ _
  rw [plugOn, plugOff] at related
  obtain ⟨other, step, related'⟩ := forward related
    (Fires.fire : Fires (.pending gatedLaw _) (.result (gatedLaw _)))
  have fires : Fires (.pending gatedLaw fun key =>
      (lookupValue (doBinding Switch.guard true) key).getD (secretOff key)) other := step
  cases fires
  have shown := (atoms related' true).mp (by
    change Stage.result _ = Stage.result true
    simp [gatedLaw, doBinding, lookupValue_bind, lookupValue_empty, single, secretOn])
  change Stage.result _ = Stage.result true at shown
  simp [gatedLaw, doBinding, lookupValue_bind, lookupValue_empty, single, secretOff] at shown

/-- **The region is the authority**: the pair the region's contexts cannot
separate, global contexts separate. -/
theorem region_witness :
    Agree ((oneShotAction Switch Bool).regionDerived {Switch.open_}) (shows Switch Bool)
        .counterfactual (.pending gatedLaw secretOn) (.pending gatedLaw secretOff) ∧
      ¬ Agree (⊤ : AdmissibleClass (oneShotAction Switch Bool).derivedRules) (shows Switch Bool)
        .intervention (.pending gatedLaw secretOn) (.pending gatedLaw secretOff) :=
  ⟨region_cannot_separate .counterfactual, global_separates⟩

end OneShot

/-! ## Retention on the ladder -/

namespace Retention

open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes
open Mettapedia.GSLT.Causality.WeightedResponseTypes
open Mettapedia.GSLT.Dynamics.DemandAgreement

/-- **The twin query** (rung three): some drawn individual shows `treated`
when treated and `untreated` when not. -/
def twinQuery (treated untreated : Bool) : Query :=
  .dia proceed (.conj (literal (effectUnder true) treated) (literal (effectUnder false) untreated))

/-- **The marginal query** (rung two): under one imposed treatment, some drawn
individual shows `shown`. -/
def marginalQuery (treatment shown : Bool) : Query :=
  underIntervention everyIntervention quantities ⟨some treatment, AdmissibleClass.top_admissible _⟩
    (.dia () (.dia () (passiveLiteral .effect shown)))

theorem sat_literal_effectUnder (treatment shown : Bool) (individual : Individual) :
    ladder.sat (literal (effectUnder treatment) shown) (drawn none individual) ↔
      individual.2.outcome treatment = shown := by
  rw [sat_literal, sat_effectUnder]
  exact Bool.coe_iff_coe

/-- **The twin query reads the shared draw.** -/
theorem sat_twinQuery (individuals : List Individual) (treated untreated : Bool) :
    ladder.sat (twinQuery treated untreated) (.population individuals none) ↔
      ∃ individual ∈ individuals,
        individual.2.outcome true = treated ∧ individual.2.outcome false = untreated := by
  constructor
  · rintro ⟨target, step, holds⟩
    cases moves_of_step step with
    | @draw _ _ natural response member =>
        have both := holds
        change ladder.sat (literal (effectUnder true) treated) (drawn none (natural, response)) ∧
          ladder.sat (literal (effectUnder false) untreated) (drawn none (natural, response)) at both
        rw [sat_literal_effectUnder, sat_literal_effectUnder] at both
        exact ⟨(natural, response), member, both⟩
  · rintro ⟨⟨natural, response⟩, member, outcomes⟩
    refine ⟨drawn none (natural, response), Moves.draw member, ?_⟩
    change ladder.sat (literal (effectUnder true) treated) (drawn none (natural, response)) ∧
      ladder.sat (literal (effectUnder false) untreated) (drawn none (natural, response))
    rw [sat_literal_effectUnder, sat_literal_effectUnder]
    exact outcomes

/-- **The marginal query draws afresh under its regime.** -/
theorem sat_marginalQuery (individuals : List Individual) (treatment shown : Bool) :
    ladder.sat (marginalQuery treatment shown) (.population individuals none) ↔
      ∃ individual ∈ individuals, individual.2.outcome treatment = shown := by
  rw [marginalQuery, sat_underIntervention]
  constructor
  · rintro ⟨target, step, final, finalStep, holds⟩
    cases moves_of_step step with
    | @draw _ _ natural response member =>
        cases moves_of_step finalStep
        rw [sat_passiveLiteral] at holds
        exact ⟨(natural, response), member, Bool.coe_iff_coe.mp holds⟩
  · rintro ⟨⟨natural, response⟩, member, outcome⟩
    refine ⟨.individual natural response (some treatment), Moves.draw member, _, Moves.respond, ?_⟩
    rw [sat_passiveLiteral]
    exact Bool.coe_iff_coe.mpr outcome

/-- The potential outcomes of a pair of draws: the first treated, the second
not. -/
def outcomes (pair : Individual × Individual) : Bool × Bool :=
  (pair.1.2.outcome true, pair.2.2.outcome false)

/-- **The twin**: the potential outcomes of the shared draw. -/
def twinSet (individuals : List Individual) : Finset (Bool × Bool) :=
  (sharedPairSet individuals.toFinset).image outcomes

/-- **The experiment**: the potential outcomes of two separate draws. -/
def experimentSet (individuals : List Individual) : Finset (Bool × Bool) :=
  (resampledPairSet individuals.toFinset).image outcomes

theorem mem_twinSet (individuals : List Individual) (treated untreated : Bool) :
    (treated, untreated) ∈ twinSet individuals ↔
      ∃ individual ∈ individuals,
        individual.2.outcome true = treated ∧ individual.2.outcome false = untreated := by
  simp [twinSet, sharedPairSet, outcomes]

theorem mem_experimentSet (individuals : List Individual) (treated untreated : Bool) :
    (treated, untreated) ∈ experimentSet individuals ↔
      (∃ individual ∈ individuals, individual.2.outcome true = treated) ∧
        ∃ individual ∈ individuals, individual.2.outcome false = untreated := by
  constructor
  · intro member
    obtain ⟨⟨first, second⟩, pairMember, same⟩ := Finset.mem_image.mp member
    obtain ⟨first', firstMember, pairIn⟩ := Finset.mem_biUnion.mp pairMember
    obtain ⟨second', secondMember, pairEq⟩ := Finset.mem_image.mp pairIn
    simp only [Prod.mk.injEq] at pairEq
    obtain ⟨rfl, rfl⟩ := pairEq
    simp only [outcomes, Prod.mk.injEq] at same
    exact ⟨⟨first', List.mem_toFinset.mp firstMember, same.1⟩,
      ⟨second', List.mem_toFinset.mp secondMember, same.2⟩⟩
  · rintro ⟨⟨first, member, treatedSame⟩, ⟨second, member', untreatedSame⟩⟩
    refine Finset.mem_image.mpr ⟨(first, second), Finset.mem_biUnion.mpr ⟨first,
      List.mem_toFinset.mpr member, Finset.mem_image.mpr ⟨second, List.mem_toFinset.mpr member',
        rfl⟩⟩, ?_⟩
    simp [outcomes, treatedSame, untreatedSame]

/-- **The rung-3 query equals the twin built from the shared cell.** -/
theorem sat_twinQuery_iff_mem (individuals : List Individual) (treated untreated : Bool) :
    ladder.sat (twinQuery treated untreated) (.population individuals none) ↔
      (treated, untreated) ∈ twinSet individuals :=
  (sat_twinQuery individuals treated untreated).trans (mem_twinSet individuals treated untreated).symm

/-- **The rung-2 queries equal the experiment built from the resampled cell.** -/
theorem sat_experimentQueries (individuals : List Individual) (treated untreated : Bool) :
    (ladder.sat (marginalQuery true treated) (.population individuals none) ∧
        ladder.sat (marginalQuery false untreated) (.population individuals none)) ↔
      (treated, untreated) ∈ experimentSet individuals := by
  rw [sat_marginalQuery, sat_marginalQuery, mem_experimentSet]

/-- **Under the condition of `DemandAgreement` the twin is the experiment.** -/
theorem twinSet_eq_experimentSet_of_card_le_one {individuals : List Individual}
    (deterministic : individuals.toFinset.card ≤ 1) :
    twinSet individuals = experimentSet individuals := by
  rw [twinSet, experimentSet,
    (sharedPairSet_eq_resampledPairSet_iff individuals.toFinset).mpr deterministic]

/-- **Mixed and fixed: one experiment, two twins.** -/
theorem mixed_fixed_retention :
    experimentSet mixedIndividuals = experimentSet fixedIndividuals ∧
      twinSet mixedIndividuals ≠ twinSet fixedIndividuals := by
  refine ⟨?_, ?_⟩
  · ext ⟨treated, untreated⟩
    rw [mem_experimentSet, mem_experimentSet]
    cases treated <;> cases untreated <;> simp [Response.outcome]
  · intro same
    have member : (true, false) ∈ twinSet mixedIndividuals :=
      (mem_twinSet _ _ _).mpr ⟨(false, .helped), by simp, rfl, rfl⟩
    rw [same, mem_twinSet] at member
    obtain ⟨individual, member', treatedSame, untreatedSame⟩ := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl <;> simp [Response.outcome] at treatedSame untreatedSame

/-- Helped and always-affected individuals. -/
abbrev helpedOrAlways : List Individual := [(false, .helped), (false, .always)]

/-- **On the readout the condition is sufficient and not necessary**: two
individuals whose twin is the experiment. -/
theorem retention_beyond_condition :
    twinSet helpedOrAlways = experimentSet helpedOrAlways ∧ ¬ helpedOrAlways.toFinset.card ≤ 1 := by
  refine ⟨?_, by decide⟩
  ext ⟨treated, untreated⟩
  rw [mem_twinSet, mem_experimentSet]
  cases treated <;> cases untreated <;> simp [Response.outcome]

end Retention

end Mettapedia.GSLT.Causality.ContextOperatorsControls
