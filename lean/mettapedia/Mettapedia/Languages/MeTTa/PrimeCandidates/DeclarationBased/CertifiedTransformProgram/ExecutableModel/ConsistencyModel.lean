import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Model
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRules
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.InstanceNames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws

/-!
# The consistency model of the executable package with its codes

The program's propositions are codes: implication, and the quantifier
`all@A` and the equation `eq@A` at every simple type `A` of the profile,
decoded by `holds`. The instance names are read by the profile's parser, so
no choice is involved. The consistency model reads the executable package
with these codes through its own reduction:

* the package's computations, with identity elimination returning its method
  on every path;
* no decoding of `holds`, which is rigid in the model;
* the code constructors as constructors.

This file builds that reduction, its shape, and the model's laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative.Consistency
open Mettapedia.Logic
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName)

namespace CodeModel

/-! ## The codes of the program -/


/-- The carrier of a simple type of the profile: the numbers are data, the sets
a rigid type, and a function type has the kind of its codomain. -/
def carrierOf : HOL.Ty SetProfile.SetBase → Σ k, Carrier k
  | .prop => ⟨.gen, .prop⟩
  | .base .num => ⟨.data, .num⟩
  | .base .set => ⟨.gen, .rigid setN⟩
  | .arr a b => ⟨(carrierOf b).1, .arr (carrierOf a).2 (carrierOf b).2⟩

/-- The carriers of the quantifier instances: `all@A` ranges over `A`. -/
def allCarrierOf (name : DeclName) : Option (Σ k, Carrier k) :=
  (SetProfile.allInstance? name).map carrierOf

/-- The carriers of the equation instances: `eq@A` compares at `A`. -/
def eqCarrierOf (name : DeclName) : Option (Σ k, Carrier k) :=
  (SetProfile.eqInstance? name).map carrierOf

/-! ## The model's reduction -/

/-- The model's roles: identity elimination inspects no argument, and the code
constructors construct. -/
def modelRoles : Roles Tower.Head := fun name =>
  if name = jName then .computes 6 .leaf
  else if name = impN then .constructor 2
  else if (SetProfile.allInstance? name).isSome then .constructor 1
  else if (SetProfile.eqInstance? name).isSome then .constructor 2
  else roles name

/-- The package's computations, with identity elimination on every path. -/
def modelComputations : List (DeclName × RootComputation Tower.Head) :=
  [(numRecName, iotaComputation numRecName ctors),
   (addN, recursionComputation addN ctors addEntries 1 0 addBody),
   (powN, recursionComputation powN ctors powEntries 0 1 powBody),
   (jName, castComputation jName),
   (eqAtName, definitionComputation eqAtName eqAtTele eqAtRhs),
   (sucMoveName, definitionComputation sucMoveName Package.eqAtTelescope sucMoveRhs),
   (keepName, definitionComputation keepName keepTele keepRhs),
   (transportName, definitionComputation transportName Package.transportTelescope transportRhs),
   (composeName, definitionComputation composeName Package.composeTelescope composeRhs),
   (iterName, recursionComputation iterName ctors iterEntries 0 5 iterBody),
   (returnIterName, definitionComputation returnIterName returnIterTele returnIterRhs),
   (sucStepName, definitionComputation sucStepName Package.eqAtTelescope sucStepRhs)]

/-- The model's reduction package. -/
def modelRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := allTypes
    computation := RootComputation.unionAll modelComputations }

/-! ## Roles -/

theorem modelRoles_of {name : DeclName} (hj : name ≠ jName) (hi : name ≠ impN)
    (ha : SetProfile.allInstance? name = none) (he : SetProfile.eqInstance? name = none) :
    modelRoles name = roles name := by
  simp [modelRoles, hj, hi, ha, he]

theorem modelRoles_num : modelRoles numN = .inductive ctors :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_num
theorem modelRoles_zero : modelRoles zeroN = .constructor 0 :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_zero
theorem modelRoles_suc : modelRoles sucN = .constructor 1 :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_suc
theorem modelRoles_numRec : modelRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_numRec
theorem modelRoles_add : modelRoles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_add
theorem modelRoles_pow : modelRoles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_pow
theorem modelRoles_j : modelRoles jName = .computes 6 .leaf := by simp [modelRoles]
theorem modelRoles_eqAt : modelRoles eqAtName = .computes 1 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_eqAt
theorem modelRoles_sucMove : modelRoles sucMoveName = .computes 2 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_sucMove
theorem modelRoles_keep : modelRoles keepName = .computes 4 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_keep
theorem modelRoles_transport : modelRoles transportName = .computes 6 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans
    roles_transport
theorem modelRoles_compose : modelRoles composeName = .computes 6 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_compose
theorem modelRoles_iter : modelRoles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_iter
theorem modelRoles_returnIter : modelRoles returnIterName = .computes 1 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans
    roles_returnIter
theorem modelRoles_sucStep : modelRoles sucStepName = .computes 2 .leaf :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_sucStep
theorem modelRoles_imp : modelRoles impN = .constructor 2 := by
  simp [modelRoles, show impN ≠ jName by decide]
theorem modelRoles_all {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.allInstance? name = some type) : modelRoles name = .constructor 1 := by
  have hj : name ≠ jName := fun h => by
    rw [h, show SetProfile.allInstance? jName = none by decide] at found; cases found
  have hi : name ≠ impN := fun h => by
    rw [h, SetProfile.allInstance?_impName] at found; cases found
  simp [modelRoles, hj, hi, found]
theorem modelRoles_eq {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.eqInstance? name = some type) : modelRoles name = .constructor 2 := by
  have hj : name ≠ jName := fun h => by
    rw [h, show SetProfile.eqInstance? jName = none by decide] at found; cases found
  have hi : name ≠ impN := fun h => by
    rw [h, SetProfile.eqInstance?_impName] at found; cases found
  have ha : SetProfile.allInstance? name = none := by
    rw [SetProfile.eqInstance?_eq_some found, SetProfile.allInstance?_eqName]
  simp [modelRoles, hj, hi, ha, found]
theorem modelRoles_prop : modelRoles propN = .rigid :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans rfl
theorem modelRoles_holds : modelRoles holdsN = .rigid :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans rfl

/-- The only inductive type of the model is the numbers. -/
theorem modelRoles_inductive {T : DeclName} {cs : List (DeclName × List CtorField)}
    (role : modelRoles T = .inductive cs) : T = numN ∧ cs = ctors := by
  by_cases hj : T = jName
  · subst hj; rw [modelRoles_j] at role; cases role
  by_cases hi : T = impN
  · subst hi; rw [modelRoles_imp] at role; cases role
  cases ha : SetProfile.allInstance? T with
  | some _ => rw [modelRoles_all ha] at role; cases role
  | none =>
      cases he : SetProfile.eqInstance? T with
      | some _ => rw [modelRoles_eq he] at role; cases role
      | none =>
          rw [modelRoles_of hj hi ha he] at role
          exact roles_inductive role

theorem modelConstructorsDeclared : ConstructorsDeclared modelRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := modelRoles_inductive role
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact modelRoles_zero
    · exact modelRoles_suc
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := modelRoles_inductive role
    decide

/-! ## The shape of the model's reduction -/

theorem modelComputations_spine :
    ∀ entry ∈ modelComputations, SpineShaped modelRoles entry.2 := by
  intro entry mem
  simp only [modelComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ step =>
      IotaStep.spine modelRoles_num modelRoles_numRec modelConstructorsDeclared step
  · exact fun _ _ _ step =>
      RecursionStep.spine modelRoles_num modelConstructorsDeclared modelRoles_add step
  · exact fun _ _ _ step =>
      RecursionStep.spine modelRoles_num modelConstructorsDeclared modelRoles_pow step
  · exact castComputation_spine modelRoles_j
  · exact definitionComputation_spine modelRoles_eqAt
  · exact definitionComputation_spine modelRoles_sucMove
  · exact definitionComputation_spine modelRoles_keep
  · exact definitionComputation_spine modelRoles_transport
  · exact definitionComputation_spine modelRoles_compose
  · exact fun _ _ _ step =>
      RecursionStep.spine modelRoles_num modelConstructorsDeclared modelRoles_iter step
  · exact definitionComputation_spine modelRoles_returnIter
  · exact definitionComputation_spine modelRoles_sucStep

theorem modelComputations_headed :
    ∀ entry ∈ modelComputations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [modelComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · exact castComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact recursionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed

theorem modelComputations_deterministic :
    ∀ entry ∈ modelComputations, Deterministic entry.2 := by
  intro entry mem
  simp only [modelComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := numN) modelRoles_num modelConstructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic modelRoles_num modelConstructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic modelRoles_num modelConstructorsDeclared step step'
  · exact castComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic modelRoles_num modelConstructorsDeclared step step'
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic

theorem modelComputations_distinct : (modelComputations.map Prod.fst).Nodup := by
  decide

theorem modelShape : RootShape modelRules modelRoles where
  spine := fun step => RootComputation.unionAll_spine modelComputations_spine step
  deterministic := by
    intro n t u u' step step'
    exact (RootComputation.unionAll_deterministic modelComputations_distinct
      modelComputations_headed modelComputations_deterministic step step').symm

/-! ## The model -/

/-- The tower's level model, for the model's reduction package. -/
def modelLevels (valuation : Nat → Nat) : LevelModel modelRules ℕ where
  level := (TowerModel.levels valuation).level
  successor := (TowerModel.levels valuation).successor
  universe_typing := (TowerModel.levels valuation).universe_typing
  ground_typing := (TowerModel.levels valuation).ground_typing
  cumulative_universe := (TowerModel.levels valuation).cumulative_universe
  headEq_level := (TowerModel.levels valuation).headEq_level
  join_level := (TowerModel.levels valuation).join_level
  join_exists := (TowerModel.levels valuation).join_exists
  join_upper := (TowerModel.levels valuation).join_upper
  cumulative_refl := (TowerModel.levels valuation).cumulative_refl
  headEq_symm := (TowerModel.levels valuation).headEq_symm
  headEq_trans := (TowerModel.levels valuation).headEq_trans
  universe_decided := (TowerModel.levels valuation).universe_decided

/-- The consistency model of the executable package with the program's codes. -/
def model (valuation : Nat → Nat) : Model Tower.Head ℕ where
  rules := modelRules
  roles := modelRoles
  zero := zeroN
  suc := sucN
  imp := impN
  allCarrier := allCarrierOf
  eqCarrier := eqCarrierOf
  num := numN
  prop := propN
  holds := holdsN
  levels := modelLevels valuation

theorem model_laws (valuation : Nat → Nat) : (model valuation).Laws where
  truth :=
    { shape := modelShape
      zero := modelRoles_zero
      suc := modelRoles_suc
      imp := modelRoles_imp
      all := by
        intro a A carrier
        change (SetProfile.allInstance? a).map carrierOf = some A at carrier
        cases found : SetProfile.allInstance? a with
        | none => rw [found] at carrier; cases carrier
        | some _ => exact modelRoles_all found
      eq := by
        intro e A carrier
        change (SetProfile.eqInstance? e).map carrierOf = some A at carrier
        cases found : SetProfile.eqInstance? e with
        | none => rw [found] at carrier; cases carrier
        | some _ => exact modelRoles_eq found
      impNotEq := by
        change (SetProfile.eqInstance? impN).map carrierOf = none
        rw [SetProfile.eqInstance?_impName]
        rfl }
  num := modelRoles_num
  prop := modelRoles_prop
  holds := modelRoles_holds

/-! ## The package's steps in the model -/

theorem model_step {entry : DeclName × RootComputation Tower.Head}
    (mem : entry ∈ modelComputations) {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    modelRules.computation.step l r :=
  RootComputation.step_unionAll mem h

theorem modelListed (i : Nat) (h : i < modelComputations.length) :
    modelComputations[i] ∈ modelComputations :=
  List.getElem_mem h

/-- Every root step of the package is a step of the model's reduction: the two
lists of computations agree except at identity elimination, whose step at
reflexivity is an instance of the cast. -/
theorem model_step_of_rules {n : Nat} {l r : Tower.Tm n} (step : rules.computation.step l r) :
    modelRules.computation.step l r := by
  change (RootComputation.unionAll (computations.filter
    fun entry => (fun _ => true) entry.1)).step l r at step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  have listedIn : entry ∈ computations := (List.mem_filter.mp mem).1
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
  rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact model_step (modelListed 0 (by decide)) h
  · exact model_step (modelListed 1 (by decide)) h
  · exact model_step (modelListed 2 (by decide)) h
  · exact model_step (modelListed 3 (by decide)) (eliminator_step_cast h)
  · exact model_step (modelListed 4 (by decide)) h
  · exact model_step (modelListed 5 (by decide)) h
  · exact model_step (modelListed 6 (by decide)) h
  · exact model_step (modelListed 7 (by decide)) h
  · exact model_step (modelListed 8 (by decide)) h
  · exact model_step (modelListed 9 (by decide)) h
  · exact model_step (modelListed 10 (by decide)) h
  · exact model_step (modelListed 11 (by decide)) h

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
