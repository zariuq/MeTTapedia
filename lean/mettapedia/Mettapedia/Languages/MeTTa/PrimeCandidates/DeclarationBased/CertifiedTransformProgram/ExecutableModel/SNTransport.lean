import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TransportRules

/-!
# The transport value model of the executable package

The value side of model S for the executable package: model C's consistency
model with a daimon, on which identity elimination transports its method along
its motive instead of casting it (`tmodelC`).

* The daimon is a fresh constant `⋆` that no rule of the package declares; it is
  rigid.
* The roles are model C's, with six fresh constants that no rule of the
  package declares, like the daimon: `coe` inspects its target for a head
  form, and `coeU`, `coeNum`, `coeProp`, `coePi`, `coeSigma` inspect its
  source. `holds` stays rigid.
* The reduction is model C's, with the cast of identity elimination replaced by
  `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`, and the rows of the transport
  table added; the row of `coeU` compares universe levels at the valuation.

The package is root-shaped and deterministic, has the laws of a consistency
model, and has the transport table with the daimon (`tmodel_coeTable`), so every
row of the table holds on the skeleton-free value side over it
(`vmodel_coeRules`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative.Consistency
open Presentation.TypedEquality.Impredicative.Realizability
open Presentation.TypedEquality.Impredicative.ValueSide (coeApp)
open Mettapedia.Logic
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName)

namespace CodeModel

/-! ## The daimon -/

/-- The daimon: a fresh constant. -/
def starN : DeclName := .mkSimple "⋆"

theorem starN_undeclared : objectRules.constantType starN = none := by
  decide

theorem modelRoles_star : modelRoles starN = .rigid :=
  (modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans rfl

/-! ## The transport's constants -/

/-- The transport. -/
def coeN : DeclName := .mkSimple "coe"
/-- The transport into a universe, once the target is read. -/
def coeUN : DeclName := .mkSimple "coe-univ"
/-- The transport into the numbers, once the target is read. -/
def coeNumN : DeclName := .mkSimple "coe-num"
/-- The transport into the codes, once the target is read. -/
def coePropN : DeclName := .mkSimple "coe-prop"
/-- The transport into a dependent function type, once the target is read. -/
def coePiN : DeclName := .mkSimple "coe-pi"
/-- The transport into a dependent pair type, once the target is read. -/
def coeSigmaN : DeclName := .mkSimple "coe-sigma"

/-- The transport's constants. -/
def coeNames : CoeNames where
  coe := coeN
  coeU := coeUN
  coeNum := coeNumN
  coeProp := coePropN
  coePi := coePiN
  coeSigma := coeSigmaN

/-- The transport's constants, as a list. -/
abbrev coeNameList : List DeclName := [coeN, coeUN, coeNumN, coePropN, coePiN, coeSigmaN]

/-- **The transport's constants are fresh**: neither the package nor the
object package declares them, they are no code instance, and they differ from
the daimon. -/
theorem coeNames_fresh : ∀ c ∈ coeNameList, allTypes c = none ∧
    objectRules.constantType c = none ∧ SetProfile.allInstance? c = none ∧
    SetProfile.eqInstance? c = none ∧ c ≠ starN := by
  decide

/-! ## Roles -/

/-- The roles of the transport value model: model C's, with the transport's
constants inspecting their type arguments for head forms. -/
def tmodelRoles : Roles Tower.Head := fun name =>
  if name = coeN then .computes 3 (headAt 1)
  else if name = coeUN then .computes 3 headAtBoth
  else if name = coeNumN then .computes 2 (headAt 0)
  else if name = coePropN then .computes 2 (headAt 0)
  else if name = coePiN then .computes 4 (headAt 2)
  else if name = coeSigmaN then .computes 4 (headAt 2)
  else modelRoles name

theorem tmodelRoles_eq {name : DeclName} (fresh : name ∉ coeNameList) :
    tmodelRoles name = modelRoles name := by
  simp only [coeNameList, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := fresh
  unfold tmodelRoles
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg h₆]

theorem tmodelRoles_coe : tmodelRoles coeN = .computes 3 (headAt 1) := by
  unfold tmodelRoles
  rw [if_pos rfl]

theorem tmodelRoles_coeU : tmodelRoles coeUN = .computes 3 headAtBoth := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_pos rfl]

theorem tmodelRoles_coeNum : tmodelRoles coeNumN = .computes 2 (headAt 0) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem tmodelRoles_coeProp : tmodelRoles coePropN = .computes 2 (headAt 0) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem tmodelRoles_coePi : tmodelRoles coePiN = .computes 4 (headAt 2) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

theorem tmodelRoles_coeSigma : tmodelRoles coeSigmaN = .computes 4 (headAt 2) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

theorem tmodelRoles_num : tmodelRoles numN = .inductive ctors :=
  (tmodelRoles_eq (by decide)).trans modelRoles_num
theorem tmodelRoles_zero : tmodelRoles zeroN = .constructor 0 :=
  (tmodelRoles_eq (by decide)).trans modelRoles_zero
theorem tmodelRoles_suc : tmodelRoles sucN = .constructor 1 :=
  (tmodelRoles_eq (by decide)).trans modelRoles_suc
theorem tmodelRoles_numRec :
    tmodelRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  (tmodelRoles_eq (by decide)).trans modelRoles_numRec
theorem tmodelRoles_add : tmodelRoles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  (tmodelRoles_eq (by decide)).trans modelRoles_add
theorem tmodelRoles_pow : tmodelRoles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  (tmodelRoles_eq (by decide)).trans modelRoles_pow
theorem tmodelRoles_j : tmodelRoles jName = .computes 6 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_j
theorem tmodelRoles_eqAt : tmodelRoles eqAtName = .computes 1 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_eqAt
theorem tmodelRoles_sucMove : tmodelRoles sucMoveName = .computes 2 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_sucMove
theorem tmodelRoles_keep : tmodelRoles keepName = .computes 4 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_keep
theorem tmodelRoles_transport : tmodelRoles transportName = .computes 6 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_transport
theorem tmodelRoles_compose : tmodelRoles composeName = .computes 6 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_compose
theorem tmodelRoles_iter :
    tmodelRoles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  (tmodelRoles_eq (by decide)).trans modelRoles_iter
theorem tmodelRoles_returnIter : tmodelRoles returnIterName = .computes 1 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_returnIter
theorem tmodelRoles_sucStep : tmodelRoles sucStepName = .computes 2 .leaf :=
  (tmodelRoles_eq (by decide)).trans modelRoles_sucStep
theorem tmodelRoles_imp : tmodelRoles impN = .constructor 2 :=
  (tmodelRoles_eq (by decide)).trans modelRoles_imp
theorem tmodelRoles_prop : tmodelRoles propN = .rigid :=
  (tmodelRoles_eq (by decide)).trans modelRoles_prop
theorem tmodelRoles_holds : tmodelRoles holdsN = .rigid :=
  (tmodelRoles_eq (by decide)).trans modelRoles_holds
theorem tmodelRoles_star : tmodelRoles starN = .rigid :=
  (tmodelRoles_eq (by decide)).trans modelRoles_star

/-- A name that is a code instance is none of the transport's constants. -/
theorem not_mem_coeNameList {name : DeclName}
    (instance_ : SetProfile.allInstance? name ≠ none ∨ SetProfile.eqInstance? name ≠ none) :
    name ∉ coeNameList := by
  intro mem
  obtain ⟨-, -, all, eq, -⟩ := coeNames_fresh name mem
  rcases instance_ with h | h
  · exact h all
  · exact h eq

theorem tmodelRoles_all {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.allInstance? name = some type) : tmodelRoles name = .constructor 1 :=
  (tmodelRoles_eq (not_mem_coeNameList (.inl (by rw [found]; exact Option.some_ne_none _)))).trans
    (modelRoles_all found)

theorem tmodelRoles_eqCode {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.eqInstance? name = some type) : tmodelRoles name = .constructor 2 :=
  (tmodelRoles_eq (not_mem_coeNameList (.inr (by rw [found]; exact Option.some_ne_none _)))).trans
    (modelRoles_eq found)

/-- The only inductive type of the transport value model is the numbers. -/
theorem tmodelRoles_inductive {T : DeclName} {cs : List (DeclName × List CtorField)}
    (role : tmodelRoles T = .inductive cs) : T = numN ∧ cs = ctors := by
  by_cases fresh : T ∈ coeNameList
  · exfalso
    simp only [coeNameList, List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tmodelRoles_coe] at role; cases role
    · rw [tmodelRoles_coeU] at role; cases role
    · rw [tmodelRoles_coeNum] at role; cases role
    · rw [tmodelRoles_coeProp] at role; cases role
    · rw [tmodelRoles_coePi] at role; cases role
    · rw [tmodelRoles_coeSigma] at role; cases role
  · rw [tmodelRoles_eq fresh] at role
    exact modelRoles_inductive role

theorem tmodelConstructorsDeclared : ConstructorsDeclared tmodelRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := tmodelRoles_inductive role
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact tmodelRoles_zero
    · exact tmodelRoles_suc
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := tmodelRoles_inductive role
    decide

theorem tmodelRoles_num_stuck : ∀ arity inspect, tmodelRoles numN ≠ .computes arity inspect :=
  fun _ _ h => nomatch tmodelRoles_num.symm.trans h

theorem tmodelRoles_prop_stuck : ∀ arity inspect, tmodelRoles propN ≠ .computes arity inspect :=
  fun _ _ h => nomatch tmodelRoles_prop.symm.trans h

/-! ## The reduction -/

/-- The parameters of the transport table at the valuation `v`. -/
def tcoeParams (v : Nat → Nat) : CoeParams Tower.Head ℕ where
  roles := tmodelRoles
  isUniverse := Tower.rules.isUniverse
  level := (TowerModel.levels v).level
  num := numN
  prop := propN
  star := starN

/-- Model C's computations, with the transport in place of the cast of identity
elimination, and the rows of the transport table. -/
def tmodelComputations (v : Nat → Nat) : List (DeclName × RootComputation Tower.Head) :=
  [(numRecName, iotaComputation numRecName ctors),
   (addN, recursionComputation addN ctors addEntries 1 0 addBody),
   (powN, recursionComputation powN ctors powEntries 0 1 powBody),
   (jName, transportJ jName coeN),
   (eqAtName, definitionComputation eqAtName eqAtTele eqAtRhs),
   (sucMoveName, definitionComputation sucMoveName Package.eqAtTelescope sucMoveRhs),
   (keepName, definitionComputation keepName keepTele keepRhs),
   (transportName, definitionComputation transportName Package.transportTelescope transportRhs),
   (composeName, definitionComputation composeName Package.composeTelescope composeRhs),
   (iterName, recursionComputation iterName ctors iterEntries 0 5 iterBody),
   (returnIterName, definitionComputation returnIterName returnIterTele returnIterRhs),
   (sucStepName, definitionComputation sucStepName Package.eqAtTelescope sucStepRhs),
   (coeN, coeComputation (tcoeParams v) coeNames),
   (coeUN, coeUComputation (tcoeParams v) coeNames),
   (coeNumN, coeConstComputation (tcoeParams v) coeNumN numN),
   (coePropN, coeConstComputation (tcoeParams v) coePropN propN),
   (coePiN, coePiComputation (tcoeParams v) coeNames),
   (coeSigmaN, coeSigmaComputation (tcoeParams v) coeNames)]

/-- The reduction package of the transport value model. -/
def tmodelRules (v : Nat → Nat) : Rules Tower.Head :=
  { Tower.rules with
    constantType := allTypes
    computation := RootComputation.unionAll (tmodelComputations v) }

theorem tmodelComputations_names (v : Nat → Nat) :
    (tmodelComputations v).map Prod.fst =
      [numRecName, addN, powN, jName, eqAtName, sucMoveName, keepName, transportName,
        composeName, iterName, returnIterName, sucStepName, coeN, coeUN, coeNumN, coePropN,
        coePiN, coeSigmaN] :=
  rfl

theorem tmodelComputations_distinct (v : Nat → Nat) :
    ((tmodelComputations v).map Prod.fst).Nodup := by
  rw [tmodelComputations_names]
  decide

theorem tmodelComputations_spine (v : Nat → Nat) :
    ∀ entry ∈ tmodelComputations v, SpineShaped tmodelRoles entry.2 := by
  intro entry mem
  simp only [tmodelComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ step =>
      IotaStep.spine tmodelRoles_num tmodelRoles_numRec tmodelConstructorsDeclared step
  · exact fun _ _ _ step =>
      RecursionStep.spine tmodelRoles_num tmodelConstructorsDeclared tmodelRoles_add step
  · exact fun _ _ _ step =>
      RecursionStep.spine tmodelRoles_num tmodelConstructorsDeclared tmodelRoles_pow step
  · exact transportJ_spine tmodelRoles_j
  · exact definitionComputation_spine tmodelRoles_eqAt
  · exact definitionComputation_spine tmodelRoles_sucMove
  · exact definitionComputation_spine tmodelRoles_keep
  · exact definitionComputation_spine tmodelRoles_transport
  · exact definitionComputation_spine tmodelRoles_compose
  · exact fun _ _ _ step =>
      RecursionStep.spine tmodelRoles_num tmodelConstructorsDeclared tmodelRoles_iter step
  · exact definitionComputation_spine tmodelRoles_returnIter
  · exact definitionComputation_spine tmodelRoles_sucStep
  · exact coeComputation_spine tmodelRoles_coe tmodelRoles_num_stuck tmodelRoles_prop_stuck
  · exact coeUComputation_spine tmodelRoles_coeU
  · exact coeConstComputation_spine tmodelRoles_coeNum tmodelRoles_num_stuck
  · exact coeConstComputation_spine tmodelRoles_coeProp tmodelRoles_prop_stuck
  · exact coePiComputation_spine tmodelRoles_coePi
  · exact coeSigmaComputation_spine tmodelRoles_coeSigma

theorem tmodelComputations_headed (v : Nat → Nat) :
    ∀ entry ∈ tmodelComputations v, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [tmodelComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · exact transportJ_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact recursionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact coeComputation_headed
  · exact coeUComputation_headed
  · exact coeConstComputation_headed
  · exact coeConstComputation_headed
  · exact coePiComputation_headed
  · exact coeSigmaComputation_headed

theorem tmodelComputations_deterministic (v : Nat → Nat) :
    ∀ entry ∈ tmodelComputations v, Deterministic entry.2 := by
  intro entry mem
  simp only [tmodelComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := numN) tmodelRoles_num tmodelConstructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic tmodelRoles_num tmodelConstructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic tmodelRoles_num tmodelConstructorsDeclared step step'
  · exact transportJ_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic tmodelRoles_num tmodelConstructorsDeclared step step'
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact coeComputation_deterministic (show numN ≠ propN by decide)
  · exact coeUComputation_deterministic
  · exact coeConstComputation_deterministic
  · exact coeConstComputation_deterministic
  · exact coePiComputation_deterministic
  · exact coeSigmaComputation_deterministic

/-- **The transport value model's reduction is root-shaped and deterministic**:
its root steps occur at computing spines of exact arity whose inspected values
have the shapes their skeletons require, and at most one applies. -/
theorem tmodelShape (v : Nat → Nat) : RootShape (tmodelRules v) tmodelRoles where
  spine := fun step => RootComputation.unionAll_spine (tmodelComputations_spine v) step
  deterministic := by
    intro n t u u' step step'
    exact (RootComputation.unionAll_deterministic (tmodelComputations_distinct v)
      (tmodelComputations_headed v) (tmodelComputations_deterministic v) step step').symm

/-- Weak-head reduction of the transport value model is deterministic. -/
theorem tmodel_whStep_deterministic (v : Nat → Nat) {n : Nat} {t u u' : Tower.Tm n}
    (first : WhStep (tmodelRules v) tmodelRoles t u)
    (second : WhStep (tmodelRules v) tmodelRoles t u') : u' = u :=
  WhStep.deterministic (tmodelShape v) first second

theorem tmodel_step (v : Nat → Nat) {entry : DeclName × RootComputation Tower.Head}
    (mem : entry ∈ tmodelComputations v) {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    (tmodelRules v).computation.step l r :=
  RootComputation.step_unionAll mem h

theorem tmodelComputations_length (v : Nat → Nat) : (tmodelComputations v).length = 18 :=
  rfl

theorem tmodelListed (v : Nat → Nat) (i : Nat) (h : i < 18) :
    (tmodelComputations v)[i]'(by rw [tmodelComputations_length]; exact h) ∈
      tmodelComputations v :=
  List.getElem_mem _

/-! ## The model -/

/-- The tower's level model, for the transport value model's reduction. -/
def tmodelLevels (valuation : Nat → Nat) : LevelModel (tmodelRules valuation) ℕ where
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

/-- The value side of the transport value model. -/
def tmodelC (v : Nat → Nat) : Model Tower.Head ℕ where
  rules := tmodelRules v
  roles := tmodelRoles
  zero := zeroN
  suc := sucN
  imp := impN
  allCarrier := allCarrierOf
  eqCarrier := eqCarrierOf
  num := numN
  prop := propN
  holds := holdsN
  levels := tmodelLevels v

theorem tmodelC_laws (v : Nat → Nat) : (tmodelC v).Laws where
  truth :=
    { shape := tmodelShape v
      zero := tmodelRoles_zero
      suc := tmodelRoles_suc
      imp := tmodelRoles_imp
      all := by
        intro a A carrier
        change (SetProfile.allInstance? a).map carrierOf = some A at carrier
        cases found : SetProfile.allInstance? a with
        | none => rw [found] at carrier; cases carrier
        | some _ => exact tmodelRoles_all found
      eq := by
        intro e A carrier
        change (SetProfile.eqInstance? e).map carrierOf = some A at carrier
        cases found : SetProfile.eqInstance? e with
        | none => rw [found] at carrier; cases carrier
        | some _ => exact tmodelRoles_eqCode found
      impNotEq := (model_laws v).truth.impNotEq }
  num := tmodelRoles_num
  prop := tmodelRoles_prop
  holds := tmodelRoles_holds

/-- On the value side, identity elimination transports its method along its
motive. -/
theorem tmodel_j_step (v : Nat → Nat) {n : Nat} (A x P d y e : Tower.Tm n) :
    WhStep (tmodelC v).rules (tmodelC v).roles (appSpine (.const jName) [A, x, P, d, y, e])
      (coeApp coeN (.app (.app P x) (.refl x)) (.app (.app P y) e) d) :=
  .root (tmodel_step v (tmodelListed v 3 (by decide)) (transportJ_step A x P d y e))

/-- **The transport value model has the transport table**, with the daimon as
the rows' stuck value. -/
theorem tmodel_coeTable (v : Nat → Nat) : CoeTable (tmodelC v) starN coeNames where
  roleCoe := tmodelRoles_coe
  roleU := tmodelRoles_coeU
  roleNum := tmodelRoles_coeNum
  roleProp := tmodelRoles_coeProp
  rolePi := tmodelRoles_coePi
  roleSigma := tmodelRoles_coeSigma
  stepCoe := fun h => tmodel_step v (tmodelListed v 12 (by decide)) h
  stepU := fun h => tmodel_step v (tmodelListed v 13 (by decide)) h
  stepNum := fun h => tmodel_step v (tmodelListed v 14 (by decide)) h
  stepProp := fun h => tmodel_step v (tmodelListed v 15 (by decide)) h
  stepPi := fun h => tmodel_step v (tmodelListed v 16 (by decide)) h
  stepSigma := fun h => tmodel_step v (tmodelListed v 17 (by decide)) h

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
