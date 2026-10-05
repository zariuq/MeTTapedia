import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TransportRules

/-!
# The transport value model of the executable package

The value side of model SN for the executable package: model C's consistency
model with a daimon, on which identity elimination transports its method along
its motive instead of casting it (`tmodelC`).

* The daimon is a fresh constant `⋆` that no rule of the package declares; it is
  rigid.
* The roles are model C's, with five fresh constants that no rule of the
  package declares, like the daimon: `coe` inspects its target for a head
  form, and `coeU`, `coeConst`, `coePi`, `coeSigma` inspect its source.
  `holds` stays rigid.
* The reduction is model C's, with the cast of identity elimination replaced by
  `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`, and the rows of the transport
  table added; the row of `coeU` compares universe levels at the valuation.

The package is root-shaped and deterministic, has the laws of a consistency
model, and has the transport table with the daimon (`tmodel_coeTable`), so every
row of the table holds on the skeleton-free value side over it
(`vmodel_coeRules`).

The model is built from its roles and its computations (`tmodelOf`), and the rows
of the transport read the roles (`tmodelComputationsAt`): a value side with more
inductive types, read by other roles, has the same construction, its transport
rows reading its own type constants. The transport value model is the instance at
model C's roles (`tmodelC`).
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
/-- The transport into a type constant, the codes or an inductive type, once the
target is read. -/
def coeConstN : DeclName := .mkSimple "coe-const"
/-- The transport into a dependent function type, once the target is read. -/
def coePiN : DeclName := .mkSimple "coe-pi"
/-- The transport into a dependent pair type, once the target is read. -/
def coeSigmaN : DeclName := .mkSimple "coe-sigma"

/-- The transport's constants. -/
def coeNames : CoeNames where
  coe := coeN
  coeU := coeUN
  coeConst := coeConstN
  coePi := coePiN
  coeSigma := coeSigmaN

/-- The transport's constants, as a list. -/
abbrev coeNameList : List DeclName := [coeN, coeUN, coeConstN, coePiN, coeSigmaN]

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
  else if name = coeConstN then .computes 3 (headAt 1)
  else if name = coePiN then .computes 4 (headAt 2)
  else if name = coeSigmaN then .computes 4 (headAt 2)
  else modelRoles name

theorem tmodelRoles_eq {name : DeclName} (fresh : name ∉ coeNameList) :
    tmodelRoles name = modelRoles name := by
  simp only [coeNameList, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := fresh
  unfold tmodelRoles
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅]

theorem tmodelRoles_coe : tmodelRoles coeN = .computes 3 (headAt 1) := by
  unfold tmodelRoles
  rw [if_pos rfl]

theorem tmodelRoles_coeU : tmodelRoles coeUN = .computes 3 headAtBoth := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_pos rfl]

theorem tmodelRoles_coeConst : tmodelRoles coeConstN = .computes 3 (headAt 1) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem tmodelRoles_coePi : tmodelRoles coePiN = .computes 4 (headAt 2) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem tmodelRoles_coeSigma : tmodelRoles coeSigmaN = .computes 4 (headAt 2) := by
  unfold tmodelRoles
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

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
    rcases fresh with rfl | rfl | rfl | rfl | rfl
    · rw [tmodelRoles_coe] at role; cases role
    · rw [tmodelRoles_coeU] at role; cases role
    · rw [tmodelRoles_coeConst] at role; cases role
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

/-! ## Roles that extend the transport value model's -/

/-- **Roles extending the transport value model's by new names**: they agree with
`tmodelRoles` at every other name, and no new name is declared by the package or its
codes, is a code instance, a constant of the transport, or the daimon. -/
structure TExtends (roles : Roles Tower.Head) (names : List DeclName) : Prop where
  old : ∀ {c : DeclName}, c ∉ names → roles c = tmodelRoles c
  fresh : ∀ c ∈ names, objectRules.constantType c = none ∧ c ∉ coeNameList ∧ c ≠ starN ∧
    SetProfile.allInstance? c = none ∧ SetProfile.eqInstance? c = none

/-- The transport value model's roles extend themselves by no name. -/
theorem tmodelRoles_extends : TExtends tmodelRoles [] :=
  ⟨fun _ => rfl, fun _ h => nomatch h⟩

namespace TExtends

variable {roles : Roles Tower.Head} {names : List DeclName} (ext : TExtends roles names)
include ext

/-- A name the package or its codes declare, a code instance, a constant of the transport
or the daimon keeps its role. -/
theorem keep {c : DeclName}
    (known : objectRules.constantType c ≠ none ∨ c ∈ coeNameList ∨ c = starN ∨
      SetProfile.allInstance? c ≠ none ∨ SetProfile.eqInstance? c ≠ none) :
    roles c = tmodelRoles c := by
  refine ext.old fun mem => ?_
  obtain ⟨declared, notCoe, notStar, notAll, notEq⟩ := ext.fresh c mem
  rcases known with h | h | h | h | h
  · exact h declared
  · exact notCoe h
  · exact notStar h
  · exact h notAll
  · exact h notEq

theorem num : roles numN = .inductive ctors := (ext.keep (.inl (by decide))).trans tmodelRoles_num
theorem zero : roles zeroN = .constructor 0 := (ext.keep (.inl (by decide))).trans tmodelRoles_zero
theorem suc : roles sucN = .constructor 1 := (ext.keep (.inl (by decide))).trans tmodelRoles_suc
theorem numRec :
    roles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_numRec
theorem add : roles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_add
theorem pow : roles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_pow
theorem j : roles jName = .computes 6 .leaf := (ext.keep (.inl (by decide))).trans tmodelRoles_j
theorem eqAt : roles eqAtName = .computes 1 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_eqAt
theorem sucMove : roles sucMoveName = .computes 2 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_sucMove
theorem keepRole : roles keepName = .computes 4 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_keep
theorem transport : roles transportName = .computes 6 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_transport
theorem compose : roles composeName = .computes 6 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_compose
theorem iter : roles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_iter
theorem returnIter : roles returnIterName = .computes 1 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_returnIter
theorem sucStep : roles sucStepName = .computes 2 .leaf :=
  (ext.keep (.inl (by decide))).trans tmodelRoles_sucStep
theorem coe : roles coeN = .computes 3 (headAt 1) :=
  (ext.keep (.inr (.inl (by decide)))).trans tmodelRoles_coe
theorem coeU : roles coeUN = .computes 3 headAtBoth :=
  (ext.keep (.inr (.inl (by decide)))).trans tmodelRoles_coeU
theorem coeConst : roles coeConstN = .computes 3 (headAt 1) :=
  (ext.keep (.inr (.inl (by decide)))).trans tmodelRoles_coeConst
theorem coePi : roles coePiN = .computes 4 (headAt 2) :=
  (ext.keep (.inr (.inl (by decide)))).trans tmodelRoles_coePi
theorem coeSigma : roles coeSigmaN = .computes 4 (headAt 2) :=
  (ext.keep (.inr (.inl (by decide)))).trans tmodelRoles_coeSigma
theorem imp : roles impN = .constructor 2 := (ext.keep (.inl (by decide))).trans tmodelRoles_imp
theorem prop : roles propN = .rigid := (ext.keep (.inl (by decide))).trans tmodelRoles_prop
theorem holds : roles holdsN = .rigid := (ext.keep (.inl (by decide))).trans tmodelRoles_holds
theorem star : roles starN = .rigid :=
  (ext.keep (.inr (.inr (.inl rfl)))).trans tmodelRoles_star
theorem setRigid : roles setN = .rigid :=
  (ext.keep (.inl (by decide))).trans ((tmodelRoles_eq (by decide)).trans
    ((modelRoles_of (name := setN) (by decide) (by decide) (by decide) (by decide)).trans
      roles_set))

theorem allCode {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.allInstance? name = some type) : roles name = .constructor 1 :=
  (ext.keep (.inr (.inr (.inr (.inl (by rw [found]; exact Option.some_ne_none _)))))).trans
    (tmodelRoles_all found)

theorem eqCode {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.eqInstance? name = some type) : roles name = .constructor 2 :=
  (ext.keep (.inr (.inr (.inr (.inr (by rw [found]; exact Option.some_ne_none _)))))).trans
    (tmodelRoles_eqCode found)

theorem num_stuck : ∀ arity inspect, roles numN ≠ .computes arity inspect :=
  fun _ _ h => nomatch ext.num.symm.trans h

theorem prop_stuck : ∀ arity inspect, roles propN ≠ .computes arity inspect :=
  fun _ _ h => nomatch ext.prop.symm.trans h

end TExtends

/-! ## The reduction -/

/-- The parameters of the transport table at the valuation `v`, with the roles that tell
which constants are type constants and which forms are head forms. -/
def tcoeParamsAt (roles : Roles Tower.Head) (v : Nat → Nat) : CoeParams Tower.Head ℕ where
  roles := roles
  isUniverse := Tower.rules.isUniverse
  level := (TowerModel.levels v).level
  prop := propN
  star := starN

/-- The parameters of the transport table at the valuation `v`. -/
abbrev tcoeParams (v : Nat → Nat) : CoeParams Tower.Head ℕ := tcoeParamsAt tmodelRoles v

/-- Model C's computations, with the transport in place of the cast of identity
elimination, and the rows of the transport table read with the roles `roles`. -/
def tmodelComputationsAt (roles : Roles Tower.Head) (v : Nat → Nat) :
    List (DeclName × RootComputation Tower.Head) :=
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
   (coeN, coeComputation (tcoeParamsAt roles v) coeNames),
   (coeUN, coeUComputation (tcoeParamsAt roles v) coeNames),
   (coeConstN, coeConstComputation (tcoeParamsAt roles v) coeNames),
   (coePiN, coePiComputation (tcoeParamsAt roles v) coeNames),
   (coeSigmaN, coeSigmaComputation (tcoeParamsAt roles v) coeNames)]

/-- Model C's computations, with the transport in place of the cast of identity
elimination, and the rows of the transport table. -/
abbrev tmodelComputations (v : Nat → Nat) : List (DeclName × RootComputation Tower.Head) :=
  tmodelComputationsAt tmodelRoles v

/-- A reduction package over the tower: the executable package's declared types and the
given computations. -/
def tmodelRulesOf (comps : List (DeclName × RootComputation Tower.Head)) : Rules Tower.Head :=
  { Tower.rules with
    constantType := allTypes
    computation := RootComputation.unionAll comps }

/-- The reduction package of the transport value model. -/
abbrev tmodelRules (v : Nat → Nat) : Rules Tower.Head := tmodelRulesOf (tmodelComputations v)

theorem tmodelComputationsAt_names (roles : Roles Tower.Head) (v : Nat → Nat) :
    (tmodelComputationsAt roles v).map Prod.fst =
      [numRecName, addN, powN, jName, eqAtName, sucMoveName, keepName, transportName,
        composeName, iterName, returnIterName, sucStepName, coeN, coeUN, coeConstN,
        coePiN, coeSigmaN] :=
  rfl

theorem tmodelComputationsAt_distinct (roles : Roles Tower.Head) (v : Nat → Nat) :
    ((tmodelComputationsAt roles v).map Prod.fst).Nodup := by
  rw [tmodelComputationsAt_names]
  decide

/-- Each computation is headed by a name the package declares or a constant of the
transport. -/
theorem tmodelComputationsAt_known (roles : Roles Tower.Head) (v : Nat → Nat) :
    ∀ entry ∈ tmodelComputationsAt roles v,
      objectRules.constantType entry.1 ≠ none ∨ entry.1 ∈ coeNameList := by
  intro entry mem
  have name := List.mem_map_of_mem (f := Prod.fst) mem
  rw [tmodelComputationsAt_names] at name
  simp only [List.mem_cons, List.not_mem_nil, or_false] at name
  rcases name with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] <;> decide

theorem tmodelComputationsAt_headed (roles : Roles Tower.Head) (v : Nat → Nat) :
    ∀ entry ∈ tmodelComputationsAt roles v, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [tmodelComputationsAt, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
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
  · exact coePiComputation_headed
  · exact coeSigmaComputation_headed

section Extension

variable {roles : Roles Tower.Head} {names : List DeclName} (ext : TExtends roles names)
  (declared : ConstructorsDeclared roles)
include ext declared

theorem tmodelComputationsAt_spine (v : Nat → Nat) :
    ∀ entry ∈ tmodelComputationsAt roles v, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [tmodelComputationsAt, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ step => IotaStep.spine ext.num ext.numRec declared step
  · exact fun _ _ _ step => RecursionStep.spine ext.num declared ext.add step
  · exact fun _ _ _ step => RecursionStep.spine ext.num declared ext.pow step
  · exact transportJ_spine ext.j
  · exact definitionComputation_spine ext.eqAt
  · exact definitionComputation_spine ext.sucMove
  · exact definitionComputation_spine ext.keepRole
  · exact definitionComputation_spine ext.transport
  · exact definitionComputation_spine ext.compose
  · exact fun _ _ _ step => RecursionStep.spine ext.num declared ext.iter step
  · exact definitionComputation_spine ext.returnIter
  · exact definitionComputation_spine ext.sucStep
  · exact coeComputation_spine ext.coe ext.prop_stuck
  · exact coeUComputation_spine ext.coeU
  · exact coeConstComputation_spine ext.coeConst ext.prop_stuck
  · exact coePiComputation_spine ext.coePi
  · exact coeSigmaComputation_spine ext.coeSigma

omit ext in
theorem tmodelComputationsAt_deterministic (v : Nat → Nat) (num : roles numN = .inductive ctors) :
    ∀ entry ∈ tmodelComputationsAt roles v, Deterministic entry.2 := by
  intro entry mem
  simp only [tmodelComputationsAt, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ step step' => IotaStep.deterministic (T := numN) num declared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic num declared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic num declared step step'
  · exact transportJ_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic num declared step step'
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact coeComputation_deterministic
  · exact coeUComputation_deterministic
  · exact coeConstComputation_deterministic
  · exact coePiComputation_deterministic
  · exact coeSigmaComputation_deterministic

end Extension

/-- **A reduction package over the tower is root-shaped and deterministic** when each of its
computations is spine-shaped, headed by its name and deterministic, and the names are
distinct. -/
theorem tmodelShapeOf {roles : Roles Tower.Head} {comps : List (DeclName × RootComputation Tower.Head)}
    (spine : ∀ entry ∈ comps, SpineShaped roles entry.2)
    (headed : ∀ entry ∈ comps, HeadedBy entry.1 entry.2)
    (deterministic : ∀ entry ∈ comps, Deterministic entry.2)
    (distinct : (comps.map Prod.fst).Nodup) : RootShape (tmodelRulesOf comps) roles where
  spine := fun step => RootComputation.unionAll_spine spine step
  deterministic := by
    intro n t u u' step step'
    exact (RootComputation.unionAll_deterministic distinct headed deterministic step step').symm

/-- **The transport value model's reduction is root-shaped and deterministic**:
its root steps occur at computing spines of exact arity whose inspected values
have the shapes their skeletons require, and at most one applies. -/
theorem tmodelShape (v : Nat → Nat) : RootShape (tmodelRules v) tmodelRoles :=
  tmodelShapeOf (tmodelComputationsAt_spine tmodelRoles_extends tmodelConstructorsDeclared v)
    (tmodelComputationsAt_headed tmodelRoles v)
    (tmodelComputationsAt_deterministic tmodelConstructorsDeclared v tmodelRoles_num)
    (tmodelComputationsAt_distinct tmodelRoles v)

/-- Weak-head reduction of the transport value model is deterministic. -/
theorem tmodel_whStep_deterministic (v : Nat → Nat) {n : Nat} {t u u' : Tower.Tm n}
    (first : WhStep (tmodelRules v) tmodelRoles t u)
    (second : WhStep (tmodelRules v) tmodelRoles t u') : u' = u :=
  WhStep.deterministic (tmodelShape v) first second

/-- A computation listed in a reduction package over the tower computes in it. -/
theorem tmodelOf_step {comps : List (DeclName × RootComputation Tower.Head)}
    {entry : DeclName × RootComputation Tower.Head} (mem : entry ∈ comps) {n : Nat}
    {l r : Tower.Tm n} (h : entry.2.step l r) : (tmodelRulesOf comps).computation.step l r :=
  RootComputation.step_unionAll mem h

theorem tmodel_step (v : Nat → Nat) {entry : DeclName × RootComputation Tower.Head}
    (mem : entry ∈ tmodelComputations v) {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    (tmodelRules v).computation.step l r :=
  tmodelOf_step mem h

theorem tmodelComputationsAt_length (roles : Roles Tower.Head) (v : Nat → Nat) :
    (tmodelComputationsAt roles v).length = 17 :=
  rfl

theorem tmodelListedAt (roles : Roles Tower.Head) (v : Nat → Nat) (i : Nat) (h : i < 17) :
    (tmodelComputationsAt roles v)[i]'(by rw [tmodelComputationsAt_length]; exact h) ∈
      tmodelComputationsAt roles v :=
  List.getElem_mem _

theorem tmodelListed (v : Nat → Nat) (i : Nat) (h : i < 17) :
    (tmodelComputations v)[i]'(by rw [tmodelComputationsAt_length]; exact h) ∈
      tmodelComputations v :=
  tmodelListedAt tmodelRoles v i h

/-! ## The model -/

/-- The tower's level model, for a reduction package over the tower. -/
def tmodelLevelsOf (valuation : Nat → Nat) (comps : List (DeclName × RootComputation Tower.Head)) :
    LevelModel (tmodelRulesOf comps) ℕ where
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

/-- **A value side over the tower**: model C's numbers, codes and decoder, with the given
roles and computations, its levels at the valuation `v`. -/
def tmodelOf (v : Nat → Nat) (roles : Roles Tower.Head)
    (comps : List (DeclName × RootComputation Tower.Head)) : Model Tower.Head ℕ where
  rules := tmodelRulesOf comps
  roles := roles
  zero := zeroN
  suc := sucN
  imp := impN
  allCarrier := allCarrierOf
  eqCarrier := eqCarrierOf
  num := numN
  prop := propN
  holds := holdsN
  levels := tmodelLevelsOf v comps

/-- The value side of the transport value model. -/
def tmodelC (v : Nat → Nat) : Model Tower.Head ℕ := tmodelOf v tmodelRoles (tmodelComputations v)

/-- **A value side over the tower with roles extending the transport value model's, and
root shape, has the laws of a consistency model.** -/
theorem tmodelOf_laws (v : Nat → Nat) {roles : Roles Tower.Head} {names : List DeclName}
    (ext : TExtends roles names) {comps : List (DeclName × RootComputation Tower.Head)}
    (shape : RootShape (tmodelRulesOf comps) roles) : (tmodelOf v roles comps).Laws where
  truth :=
    { shape := shape
      zero := ext.zero
      suc := ext.suc
      imp := ext.imp
      all := by
        intro a A carrier
        change (SetProfile.allInstance? a).map carrierOf = some A at carrier
        cases found : SetProfile.allInstance? a with
        | none => rw [found] at carrier; cases carrier
        | some _ => exact ext.allCode found
      eq := by
        intro e A carrier
        change (SetProfile.eqInstance? e).map carrierOf = some A at carrier
        cases found : SetProfile.eqInstance? e with
        | none => rw [found] at carrier; cases carrier
        | some _ => exact ext.eqCode found
      impNotEq := (model_laws v).truth.impNotEq }
  num := ext.num
  prop := ext.prop
  holds := ext.holds

theorem tmodelC_laws (v : Nat → Nat) : (tmodelC v).Laws :=
  tmodelOf_laws v tmodelRoles_extends (tmodelShape v)

/-- On the value side, identity elimination transports its method along its
motive. -/
theorem tmodel_j_step (v : Nat → Nat) {n : Nat} (A x P d y e : Tower.Tm n) :
    WhStep (tmodelC v).rules (tmodelC v).roles (appSpine (.const jName) [A, x, P, d, y, e])
      (coeApp coeN (.app (.app P x) (.refl x)) (.app (.app P y) e) d) :=
  .root (tmodel_step v (tmodelListed v 3 (by decide)) (transportJ_step A x P d y e))

/-- **A value side over the tower with roles extending the transport value model's, whose
computations contain the transport's rows read with its roles, has the transport table**, with
the daimon as the rows' stuck value. -/
theorem tmodelOf_coeTable (v : Nat → Nat) {roles : Roles Tower.Head} {names : List DeclName}
    (ext : TExtends roles names) {comps : List (DeclName × RootComputation Tower.Head)}
    (listed : ∀ entry ∈ tmodelComputationsAt roles v, entry ∈ comps) :
    CoeTable (tmodelOf v roles comps) starN coeNames where
  roleCoe := ext.coe
  roleU := ext.coeU
  roleConst := ext.coeConst
  rolePi := ext.coePi
  roleSigma := ext.coeSigma
  stepCoe := fun h => tmodelOf_step (listed _ (tmodelListedAt roles v 12 (by decide))) h
  stepU := fun h => tmodelOf_step (listed _ (tmodelListedAt roles v 13 (by decide))) h
  stepConst := fun h => tmodelOf_step (listed _ (tmodelListedAt roles v 14 (by decide))) h
  stepPi := fun h => tmodelOf_step (listed _ (tmodelListedAt roles v 15 (by decide))) h
  stepSigma := fun h => tmodelOf_step (listed _ (tmodelListedAt roles v 16 (by decide))) h

/-- **The transport value model has the transport table**, with the daimon as
the rows' stuck value. -/
theorem tmodel_coeTable (v : Nat → Nat) : CoeTable (tmodelC v) starN coeNames :=
  tmodelOf_coeTable v tmodelRoles_extends fun _ mem => mem

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
