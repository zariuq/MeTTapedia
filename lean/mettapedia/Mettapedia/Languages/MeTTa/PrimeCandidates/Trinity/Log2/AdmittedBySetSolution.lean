import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectDatatypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.Logic.HOL.Embedding.ZFSetWellFoundedRecursion

/-!
# The base-two logarithm by its written equations, admitted on its solution in sets

`log2` does not recurse on a part of its argument:

    half zero          ⟶ zero              log2 zero          ⟶ zero
    half (suc zero)    ⟶ zero              log2 (suc zero)    ⟶ zero
    half (suc (suc n)) ⟶ suc (half n)      log2 (suc (suc n)) ⟶ suc (log2 (half (suc (suc n))))

The third equation of `log2` calls it at `half (suc (suc n))`, which is not a part of
`suc (suc n)`, and the third equation of `half` calls it two constructors down. A check for
recursion on an immediate part declines both. This module admits both definitions into the
candidate, with exactly these equations as their computation steps, on another kind of
evidence: the equations have a solution in sets.

A definition by equations asks three different things. That both sides of each equation have
one type; the judgment checks this. That some value satisfies the equations; this is a fact
about sets. That the equations, read as rewrite rules, agree with each other and stop; this is
a fact about running. The check for structural recursion answers all three at once. Here the
second is answered from the set side: the recursion theorem for a well-founded relation gives
the functions `half` and `log2` on the natural numbers
(`Mettapedia.Logic.HOL.Embedding.ZFSetWellFoundedRecursion`), and they satisfy the written
equations at every typed instance (`half_valid`, `log_valid`). The general criterion for a
definition by equations (`definition_setModel_of_value`) then gives the set model
(`objectHalf_model`, `objectLog_model`).

**Consequences**, relative to `CofinalInaccessibles`: the package with both definitions is
consistent (`objectLog_consistent`). In its judgment `log2` has the type of functions from
numbers to numbers (`log_typed`), the written equations hold at typed arguments
(`halfStep_rule`, `logStep_rule`), and `log2` of two is one by four uses of them
(`log_two`). In the model `log2` of eight is three (`log_eight_value`).

**The evidence is for these equations and for no others.** Negative example: with the
successor left out of the third equation, `log2 (suc (suc n)) ⟶ log2 (half (suc (suc n)))`,
the same value is not a model: it gives one at two and the altered equation asks for zero
(`altered_not_model`). An equation with no solution at all is in
`ObjectAppendByEquations.lean` (`bad_no_setModel`).

What this does not give: that the equations stop when run. Nothing here lets a checker unfold
`log2` to a normal form at an open term; that needs its own evidence (the measure `n`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Log2

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (traceApp traceLam tracePiSet traceApp_graph_beta traceApp_mem)
open ZFSetWellFoundedRecursion (half halfSet halfSet_mem half_value log2 logSet logSet_mem
  log2_small log2_large log2_eight)

universe u

/-! ## The two definitions -/

/-- The name of the halving function. -/
def halfN : DeclName := .str .anonymous "half"

/-- The name of the base-two logarithm. -/
def logN : DeclName := .str .anonymous "log2"

section Terms

variable {n : Nat}

/-- The type of functions from numbers to numbers. -/
abbrev numFn : CTm Tower.Head n := .pi cnum cnum

/-- `half` applied to a term. -/
abbrev chalf (x : CTm Tower.Head n) : CTm Tower.Head n := .app (.const halfN) x

/-- `log2` applied to a term. -/
abbrev clog (x : CTm Tower.Head n) : CTm Tower.Head n := .app (.const logN) x

end Terms

/-- `half zero ⟶ zero`. -/
def halfZero : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := chalf czero
  right := czero

/-- `half (suc zero) ⟶ zero`. -/
def halfOne : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := chalf (csuc czero)
  right := czero

/-- `half (suc (suc n)) ⟶ suc (half n)`. -/
def halfStep : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := chalf (csuc (csuc (.var 0)))
  right := csuc (chalf (.var 0))

/-- The written equations of `half`. -/
def halfEquations : List (DefiningEquation Tower.Head) := [halfZero, halfOne, halfStep]

/-- **The object package with `half` defined by its written equations.** -/
abbrev objectHalf := withDefinition objectChurch halfN numFn halfEquations

/-- `log2 zero ⟶ zero`. -/
def logZero : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := clog czero
  right := czero

/-- `log2 (suc zero) ⟶ zero`. -/
def logOne : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := clog (csuc czero)
  right := czero

/-- `log2 (suc (suc n)) ⟶ suc (log2 (half (suc (suc n))))`: the call is at the half, which is
not a part of the argument. -/
def logStep : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := clog (csuc (csuc (.var 0)))
  right := csuc (clog (chalf (csuc (csuc (.var 0)))))

/-- The written equations of `log2`. -/
def logEquations : List (DefiningEquation Tower.Head) := [logZero, logOne, logStep]

/-- **The package with `half` and `log2` defined by their written equations.** -/
abbrev objectLog := withDefinition objectHalf logN numFn logEquations

/-- The name of `half` is new to the object package. -/
theorem half_new : objectChurch.constantType halfN = none := by decide

/-- The name of `log2` is new to the package with `half`. -/
theorem log_new : objectHalf.constantType logN = none := by decide

/-! ## The values of the object package that the equations mention -/

section Values

variable (h : CofinalInaccessibles.{u}) {consts : DeclName → ZFSet.{u}}

/-- An assignment that agrees with the object package's on the names it declares reads the
numbers as the set of natural numbers. -/
theorem num_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    consts numN = ZFSet.omega := by
  rw [agrees numN (objectChurch_constantType_ne_none (by decide))]
  exact setConst_num h

/-- It reads `zero` as the numeral zero. -/
theorem zero_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    consts zeroN = numeral 0 := by
  rw [agrees zeroN (objectChurch_constantType_ne_none (by decide))]
  exact setConst_zero h

/-- It reads `suc` as the successor of natural numbers. -/
theorem suc_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : traceApp (consts sucN) x = insert x x := by
  rw [agrees sucN (objectChurch_constantType_ne_none (by decide))]
  exact suc_apply h hx

end Values

/-! ## The set solutions at the shapes of the equations -/

section Solutions

/-- The successor of the successor of a natural number is a natural number above one. -/
theorem two_more {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    insert (insert x x) (insert x x) ∈ ZFSet.omega ∧
      natOf (insert (insert x x) (insert x x)) = natOf x + 2 := by
  have once : insert x x ∈ ZFSet.omega := insert_mem_omega hx
  exact ⟨insert_mem_omega once, by rw [natOf_insert once, natOf_insert hx]⟩

/-- The traced graph of `half` applied to a natural number is `half` of it. -/
theorem halfSet_apply {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : traceApp halfSet x = half x :=
  traceApp_graph_beta half hx

/-- The traced graph of `log2` applied to a natural number is `log2` of it. -/
theorem logSet_apply {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : traceApp logSet x = log2 x :=
  traceApp_graph_beta log2 hx

/-- `half` of a natural number is a natural number. -/
theorem half_mem {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : half x ∈ ZFSet.omega := by
  rw [half_value hx]
  exact numeral_mem_omega _

/-- `log2` of a natural number is a natural number. -/
theorem log_mem {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : log2 x ∈ ZFSet.omega := by
  rw [← logSet_apply hx]
  exact traceApp_mem ⟨logSet, logSet_mem⟩ ⟨x, hx⟩

/-- `half` at zero. -/
theorem half_zero : half (numeral.{u} 0) = numeral 0 := by
  rw [half_value (numeral_mem_omega 0), natOf_numeral]

/-- `half` at one. -/
theorem half_one : half (insert (numeral.{u} 0) (numeral 0)) = numeral 0 := by
  rw [← numeral_succ 0, half_value (numeral_mem_omega 1), natOf_numeral]

/-- `half` two above a natural number is the successor of `half` at the number. -/
theorem half_two_more {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    half (insert (insert x x) (insert x x)) = insert (half x) (half x) := by
  obtain ⟨member, size⟩ := two_more hx
  rw [half_value member, size, half_value hx, Nat.add_div_right _ (Nat.succ_pos 1)]
  exact numeral_succ _

/-- `log2` at zero. -/
theorem log_zero : log2 (numeral.{u} 0) = numeral 0 :=
  log2_small (numeral_mem_omega 0) (by rw [natOf_numeral]; exact Nat.zero_le 1)

/-- `log2` at one. -/
theorem log_one : log2 (insert (numeral.{u} 0) (numeral 0)) = numeral 0 := by
  rw [← numeral_succ 0]
  exact log2_small (numeral_mem_omega 1) (by rw [natOf_numeral])

/-- `log2` two above a natural number is the successor of `log2` at the half. -/
theorem log_two_more {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    log2 (insert (insert x x) (insert x x)) =
      insert (log2 (half (insert (insert x x) (insert x x))))
        (log2 (half (insert (insert x x) (insert x x)))) := by
  obtain ⟨member, size⟩ := two_more hx
  exact log2_large member (by rw [size]; exact Nat.succ_lt_succ (Nat.succ_pos _))

end Solutions

/-! ## The set model of `half` -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The set of the type of functions from numbers to numbers. -/
theorem ev_numFn {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    ev (objHeads h) consts (numFn : CTm Tower.Head 0) Fin.elim0 =
      tracePiSet ZFSet.omega (fun _ => ZFSet.omega) := by
  show tracePiSet (consts numN) (fun _ => consts numN) = _
  rw [num_value h agrees]

/-- The third equation of `half` between sets, at every number. -/
theorem halfStep_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    (atHalf : consts halfN = halfSet) (η : Env.{u} 1)
    (sat : Sat (objHeads h) consts (.snoc .nil cnum : CCtx Tower.Head 1) η) :
    ev (objHeads h) consts (chalf (csuc (csuc (.var 0))) : CTm Tower.Head 1) η =
      ev (objHeads h) consts (csuc (chalf (.var 0)) : CTm Tower.Head 1) η := by
  have hx : η 0 ∈ ZFSet.omega := by
    have member := sat 0
    change η 0 ∈ consts numN at member
    rwa [num_value h agrees] at member
  obtain ⟨above, -⟩ := two_more hx
  show traceApp (consts halfN) (traceApp (consts sucN) (traceApp (consts sucN) (η 0))) =
    traceApp (consts sucN) (traceApp (consts halfN) (η 0))
  rw [atHalf, suc_value h agrees hx, suc_value h agrees (insert_mem_omega hx),
    halfSet_apply above, halfSet_apply hx, suc_value h agrees (half_mem hx)]
  exact half_two_more hx

/-- **The set solution of `half` satisfies its written equations** at every typed instance. -/
theorem half_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    (atHalf : consts halfN = halfSet) :
    ∀ e ∈ halfEquations, ∀ η : Env.{u} e.arity, Sat (objHeads h) consts e.telescope η →
      ev (objHeads h) consts e.left η = ev (objHeads h) consts e.right η := by
  intro e member η sat
  have cases : e = halfZero ∨ e = halfOne ∨ e = halfStep := by
    simpa [halfEquations] using member
  rcases cases with rfl | rfl | rfl
  · show traceApp (consts halfN) (consts zeroN) = consts zeroN
    rw [atHalf, zero_value h agrees, halfSet_apply (numeral_mem_omega 0)]
    exact half_zero
  · show traceApp (consts halfN) (traceApp (consts sucN) (consts zeroN)) = consts zeroN
    rw [atHalf, zero_value h agrees, suc_value h agrees (numeral_mem_omega 0),
      halfSet_apply (insert_mem_omega (numeral_mem_omega 0))]
    exact half_one
  · exact halfStep_valid h agrees atHalf η sat

/-- The assignment of the model with `half`: the object package's, and `half` as its set
solution. -/
noncomputable def halfConsts : DeclName → ZFSet.{u} :=
  Function.update (objectSetConsts h) halfN halfSet

/-- **The package with `half` defined by its written equations has a set model**, at every
assignment that agrees with the object package's and gives `half` its set solution, relative
to `CofinalInaccessibles`. -/
theorem objectHalf_model (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c) :
    SetModel (objHeads h) consts objectHalf :=
  definition_setModel_of_value objectChurch (object_baseModel h) half_new halfSet
    (fun _ agreesBase _ => by
      rw [ev_numFn h agreesBase]
      exact halfSet_mem)
    (fun _ agreesBase atHalf => half_valid h agreesBase atHalf) consts agrees

/-! ## The set model of `log2` -/

/-- An assignment that agrees with the model with `half` on the names it declares agrees with
the object package's on the names that one declares. -/
theorem agrees_object {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c) :
    ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c := by
  intro c declared
  have other : c ≠ halfN := fun same => declared (same ▸ half_new)
  have inSum : objectHalf.constantType c ≠ none := by
    cases found : objectChurch.constantType c with
    | none => exact absurd found declared
    | some type =>
      have known : objectHalf.constantType c = some type := sumDecls_left found
      rw [known]
      exact Option.some_ne_none type
  rw [agrees c inSum]
  exact Function.update_of_ne other _ _

/-- Such an assignment gives `half` its set solution. -/
theorem half_at {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c) :
    consts halfN = halfSet := by
  have declared : objectHalf.constantType halfN ≠ none := by
    rw [withDefinition_defined objectChurch half_new]
    exact Option.some_ne_none _
  rw [agrees halfN declared]
  exact Function.update_self _ _ _

/-- The third equation of `log2` between sets, at every number: the call at the half. -/
theorem logStep_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c)
    (atLog : consts logN = logSet) (η : Env.{u} 1)
    (sat : Sat (objHeads h) consts (.snoc .nil cnum : CCtx Tower.Head 1) η) :
    ev (objHeads h) consts (clog (csuc (csuc (.var 0))) : CTm Tower.Head 1) η =
      ev (objHeads h) consts (csuc (clog (chalf (csuc (csuc (.var 0))))) : CTm Tower.Head 1) η := by
  have base := agrees_object h agrees
  have atHalf := half_at h agrees
  have hx : η 0 ∈ ZFSet.omega := by
    have member := sat 0
    change η 0 ∈ consts numN at member
    rwa [num_value h base] at member
  obtain ⟨above, -⟩ := two_more hx
  show traceApp (consts logN) (traceApp (consts sucN) (traceApp (consts sucN) (η 0))) =
    traceApp (consts sucN) (traceApp (consts logN)
      (traceApp (consts halfN) (traceApp (consts sucN) (traceApp (consts sucN) (η 0)))))
  rw [atLog, atHalf, suc_value h base hx, suc_value h base (insert_mem_omega hx),
    logSet_apply above, halfSet_apply above, logSet_apply (half_mem above),
    suc_value h base (log_mem (half_mem above))]
  exact log_two_more hx

/-- **The set solution of `log2` satisfies its written equations** at every typed instance. -/
theorem log_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c)
    (atLog : consts logN = logSet) :
    ∀ e ∈ logEquations, ∀ η : Env.{u} e.arity, Sat (objHeads h) consts e.telescope η →
      ev (objHeads h) consts e.left η = ev (objHeads h) consts e.right η := by
  have base := agrees_object h agrees
  intro e member η sat
  have cases : e = logZero ∨ e = logOne ∨ e = logStep := by
    simpa [logEquations] using member
  rcases cases with rfl | rfl | rfl
  · show traceApp (consts logN) (consts zeroN) = consts zeroN
    rw [atLog, zero_value h base, logSet_apply (numeral_mem_omega 0)]
    exact log_zero
  · show traceApp (consts logN) (traceApp (consts sucN) (consts zeroN)) = consts zeroN
    rw [atLog, zero_value h base, suc_value h base (numeral_mem_omega 0),
      logSet_apply (insert_mem_omega (numeral_mem_omega 0))]
    exact log_one
  · exact logStep_valid h agrees atLog η sat

/-- The assignment of the model: `half` and `log2` as their set solutions. -/
noncomputable def logConsts : DeclName → ZFSet.{u} :=
  Function.update (halfConsts h) logN logSet

/-- **The package with `half` and `log2` defined by their written equations has a set
model**, relative to `CofinalInaccessibles`. The evidence for `log2` is its solution in sets;
no rule about recursion is used. -/
theorem objectLog_model (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectLog.constantType c ≠ none → consts c = logConsts h c) :
    SetModel (objHeads h) consts objectLog :=
  definition_setModel_of_value objectHalf (objectHalf_model h) log_new logSet
    (fun _ agreesHalf _ => by
      rw [ev_numFn h (agrees_object h agreesHalf)]
      exact logSet_mem)
    (fun _ agreesHalf atLog => log_valid h agreesHalf atLog) consts agrees

/-- The model at the assignment itself. -/
theorem objectLog_model_read : SetModel (objHeads h) (logConsts h) objectLog :=
  objectLog_model h (logConsts h) fun _ _ => rfl

/-- **Soundness**: every derivable statement of the package holds in the model. -/
theorem objectLog_sound {s : CStatement Tower.Head} (derivation : CDerivable objectLog s) :
    Holds (objHeads h) (logConsts h) s :=
  CDerivable.sound (objectLog_model_read h) derivation

include h in
/-- **Consistency**, relative to `CofinalInaccessibles`: no closed term of the package with
`half` and `log2` has the type `Π (X : U₀). X`. -/
theorem objectLog_consistent (t : CTm Tower.Head 0) : ¬ CTyped objectLog .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectLog_model_read h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (logConsts h)) t

/-- Positive example: **in the model `log2` of eight is three.** -/
theorem log_eight_value : traceApp (logConsts h logN) (numeral 8) = numeral.{u} 3 := by
  have atLog : logConsts h logN = logSet := Function.update_self _ _ _
  rw [atLog, logSet_apply (numeral_mem_omega 8)]
  exact log2_eight

end Model

/-! ## The written equations in the judgment -/

section Rules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the object package is one of the package with `half` and `log2`. -/
theorem ofObjectLog {s : CStatement Tower.Head} (derivation : CDerivable objectChurch s) :
    CDerivable objectLog s :=
  CDerivable.sum_left _ (CDerivable.sum_left _ derivation)

/-- The type of functions from numbers to numbers is a type of the lowest universe. -/
theorem numFn_formed : CTyped objectChurch Γ numFn cU0 := cpiT cnum_typed cnum_typed

/-- `half` is declared at its type in the package with `log2`. -/
theorem half_declared : objectLog.constantType halfN = some numFn :=
  (ChurchRulesSub.sum_left objectHalf _).constantType
    (withDefinition_defined objectChurch half_new)

/-- **`half` has its declared type.** -/
theorem half_typed : CTyped objectLog Γ (.const halfN) numFn :=
  definition_typed half_declared (ofObjectLog numFn_formed) (LevelTower.IsUniverse.sort _)

/-- **`log2` has its declared type**: a function from numbers to numbers. -/
theorem log_typed : CTyped objectLog Γ (.const logN) numFn :=
  definition_typed (withDefinition_defined objectHalf log_new) (ofObjectLog numFn_formed)
    (LevelTower.IsUniverse.sort _)

theorem zero_typed : CTyped objectLog Γ czero cnum := ofObjectLog czero_typed

theorem sucConst_typed : CTyped objectLog Γ (.const sucN) numFn := ofObjectLog csucConst_typed

theorem suc_typed {x : CTm Tower.Head n} (hx : CTyped objectLog Γ x cnum) :
    CTyped objectLog Γ (csuc x) cnum :=
  .appElim (B := cnum) sucConst_typed hx

theorem chalf_typed {x : CTm Tower.Head n} (hx : CTyped objectLog Γ x cnum) :
    CTyped objectLog Γ (chalf x) cnum :=
  .appElim (B := cnum) half_typed hx

theorem clog_typed {x : CTm Tower.Head n} (hx : CTyped objectLog Γ x cnum) :
    CTyped objectLog Γ (clog x) cnum :=
  .appElim (B := cnum) log_typed hx

/-- The steps of `half` are steps of the package with `log2`. -/
theorem half_steps :
    StepsWithin (definedChurch objectRules halfN numFn halfEquations) objectLog :=
  (StepsWithin.sum_right objectChurch _).trans (StepsWithin.sum_left objectHalf _)

/-- `half zero` is zero, in the judgment. -/
theorem half_zero_rule : CEqual objectLog Γ (chalf czero) czero cnum :=
  equation_holds _ half_steps (e := halfZero) List.mem_cons_self (fun i => i.elim0)
    (fun i => i.elim0) (chalf_typed zero_typed) zero_typed

/-- **The third equation of `half` in the judgment.** -/
theorem halfStep_rule {x : CTm Tower.Head n} (hx : CTyped objectLog Γ x cnum) :
    CEqual objectLog Γ (chalf (csuc (csuc x))) (csuc (chalf x)) cnum :=
  have typed : CSubstMor objectLog (CCtx.snoc .nil cnum) Γ (fun _ : Fin 1 => x) :=
    fun j => match j with
      | ⟨0, _⟩ => hx
  equation_holds _ half_steps (e := halfStep)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (fun _ => x) typed
    (chalf_typed (suc_typed (suc_typed hx))) (suc_typed (chalf_typed hx))

/-- `log2 (suc zero)` is zero, in the judgment. -/
theorem log_one_rule : CEqual objectLog Γ (clog (csuc czero)) czero cnum :=
  equation_holds _ (StepsWithin.sum_right _ _) (e := logOne)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => i.elim0) (fun i => i.elim0)
    (clog_typed (suc_typed zero_typed)) zero_typed

/-- **The third equation of `log2` in the judgment**: the written equation, with its call at
the half, holds at every typed argument. -/
theorem logStep_rule {x : CTm Tower.Head n} (hx : CTyped objectLog Γ x cnum) :
    CEqual objectLog Γ (clog (csuc (csuc x))) (csuc (clog (chalf (csuc (csuc x))))) cnum :=
  have typed : CSubstMor objectLog (CCtx.snoc .nil cnum) Γ (fun _ : Fin 1 => x) :=
    fun j => match j with
      | ⟨0, _⟩ => hx
  equation_holds _ (StepsWithin.sum_right _ _) (e := logStep)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (fun _ => x) typed
    (clog_typed (suc_typed (suc_typed hx)))
    (suc_typed (clog_typed (chalf_typed (suc_typed (suc_typed hx)))))

/-- Positive example: **`log2` of two is one**, by four uses of the written equations: the
third of `log2`, the third and the first of `half`, and the second of `log2`. -/
theorem log_two :
    CEqual objectLog .nil (clog (csuc (csuc czero))) (csuc czero) cnum := by
  have zero : CTyped objectLog .nil czero cnum := zero_typed
  have halfTwo : CEqual objectLog .nil (chalf (csuc (csuc czero))) (csuc czero) cnum :=
    .trans (halfStep_rule zero) (.appCong (B := cnum) (.refl sucConst_typed) half_zero_rule)
  have inner : CEqual objectLog .nil (clog (chalf (csuc (csuc czero)))) czero cnum :=
    .trans (.appCong (B := cnum) (.refl log_typed) halfTwo) log_one_rule
  exact .trans (logStep_rule zero) (.appCong (B := cnum) (.refl sucConst_typed) inner)

/-- In the set model the equation holds. -/
theorem log_two_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (logConsts h)
      (.equality .nil (clog (csuc (csuc czero))) (csuc czero) cnum) :=
  objectLog_sound h log_two

end Rules

/-! ## The evidence is for these equations -/

/-- `log2 (suc (suc n)) ⟶ log2 (half (suc (suc n)))`: the third equation with its successor
left out. -/
def logAltered : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := clog (csuc (csuc (.var 0)))
  right := clog (chalf (csuc (csuc (.var 0))))

/-- Negative example: **the set solution of `log2` is no model of the altered equation.** At
two the solution gives the successor of its value at one, and the altered equation asks for
the value at one itself. -/
theorem altered_not_model (h : CofinalInaccessibles.{u}) (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c)
    (atLog : consts logN = logSet) :
    ¬ SetModel (objHeads h) consts
        (withDefinition objectHalf logN numFn [logZero, logOne, logAltered]) := by
  intro model
  have base := agrees_object h agrees
  have atHalf := half_at h agrees
  have member : logAltered ∈ [logZero, logOne, logAltered] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have step : (withDefinition objectHalf logN numFn
      [logZero, logOne, logAltered]).computation.step
      (clog (csuc (csuc czero)) : CTm Tower.Head 0) (clog (chalf (csuc (csuc czero)))) :=
    .inr ⟨logAltered, member, fun _ => czero, rfl, rfl⟩
  have required : (withDefinition objectHalf logN numFn
      [logZero, logOne, logAltered]).computation.requires
      (clog (csuc (csuc czero)) : CTm Tower.Head 0) (clog (chalf (csuc (csuc czero))))
      (telescopePremises (.snoc .nil cnum : CCtx Tower.Head 1) fun _ => czero) :=
    .inr ⟨⟨logAltered, member, fun _ => czero, rfl, rfl⟩,
      ⟨logAltered, member, fun _ => czero, rfl, rfl, rfl⟩⟩
  have zeroMember : consts zeroN ∈ consts numN := by
    rw [zero_value h base, num_value h base]
    exact numeral_mem_omega 0
  have equal := model.steps (Γ := .nil) step required
    (fun premise among => by
      obtain ⟨i, rfl⟩ := mem_telescopePremises.mp among
      match i with
      | ⟨0, _⟩ =>
        intro ρ _
        exact zeroMember)
    Fin.elim0 (sat_nil _ _ _)
  have two : insert (insert (numeral.{u} 0) (numeral 0)) (insert (numeral 0) (numeral 0)) ∈
      ZFSet.omega := (two_more (numeral_mem_omega 0)).1
  have same : traceApp (consts logN)
        (traceApp (consts sucN) (traceApp (consts sucN) (consts zeroN))) =
      traceApp (consts logN)
        (traceApp (consts halfN)
          (traceApp (consts sucN) (traceApp (consts sucN) (consts zeroN)))) := equal
  rw [atLog, atHalf, zero_value h base, suc_value h base (numeral_mem_omega 0),
    suc_value h base (insert_mem_omega (numeral_mem_omega 0)), logSet_apply two,
    halfSet_apply two, logSet_apply (half_mem two), log_two_more (numeral_mem_omega 0)] at same
  have inside := ZFSet.mem_insert
    (log2 (half (insert (insert (numeral.{u} 0) (numeral 0)) (insert (numeral 0) (numeral 0)))))
    (log2 (half (insert (insert (numeral.{u} 0) (numeral 0)) (insert (numeral 0) (numeral 0)))))
  rw [same] at inside
  exact ZFSet.mem_irrefl _ inside

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Log2
