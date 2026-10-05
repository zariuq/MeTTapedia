import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectDatatypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitionsByBound
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitionsBySolution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextualPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle

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
definition by equations (`definition_setModel_of_value`) then gives the set model of `half`
(`objectHalf_model`). `log2` is admitted the way an admission on a set solution admits it: the
statement that some function from numbers to numbers satisfies its equations is true in the
model of the package with `half`, with the witness the set solution, which is also the one
value of its admission by a bound (`log_unique` below); `definition_setModel_of_solution` gives
the set model (`objectLog_model`).

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

**Admitted by a bound** (`objectHalf_admitted`, `objectLog_admitted`). The same packages follow
from the general criterion for a definition whose calls go down a bound
(`definition_setModel_of_bound`), with the bound `n` for both. Each is read as a definition by
the cases zero, one, and two more than a number (`NumberCases`). The checks hold: the patterns
are numbers, no two typed instances have one number (`NumberCases.checks`), and the right sides
are numbers whatever function the defined name denotes (`half_checks`, `log_checks`). The
obligations hold: `half` calls itself at `n` and `log2` at the half of `suc (suc n)`, and both
are members of `suc (suc n)` (`half_obligations`, `log_obligations`). The patterns cover the
numbers (`NumberCases.covers`), so every set model gives `half` and `log2` their set solutions
(`half_unique`, `log_unique`). The altered equation is admitted the same way
(`objectAltered_admitted`). Its one value is the zero function (`altered_unique`), which agrees
with the run of `log2 2` to zero (`altered_runs_two`).

**A bound must go down.** `loop n ⟶ suc (loop n)` and `spin n ⟶ spin n` pass every check
(`loop_checks`, `spin_checks`, `spin_covers`). Their calls are at `n` itself, so no bound goes
down at them (`loop_no_obligations`, `spin_no_obligations`). The first has no set model
(`loop_no_setModel`), so the criterion without its obligations is false
(`obligations_needed_for_model`). The second has a model at every function from numbers to
numbers (`spin_model`), so the uniqueness without them is false too
(`obligations_needed_for_uniqueness`).

**Admitted on evidence, without a bound.** `spin` is admitted on the evidence `λ n. zero`, and
the evidence does not determine its value: two models give `spin` different values
(`spin_value_not_determined`). `loop n ⟶ suc (loop n)` has no evidence: no function from
numbers to numbers satisfies it (`loop_no_evidence`), and a copy of the admission on evidence
without its evidence is false at it (`evidence_needed_for_model`).

**The three faces joined** (`logTriangle`). What runs: a closed expression of numerals, `half`
and `log2` (`LogExpr`) runs by the steps of the package to the numeral of its number
(`LogExpr.runs`); the number is computed by the written equations (`runLog`, whose call at the
half is at a smaller number). Positive example: `log2 8` runs to three. What is typed: the term
of the expression is a number (`LogExpr.toTerm_typed`). What it is as a set: the value of the
term in the set model. The triangle maps an expression to its typed term, a typed term to its
value in the model, and an expression directly to the numeral it runs to, read as a set; it
commutes by proof (`meaning_typing`): the set solution of `log2` at every numeral is the
numeral running reaches (`log2_numeral`), although the one comes from the recursion theorem in
sets and the other from running. The triangle is not exact: `log2 2` and `log2 3` are two
inputs with one value (`logTriangle_loses`). Negative example: with the altered equation the
package runs `log2 2` to zero (`altered_runs_two`) where the typed term means one, so typing,
meaning and the altered run form no triangle (`altered_disagrees`).

What this does not give: that every run stops. At a closed numeral one run reaches a numeral
(`log_runs`); nothing here bounds the other runs. One unfolding of an equation at an open term
is an equality of the judgment (`equation_holds`): the substitution is typed along the
equation's telescope, and a variable of that telescope may stay open. For the third equation
that unfolding is one step (`logStep`). Reaching a normal form at an open term needs
termination, which is not stated. The bound `n` gives the solution in sets.
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
open ZFSetDependentProducts (graph)
open ZFSetWellFoundedRecursion (half halfSet halfSet_mem half_value half_numeral half_mem_earlier
  log2 logSet logSet_mem log2_small log2_large log2_eight before natBefore nat_wf boundBefore
  boundBefore_wf mem_earlier)
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.Computability.ComputationalTrinity

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

/-- An environment of the telescope `n : num` gives `n` a natural number. -/
theorem number_of_sat
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    {η : Env.{u} 1} (sat : Sat (objHeads h) consts (.snoc .nil cnum : CCtx Tower.Head 1) η) :
    η 0 ∈ ZFSet.omega := by
  have member := sat 0
  change η 0 ∈ consts numN at member
  rwa [num_value h agrees] at member

/-- A natural number gives an environment of the telescope `n : num`. -/
theorem sat_number
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    Sat (objHeads h) consts (.snoc .nil cnum : CCtx Tower.Head 1) fun _ => x := fun i =>
  match i with
  | ⟨0, _⟩ => by
      change x ∈ consts numN
      rw [num_value h agrees]
      exact hx

/-- `suc zero` is read as one. -/
theorem one_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    {n : Nat} (η : Env.{u} n) :
    ev (objHeads h) consts (csuc czero : CTm Tower.Head n) η = numeral 1 := by
  show traceApp (consts sucN) (consts zeroN) = _
  rw [zero_value h agrees, suc_value h agrees (numeral_mem_omega 0)]
  exact (numeral_succ 0).symm

/-- `suc (suc n)` is read as two more than the number of `n`. -/
theorem twoMore_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    {η : Env.{u} 1} (hx : η 0 ∈ ZFSet.omega) :
    ev (objHeads h) consts (csuc (csuc (.var 0)) : CTm Tower.Head 1) η =
      insert (insert (η 0) (η 0)) (insert (η 0) (η 0)) := by
  show traceApp (consts sucN) (traceApp (consts sucN) (η 0)) = _
  rw [suc_value h agrees hx, suc_value h agrees (insert_mem_omega hx)]

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
  have hx := number_of_sat h agrees sat
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
  have hx := number_of_sat h base sat
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

/-- The definition of `log2` mentions only `log2` and names that the package with `half`
declares. -/
theorem log_mentions : MentionsDeclared objectHalf logN numFn logEquations :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **The package with `half` and `log2` defined by their written equations has a set
model**, relative to `CofinalInaccessibles`. `log2` is admitted on the evidence of its solution
in sets; no rule about recursion is used. -/
theorem objectLog_model (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectLog.constantType c ≠ none → consts c = logConsts h c) :
    SetModel (objHeads h) consts objectLog :=
  definition_setModel_of_solution (objHeads h) objectHalf (objectHalf_model h) log_new log_mentions
    (by rw [ev_numFn h (agrees_object h fun _ _ => rfl)]; exact logSet_mem)
    (log_valid h (update_agrees_of_new log_new _ _) (Function.update_self _ _ _)) consts agrees

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

/-! ## Running -/

section Running

/-- **`half` run on a number by its three equations.** -/
def runHalf : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => runHalf n + 1

/-- Running `half` halves. -/
theorem runHalf_eq : ∀ n, runHalf n = n / 2
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [runHalf, runHalf_eq n]
      omega

/-- The call of the third equation of `log2` is at a smaller number. -/
theorem runHalf_lt (n : Nat) : runHalf (n + 2) < n + 2 := by
  rw [runHalf_eq]
  omega

/-- **`log2` run on a number by its three equations**: the call is at the half, and it is at a
smaller number, so the run stops. -/
def runLog : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => runLog (runHalf (n + 2)) + 1
termination_by n => n
decreasing_by exact runHalf_lt n

theorem runLog_zero : runLog 0 = 0 := by rw [runLog]

theorem runLog_one : runLog 1 = 0 := by rw [runLog]

theorem runLog_two_more (n : Nat) : runLog (n + 2) = runLog (runHalf (n + 2)) + 1 := by
  rw [runLog]

/-- **A closed expression of the program**: numerals, `half` and `log2`. -/
inductive LogExpr where
  | zero
  | suc (e : LogExpr)
  | half (e : LogExpr)
  | log (e : LogExpr)
  deriving DecidableEq, Repr

/-- The term of an expression. -/
def LogExpr.toTerm : LogExpr → CTm Tower.Head 0
  | .zero => czero
  | .suc e => csuc e.toTerm
  | .half e => chalf e.toTerm
  | .log e => clog e.toTerm

/-- The numeral of a number: the values of the program. -/
def LogExpr.ofNat : Nat → LogExpr
  | 0 => .zero
  | k + 1 => .suc (LogExpr.ofNat k)

/-- **The number an expression runs to.** -/
def LogExpr.eval : LogExpr → Nat
  | .zero => 0
  | .suc e => e.eval + 1
  | .half e => runHalf e.eval
  | .log e => runLog e.eval

/-- Positive example: `log2 8` runs to three. -/
example : (LogExpr.log (.ofNat 8)).eval = 3 := by
  simp [LogExpr.eval, LogExpr.ofNat, runLog_two_more, runHalf, runLog_one]

variable {R' : Rules Tower.Head} {Q : ChurchRules R'}

theorem reduces_suc {t t' : CTm Tower.Head 0} (run : CReduces Q t t') :
    CReduces Q (csuc t) (csuc t') :=
  run.lift (fun x => csuc x) fun _ _ step => .congAppArg step

theorem reduces_half {t t' : CTm Tower.Head 0} (run : CReduces Q t t') :
    CReduces Q (chalf t) (chalf t') :=
  run.lift (fun x => chalf x) fun _ _ step => .congAppArg step

theorem reduces_log {t t' : CTm Tower.Head 0} (run : CReduces Q t t') :
    CReduces Q (clog t) (clog t') :=
  run.lift (fun x => clog x) fun _ _ step => .congAppArg step

/-- **`half` of a numeral runs to its half**, in every package with the steps of `half`. -/
theorem half_runs (steps : StepsWithin (definedChurch objectRules halfN numFn halfEquations) Q) :
    ∀ k : Nat, CReduces Q (chalf (LogExpr.ofNat k).toTerm) (LogExpr.ofNat (runHalf k)).toTerm
  | 0 => .single (.root (steps.step ⟨halfZero, List.mem_cons_self, Fin.elim0, rfl, rfl⟩))
  | 1 => .single (.root (steps.step
      ⟨halfOne, List.mem_cons_of_mem _ List.mem_cons_self, Fin.elim0, rfl, rfl⟩))
  | k + 2 =>
      Relation.ReflTransGen.head
        (.root (steps.step ⟨halfStep,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          fun _ => (LogExpr.ofNat k).toTerm, rfl, rfl⟩))
        (reduces_suc (half_runs steps k))

end Running

/-- **`log2` of a numeral runs to the numeral of `runLog`**, by the written equations of `log2`
and `half`. -/
theorem log_runs (k : Nat) :
    CReduces objectLog (clog (LogExpr.ofNat k).toTerm) (LogExpr.ofNat (runLog k)).toTerm := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
        rw [runLog_zero]
        exact .single (.root ((StepsWithin.sum_right _ _).step
          ⟨logZero, List.mem_cons_self, Fin.elim0, rfl, rfl⟩))
    | 1, _ =>
        rw [runLog_one]
        exact .single (.root ((StepsWithin.sum_right _ _).step
          ⟨logOne, List.mem_cons_of_mem _ List.mem_cons_self, Fin.elim0, rfl, rfl⟩))
    | k + 2, ih =>
        rw [runLog_two_more]
        refine Relation.ReflTransGen.head
          (.root ((StepsWithin.sum_right _ _).step ⟨logStep,
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
            fun _ => (LogExpr.ofNat k).toTerm, rfl, rfl⟩)) ?_
        exact (reduces_suc (reduces_log (half_runs half_steps (k + 2)))).trans
          (reduces_suc (ih _ (runHalf_lt k)))

/-- **Every expression runs to the numeral of its number**, by the steps of the package. -/
theorem LogExpr.runs : ∀ e : LogExpr,
    CReduces objectLog e.toTerm (LogExpr.ofNat e.eval).toTerm
  | .zero => .refl
  | .suc e => reduces_suc e.runs
  | .half e => (reduces_half e.runs).trans (half_runs half_steps e.eval)
  | .log e => (reduces_log e.runs).trans (log_runs e.eval)

/-- **The term of every expression is a number.** -/
theorem LogExpr.toTerm_typed : ∀ e : LogExpr, CTyped objectLog .nil e.toTerm cnum
  | .zero => zero_typed
  | .suc e => suc_typed e.toTerm_typed
  | .half e => chalf_typed e.toTerm_typed
  | .log e => clog_typed e.toTerm_typed

/-! ## The set solution at numerals -/

/-- **The set solution of `log2` at a numeral is the numeral running reaches.** The two are
built apart: one by the recursion theorem for a well-founded relation on sets, the other by
running the written equations. -/
theorem log2_numeral (k : Nat) : log2 (numeral.{u} k) = numeral (runLog k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
        rw [runLog_zero]
        exact log2_small (numeral_mem_omega 0) (by rw [natOf_numeral]; exact Nat.zero_le 1)
    | 1, _ =>
        rw [runLog_one]
        exact log2_small (numeral_mem_omega 1) (by rw [natOf_numeral])
    | k + 2, ih =>
        rw [log2_large (numeral_mem_omega (k + 2))
            (by rw [natOf_numeral]; exact Nat.succ_lt_succ (Nat.succ_pos k)),
          half_numeral, ← runHalf_eq, ih _ (runHalf_lt k), runLog_two_more]
        rfl

section Joined

variable (h : CofinalInaccessibles.{u})

/-- The assignment of the model agrees with the model with `half`. -/
theorem logConsts_agrees :
    ∀ c, objectHalf.constantType c ≠ none → logConsts h c = halfConsts h c :=
  fun c declared => Function.update_of_ne
    (fun same : c = logN => declared (by rw [same]; exact log_new)) _ _

/-- **What is typed means the numeral running reaches**: in the set model, the value of the
term of an expression is the numeral of its number. -/
theorem LogExpr.toTerm_value : ∀ e : LogExpr,
    ev (objHeads h) (logConsts h) e.toTerm Fin.elim0 = numeral e.eval
  | .zero => zero_value h (agrees_object h (logConsts_agrees h))
  | .suc e => by
      show traceApp (logConsts h sucN) (ev (objHeads h) (logConsts h) e.toTerm Fin.elim0) = _
      rw [e.toTerm_value, suc_value h (agrees_object h (logConsts_agrees h)) (numeral_mem_omega _)]
      rfl
  | .half e => by
      show traceApp (logConsts h halfN) (ev (objHeads h) (logConsts h) e.toTerm Fin.elim0) = _
      rw [e.toTerm_value, half_at h (logConsts_agrees h), halfSet_apply (numeral_mem_omega _),
        half_numeral, LogExpr.eval, runHalf_eq]
  | .log e => by
      show traceApp (logConsts h logN) (ev (objHeads h) (logConsts h) e.toTerm Fin.elim0) = _
      rw [e.toTerm_value, show logConsts h logN = logSet from Function.update_self _ _ _,
        logSet_apply (numeral_mem_omega _), log2_numeral]
      rfl

end Joined

/-! ## The three faces joined -/

/-- A closed term of the package that is a number, with its typing. -/
abbrev TypedNumber : Type := { t : CTm Tower.Head 0 // CTyped objectLog .nil t cnum }

/-- **What runs is typed**: the term of an expression, with the proof that it is a number. -/
def typing (e : LogExpr) : TypedNumber := ⟨e.toTerm, e.toTerm_typed⟩

/-- **What is typed means a set**: the value of a typed term in the set model. -/
noncomputable def meaning (h : CofinalInaccessibles.{u}) (t : TypedNumber) : ZFSet.{u} :=
  ev (objHeads h) (logConsts h) t.1 Fin.elim0

/-- **What runs reaches a set**: the numeral an expression runs to, read as a set. Neither the
typed term nor the set solution is used. -/
def direct (e : LogExpr) : ZFSet.{u} := numeral e.eval

/-- **The three ways to a set agree**: the value of the typed term in the set model is the
numeral the expression runs to. -/
theorem meaning_typing (h : CofinalInaccessibles.{u}) (e : LogExpr) :
    meaning h (typing e) = direct e :=
  e.toTerm_value h

/-- **The triangle of the three faces of `log2`**: running, typing and sets, with the map from
running to sets built on its own and the commutation proved. -/
noncomputable def logTriangle (h : CofinalInaccessibles.{u}) : Comparison.{0, 0, u + 1} Closed :=
  triangleOfThree
    (fun e : ULift.{u + 1} LogExpr => (ULift.up (typing e.down) : ULift.{u + 1} TypedNumber))
    (fun t => meaning h t.down) (fun e => direct e.down) fun e => meaning_typing h e.down

theorem eval_log_two : (LogExpr.log (.ofNat 2)).eval = 1 := by
  simp [LogExpr.eval, LogExpr.ofNat, runLog_two_more, runHalf, runLog_one]

theorem eval_log_three : (LogExpr.log (.ofNat 3)).eval = 1 := by
  simp [LogExpr.eval, LogExpr.ofNat, runLog_two_more, runHalf, runLog_one]

/-- **The triangle is not exact**: `log2 2` and `log2 3` are two inputs with one value. -/
theorem logTriangle_loses (h : CofinalInaccessibles.{u}) :
    (logTriangle h).LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := ⟨.log (.ofNat 2)⟩) (right := ⟨.log (.ofNat 3)⟩)
    (fun same => absurd (congrArg ULift.down same) (by decide))
    (show (numeral (LogExpr.log (.ofNat 2)).eval : ZFSet.{u}) =
        numeral (LogExpr.log (.ofNat 3)).eval by
      rw [eval_log_two, eval_log_three])

/-! ## The agreement depends on the equations -/

/-- `log2` run by the altered equation `log2 (suc (suc n)) ⟶ log2 (half (suc (suc n)))`. -/
def runAltered : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => runAltered (runHalf (n + 2))
termination_by n => n
decreasing_by exact runHalf_lt n

/-- The number an expression runs to with the altered equation. -/
def LogExpr.evalAltered : LogExpr → Nat
  | .zero => 0
  | .suc e => e.evalAltered + 1
  | .half e => runHalf e.evalAltered
  | .log e => runAltered e.evalAltered

/-- **The package with the altered equation runs `log2 2` to zero**: the altered step, the
equations of `half`, and the second equation of `log2`. -/
theorem altered_runs_two :
    CReduces (withDefinition objectHalf logN numFn [logZero, logOne, logAltered])
      (clog (LogExpr.ofNat 2).toTerm) czero :=
  Relation.ReflTransGen.head
    (.root ((StepsWithin.sum_right _ _).step ⟨logAltered,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      fun _ => czero, rfl, rfl⟩))
    (Relation.ReflTransGen.tail
      (reduces_log (half_runs
        ((StepsWithin.sum_right objectChurch _).trans (StepsWithin.sum_left objectHalf _)) 2))
      (.root ((StepsWithin.sum_right _ _).step
        ⟨logOne, List.mem_cons_of_mem _ List.mem_cons_self, Fin.elim0, rfl, rfl⟩)))

/-- Negative example: **with the altered equation, running reaches another set, and typing,
meaning and that run form no triangle.** At `log2 2` the typed term means one and the altered
run reaches zero. -/
theorem altered_disagrees (h : CofinalInaccessibles.{u}) :
    ¬ ∀ e : LogExpr, meaning h (typing e) = numeral e.evalAltered := by
  intro agree
  have atTwo := (meaning_typing h (.log (.ofNat 2))).symm.trans (agree (.log (.ofNat 2)))
  have altered : (LogExpr.log (.ofNat 2)).evalAltered = 0 := by
    simp [LogExpr.evalAltered, LogExpr.ofNat, runAltered, runHalf]
  rw [direct, eval_log_two, altered] at atTwo
  exact absurd (numeral_injective atTwo) (by decide)

/-! ## Admitted by a bound

The written equations of `half`, of `log2` and of the altered `log2` are admitted by the general
criterion for a bound that goes down at every call (`definition_setModel_of_bound`), with the
bound `n`: each is a definition on the numbers by the cases zero, one, and two more than a
number (`NumberCases`), whose calls are at `n` or at the half of `suc (suc n)`, both members of
`suc (suc n)`. -/

section Bound

variable {R : Rules Tower.Head} {B : ChurchRules R} {f : DeclName}

/-- **A definition on the numbers by the cases zero, one, and two more than a number**: closed
right sides for zero and one, which call nothing, and for two more than `n` a body with calls
at arguments over `n`, all mentioning only names the package declares, which declares the
numbers. -/
structure NumberCases (B : ChurchRules R) (f : DeclName) where
  numbers : ∀ c ∈ [numN, zeroN, sucN], B.constantType c ≠ none
  zero : CTm Tower.Head 0
  one : CTm Tower.Head 0
  calls : Nat
  call : Fin calls → CTm Tower.Head 1
  body : CTm Tower.Head (calls + 1)
  zero_declared : ∀ c ∈ termConsts zero, B.constantType c ≠ none
  one_declared : ∀ c ∈ termConsts one, B.constantType c ≠ none
  call_declared : ∀ j, ∀ c ∈ termConsts (call j), B.constantType c ≠ none
  body_declared : ∀ c ∈ termConsts body, B.constantType c ≠ none

namespace NumberCases

variable (d : NumberCases B f)

/-- The case zero, `f zero ⟶ zero`, read with no call. -/
def zeroReading : BoundReading B f where
  equation := ⟨0, .nil, .app (.const f) czero, d.zero⟩
  pattern := czero
  calls := 0
  call := Fin.elim0
  body := d.zero
  left_eq := rfl
  right_eq := (CTm.subst_ids d.zero).symm.trans
    (congrArg (CTm.subst · d.zero) (funext fun i => i.elim0))
  pattern_declared := fun c mem => d.numbers c
    ((by decide : ∀ c ∈ termConsts (czero : CTm Tower.Head 0), c ∈ [numN, zeroN, sucN]) c mem)
  call_declared := fun j => j.elim0
  body_declared := d.zero_declared
  telescope_declared := fun i => i.elim0

/-- The case one, `f (suc zero) ⟶ one`, read with no call. -/
def oneReading : BoundReading B f where
  equation := ⟨0, .nil, .app (.const f) (csuc czero), d.one⟩
  pattern := csuc czero
  calls := 0
  call := Fin.elim0
  body := d.one
  left_eq := rfl
  right_eq := (CTm.subst_ids d.one).symm.trans
    (congrArg (CTm.subst · d.one) (funext fun i => i.elim0))
  pattern_declared := fun c mem => d.numbers c
    ((by decide : ∀ c ∈ termConsts (csuc czero : CTm Tower.Head 0), c ∈ [numN, zeroN, sucN])
      c mem)
  call_declared := fun j => j.elim0
  body_declared := d.one_declared
  telescope_declared := fun i => i.elim0

/-- The case two more than `n`, `f (suc (suc n)) ⟶ body`, with the calls put in. -/
def stepReading : BoundReading B f where
  equation := ⟨1, .snoc .nil cnum, .app (.const f) (csuc (csuc (.var 0))),
    d.body.subst (Fin.append (fun j => .app (.const f) (d.call j)) CTm.var)⟩
  pattern := csuc (csuc (.var 0))
  calls := d.calls
  call := d.call
  body := d.body
  left_eq := rfl
  right_eq := rfl
  pattern_declared := fun c mem => d.numbers c
    ((by decide : ∀ c ∈ termConsts (csuc (csuc (.var 0)) : CTm Tower.Head 1),
      c ∈ [numN, zeroN, sucN]) c mem)
  call_declared := d.call_declared
  body_declared := d.body_declared
  telescope_declared := fun i c mem => d.numbers c
    ((by decide : ∀ i, ∀ c ∈ termConsts ((CCtx.snoc .nil cnum : CCtx Tower.Head 1).lookup i),
      c ∈ [numN, zeroN, sucN]) i c mem)

/-- The three read equations. -/
def readings : List (BoundReading B f) := [d.zeroReading, d.oneReading, d.stepReading]

/-- A property of the three read equations. -/
theorem forall_readings {P : BoundReading B f → Prop} (zero : P d.zeroReading)
    (one : P d.oneReading) (step : P d.stepReading) : ∀ q ∈ d.readings, P q :=
  List.forall_mem_cons.mpr ⟨zero, List.forall_mem_cons.mpr
    ⟨one, List.forall_mem_cons.mpr ⟨step, fun _ member => nomatch member⟩⟩⟩

/-- The instance a number is the pattern of: zero, one, or two more than a number. -/
noncomputable def caseOf (x : ZFSet.{u}) : Σ q : BoundReading B f, Env.{u} q.equation.arity :=
  if natOf x = 0 then ⟨d.zeroReading, Fin.elim0⟩
  else if natOf x = 1 then ⟨d.oneReading, Fin.elim0⟩
  else ⟨d.stepReading, fun _ => numeral (natOf x - 2)⟩

variable {h : CofinalInaccessibles.{u}} {base : DeclName → ZFSet.{u}}
  (agrees : ∀ c, objectChurch.constantType c ≠ none → base c = objectSetConsts h c)
include agrees

/-- At a typed instance the pattern is a number, and the instance is the one of that number. -/
theorem pattern_spec : ∀ q ∈ d.readings, ∀ η : Env.{u} q.equation.arity,
    Sat (objHeads h) base q.equation.telescope η →
      ev (objHeads h) base q.pattern η ∈ ZFSet.omega ∧
        d.caseOf (ev (objHeads h) base q.pattern η) = ⟨q, η⟩ := by
  refine d.forall_readings (fun η _ => ?_) (fun η _ => ?_) (fun (η : Env.{u} 1) sat => ?_)
  · have value : ev (objHeads h) base d.zeroReading.pattern η = numeral 0 := zero_value h agrees
    rw [value, caseOf, natOf_numeral, if_pos rfl]
    exact ⟨numeral_mem_omega 0, congrArg (Sigma.mk _) (funext fun i => i.elim0)⟩
  · have value : ev (objHeads h) base d.oneReading.pattern η = numeral 1 := one_value h agrees η
    rw [value, caseOf, natOf_numeral, if_neg one_ne_zero, if_pos rfl]
    exact ⟨numeral_mem_omega 1, congrArg (Sigma.mk _) (funext fun i => i.elim0)⟩
  · have hx := number_of_sat h agrees sat
    obtain ⟨above, size⟩ := two_more hx
    have value : ev (objHeads h) base d.stepReading.pattern η =
        insert (insert (η 0) (η 0)) (insert (η 0) (η 0)) := twoMore_value h agrees hx
    rw [value, caseOf, size, if_neg (by omega), if_neg (by omega)]
    refine ⟨above, congrArg (Sigma.mk _) (funext fun i => ?_)⟩
    match i with
    | ⟨0, _⟩ =>
        show numeral (natOf (η 0) + 2 - 2) = η 0
        rw [Nat.add_sub_cancel, numeral_natOf hx]

/-- **The checks**, given that the right sides land in the numbers: the patterns are numbers,
and two typed instances with one number are one instance. -/
theorem checks
    (right_mem : ∀ q ∈ d.readings, ∀ η : Env.{u} q.equation.arity,
      Sat (objHeads h) base q.equation.telescope η →
        ∀ F ∈ tracePiSet ZFSet.omega (fun _ => ZFSet.omega),
        ev (objHeads h) (Function.update base f F) q.equation.right η ∈ ZFSet.omega) :
    BoundChecks (objHeads h) base ZFSet.omega ZFSet.omega d.readings where
  left_mem q member η sat := (d.pattern_spec agrees q member η sat).1
  right_mem := right_mem
  apart q member q' member' η η' sat sat' same :=
    ((d.pattern_spec agrees q member η sat).2.symm.trans (congrArg d.caseOf same)).trans
      (d.pattern_spec agrees q' member' η' sat').2

/-- **The patterns cover the numbers.** -/
theorem covers : BoundCovers (objHeads h) base ZFSet.omega d.readings := by
  intro x hx
  obtain ⟨k, rfl⟩ : ∃ k, numeral k = x := ⟨natOf x, numeral_natOf hx⟩
  match k with
  | 0 => exact ⟨d.zeroReading, List.mem_cons_self, Fin.elim0, fun i => i.elim0,
      zero_value h agrees⟩
  | 1 => exact ⟨d.oneReading, List.mem_cons_of_mem _ List.mem_cons_self, Fin.elim0,
      fun i => i.elim0, one_value h agrees _⟩
  | k + 2 =>
      refine ⟨d.stepReading,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ => numeral k,
        sat_number h agrees (numeral_mem_omega k), ?_⟩
      show ev (objHeads h) base (csuc (csuc (.var 0)) : CTm Tower.Head 1) (fun _ => numeral k) = _
      rw [twoMore_value h agrees (numeral_mem_omega k), ← numeral_succ, ← numeral_succ]

end NumberCases

/-- The function from numbers to numbers with the value `k` everywhere. -/
noncomputable def constNum (k : Nat) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun _ => numeral k)

theorem constNum_mem (k : Nat) :
    constNum.{u} k ∈ tracePiSet ZFSet.omega (fun _ => ZFSet.omega) :=
  traceLam_graph_mem fun _ _ => numeral_mem_omega k

theorem constNum_apply (k : Nat) {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    traceApp (constNum k) x = numeral k :=
  traceApp_graph_beta _ hx

/-- The constant functions zero and one are different: they differ at zero. -/
theorem constNum_zero_ne_one : constNum.{u} 0 ≠ constNum 1 := fun same => by
  have atZero : traceApp (constNum 0) (numeral.{u} 0) = traceApp (constNum 1) (numeral 0) := by
    rw [same]
  rw [constNum_apply 0 (numeral_mem_omega 0), constNum_apply 1 (numeral_mem_omega 0)] at atZero
  exact absurd (numeral_injective atZero) (by decide)

end Bound

/-! ### `half` -/

/-- **`half` read for admission by a bound**: zero, zero, and `suc (half n)` with its call
at `n`. -/
def halfCases : NumberCases objectChurch halfN where
  numbers := by decide
  zero := czero
  one := czero
  calls := 1
  call := fun _ => .var 0
  body := csuc (.var 0)
  zero_declared := by decide
  one_declared := by decide
  call_declared := by decide
  body_declared := by decide

/-- The read equations are the written equations of `half`. -/
theorem halfCases_equations : halfCases.readings.map BoundReading.equation = halfEquations := rfl

section HalfBound

variable (h : CofinalInaccessibles.{u})

/-- The checks of `half`: its right sides are numbers whatever function `half` denotes. -/
theorem half_checks :
    BoundChecks (objHeads h) (objectSetConsts h) ZFSet.omega ZFSet.omega halfCases.readings :=
  halfCases.checks (fun _ _ => rfl) <| halfCases.forall_readings
    (fun _ _ _ _ => by
      show Function.update (objectSetConsts h) halfN _ zeroN ∈ ZFSet.omega
      rw [Function.update_of_ne (by decide), setConst_zero]
      exact numeral_mem_omega 0)
    (fun _ _ _ _ => by
      show Function.update (objectSetConsts h) halfN _ zeroN ∈ ZFSet.omega
      rw [Function.update_of_ne (by decide), setConst_zero]
      exact numeral_mem_omega 0)
    (fun (η : Env.{u} 1) sat F hF => by
      have hx := number_of_sat h (fun _ _ => rfl) sat
      show traceApp (Function.update (objectSetConsts h) halfN F sucN)
        (traceApp (Function.update (objectSetConsts h) halfN F halfN) (η 0)) ∈ ZFSet.omega
      rw [Function.update_self, Function.update_of_ne (by decide)]
      have value := traceApp_mem ⟨F, hF⟩ ⟨η 0, hx⟩
      rw [suc_value h (fun _ _ => rfl) value]
      exact insert_mem_omega value)

/-- **The obligation of `half`**: its call is at `n`, a member of `suc (suc n)`. -/
theorem half_obligations :
    BoundObligations (objHeads h) (objectSetConsts h) ZFSet.omega natBefore id halfCases.readings :=
  halfCases.forall_readings (fun _ _ j => j.elim0) (fun _ _ j => j.elim0)
    fun (η : Env.{u} 1) sat _ => by
    have hx := number_of_sat h (fun _ _ => rfl) sat
    show η 0 ∈ ZFSet.omega ∧
      η 0 ∈ ev (objHeads h) (objectSetConsts h) (csuc (csuc (.var 0)) : CTm Tower.Head 1) η
    rw [twoMore_value h (fun _ _ => rfl) hx]
    exact ⟨hx, ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert _ _)⟩

/-- **`half` is admitted by the bound `n`**: the general criterion gives the package with `half`
a set model. -/
theorem objectHalf_admitted :
    ∃ value ∈ tracePiSet ZFSet.omega (fun _ => ZFSet.omega),
      ∀ consts : DeclName → ZFSet.{u},
      (∀ c, objectHalf.constantType c ≠ none →
        consts c = Function.update (objectSetConsts h) halfN value c) →
      SetModel (objHeads h) consts objectHalf := by
  have admitted := definition_setModel_of_bound (objHeads h) objectChurch (object_baseModel h)
    half_new (A := numFn) (fun _ agrees => ev_numFn h agrees) nat_wf (fun _ hx => hx)
    (half_checks h) (half_obligations h) (constNum_mem 0)
  rw [halfCases_equations] at admitted
  exact admitted

/-- **Every set model gives `half` its set solution**: the patterns cover the numbers, so the
bound leaves one value. -/
theorem half_unique {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    (model : SetModel (objHeads h) consts objectHalf) : consts halfN = halfSet := by
  have unique := bound_model_unique (objHeads h) half_new (A := numFn)
    (fun _ agrees => ev_numFn h agrees) nat_wf (fun _ hx => hx) (halfCases.covers fun _ _ => rfl)
    (half_obligations h) agrees (update_agrees_of_new half_new _ halfSet)
  rw [halfCases_equations] at unique
  exact (unique model (objectHalf_model h (halfConsts h) fun _ _ => rfl)).trans
    (Function.update_self _ _ _)

end HalfBound

/-! ### `log2` and the altered `log2` -/

/-- **`log2` read for admission by a bound**: zero, zero, and `suc (log2 (half (suc (suc n))))`
with its call at the half. -/
def logCases : NumberCases objectHalf logN where
  numbers := by decide
  zero := czero
  one := czero
  calls := 1
  call := fun _ => chalf (csuc (csuc (.var 0)))
  body := csuc (.var 0)
  zero_declared := by decide
  one_declared := by decide
  call_declared := by decide
  body_declared := by decide

/-- The read equations are the written equations of `log2`. -/
theorem logCases_equations : logCases.readings.map BoundReading.equation = logEquations := rfl

/-- **The altered `log2` read for admission by a bound**: the third right side is the call
`log2 (half (suc (suc n)))` itself. -/
def alteredCases : NumberCases objectHalf logN where
  numbers := by decide
  zero := czero
  one := czero
  calls := 1
  call := fun _ => chalf (csuc (csuc (.var 0)))
  body := .var 0
  zero_declared := by decide
  one_declared := by decide
  call_declared := by decide
  body_declared := by decide

/-- The read equations are the altered equations. -/
theorem alteredCases_equations :
    alteredCases.readings.map BoundReading.equation = [logZero, logOne, logAltered] := rfl

section LogBound

variable (h : CofinalInaccessibles.{u})

/-- The model with `half` reads the numbers as the object package does. -/
theorem halfConsts_object :
    ∀ c, objectChurch.constantType c ≠ none → halfConsts h c = objectSetConsts h c :=
  agrees_object h fun _ _ => rfl

/-- The half of `suc (suc n)` is a number below it. -/
theorem half_call_before {η : Env.{u} 1}
    (sat : Sat (objHeads h) (halfConsts h) (.snoc .nil cnum : CCtx Tower.Head 1) η) :
    before ZFSet.omega (boundBefore natBefore id)
      (ev (objHeads h) (halfConsts h) (chalf (csuc (csuc (.var 0))) : CTm Tower.Head 1) η)
      (ev (objHeads h) (halfConsts h) (csuc (csuc (.var 0)) : CTm Tower.Head 1) η) := by
  have hx := number_of_sat h (halfConsts_object h) sat
  obtain ⟨above, size⟩ := two_more hx
  show before ZFSet.omega natBefore
    (traceApp (halfConsts h halfN) (ev (objHeads h) (halfConsts h)
      (csuc (csuc (.var 0)) : CTm Tower.Head 1) η)) _
  rw [twoMore_value h (halfConsts_object h) hx, half_at h (fun _ _ => rfl), halfSet_apply above]
  exact mem_earlier.mp (half_mem_earlier above (by rw [size]; omega))

/-- The right sides for zero and one are numbers whatever function `log2` denotes. -/
theorem log_base_mem (F : ZFSet.{u}) :
    ev (objHeads h) (Function.update (halfConsts h) logN F) (czero : CTm Tower.Head 0) Fin.elim0 ∈
      ZFSet.omega := by
  show Function.update (halfConsts h) logN F zeroN ∈ ZFSet.omega
  rw [Function.update_of_ne (by decide), zero_value h (halfConsts_object h)]
  exact numeral_mem_omega 0

/-- A function from numbers to numbers applied at the half of `suc (suc n)` is a number. -/
theorem log_call_mem {η : Env.{u} 1}
    (sat : Sat (objHeads h) (halfConsts h) (.snoc .nil cnum : CCtx Tower.Head 1) η) {F : ZFSet.{u}}
    (hF : F ∈ tracePiSet ZFSet.omega (fun _ => ZFSet.omega)) :
    ev (objHeads h) (Function.update (halfConsts h) logN F)
      (clog (chalf (csuc (csuc (.var 0)))) : CTm Tower.Head 1) η ∈ ZFSet.omega := by
  have inside := (half_call_before h sat).1
  have same : ∀ t : CTm Tower.Head 1,
      (∀ c ∈ termConsts t, objectHalf.constantType c ≠ none) →
      ev (objHeads h) (Function.update (halfConsts h) logN F) t η =
        ev (objHeads h) (halfConsts h) t η := fun t declared =>
    ev_congr_consts _ _ t (fun c mem => update_agrees_of_new log_new _ F c (declared c mem)) η
  show traceApp (Function.update (halfConsts h) logN F logN)
    (ev (objHeads h) (Function.update (halfConsts h) logN F)
      (chalf (csuc (csuc (.var 0))) : CTm Tower.Head 1) η) ∈ ZFSet.omega
  rw [Function.update_self, same _ (by decide)]
  exact traceApp_mem ⟨F, hF⟩ ⟨_, inside⟩

/-- The checks of `log2`. -/
theorem log_checks :
    BoundChecks (objHeads h) (halfConsts h) ZFSet.omega ZFSet.omega logCases.readings :=
  logCases.checks (halfConsts_object h) <| logCases.forall_readings
    (fun _ _ F _ => log_base_mem h F) (fun _ _ F _ => log_base_mem h F)
    (fun (η : Env.{u} 1) sat F hF => by
      have value := log_call_mem h sat hF
      show traceApp (Function.update (halfConsts h) logN F sucN)
        (ev (objHeads h) (Function.update (halfConsts h) logN F)
          (clog (chalf (csuc (csuc (.var 0)))) : CTm Tower.Head 1) η) ∈ ZFSet.omega
      rw [Function.update_of_ne (by decide), suc_value h (halfConsts_object h) value]
      exact insert_mem_omega value)

/-- **The obligation of `log2`**: its call is at the half of `suc (suc n)`, a member of it. -/
theorem log_obligations :
    BoundObligations (objHeads h) (halfConsts h) ZFSet.omega natBefore id logCases.readings :=
  logCases.forall_readings (fun _ _ j => j.elim0) (fun _ _ j => j.elim0)
    fun (_ : Env.{u} 1) sat _ => half_call_before h sat

/-- **`log2` is admitted by the bound `n`**, over the package with `half`. -/
theorem objectLog_admitted :
    ∃ value ∈ tracePiSet ZFSet.omega (fun _ => ZFSet.omega),
      ∀ consts : DeclName → ZFSet.{u},
      (∀ c, objectLog.constantType c ≠ none →
        consts c = Function.update (halfConsts h) logN value c) →
      SetModel (objHeads h) consts objectLog := by
  have admitted := definition_setModel_of_bound (objHeads h) objectHalf (objectHalf_model h)
    log_new (A := numFn) (fun _ agrees => ev_numFn h (agrees_object h agrees)) nat_wf
    (fun _ hx => hx) (log_checks h) (log_obligations h) (constNum_mem 0)
  rw [logCases_equations] at admitted
  exact admitted

/-- **Every set model gives `log2` its set solution.** -/
theorem log_unique {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c)
    (model : SetModel (objHeads h) consts objectLog) : consts logN = logSet := by
  have unique := bound_model_unique (objHeads h) log_new (A := numFn)
    (fun _ agrees => ev_numFn h (agrees_object h agrees)) nat_wf (fun _ hx => hx)
    (logCases.covers (halfConsts_object h)) (log_obligations h) agrees
    (update_agrees_of_new log_new _ logSet)
  rw [logCases_equations] at unique
  exact (unique model (objectLog_model_read h)).trans (Function.update_self _ _ _)

/-- The checks of the altered `log2`. -/
theorem altered_checks :
    BoundChecks (objHeads h) (halfConsts h) ZFSet.omega ZFSet.omega alteredCases.readings :=
  alteredCases.checks (halfConsts_object h) <| alteredCases.forall_readings
    (fun _ _ F _ => log_base_mem h F) (fun _ _ F _ => log_base_mem h F)
    fun (_ : Env.{u} 1) sat _ hF => log_call_mem h sat hF

/-- The obligation of the altered `log2`: the same call. -/
theorem altered_obligations :
    BoundObligations (objHeads h) (halfConsts h) ZFSet.omega natBefore id alteredCases.readings :=
  alteredCases.forall_readings (fun _ _ j => j.elim0) (fun _ _ j => j.elim0)
    fun (_ : Env.{u} 1) sat _ => half_call_before h sat

/-- **The altered `log2` is admitted by the bound `n` too**: its equations have a solution,
although it is not the set solution of `log2` (`altered_not_model`). -/
theorem objectAltered_admitted :
    ∃ value ∈ tracePiSet ZFSet.omega (fun _ => ZFSet.omega),
      ∀ consts : DeclName → ZFSet.{u},
      (∀ c, (withDefinition objectHalf logN numFn [logZero, logOne, logAltered]).constantType
        c ≠ none → consts c = Function.update (halfConsts h) logN value c) →
      SetModel (objHeads h) consts
        (withDefinition objectHalf logN numFn [logZero, logOne, logAltered]) := by
  have admitted := definition_setModel_of_bound (objHeads h) objectHalf (objectHalf_model h)
    log_new (A := numFn) (fun _ agrees => ev_numFn h (agrees_object h agrees)) nat_wf
    (fun _ hx => hx) (altered_checks h) (altered_obligations h) (constNum_mem 0)
  rw [alteredCases_equations] at admitted
  exact admitted

/-- The zero function satisfies the altered equations: each right side is zero or the value at
another number. -/
theorem altered_zero_model (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c,
      (withDefinition objectHalf logN numFn [logZero, logOne, logAltered]).constantType c ≠ none →
        consts c = Function.update (halfConsts h) logN (constNum 0) c) :
    SetModel (objHeads h) consts
      (withDefinition objectHalf logN numFn [logZero, logOne, logAltered]) :=
  definition_setModel_of_value objectHalf (objectHalf_model h) log_new (constNum 0)
    (fun _ agreesHalf _ => by
      rw [ev_numFn h (agrees_object h agreesHalf)]
      exact constNum_mem 0)
    (fun consts agreesHalf atLog => by
      have numbers := agrees_object h agreesHalf
      refine List.forall_mem_cons.mpr ⟨fun _ _ => ?_, List.forall_mem_cons.mpr ⟨fun _ _ => ?_,
        List.forall_mem_cons.mpr
          ⟨fun (η : Env.{u} 1) sat => ?_, fun _ member => nomatch member⟩⟩⟩
      · show traceApp (consts logN) (consts zeroN) = consts zeroN
        rw [atLog, zero_value h numbers, constNum_apply 0 (numeral_mem_omega 0)]
      · show traceApp (consts logN) (traceApp (consts sucN) (consts zeroN)) = consts zeroN
        rw [atLog, zero_value h numbers, suc_value h numbers (numeral_mem_omega 0),
          constNum_apply 0 (insert_mem_omega (numeral_mem_omega 0))]
      · have hx := number_of_sat h numbers sat
        obtain ⟨above, -⟩ := two_more hx
        show traceApp (consts logN) (traceApp (consts sucN) (traceApp (consts sucN) (η 0))) =
          traceApp (consts logN)
            (traceApp (consts halfN) (traceApp (consts sucN) (traceApp (consts sucN) (η 0))))
        rw [suc_value h numbers hx, suc_value h numbers (insert_mem_omega hx), half_at h agreesHalf,
          halfSet_apply above, atLog, constNum_apply 0 above, constNum_apply 0 (half_mem above)])
    consts agrees

/-- **The value of the altered `log2` is the zero function** in every set model: it runs
`log2 2` to zero (`altered_runs_two`), and its sets agree. -/
theorem altered_unique {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectHalf.constantType c ≠ none → consts c = halfConsts h c)
    (model : SetModel (objHeads h) consts
      (withDefinition objectHalf logN numFn [logZero, logOne, logAltered])) :
    consts logN = constNum 0 := by
  have unique := bound_model_unique (objHeads h) log_new (A := numFn)
    (fun _ agrees => ev_numFn h (agrees_object h agrees)) nat_wf (fun _ hx => hx)
    (alteredCases.covers (halfConsts_object h)) (altered_obligations h) agrees
    (update_agrees_of_new log_new _ (constNum 0))
  rw [alteredCases_equations] at unique
  exact (unique model (altered_zero_model h _ fun _ _ => rfl)).trans (Function.update_self _ _ _)

end LogBound

/-! ## A bound must go down

Two definitions at a number `n` that pass every check of admission except the obligations,
since their calls are at `n` itself and no bound is below itself. -/

/-- The name of the definition `loop n ⟶ suc (loop n)`. -/
def loopN : DeclName := .str .anonymous "loop"

/-- The name of the definition `spin n ⟶ spin n`. -/
def spinN : DeclName := .str .anonymous "spin"

/-- `loop n ⟶ suc (loop n)`. -/
def loopEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := .app (.const loopN) (.var 0)
  right := csuc (.app (.const loopN) (.var 0))

/-- `spin n ⟶ spin n`. -/
def spinEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := .app (.const spinN) (.var 0)
  right := .app (.const spinN) (.var 0)

theorem loop_new : objectChurch.constantType loopN = none := by decide

theorem spin_new : objectChurch.constantType spinN = none := by decide

/-- `loop` mentions only itself and names that the object package declares. -/
theorem loop_mentions : MentionsDeclared objectChurch loopN numFn [loopEquation] :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- So does `spin`. -/
theorem spin_mentions : MentionsDeclared objectChurch spinN numFn [spinEquation] :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `loop` read with its pattern `n` and its call at `n`. -/
def loopReading : BoundReading objectChurch loopN where
  equation := loopEquation
  pattern := (.var 0 : CTm Tower.Head 1)
  calls := 1
  call := fun _ => (.var 0 : CTm Tower.Head 1)
  body := (csuc (.var 0) : CTm Tower.Head 2)
  left_eq := rfl
  right_eq := rfl
  pattern_declared := by decide
  call_declared := by decide
  body_declared := by decide
  telescope_declared := by decide

/-- `spin` read with its pattern `n` and its call at `n`. -/
def spinReading : BoundReading objectChurch spinN where
  equation := spinEquation
  pattern := (.var 0 : CTm Tower.Head 1)
  calls := 1
  call := fun _ => (.var 0 : CTm Tower.Head 1)
  body := (.var 0 : CTm Tower.Head 2)
  left_eq := rfl
  right_eq := rfl
  pattern_declared := by decide
  call_declared := by decide
  body_declared := by decide
  telescope_declared := by decide

section Controls

variable (h : CofinalInaccessibles.{u})

/-- **`loop` passes the checks**: its pattern and right side are numbers, and its instances are
the numbers. -/
theorem loop_checks :
    BoundChecks (objHeads h) (objectSetConsts h) ZFSet.omega ZFSet.omega [loopReading] where
  left_mem := List.forall_mem_cons.mpr ⟨fun _ sat => number_of_sat h (fun _ _ => rfl) sat,
    fun _ member => nomatch member⟩
  right_mem := List.forall_mem_cons.mpr ⟨fun (η : Env.{u} 1) sat F hF => by
      have value := traceApp_mem ⟨F, hF⟩ ⟨η 0, number_of_sat h (fun _ _ => rfl) sat⟩
      show traceApp (Function.update (objectSetConsts h) loopN F sucN)
        (traceApp (Function.update (objectSetConsts h) loopN F loopN) (η 0)) ∈ ZFSet.omega
      rw [Function.update_self, Function.update_of_ne (by decide),
        suc_value h (fun _ _ => rfl) value]
      exact insert_mem_omega value,
    fun _ member => nomatch member⟩
  apart := List.forall_mem_cons.mpr ⟨List.forall_mem_cons.mpr
    ⟨fun (η η' : Env.{u} 1) _ _ same => congrArg (Sigma.mk _) (funext fun i =>
      match i with
      | ⟨0, _⟩ => (same : η 0 = η' 0)), fun _ member => nomatch member⟩,
    fun _ member => nomatch member⟩

/-- **`spin` passes the checks.** -/
theorem spin_checks :
    BoundChecks (objHeads h) (objectSetConsts h) ZFSet.omega ZFSet.omega [spinReading] where
  left_mem := List.forall_mem_cons.mpr ⟨fun _ sat => number_of_sat h (fun _ _ => rfl) sat,
    fun _ member => nomatch member⟩
  right_mem := List.forall_mem_cons.mpr ⟨fun (η : Env.{u} 1) sat F hF => by
      show traceApp (Function.update (objectSetConsts h) spinN F spinN) (η 0) ∈ ZFSet.omega
      rw [Function.update_self]
      exact traceApp_mem ⟨F, hF⟩ ⟨η 0, number_of_sat h (fun _ _ => rfl) sat⟩,
    fun _ member => nomatch member⟩
  apart := List.forall_mem_cons.mpr ⟨List.forall_mem_cons.mpr
    ⟨fun (η η' : Env.{u} 1) _ _ same => congrArg (Sigma.mk _) (funext fun i =>
      match i with
      | ⟨0, _⟩ => (same : η 0 = η' 0)), fun _ member => nomatch member⟩,
    fun _ member => nomatch member⟩

/-- **The patterns of `spin` cover the numbers.** -/
theorem spin_covers : BoundCovers (objHeads h) (objectSetConsts h) ZFSet.omega [spinReading] :=
  fun x hx =>
    ⟨spinReading, List.mem_cons_self, fun _ => x, sat_number h (fun _ _ => rfl) hx, rfl⟩

/-- **No bound goes down at the call of `loop`**: the call is at the pattern itself. -/
theorem loop_no_obligations {T : ZFSet.{u}} {below : ZFSet.{u} → ZFSet.{u} → Prop}
    (wf : WellFounded (before T below)) {bound : ZFSet.{u} → ZFSet.{u}}
    (into : ∀ x, x ∈ ZFSet.omega → bound x ∈ T) :
    ¬ BoundObligations (objHeads h) (objectSetConsts h) ZFSet.omega below bound [loopReading] :=
  fun obligations => (boundBefore_wf wf into).induction
    (C := fun x => ¬ before ZFSet.omega (boundBefore below bound) x x) _
    (fun _ less self => less _ self self)
    (obligations loopReading List.mem_cons_self (fun _ => numeral 0)
      (sat_number h (fun _ _ => rfl) (numeral_mem_omega 0)) ⟨0, Nat.one_pos⟩)

/-- **No bound goes down at the call of `spin`.** -/
theorem spin_no_obligations {T : ZFSet.{u}} {below : ZFSet.{u} → ZFSet.{u} → Prop}
    (wf : WellFounded (before T below)) {bound : ZFSet.{u} → ZFSet.{u}}
    (into : ∀ x, x ∈ ZFSet.omega → bound x ∈ T) :
    ¬ BoundObligations (objHeads h) (objectSetConsts h) ZFSet.omega below bound [spinReading] :=
  fun obligations => (boundBefore_wf wf into).induction
    (C := fun x => ¬ before ZFSet.omega (boundBefore below bound) x x) _
    (fun _ less self => less _ self self)
    (obligations spinReading List.mem_cons_self (fun _ => numeral 0)
      (sat_number h (fun _ _ => rfl) (numeral_mem_omega 0)) ⟨0, Nat.one_pos⟩)

/-- Negative example: **`loop n ⟶ suc (loop n)` has no set model**: at zero its value would
be a number equal to its own successor. -/
theorem loop_no_setModel (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    ¬ SetModel (objHeads h) consts (withDefinition objectChurch loopN numFn [loopEquation]) := by
  intro model
  have typed := model.constants (withDefinition_defined objectChurch loop_new)
  rw [ev_numFn h agrees] at typed
  have zero := numeral_mem_omega.{u} 0
  have value := traceApp_mem ⟨_, typed⟩ ⟨_, zero⟩
  have equal : traceApp (consts loopN) (numeral 0) =
      traceApp (consts sucN) (traceApp (consts loopN) (numeral 0)) :=
    definition_valid_of_setModel (objHeads h) model loopEquation List.mem_cons_self
      (fun _ => numeral 0) (sat_number h agrees zero)
  rw [suc_value h agrees value] at equal
  have inside := ZFSet.mem_insert (traceApp (consts loopN) (numeral.{u} 0))
    (traceApp (consts loopN) (numeral 0))
  rw [← equal] at inside
  exact ZFSet.mem_irrefl _ inside

/-- **`spin n ⟶ spin n` has a set model at every function from numbers to numbers**, so at
more than one. -/
theorem spin_model (k : Nat) :
    SetModel (objHeads h) (Function.update (objectSetConsts h) spinN (constNum k))
      (withDefinition objectChurch spinN numFn [spinEquation]) :=
  definition_setModel_of_solution (objHeads h) objectChurch (object_baseModel h) spin_new
    spin_mentions (by rw [ev_numFn h fun _ _ => rfl]; exact constNum_mem k)
    (List.forall_mem_singleton.mpr fun _ _ => rfl) _ fun _ _ => rfl

/-- **Without the obligations the checks give no model**: a copy of
`definition_setModel_of_bound` without its obligations is false at `loop`. -/
theorem obligations_needed_for_model :
    ¬ ∀ eqs : List (BoundReading objectChurch loopN),
      BoundChecks (objHeads h) (objectSetConsts h) ZFSet.omega ZFSet.omega eqs →
      ∃ value, ∀ consts : DeclName → ZFSet.{u},
        (∀ c, (withDefinition objectChurch loopN numFn
            (eqs.map BoundReading.equation)).constantType c ≠ none →
          consts c = Function.update (objectSetConsts h) loopN value c) →
        SetModel (objHeads h) consts (withDefinition objectChurch loopN numFn
          (eqs.map BoundReading.equation)) := by
  intro copy
  obtain ⟨value, model⟩ := copy [loopReading] (loop_checks h)
  have atValue := model _ fun _ _ => rfl
  rw [show [loopReading].map BoundReading.equation = [loopEquation] from rfl] at atValue
  exact loop_no_setModel h _ (update_agrees_of_new loop_new _ value) atValue

/-- **Without the obligations the checks and a cover give no uniqueness**: a copy of
`bound_model_unique` without its obligations is false at `spin`. -/
theorem obligations_needed_for_uniqueness :
    ¬ ∀ eqs : List (BoundReading objectChurch spinN),
      BoundChecks (objHeads h) (objectSetConsts h) ZFSet.omega ZFSet.omega eqs →
      BoundCovers (objHeads h) (objectSetConsts h) ZFSet.omega eqs →
      ∀ consts consts' : DeclName → ZFSet.{u},
        (∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) →
        (∀ c, objectChurch.constantType c ≠ none → consts' c = objectSetConsts h c) →
        SetModel (objHeads h) consts
          (withDefinition objectChurch spinN numFn (eqs.map BoundReading.equation)) →
        SetModel (objHeads h) consts'
          (withDefinition objectChurch spinN numFn (eqs.map BoundReading.equation)) →
        consts spinN = consts' spinN := by
  intro copy
  have copySpin := copy [spinReading] (spin_checks h) (spin_covers h) _ _
    (update_agrees_of_new spin_new _ (constNum 0)) (update_agrees_of_new spin_new _ (constNum 1))
  rw [show [spinReading].map BoundReading.equation = [spinEquation] from rfl] at copySpin
  have same := copySpin (spin_model h 0) (spin_model h 1)
  rw [Function.update_self, Function.update_self] at same
  exact constNum_zero_ne_one same

/-! ### Admitted on evidence, without a bound -/

/-- **The evidence for `spin`**: `λ n. zero` satisfies `spin n ⟶ spin n`. -/
theorem spin_evidence :
    SolutionStatement (objHeads h) (objectSetConsts h) spinN numFn [spinEquation] :=
  ⟨constNum 0, by rw [ev_numFn h fun _ _ => rfl]; exact constNum_mem 0,
    List.forall_mem_singleton.mpr fun _ _ => rfl⟩

/-- **The evidence does not determine the value.** `spin n ⟶ spin n` is admitted on the
evidence `λ n. zero`, and the package has two set models, over the object package's
assignment, that give `spin` different values: the constant functions zero and one. -/
theorem spin_value_not_determined :
    SolutionStatement (objHeads h) (objectSetConsts h) spinN numFn [spinEquation] ∧
      ∃ consts consts' : DeclName → ZFSet.{u},
        (∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) ∧
        (∀ c, objectChurch.constantType c ≠ none → consts' c = objectSetConsts h c) ∧
        SetModel (objHeads h) consts (withDefinition objectChurch spinN numFn [spinEquation]) ∧
        SetModel (objHeads h) consts' (withDefinition objectChurch spinN numFn [spinEquation]) ∧
        consts spinN ≠ consts' spinN := by
  refine ⟨spin_evidence h, _, _, update_agrees_of_new spin_new _ (constNum 0),
    update_agrees_of_new spin_new _ (constNum 1), spin_model h 0, spin_model h 1, ?_⟩
  rw [Function.update_self, Function.update_self]
  exact constNum_zero_ne_one

/-- Negative example: **`loop n ⟶ suc (loop n)` has no evidence.** No function from numbers to
numbers satisfies it: with such evidence the admission would give a set model, and there is
none (`loop_no_setModel`). -/
theorem loop_no_evidence :
    ¬ SolutionStatement (objHeads h) (objectSetConsts h) loopN numFn [loopEquation] :=
  fun evidence => by
    obtain ⟨value, -, model⟩ := definition_setModel_of_evidence (objHeads h) objectChurch
      (object_baseModel h) loop_new loop_mentions evidence
    exact loop_no_setModel h _ (update_agrees_of_new loop_new _ value) (model _ fun _ _ => rfl)

/-- **Without the evidence there is no model**: a copy of `definition_setModel_of_evidence`
without its evidence is false at `loop`. -/
theorem evidence_needed_for_model :
    ¬ ∀ eqs : List (DefiningEquation Tower.Head), MentionsDeclared objectChurch loopN numFn eqs →
      ∃ value ∈ ev (objHeads h) (objectSetConsts h) (numFn : CTm Tower.Head 0) Fin.elim0,
        ∀ consts : DeclName → ZFSet.{u},
          (∀ c, (withDefinition objectChurch loopN numFn eqs).constantType c ≠ none →
            consts c = Function.update (objectSetConsts h) loopN value c) →
          SetModel (objHeads h) consts (withDefinition objectChurch loopN numFn eqs) := by
  intro copy
  obtain ⟨value, -, model⟩ := copy [loopEquation] loop_mentions
  exact loop_no_setModel h _ (update_agrees_of_new loop_new _ value) (model _ fun _ _ => rfl)

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Log2
