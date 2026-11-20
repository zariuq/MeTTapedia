import Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts
import Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationCache

/-!
# Scoped factor cells in GSLT readouts

A reference expression reads a factor through its slot and mixed-radix row
within that factor's scope. Compiling the same elimination plan into a
polynomial term or retaining its intermediate tables yields the same mass.
The reference expression describes the arithmetic, including the order of
primitive requests. A retained evaluator can share that computation.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open PolynomialReadoutCalculus PolynomialReadoutEvaluation Cost.LiteralSignatureCommitment
open ExecutableFactorTable

variable {n m : Nat} {domains : Fin n → Nat}

/-- The two coordinates select a factor slot and a row in its ordered scope. -/
def entry (slot row : Nat) : Pattern :=
  .apply "ScopedFactorEntry" [encodeNat slot, encodeNat row]

theorem entry_equal_iff (slot row otherSlot otherRow : Nat) :
    entry slot row = entry otherSlot otherRow ↔ slot = otherSlot ∧ row = otherRow := by
  constructor
  · intro same
    have encoded : encodeNat slot = encodeNat otherSlot ∧ encodeNat row = encodeNat otherRow := by
      simpa [entry] using same
    exact ⟨encodeNat_injective encoded.1, encodeNat_injective encoded.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The provider distinguishes an absent cell from a present zero. -/
def lookup? (tables : Fin m → Table domains) : Pattern → Option ℚ
  | .apply "ScopedFactorEntry" [index, coordinate] => do
    let slot ← decodeNat? index
    let row ← decodeNat? coordinate
    if within : slot < m then (tables ⟨slot, within⟩).coefficients[row]? else none
  | _ => none

@[simp] theorem lookup_entry (tables : Fin m → Table domains) (slot : Fin m) (row : Nat) :
    lookup? tables (entry slot.val row) = (tables slot).coefficients[row]? := by
  simp [lookup?, entry, slot.isLt]

def values (tables : Fin m → Table domains) (request : Pattern) : ℚ :=
  (lookup? tables request).getD 0

/-- Check that every primitive request of the reference execution is
available before returning its mass. -/
def execute? (tables : Fin m → Table domains) (term : Pattern) : Option ℚ :=
  let result := run (values tables) term
  if result.profile.requests.all (fun request => (lookup? tables request).isSome) then
    some result.value
  else none

theorem execute_eq_value {tables : Fin m → Table domains} {term : Pattern} {answer : ℚ}
    (defined : execute? tables term = some answer) :
    answer = (run (values tables) term).value := by
  dsimp only [execute?] at defined
  split at defined
  · exact (Option.some.inj defined).symm
  · contradiction

private def sumTree : List Pattern → Pattern
  | [] => zero
  | term :: rest => add term (sumTree rest)

private theorem run_sumTree_value (lookup : Pattern → ℚ) (terms : List Pattern) :
    (run lookup (sumTree terms)).value = (terms.map fun term => (run lookup term).value).sum := by
  induction terms with
  | nil => simp [sumTree, zero, FirstOrderCalculus.app, run]
  | cons term rest ih =>
    simp only [sumTree, add, FirstOrderCalculus.app, run, List.map_cons, List.sum_cons, ih]

private theorem run_sumTree_requests (lookup : Pattern → ℚ) (terms : List Pattern) :
    (run lookup (sumTree terms)).profile.requests =
      (terms.map fun term => (run lookup term).profile.requests).flatten := by
  induction terms with
  | nil => simp [sumTree, zero, FirstOrderCalculus.app, run]
  | cons term rest ih =>
    simp only [sumTree, add, FirstOrderCalculus.app, run, List.map_cons, List.flatten_cons, ih]

/-- Lower a plan at a specified assignment to its surviving variables.
Primitive addresses depend on the ordered scopes and assignment. -/
def lower (scopes : Fin m → List (Fin n)) : EliminationPlan n m → Config domains → Pattern
  | .unit, _ => one
  | .input slot, config => read (entry slot.val (encode domains (scopes slot) config))
  | .mul left right, config => mul (lower scopes left config) (lower scopes right config)
  | .sumOut v body, config =>
    if v ∈ body.scope scopes then
      sumTree (List.ofFn fun state : Fin (domains v) =>
        lower scopes body (put domains config v state))
    else lower scopes body config

theorem lookup_value (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (slot : Fin m) (config : Config domains) :
    lookup? tables (entry slot.val (encode domains (tables slot).scope config)) =
      some ((tables slot).value domains positive config) := by
  rw [lookup_entry, Array.getElem?_eq_getElem (by
    rw [(tables slot).size_eq]
    exact encode_bound domains positive _ config)]
  rfl

theorem entry_agree_on_scope (scopes : Fin m → List (Fin n)) (slot : Fin m)
    (first second : Config domains) (agreement : ∀ v ∈ scopes slot, first v = second v) :
    entry slot.val (encode domains (scopes slot) first) =
      entry slot.val (encode domains (scopes slot) second) :=
  congrArg (entry slot.val) (encode_agree domains _ first second agreement)

/-- The independently executed GSLT term agrees with the table operations. -/
theorem run_lower (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plan : EliminationPlan n m) (config : Config domains) :
    (run (values tables) (lower scopes plan config)).value =
      (plan.evaluate positive tables).value domains positive config := by
  induction plan generalizing config with
  | unit =>
    simp only [lower, PolynomialReadoutCalculus.one, FirstOrderCalculus.app, run, EliminationPlan.evaluate]
    exact (tabulate_value domains positive [] (by simp) (fun _ => 1) (by intros; rfl) config).symm
  | input slot =>
    simp only [lower, PolynomialReadoutCalculus.read, FirstOrderCalculus.app, run, values,
      EliminationPlan.evaluate]
    rw [← agrees slot, lookup_value positive tables slot config]
    rfl
  | mul left right ihl ihr =>
    simp only [lower, mul, FirstOrderCalculus.app, run, EliminationPlan.evaluate, ihl, ihr]
    exact ((left.evaluate positive tables).mul_value domains positive
      (right.evaluate positive tables) config).symm
  | sumOut v body ih =>
    have scopeEq := body.evaluate_scope positive tables scopes agrees
    by_cases active : v ∈ body.scope scopes
    · rw [lower, if_pos active, run_sumTree_value, List.map_ofFn]
      simp only [Function.comp_apply, ih, List.sum_ofFn, EliminationPlan.evaluate]
      exact ((body.evaluate positive tables).sumOut_value domains positive v
        (by rwa [scopeEq]) config).symm
    · rw [lower, if_neg active, ih]
      change _ = ((body.evaluate positive tables).sumOut domains positive v).value domains positive config
      rw [Table.sumOut, if_neg (by simpa only [scopeEq] using active)]

/-- Each emitted request comes from a declared input slot and addresses a
row that exists in the supplied table. -/
theorem lower_request (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plan : EliminationPlan n m) (config : Config domains) {request : Pattern}
    (present : request ∈ (run (values tables) (lower scopes plan config)).profile.requests) :
    ∃ slot : Fin m, ∃ row : Nat, slot ∈ plan.inputs ∧ request = entry slot.val row ∧
      row < (tables slot).coefficients.size := by
  induction plan generalizing config with
  | unit => simp [lower, PolynomialReadoutCalculus.one, FirstOrderCalculus.app, run] at present
  | input slot =>
    have same : request = entry slot.val (encode domains (scopes slot) config) := by
      simpa [lower, PolynomialReadoutCalculus.read, FirstOrderCalculus.app, run] using present
    refine ⟨slot, _, by simp [EliminationPlan.inputs], same, ?_⟩
    rw [(tables slot).size_eq, agrees slot]
    exact encode_bound domains positive _ config
  | mul left right ihl ihr =>
    simp only [lower, mul, FirstOrderCalculus.app, run, List.mem_append] at present
    rcases present with onLeft | onRight
    · obtain ⟨slot, row, used, same, within⟩ := ihl config onLeft
      exact ⟨slot, row, by simp [EliminationPlan.inputs, used], same, within⟩
    · obtain ⟨slot, row, used, same, within⟩ := ihr config onRight
      exact ⟨slot, row, by simp [EliminationPlan.inputs, used], same, within⟩
  | sumOut v body ih =>
    by_cases active : v ∈ body.scope scopes
    · rw [lower, if_pos active, run_sumTree_requests] at present
      obtain ⟨reads, inMap, inReads⟩ := List.mem_flatten.mp present
      obtain ⟨term, inTerms, rfl⟩ := List.mem_map.mp inMap
      obtain ⟨state, rfl⟩ := List.mem_ofFn.mp inTerms
      exact ih (put domains config v state) inReads
    · rw [lower, if_neg active] at present
      exact ih config present

theorem execute_lower (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plan : EliminationPlan n m) (config : Config domains) :
    execute? tables (lower scopes plan config) =
      some ((plan.evaluate positive tables).value domains positive config) := by
  have all : ((run (values tables) (lower scopes plan config)).profile.requests.all
      (fun request => (lookup? tables request).isSome)) = true := by
    rw [List.all_eq_true]
    intro request present
    obtain ⟨slot, row, _, same, within⟩ := lower_request positive tables scopes agrees plan config present
    simp [same, Array.getElem?_eq_getElem within]
  simp only [execute?, all, if_true, run_lower positive tables scopes agrees]

/-- A checked cache implements the same coefficient-level observation as
the GSLT readout, including after any accepted factor edit. -/
theorem execute_runtime {positive : ∀ v, 0 < domains v} {scopes : Fin m → List (Fin n)}
    {order : List (Fin n)} (runtime : EliminationPlan.Runtime positive scopes order)
    (config : Config domains) :
    execute? (fun slot : Fin m => runtime.factors[slot])
      (lower scopes (EliminationPlan.compile scopes order) config) =
      some (runtime.table.value domains positive config) := by
  rw [execute_lower positive _ scopes runtime.scopes_match, EliminationPlan.Runtime.table,
    EliminationPlan.Retained.table_exact]

open CertificateGSLT

/-- The polynomial equality checker preserves the total arithmetic value. -/
theorem checked_readout (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plan : EliminationPlan n m) (config : Config domains) (target : Pattern)
    (proof : RawOpenProof)
    (accepted : checkOpenRaw validated [] (equal target (lower scopes plan config)) proof = true) :
    (run (values tables) target).value =
      (plan.evaluate positive tables).value domains positive config := by
  have equalValue := checked_polynomial_equal [] target (lower scopes plan config) proof accepted (by simp)
  calc
    _ = (run (values tables) (lower scopes plan config)).value := by
      rw [run_value, run_value, equalValue]
    _ = _ := run_lower positive tables scopes agrees plan config

/-- Validate both arithmetic equality and the proposed read footprint.
The footprint test lets one certificate be reused after coefficient edits. -/
def checkReplacement (source target : Pattern) (proof : RawOpenProof) : Bool :=
  checkOpenRaw validated [] (equal target source) proof &&
    (run (fun _ => (0 : ℚ)) target).profile.requests.all
      (fun key => decide (key ∈ (run (fun _ => (0 : ℚ)) source).profile.requests))

theorem execute_checked (tables : Fin m → Table domains) (source target : Pattern)
    (proof : RawOpenProof) {answer : ℚ} (defined : execute? tables source = some answer)
    (accepted : checkReplacement source target proof = true) :
    execute? tables target = some answer := by
  obtain ⟨arithmetic, footprint⟩ := Bool.and_eq_true_iff.mp accepted
  have available : ((run (values tables) source).profile.requests.all
      (fun request => (lookup? tables request).isSome)) = true := by
    by_contra unavailable
    simp [execute?, unavailable] at defined
  have all : ((run (values tables) target).profile.requests.all
      (fun request => (lookup? tables request).isSome)) = true := by
    rw [List.all_eq_true]
    intro key present
    rw [profile_independent (values tables) (fun _ => (0 : ℚ)) target] at present
    have inSource := of_decide_eq_true (List.all_eq_true.mp footprint key present)
    rw [← profile_independent (values tables) (fun _ => (0 : ℚ)) source] at inSource
    exact List.all_eq_true.mp available key inSource
  have samePolynomial := checked_polynomial_equal [] target source proof arithmetic (by simp)
  have sameValue : (run (values tables) target).value = answer := by
    rw [run_value, samePolynomial, ← run_value, ← execute_eq_value defined]
  simp only [execute?, all, if_true, sameValue]

theorem execute_replacement (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plan : EliminationPlan n m) (config : Config domains) (target : Pattern)
    (proof : RawOpenProof) (accepted : checkReplacement (lower scopes plan config) target proof = true) :
    execute? tables target = some ((plan.evaluate positive tables).value domains positive config) :=
  execute_checked tables (lower scopes plan config) target proof
    (execute_lower positive tables scopes agrees plan config) accepted

end Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout
