import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationAlgebra
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Init.Data.Array.OfFn
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
Dense rational tables with mixed-radix rows. The computational operations
tabulate only their declared scopes, then refine the existing valuation
algebra. The table convention makes the rightmost coordinate vary fastest.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable

open scoped BigOperators

variable {n : ℕ} (domains : Fin n → ℕ)

abbrev Config := ∀ v : Fin n, Fin (domains v)

def volume (scope : List (Fin n)) : ℕ := (scope.map domains).prod

def encode : List (Fin n) → Config domains → ℕ
  | [], _ => 0
  | v :: vs, x => (x v).val * volume domains vs + encode vs x

def put (x : Config domains) (v : Fin n) (value : Fin (domains v)) : Config domains :=
  fun u => if h : u = v then h.symm ▸ value else x u

@[simp] theorem put_same (x : Config domains) (v : Fin n) (value : Fin (domains v)) :
    put domains x v value v = value := by simp [put]

@[simp] theorem put_other (x : Config domains) (v u : Fin n) (value : Fin (domains v))
    (different : u ≠ v) : put domains x v value u = x u := by simp [put, different]

theorem volume_pos (positive : ∀ v, 0 < domains v) (scope : List (Fin n)) :
    0 < volume domains scope := by
  induction scope with
  | nil => simp [volume]
  | cons v vs ih => simpa [volume] using Nat.mul_pos (positive v) ih

theorem encode_bound (_positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (x : Config domains) : encode domains scope x < volume domains scope := by
  induction scope with
  | nil => simp [encode, volume]
  | cons v vs ih =>
    have next : (x v).val + 1 ≤ domains v := (x v).isLt
    calc
      encode domains (v :: vs) x < (x v).val * volume domains vs + volume domains vs := by
        simpa [encode] using Nat.add_lt_add_left ih ((x v).val * volume domains vs)
      _ = ((x v).val + 1) * volume domains vs := by ring
      _ ≤ domains v * volume domains vs := Nat.mul_le_mul_right _ next
      _ = volume domains (v :: vs) := by simp [volume]

def decode (positive : ∀ v, 0 < domains v) : List (Fin n) → ℕ → Config domains
  | [], _ => fun v => ⟨0, positive v⟩
  | v :: vs, row =>
      put domains (decode positive vs (row % volume domains vs)) v
        ⟨(row / volume domains vs) % domains v, Nat.mod_lt _ (positive v)⟩

theorem encode_agree (scope : List (Fin n)) (x y : Config domains)
    (agreement : ∀ v ∈ scope, x v = y v) : encode domains scope x = encode domains scope y := by
  induction scope with
  | nil => rfl
  | cons v vs ih =>
    rw [encode, encode, agreement v (by simp), ih (by
      intro u member
      exact agreement u (by simp [member]))]

theorem decode_encode_agree (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (x : Config domains) :
    ∀ v ∈ scope, decode domains positive scope (encode domains scope x) v = x v := by
  induction scope with
  | nil => simp
  | cons v vs ih =>
    have tail_bound := encode_bound domains positive vs x
    have tail_pos := volume_pos domains positive vs
    have remainder : encode domains (v :: vs) x % volume domains vs = encode domains vs x := by
      simp [encode, Nat.add_mod, Nat.mod_eq_of_lt tail_bound]
    have quotient : encode domains (v :: vs) x / volume domains vs = (x v).val := by
      rw [encode, Nat.mul_comm (x v).val _, Nat.mul_add_div tail_pos]
      simp [Nat.div_eq_of_lt tail_bound]
    intro u member
    rcases List.mem_cons.mp member with equal | member
    · subst u
      apply Fin.ext
      simp [decode, quotient, Nat.mod_eq_of_lt (x v).isLt]
    · have different : u ≠ v := by
        intro equal
        subst u
        exact (List.nodup_cons.mp distinct).1 member
      simpa [decode, remainder, different] using ih (List.nodup_cons.mp distinct).2 u member

structure Table where
  scope : List (Fin n)
  distinct : scope.Nodup
  coefficients : Array ℚ
  size_eq : coefficients.size = volume domains scope
deriving DecidableEq

def Table.value (table : Table domains) (positive : ∀ v, 0 < domains v)
    (x : Config domains) : ℚ :=
  table.coefficients[encode domains table.scope x]'(by
    rw [table.size_eq]
    exact encode_bound domains positive table.scope x)

def tabulate (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (f : Config domains → ℚ) : Table domains where
  scope := scope
  distinct := distinct
  coefficients := Array.ofFn (fun row : Fin (volume domains scope) =>
    f (decode domains positive scope row.val))
  size_eq := by simp

theorem tabulate_value (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (f : Config domains → ℚ)
    (respects : ∀ x y, (∀ v ∈ scope, x v = y v) → f x = f y) (x : Config domains) :
    (tabulate domains positive scope distinct f).value domains positive x = f x := by
  simp only [Table.value, tabulate, Array.getElem_ofFn]
  exact respects _ x (decode_encode_agree domains positive scope distinct x)

def Table.toValuation (positive : ∀ v, 0 < domains v) (table : Table domains) :
    Valuation (Fin n) (fun v => Fin (domains v)) ℚ :=
  ⟨table.scope.toFinset, table.value domains positive⟩

theorem Table.respects (positive : ∀ v, 0 < domains v) (table : Table domains) :
    RespectsScope (table.toValuation domains positive) := by
  intro x y agreement
  have indices := encode_agree domains table.scope x y (by
    intro v member
    exact agreement v (List.mem_toFinset.mpr member))
  simp only [Table.toValuation, Table.value, indices]

def Table.mul (positive : ∀ v, 0 < domains v) (left right : Table domains) : Table domains :=
  tabulate domains positive (left.scope ++ right.scope).dedup (List.nodup_dedup _)
    (fun x => left.value domains positive x * right.value domains positive x)

theorem Table.mul_value (positive : ∀ v, 0 < domains v) (left right : Table domains)
    (x : Config domains) :
    (left.mul domains positive right).value domains positive x =
      left.value domains positive x * right.value domains positive x := by
  apply tabulate_value
  intro a b agreement
  have equalLeft := left.respects domains positive a b (by
    intro v member
    change v ∈ left.scope.toFinset at member
    exact agreement v (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl (List.mem_toFinset.mp member)))))
  have equalRight := right.respects domains positive a b (by
    intro v member
    change v ∈ right.scope.toFinset at member
    exact agreement v (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr (List.mem_toFinset.mp member)))))
  change left.value domains positive a = left.value domains positive b at equalLeft
  change right.value domains positive a = right.value domains positive b at equalRight
  rw [equalLeft, equalRight]

theorem Table.mul_refines (positive : ∀ v, 0 < domains v) (left right : Table domains) :
    (left.mul domains positive right).toValuation domains positive =
      combine (left.toValuation domains positive) (right.toValuation domains positive) := by
  apply Valuation.ext
  · ext v
    simp [Table.mul, tabulate, Table.toValuation, combine]
  · intro x
    exact left.mul_value domains positive right x

def Table.sumOut (positive : ∀ v, 0 < domains v) (table : Table domains)
    (v : Fin n) : Table domains :=
  if v ∈ table.scope then
    tabulate domains positive (table.scope.erase v) (table.distinct.erase v)
      (fun x => (List.ofFn (fun value : Fin (domains v) =>
        table.value domains positive (put domains x v value))).sum)
  else table

theorem put_agree (scope : List (Fin n)) (v : Fin n) (value : Fin (domains v))
    (x y : Config domains) (agreement : ∀ u ∈ scope.erase v, x u = y u) :
    ∀ u ∈ scope, put domains x v value u = put domains y v value u := by
  intro u member
  by_cases equal : u = v
  · subst u
    simp
  · simp only [put_other domains x v u value equal, put_other domains y v u value equal]
    exact agreement u ((List.mem_erase_of_ne equal).mpr member)

theorem put_eq_update (x : Config domains) (v : Fin n) (value : Fin (domains v)) :
    put domains x v value = update x v value := by
  funext u
  by_cases equal : u = v
  · subst u
    simp [put, update]
  · simp [put, update, equal]

theorem Table.sumOut_value (positive : ∀ v, 0 < domains v) (table : Table domains)
    (v : Fin n) (mentioned : v ∈ table.scope) (x : Config domains) :
    (table.sumOut domains positive v).value domains positive x =
      ∑ value : Fin (domains v), table.value domains positive (put domains x v value) := by
  rw [Table.sumOut, if_pos mentioned]
  rw [tabulate_value]
  · exact List.sum_ofFn
  · intro a b agreement
    congr 1
    congr 1
    funext value
    exact table.respects domains positive _ _ (by
      intro u member
      exact put_agree domains table.scope v value a b agreement u (List.mem_toFinset.mp member))

theorem Table.sumOut_refines (positive : ∀ v, 0 < domains v) (table : Table domains)
    (v : Fin n) :
    (table.sumOut domains positive v).toValuation domains positive =
      BayesianNetworks.sumOut (table.toValuation domains positive) v := by
  by_cases mentioned : v ∈ table.scope
  · apply Valuation.ext
    · ext u
      simp [Table.sumOut, mentioned, tabulate, Table.toValuation, sumOut_scope]
      exact table.distinct.mem_erase_iff
    · intro x
      change (table.sumOut domains positive v).value domains positive x = _
      rw [table.sumOut_value domains positive v mentioned]
      simp [BayesianNetworks.sumOut, Table.toValuation, mentioned, put_eq_update]
  · simp [Table.sumOut, mentioned, BayesianNetworks.sumOut, Table.toValuation]

def one (positive : ∀ v, 0 < domains v) : Table domains :=
  tabulate domains positive [] (by simp) (fun _ => 1)

theorem one_refines (positive : ∀ v, 0 < domains v) :
    (one domains positive).toValuation domains positive =
      oneValuation (Fin n) (fun v => Fin (domains v)) ℚ := by
  apply Valuation.ext
  · rfl
  · intro x
    exact tabulate_value domains positive [] (by simp) (fun _ => 1) (by intros; rfl) x

def combineAll (positive : ∀ v, 0 < domains v) (tables : List (Table domains)) : Table domains :=
  tables.foldr (fun table rest => table.mul domains positive rest) (one domains positive)

theorem combineAll_refines (positive : ∀ v, 0 < domains v) (tables : List (Table domains)) :
    (combineAll domains positive tables).toValuation domains positive =
      BayesianNetworks.combineAll (tables.map (Table.toValuation domains positive)) := by
  induction tables with
  | nil => exact one_refines domains positive
  | cons table tables ih =>
    change (table.mul domains positive (combineAll domains positive tables)).toValuation domains positive =
      combine (table.toValuation domains positive)
        (BayesianNetworks.combineAll (tables.map (Table.toValuation domains positive)))
    rw [Table.mul_refines, ih]

theorem combineAll_value (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (x : Config domains) :
    (combineAll domains positive tables).value domains positive x =
      (tables.map (fun table => table.value domains positive x)).prod := by
  induction tables with
  | nil => exact tabulate_value domains positive [] (by simp) (fun _ => 1) (by intros; rfl) x
  | cons table tables ih =>
      change (table.mul domains positive (combineAll domains positive tables)).value domains positive x =
        table.value domains positive x * (tables.map (fun t => t.value domains positive x)).prod
      rw [Table.mul_value, ih]

def eliminateVar (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (v : Fin n) : List (Table domains) :=
  let hit := tables.filter (fun table => decide (v ∈ table.scope))
  let rest := tables.filter (fun table => !decide (v ∈ table.scope))
  match hit with
  | [] => rest
  | _ => (combineAll domains positive hit).sumOut domains positive v :: rest

theorem eliminateVar_refines (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (v : Fin n) :
    (eliminateVar domains positive tables v).map (Table.toValuation domains positive) =
      BayesianNetworks.eliminateVar (tables.map (Table.toValuation domains positive)) v := by
  have predicate (table : Table domains) :
      hasVar v (table.toValuation domains positive) = decide (v ∈ table.scope) := by
    simp [hasVar, Table.toValuation]
  unfold eliminateVar BayesianNetworks.eliminateVar
  rw [List.filter_map, List.filter_map]
  simp only [Function.comp_def, predicate]
  generalize tables.filter (fun table => decide (v ∈ table.scope)) = hit
  cases hit with
  | nil => simp
  | cons table rest =>
    simp only [List.map_cons, List.map_cons, Table.sumOut_refines, combineAll_refines]

def eliminateVars (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (order : List (Fin n)) : List (Table domains) :=
  order.foldl (eliminateVar domains positive) tables

theorem eliminateVars_refines (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (order : List (Fin n)) :
    (eliminateVars domains positive tables order).map (Table.toValuation domains positive) =
      BayesianNetworks.eliminateVars (tables.map (Table.toValuation domains positive)) order := by
  induction order generalizing tables with
  | nil => rfl
  | cons v vs ih =>
    simpa only [eliminateVars, List.foldl_cons, BayesianNetworks.eliminateVars,
      eliminateVar_refines] using ih (eliminateVar domains positive tables v)

theorem elimination_correct (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (order : List (Fin n)) :
    (combineAll domains positive (eliminateVars domains positive tables order)).toValuation domains positive =
      BayesianNetworks.sumOutAll
        (BayesianNetworks.combineAll (tables.map (Table.toValuation domains positive))) order := by
  rw [combineAll_refines, eliminateVars_refines]
  apply combineAll_eliminateVars
  intro table member
  rcases List.mem_map.mp member with ⟨original, _, rfl⟩
  exact original.respects domains positive

def extendScope (positive : ∀ v, 0 < domains v) (scope : Finset (Fin n))
    (assignment : ∀ v ∈ scope, Fin (domains v)) : Config domains :=
  fun v => if member : v ∈ scope then assignment v member else ⟨0, positive v⟩

def graph (positive : ∀ v, 0 < domains v) (tables : List (Table domains)) :
    FactorGraph (Fin n) ℚ where
  stateSpace v := Fin (domains v)
  factors := Fin tables.length
  scope index := tables[index].scope.toFinset
  potential index assignment :=
    tables[index].value domains positive
      (extendScope domains positive tables[index].scope.toFinset assignment)

instance graph_state_fintype (positive : ∀ v, 0 < domains v) (tables : List (Table domains)) :
    (v : Fin n) → Fintype ((graph domains positive tables).stateSpace v) :=
  fun v => inferInstanceAs (Fintype (Fin (domains v)))

def Table.toFactor (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (table : Table domains) : VariableElimination.Factor (graph domains positive tables) :=
  ⟨table.scope.toFinset, fun assignment => table.value domains positive
    (extendScope domains positive table.scope.toFinset assignment)⟩

theorem Table.toFactor_refines (positive : ∀ v, 0 < domains v)
    (tables : List (Table domains)) (table : Table domains) :
    (table.toFactor domains positive tables).toValuation = table.toValuation domains positive := by
  apply Valuation.ext
  · rfl
  · intro x
    apply table.respects domains positive
    intro v member
    change v ∈ table.scope.toFinset at member
    simp [extendScope, member]
    rfl

theorem combine_toFactor_refines (positive : ∀ v, 0 < domains v)
    (tables : List (Table domains)) :
    (VariableElimination.combineAll
      (tables.map (Table.toFactor domains positive tables))).toValuation =
      (combineAll domains positive tables).toValuation domains positive := by
  rw [VariableElimination.Factor.toValuation_combineAll, combineAll_refines]
  congr 1
  simp only [List.map_map, Function.comp_def, Table.toFactor_refines]
  rfl

theorem eliminate_toFactor_refines (positive : ∀ v, 0 < domains v)
    (tables : List (Table domains)) (order : List (Fin n)) :
    (combineAll domains positive (eliminateVars domains positive tables order)).toValuation domains positive =
      (VariableElimination.sumOutAll
        (VariableElimination.combineAll (tables.map (Table.toFactor domains positive tables)))
        order).toValuation := by
  rw [elimination_correct, VariableElimination.Factor.toValuation_sumOutAll,
    combine_toFactor_refines, combineAll_refines]
  rfl

def covering (positive : ∀ v, 0 < domains v) : List (Table domains) :=
  (List.ofFn (fun v : Fin n => v)).map (fun v =>
    tabulate domains positive [v] (by simp) (fun _ => 1))

theorem covering_value (positive : ∀ v, 0 < domains v) (x : Config domains) :
    (combineAll domains positive (covering domains positive)).value domains positive x = 1 := by
  have tableValue (v : Fin n) :
      (tabulate domains positive [v] (by simp) (fun _ => 1)).value domains positive x = 1 :=
    tabulate_value domains positive [v] (by simp) (fun _ => 1) (by intros; rfl) x
  rw [combineAll_value]
  simp [covering, Function.comp_def, tableValue]

theorem covering_scope (positive : ∀ v, 0 < domains v) (tables : List (Table domains)) :
    (combineAll domains positive (tables ++ covering domains positive)).scope.toFinset = Finset.univ := by
  have factorMem : ∀ (table : Table domains) (ts : List (Table domains)),
      table ∈ ts → ∀ v ∈ table.scope, v ∈ (combineAll domains positive ts).scope := by
    intro table ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      intro member v inside
      rcases List.mem_cons.mp member with equal | member
      · subst table
        change v ∈ (t.scope ++ (combineAll domains positive ts).scope).dedup
        exact List.mem_dedup.mpr (List.mem_append.mpr (Or.inl inside))
      · have tail := ih member v inside
        change v ∈ (t.scope ++ (combineAll domains positive ts).scope).dedup
        exact List.mem_dedup.mpr (List.mem_append.mpr (Or.inr tail))
  ext v
  simp only [Finset.mem_univ, iff_true]
  apply List.mem_toFinset.mpr
  let unit := tabulate domains positive [v] (by simp) (fun _ => (1 : ℚ))
  apply factorMem unit (tables ++ covering domains positive)
  · apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    exact ⟨v, by simp, rfl⟩
  · simp [unit, tabulate]

def weight (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (order : List (Fin n)) : ℚ :=
  (combineAll domains positive (eliminateVars domains positive tables order)).value
    domains positive (fun v => ⟨0, positive v⟩)

theorem weight_eq_full_sum (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (order : List (Fin n)) (covers : ∀ v, v ∈ order)
    (fullScope : (combineAll domains positive tables).scope.toFinset = Finset.univ) :
    weight domains positive tables order =
      ∑ x : Config domains, (combineAll domains positive tables).value domains positive x := by
  classical
  let fs := tables.map (Table.toFactor domains positive tables)
  let combined := VariableElimination.combineAll fs
  let eliminated := VariableElimination.sumOutAll combined order
  have same := eliminate_toFactor_refines domains positive tables order
  have combinedScope : combined.scope = Finset.univ := by
    have scope := congrArg Valuation.scope (combine_toFactor_refines domains positive tables)
    exact scope.trans fullScope
  have emptyScope : eliminated.scope = ∅ := by
    dsimp [eliminated]
    rw [VariableElimination.sumOutAll_scope]
    rw [VariableElimination.eraseList_eq_sdiff]
    ext v
    simp [covers v]
  have constantValue (x : Config domains) :
      eliminated.toValuation.val x = eliminated.evalConst emptyScope := by
    apply congrArg eliminated.potential
    funext v member
    simp [emptyScope] at member
  calc
    weight domains positive tables order =
        eliminated.toValuation.val (fun v => ⟨0, positive v⟩) := by
      exact congrArg (fun f => f.val (fun v => ⟨0, positive v⟩)) same
    _ = eliminated.evalConst emptyScope := constantValue _
    _ = eliminated.totalWeight :=
      (VariableElimination.Factor.totalWeight_eq_evalConst_of_scope_empty eliminated emptyScope).symm
    _ = combined.totalWeight := VariableElimination.totalWeight_sumOutAll combined order
    _ = combined.fullConfigWeightSum :=
      VariableElimination.Factor.totalWeight_eq_fullConfigSum_of_scope_univ combined combinedScope
    _ = ∑ x : Config domains, (combineAll domains positive tables).value domains positive x := by
      change (∑ x : Config domains, combined.toValuation.val x) = _
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun f => f.val x) (combine_toFactor_refines domains positive tables)

abbrev Constraint := Σ v : Fin n, Fin (domains v)

def indicator (positive : ∀ v, 0 < domains v) (constraint : Constraint domains) : Table domains :=
  tabulate domains positive [constraint.1] (by simp)
    (fun x => if x constraint.1 = constraint.2 then 1 else 0)

theorem indicator_value (positive : ∀ v, 0 < domains v) (constraint : Constraint domains)
    (x : Config domains) :
    (indicator domains positive constraint).value domains positive x =
      if x constraint.1 = constraint.2 then 1 else 0 := by
  apply tabulate_value
  intro a b agreement
  rw [agreement constraint.1 (by simp)]

def satisfies (constraints : List (Constraint domains)) (x : Config domains) : Prop :=
  ∀ constraint ∈ constraints, x constraint.1 = constraint.2

instance (constraints : List (Constraint domains)) (x : Config domains) :
    Decidable (satisfies domains constraints x) :=
  inferInstanceAs (Decidable (∀ constraint ∈ constraints, x constraint.1 = constraint.2))

def queryTables (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraints : List (Constraint domains)) : List (Table domains) :=
  constraints.map (indicator domains positive) ++ tables ++ covering domains positive

theorem indicators_product (positive : ∀ v, 0 < domains v)
    (constraints : List (Constraint domains)) (x : Config domains) :
    ((constraints.map (indicator domains positive)).map (fun t => t.value domains positive x)).prod =
      if satisfies domains constraints x then 1 else 0 := by
  induction constraints with
  | nil => simp [satisfies]
  | cons constraint constraints ih =>
      simp only [List.map_cons, List.prod_cons, indicator_value, ih]
      by_cases head : x constraint.1 = constraint.2
      · simp [satisfies, head]
        rfl
      · simp [satisfies, head]

theorem queryTables_value (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraints : List (Constraint domains)) (x : Config domains) :
    (combineAll domains positive (queryTables domains positive tables constraints)).value domains positive x =
      if satisfies domains constraints x then (combineAll domains positive tables).value domains positive x else 0 := by
  rw [combineAll_value]
  simp only [queryTables, List.map_append, List.prod_append]
  rw [indicators_product, ← combineAll_value, ← combineAll_value, covering_value]
  split <;> simp_all

def queryWeight (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraints : List (Constraint domains)) (order : List (Fin n)) : ℚ :=
  weight domains positive (queryTables domains positive tables constraints) order

theorem queryWeight_correct (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraints : List (Constraint domains)) (order : List (Fin n)) (covers : ∀ v, v ∈ order) :
    queryWeight domains positive tables constraints order =
      ∑ x : Config domains,
        if satisfies domains constraints x then (combineAll domains positive tables).value domains positive x else 0 := by
  have fullScope : (combineAll domains positive (queryTables domains positive tables constraints)).scope.toFinset =
      Finset.univ := by
    simpa only [queryTables, List.append_assoc] using
      covering_scope domains positive (constraints.map (indicator domains positive) ++ tables)
  rw [queryWeight, weight_eq_full_sum domains positive _ order covers fullScope]
  apply Finset.sum_congr rfl
  intro x _
  exact queryTables_value domains positive tables constraints x

def conditionalQuery (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n)) : Option ℚ :=
  let normalizer := queryWeight domains positive tables evidence order
  if 0 < normalizer then
    some (queryWeight domains positive tables (evidence ++ query) order / normalizer)
  else none

theorem conditionalQuery_correct (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n)) (covers : ∀ v, v ∈ order) :
    conditionalQuery domains positive tables evidence query order =
      let normalizer := ∑ x : Config domains,
        if satisfies domains evidence x then (combineAll domains positive tables).value domains positive x else 0
      if 0 < normalizer then some ((∑ x : Config domains,
        if satisfies domains (evidence ++ query) x then (combineAll domains positive tables).value domains positive x else 0) /
          normalizer) else none := by
  simp only [conditionalQuery, queryWeight_correct domains positive _ _ order covers]

theorem normalized_mass (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence : List (Constraint domains)) (order : List (Fin n)) (covers : ∀ v, v ∈ order)
    (normalizerPositive : 0 < queryWeight domains positive tables evidence order) :
    (∑ x : Config domains,
      (if satisfies domains evidence x then (combineAll domains positive tables).value domains positive x else 0) /
        queryWeight domains positive tables evidence order) = 1 := by
  rw [← Finset.sum_div, ← queryWeight_correct domains positive tables evidence order covers]
  exact div_self (ne_of_gt normalizerPositive)

theorem duplicate_constraint (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraint : Constraint domains) (rest : List (Constraint domains))
    (order : List (Fin n)) (covers : ∀ v, v ∈ order) :
    queryWeight domains positive tables (constraint :: constraint :: rest) order =
      queryWeight domains positive tables (constraint :: rest) order := by
  rw [queryWeight_correct domains positive tables _ order covers,
    queryWeight_correct domains positive tables _ order covers]
  apply Finset.sum_congr rfl
  intro x _
  simp [satisfies]

/-! Dependency keys retain a component's factors and constraints. The revision
of the enclosing space is not itself a mathematical dependency of a retained
component. Elimination orders and repeated deliveries may differ. -/

structure QueryRequest where
  tables : List (Table domains)
  evidence : List (Constraint domains)
  query : List (Constraint domains)
  order : List (Fin n)
  covers : ∀ v, v ∈ order
  spaceRevision : ℕ

abbrev QueryKey := List (Table domains) × Finset (Constraint domains) × Finset (Constraint domains)

def QueryRequest.key (request : QueryRequest domains) : QueryKey domains :=
  (request.tables, request.evidence.toFinset, request.query.toFinset)

def QueryRequest.observe (positive : ∀ v, 0 < domains v)
    (request : QueryRequest domains) : Option ℚ :=
  conditionalQuery domains positive request.tables request.evidence request.query request.order

theorem satisfies_finset (a b : List (Constraint domains)) (same : a.toFinset = b.toFinset)
    (x : Config domains) : satisfies domains a x ↔ satisfies domains b x := by
  have member (c : Constraint domains) : c ∈ a ↔ c ∈ b := by
    exact Eq.to_iff (by simpa only [List.mem_toFinset] using congrArg (fun s => c ∈ s) same)
  constructor <;> intro h c hc
  · exact h c ((member c).mpr hc)
  · exact h c ((member c).mp hc)

theorem satisfies_append (a b : List (Constraint domains)) (x : Config domains) :
    satisfies domains (a ++ b) x ↔ satisfies domains a x ∧ satisfies domains b x := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨ha, hb⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha c hc
    · exact hb c hc

/-- Sound even when an unrelated space revision changes, an order changes, or
the same constraint was delivered twice. The proof uses independent sums over
complete assignments, rather than identifying the key with the answer. -/
theorem queryKey_sound (positive : ∀ v, 0 < domains v) :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      (QueryRequest.key domains) (QueryRequest.observe domains positive) := by
  intro a b same
  rcases Prod.mk.inj same with ⟨tables, constraints⟩
  rcases Prod.mk.inj constraints with ⟨evidence, query⟩
  have evidenceEq (x : Config domains) :
      satisfies domains a.evidence x = satisfies domains b.evidence x :=
    propext (satisfies_finset domains _ _ evidence x)
  have queryEq (x : Config domains) :
      satisfies domains (a.evidence ++ a.query) x =
        satisfies domains (b.evidence ++ b.query) x := by
    apply propext
    rw [satisfies_append, satisfies_append]
    exact and_congr (satisfies_finset domains _ _ evidence x)
      (satisfies_finset domains _ _ query x)
  simp only [QueryRequest.observe, conditionalQuery_correct domains positive _ _ _ _ a.covers,
    conditionalQuery_correct domains positive _ _ _ _ b.covers, evidenceEq, queryEq, tables]

/-- Stores formed from actual requests remain coherent across later revisions. -/
theorem query_cache_answers (positive : ∀ v, 0 < domains v)
    (history : List (QueryRequest domains)) (next : QueryRequest domains) :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.lookupOrCompute
      (QueryRequest.key domains) (QueryRequest.observe domains positive)
      (history.foldl (Mettapedia.GSLT.Dynamics.MemoizationObserver.store
        (QueryRequest.key domains) (QueryRequest.observe domains positive))
        Mettapedia.GSLT.Dynamics.MemoizationObserver.Table.empty) next =
      next.observe domains positive := by
  classical
  exact Mettapedia.GSLT.Dynamics.MemoizationObserver.lookupOrCompute_eq_obs
    (Mettapedia.GSLT.Dynamics.MemoizationObserver.coherent_foldl_store_of_soundKey
      (queryKey_sound domains positive) history) next

theorem query_cache_eviction (positive : ∀ v, 0 < domains v)
    (history : List (QueryRequest domains))
    (retained : Mettapedia.GSLT.Dynamics.MemoizationObserver.Table (QueryKey domains) (Option ℚ))
    (subtable : Mettapedia.GSLT.Dynamics.MemoizationObserver.Subtable retained
      (history.foldl (Mettapedia.GSLT.Dynamics.MemoizationObserver.store
        (QueryRequest.key domains) (QueryRequest.observe domains positive))
        Mettapedia.GSLT.Dynamics.MemoizationObserver.Table.empty))
    (next : QueryRequest domains) :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.lookupOrCompute
      (QueryRequest.key domains) (QueryRequest.observe domains positive) retained next =
      next.observe domains positive := by
  classical
  exact Mettapedia.GSLT.Dynamics.MemoizationObserver.lookupOrCompute_eq_obs
    (Mettapedia.GSLT.Dynamics.MemoizationObserver.coherent_of_subtable
      (Mettapedia.GSLT.Dynamics.MemoizationObserver.coherent_foldl_store_of_soundKey
        (queryKey_sound domains positive) history) subtable) next

end Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable
