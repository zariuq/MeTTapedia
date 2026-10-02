import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.TypedInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Eliminators
import Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure

/-!
# The natural numbers and identity elimination in the set tower

**The natural numbers.** The numerals are the finite ordinals (`numeral`), and the
natural numbers are the set `ZFSet.omega` of them (`mem_omega_iff`); distinct naturals give
distinct numerals, since a numeral's rank is its natural (`rank_numeral`). Recursion on the
naturals into the values of a motive (`natRec`) stays in the motive's values when the value at
zero and the step do (`natRec_mem`).

**The hereditarily finite sets** `V_ω` (`finiteSets`) are closed under the power set
(`powerset_mem_finiteSets`), and a closed universe that contains the natural numbers contains
them (`finiteSets_mem`). A closed universe need not contain the natural numbers: the least one
around the empty set lies inside `V_ω` (`omega_not_mem_univOf_empty`), whatever the hypothesis
`CofinalInaccessibles` that builds it.

**The recursor of the natural numbers** (`numRecValue`): over the telescope of its declared
type `nrTypeC` (the motive, the value at zero, the step, the number), the traced graph of
recursion on the naturals. It lies in the value of its declared type when the numbers are read
as `ω`, zero as `∅` and the successor as the successor of numerals (`numRecValue_mem`), and at a
typed instance its value at zero is the value at zero and at a successor the step applied to the
value at the predecessor (`numRecValue_zero`, `numRecValue_succ`): the two iota steps hold.

**Identity elimination** (`jValue`): over the telescope of its declared type `jTypeC`, the
traced graph returning the method. It lies in the value of its declared type
(`jValue_mem`) by uniqueness of identity proofs: an identity value is a truth value, so a path
is the value of reflexivity and its endpoints are equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (pisCtx NumNames nrTypeC nrStepTypeC sucTypeC
  jTypeC)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (Closed CofinalInaccessibles univOf univOf_minimal)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

/-! ## The natural numbers -/

/-- The numerals, the finite ordinals: `0 = ∅` and `k + 1 = k ∪ {k}`. -/
def numeral : ℕ → ZFSet.{u}
  | 0 => ∅
  | k + 1 => insert (numeral k) (numeral k)

theorem numeral_succ (k : ℕ) : numeral.{u} (k + 1) = insert (numeral k) (numeral k) := rfl

/-- The rank of a numeral is its natural. -/
theorem rank_numeral : ∀ k : ℕ, (numeral.{u} k).rank = k
  | 0 => ZFSet.rank_empty
  | k + 1 => by
      rw [numeral_succ, ZFSet.rank_insert, rank_numeral k,
        max_eq_left (Order.le_succ _), Order.succ_eq_add_one]
      push_cast
      rfl

/-- Distinct naturals give distinct numerals. -/
theorem numeral_injective : Function.Injective numeral.{u} := fun j k same => by
  have ranks := congrArg ZFSet.rank same
  rw [rank_numeral, rank_numeral] at ranks
  exact_mod_cast ranks

theorem mk_ofNat : ∀ k : ℕ, ZFSet.mk (PSet.ofNat k) = numeral.{u} k
  | 0 => rfl
  | k + 1 => by
      rw [numeral_succ, ← mk_ofNat k]
      rfl

/-- **The natural numbers are the numerals.** -/
theorem mem_omega_iff {x : ZFSet.{u}} : x ∈ ZFSet.omega ↔ ∃ k, numeral k = x := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  change ZFSet.mk p ∈ ZFSet.mk PSet.omega ↔ _
  rw [ZFSet.mk_mem_iff, PSet.mem_def]
  constructor
  · rintro ⟨⟨k⟩, equivalent⟩
    exact ⟨k, (mk_ofNat k).symm.trans (ZFSet.sound equivalent).symm⟩
  · rintro ⟨k, same⟩
    refine ⟨⟨k⟩, ZFSet.exact ?_⟩
    change ZFSet.mk p = ZFSet.mk (PSet.ofNat k)
    rw [mk_ofNat]
    exact same.symm

theorem numeral_mem_omega (k : ℕ) : numeral.{u} k ∈ ZFSet.omega :=
  mem_omega_iff.mpr ⟨k, rfl⟩

/-- The natural of a number: a `k` whose numeral it is, and `0` outside the numbers. -/
noncomputable def natOf (x : ZFSet.{u}) : ℕ :=
  @dite _ (∃ k, numeral k = x) (Classical.propDecidable _) Classical.choose fun _ => 0

theorem numeral_natOf {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : numeral (natOf x) = x := by
  have present := mem_omega_iff.mp hx
  rw [natOf, dif_pos present]
  exact Classical.choose_spec present

theorem natOf_numeral (k : ℕ) : natOf (numeral.{u} k) = k :=
  numeral_injective (numeral_natOf (numeral_mem_omega k))

/-- The successor of a number is a number. -/
theorem insert_mem_omega {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : insert x x ∈ ZFSet.omega := by
  rw [← numeral_natOf hx]
  exact numeral_mem_omega (natOf x + 1)

/-- **Recursion on the naturals**: at `0` the value at zero, at `k + 1` the step at the numeral
`k` applied to the value at `k`. -/
noncomputable def natRec (z s : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => z
  | k + 1 => traceApp (traceApp s (numeral k)) (natRec z s k)

/-- **Recursion stays in the motive's values** when the value at zero and the step do. -/
theorem natRec_mem {P z s : ZFSet.{u}} (hz : z ∈ traceApp P (numeral 0))
    (hs : ∀ k, ∀ y ∈ traceApp P (numeral k),
      traceApp (traceApp s (numeral k)) y ∈ traceApp P (numeral (k + 1))) :
    ∀ k, natRec z s k ∈ traceApp P (numeral k)
  | 0 => hz
  | k + 1 => hs k _ (natRec_mem hz hs k)

/-! ## The hereditarily finite sets -/

/-- The hereditarily finite sets `V_ω`. -/
noncomputable def finiteSets : ZFSet.{u} := ZFSet.vonNeumann Ordinal.omega0

theorem powerset_mem_finiteSets {x : ZFSet.{u}} (hx : x ∈ finiteSets) :
    ZFSet.powerset x ∈ finiteSets :=
  ZFSetIndexedClosure.finite_universe_closed.power_mem hx

theorem range_numeral : ZFSet.range numeral.{u} = ZFSet.omega := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_range, mem_omega_iff]

/-- The stages `V_k` of finite rank. -/
theorem finiteRankStage_mem {U : ZFSet.{u}} (closed : Closed U) (hU : (∅ : ZFSet.{u}) ∈ U) :
    ∀ k : ℕ, ZFSet.vonNeumann (k : Ordinal.{u}) ∈ U
  | 0 => by
      rw [Nat.cast_zero, ZFSet.vonNeumann_zero]
      exact hU
  | k + 1 => by
      rw [Nat.cast_succ, ZFSet.vonNeumann_add_one]
      exact closed.power_mem (finiteRankStage_mem closed hU k)

/-- `V_ω` is the union of the stages of finite rank. -/
theorem finiteSets_eq_sUnion :
    finiteSets.{u} = ZFSet.sUnion (ZFSet.range fun k : ℕ => ZFSet.vonNeumann (k : Ordinal.{u})) := by
  apply ZFSet.ext
  intro x
  rw [finiteSets, ZFSet.mem_vonNeumann, ZFSet.mem_sUnion]
  constructor
  · intro lt
    obtain ⟨n, same⟩ := Ordinal.lt_omega0.mp lt
    refine ⟨ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{u}), ZFSet.mem_range_self _, ?_⟩
    rw [ZFSet.mem_vonNeumann, same]
    exact_mod_cast Nat.lt_succ_self n
  · rintro ⟨y, hy, hx⟩
    obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
    exact (ZFSet.mem_vonNeumann.mp hx).trans (Ordinal.natCast_lt_omega0 k)

/-- **A closed universe containing the natural numbers contains `V_ω`.** -/
theorem finiteSets_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega.{u} ∈ U) :
    finiteSets ∈ U := by
  have hEmpty : (∅ : ZFSet.{u}) ∈ U := closed.empty_mem hω
  rw [finiteSets_eq_sUnion]
  refine closed.union_mem (ZFSetIndexedClosure.range_mem_of_index closed numeral
    numeral_injective ?_ _ (finiteRankStage_mem closed hEmpty))
  rw [range_numeral]
  exact hω

/-- The natural numbers are not hereditarily finite. -/
theorem omega_not_mem_finiteSets : ZFSet.omega.{u} ∉ finiteSets := by
  intro member
  obtain ⟨n, same⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp member)
  have below := ZFSet.rank_lt_of_mem (numeral_mem_omega.{u} n)
  rw [rank_numeral, same] at below
  exact lt_irrefl _ below

/-- **The least closed universe around the empty set does not contain the natural numbers**:
it lies inside `V_ω`, which is closed. -/
theorem omega_not_mem_univOf_empty (h : CofinalInaccessibles.{u}) :
    ZFSet.omega.{u} ∉ univOf h ∅ := fun member =>
  omega_not_mem_finiteSets (univOf_minimal h
    (ZFSet.mem_vonNeumann.mpr (by rw [ZFSet.rank_empty]; exact Ordinal.omega0_pos))
    ZFSetIndexedClosure.finite_universe_closed member)

/-! ## The recursor -/

variable {Head : Type} (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-- The telescope of the declared type of numeral recursion: the motive, the value at zero,
the step and the number. -/
def nrTele (N : NumNames Head) : CCtx Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (.pi (.const N.num) (.head N.univ)))
    (.app (.var 0) (.const N.zero))) (nrStepTypeC N)) (.const N.num)

theorem nrTypeC_eq (N : NumNames Head) : nrTypeC N = pisCtx (nrTele N) (.app (.var 3) (.var 0)) :=
  rfl

/-- **The value of numeral recursion**: the traced graph, over its telescope, of recursion on
the naturals with the given value at zero and step. -/
noncomputable def numRecValue (N : NumNames Head) : ZFSet.{u} :=
  telescopeGraph heads consts (nrTele N) fun η => natRec (η 2) (η 1) (natOf (η 0))

/-- The numbers read as `ω`, zero as `∅`, and the successor as the successor of numerals. -/
structure NumberReading (N : NumNames Head) : Prop where
  num : consts N.num = ZFSet.omega
  zero : consts N.zero = numeral 0
  succ : ∀ k, traceApp (consts N.suc) (numeral k) = numeral (k + 1)

variable {heads consts}

/-- What a typed instance of the recursor's telescope says: the number is a number, the
value at zero lies in the motive at zero, and the step takes the motive's values at a number
to its values at the successor. -/
theorem nrTele_sat {N : NumNames Head} (reading : NumberReading consts N) {η : Env.{u} 4}
    (sat : Sat heads consts (nrTele N) η) :
    η 0 ∈ ZFSet.omega ∧ η 2 ∈ traceApp (η 3) (numeral 0) ∧
      ∀ k, ∀ y ∈ traceApp (η 3) (numeral k),
        traceApp (traceApp (η 1) (numeral k)) y ∈ traceApp (η 3) (numeral (k + 1)) := by
  have number : η 0 ∈ consts N.num := sat 0
  have atZero : η 2 ∈ traceApp (η 3) (consts N.zero) := sat 2
  have step : η 1 ∈ tracePiSet (consts N.num) fun v =>
      tracePiSet (traceApp (η 3) v) fun _ => traceApp (η 3) (traceApp (consts N.suc) v) := sat 1
  rw [reading.num] at number step
  rw [reading.zero] at atZero
  refine ⟨number, atZero, fun k y hy => ?_⟩
  have atNumber := traceApp_mem_fibre step (numeral_mem_omega k)
  have applied := traceApp_mem_fibre atNumber hy
  rwa [reading.succ] at applied

/-- **The recursor's value lies in the value of its declared type.** -/
theorem numRecValue_mem {N : NumNames Head} (reading : NumberReading consts N) :
    numRecValue heads consts N ∈ ev heads consts (nrTypeC N) Fin.elim0 := by
  rw [nrTypeC_eq]
  apply telescopeGraph_mem_pisCtx
  intro η sat
  obtain ⟨number, atZero, step⟩ := nrTele_sat reading sat
  change natRec (η 2) (η 1) (natOf (η 0)) ∈ traceApp (η 3) (η 0)
  have typed := natRec_mem atZero step (natOf (η 0))
  rwa [numeral_natOf number] at typed

/-- The recursor applied to a typed instance of its telescope: recursion on the number's
natural. -/
theorem numRecValue_apply {N : NumNames Head} {η : Env.{u} 4}
    (sat : Sat heads consts (nrTele N) η) :
    applyValues (numRecValue heads consts N) 4 η = natRec (η 2) (η 1) (natOf (η 0)) :=
  applyValues_telescopeGraph heads consts _ _ η sat

/-- **The iota step at zero**: at a typed instance whose number is zero, the recursor gives the
value at zero. -/
theorem numRecValue_zero {N : NumNames Head} {η : Env.{u} 4}
    (sat : Sat heads consts (nrTele N) η) (zero : η 0 = numeral 0) :
    applyValues (numRecValue heads consts N) 4 η = η 2 := by
  rw [numRecValue_apply sat, zero, natOf_numeral]
  rfl

/-- **The iota step at a successor**: at a typed instance whose number is the successor of
the numeral `k`, the recursor gives the step at `k` applied to its value at `k`. -/
theorem numRecValue_succ {N : NumNames Head} {η : Env.{u} 4}
    (sat : Sat heads consts (nrTele N) η) {k : ℕ} (succ : η 0 = numeral (k + 1)) :
    applyValues (numRecValue heads consts N) 4 η =
      traceApp (traceApp (η 1) (numeral k)) (natRec (η 2) (η 1) k) := by
  rw [numRecValue_apply sat, succ, natOf_numeral]
  rfl

/-! ## Identity elimination -/

/-- The telescope of the declared type of identity elimination at a universe `u`: the carrier,
the base point, the motive, the method, the endpoint and the path. -/
def jTele (univ : Head) : CCtx Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil (.head univ)) (.var 0))
    (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head univ))))
    (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))) (.var 3)) (.id (.var 4) (.var 3) (.var 0))

theorem jTypeC_eq (univ : Head) :
    jTypeC univ = pisCtx (jTele univ) (.app (.app (.var 3) (.var 1)) (.var 0)) :=
  rfl

variable (heads consts) in
/-- **The value of identity elimination**: the traced graph, over its telescope, returning the
method. -/
noncomputable def jValue (univ : Head) : ZFSet.{u} :=
  telescopeGraph heads consts (jTele univ) fun η => η 2

/-- **Uniqueness of identity proofs in the set model**: at a typed instance of the
eliminator's telescope the path is the value of reflexivity and the endpoints are equal. -/
theorem jTele_path {univ : Head} {η : Env.{u} 6} (sat : Sat heads consts (jTele univ) η) :
    η 0 = ∅ ∧ η 4 = η 1 :=
  (mem_truthCode _ _).mp (sat 0)

/-- **Identity elimination lies in the value of its declared type**, by uniqueness of identity
proofs: at a path the motive's value is its value at reflexivity. -/
theorem jValue_mem (univ : Head) :
    jValue heads consts univ ∈ ev heads consts (jTypeC univ) Fin.elim0 := by
  rw [jTypeC_eq]
  apply telescopeGraph_mem_pisCtx
  intro η sat
  obtain ⟨path, ends⟩ := jTele_path sat
  have method : η 2 ∈ traceApp (traceApp (η 3) (η 4)) ∅ := sat 2
  change η 2 ∈ traceApp (traceApp (η 3) (η 1)) (η 0)
  rwa [path, ← ends]

/-- **The linear rule of identity elimination**: at a typed instance of its telescope, the
eliminator gives the method. -/
theorem jValue_apply {univ : Head} {η : Env.{u} 6} (sat : Sat heads consts (jTele univ) η) :
    applyValues (jValue heads consts univ) 6 η = η 2 :=
  applyValues_telescopeGraph heads consts _ _ η sat

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
