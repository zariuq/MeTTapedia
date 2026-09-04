/-
# Hamiltonicity Theorems

This file contains the classical Hamiltonicity theorems from Bondy & Murty Chapter 18:
- Dirac's Theorem (18.4): δ ≥ n/2 → Hamiltonian
- Ore's Theorem

Reference: Bondy & Murty, "Graph Theory" (GTM 244), Chapter 18
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mettapedia.GraphTheory.HamiltonianDegree

set_option checkBinderAnnotations false

open Classical Finset

namespace Mettapedia.GraphTheory.Hamiltonicity

variable {V : Type*} [DecidableEq V] [Fintype V]

/-!
## Section 1: Complete Graphs are Hamiltonian

The complete graph K_n is Hamiltonian for n ≥ 3.
This is needed as a base case for closure-based proofs.
-/

omit [DecidableEq V] [Fintype V] in
/-- In the complete graph, any two distinct vertices are adjacent -/
lemma top_adj_of_ne (u v : V) (h : u ≠ v) : (⊤ : SimpleGraph V).Adj u v := h

/-- The complete graph on n ≥ 3 vertices is Hamiltonian -/
theorem complete_isHamiltonian (hn : Fintype.card V ≥ 3) : (⊤ : SimpleGraph V).IsHamiltonian := by
  intro _
  let k := Fintype.card V - 3
  have hcard : k + 3 = Fintype.card V := by
    dsimp [k]
    omega
  obtain ⟨e⟩ := Fintype.truncEquivFin V
  let eV : Fin (k + 3) ≃ V :=
    (Equiv.cast (by rw [hcard])).trans e.symm
  let includeCycle : (SimpleGraph.cycleGraph (k + 3) : SimpleGraph (Fin (k + 3))) →g
      (⊤ : SimpleGraph (Fin (k + 3))) :=
    SimpleGraph.Hom.ofLE le_top
  have hcycle : (SimpleGraph.cycleGraph.cycle k).IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨SimpleGraph.cycleGraph.isCycle_cycle, by simp⟩
  have hcycleTop : ((SimpleGraph.cycleGraph.cycle k).map includeCycle).IsHamiltonianCycle :=
    hcycle.map (by
      change Function.Bijective (id : Fin (k + 3) → Fin (k + 3))
      exact Function.bijective_id)
  let transport : (⊤ : SimpleGraph (Fin (k + 3))) →g (⊤ : SimpleGraph V) :=
    (SimpleGraph.Iso.completeGraph eV).toHom
  refine ⟨eV 0, (SimpleGraph.cycleGraph.cycle k).map includeCycle |>.map transport, ?_⟩
  exact hcycleTop.map (by
    change Function.Bijective eV
    exact eV.bijective)

/-!
## Section 2: Cycle Exchange (Path Exchange)

The key technique from B&M §18.3.
Given a Hamilton cycle C of the complete graph K with edges colored blue (in G) or red (not in G),
if xx⁺ is red, we can find y⁺ ∈ S⁺ ∩ T and exchange to get more blue edges.
-/

variable (n : ℕ) (hn_pos : 0 < n)

/-- A Hamilton cycle represented as an ordering of n vertices with cyclic adjacency.
    Uses an equivalence (bijection with inverse) for clean successor/predecessor definitions.
    Indices are Fin n with modular arithmetic for cyclic ordering. -/
structure HamiltonCycle (G : SimpleGraph V) (hn : Fintype.card V = n) where
  /-- The equivalence from Fin n to vertices -/
  toEquiv : Fin n ≃ V
  /-- Each consecutive pair (in cyclic order) is adjacent.
      Note: (i + 1) wraps around using Fin's modular arithmetic when i = n-1 -/
  adj_succ : ∀ i : Fin n, G.Adj (toEquiv i) (toEquiv ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩)

omit [DecidableEq V] in
/-- Two represented Hamilton cycles are equal when their cyclic vertex
enumerations are equal.  Adjacency fields are propositions and therefore do
not add a second notion of cycle identity. -/
lemma HamiltonCycle.eq_of_toEquiv_eq {G : SimpleGraph V}
    {hn : Fintype.card V = n}
    {first second : HamiltonCycle n hn_pos G hn}
    (equal : first.toEquiv = second.toEquiv) : first = second := by
  cases first
  cases second
  cases equal
  rfl

omit [DecidableEq V] in
/-- Hamilton cycles on a finite vertex type form a finite type.  The proof
embeds cycles into finite equivalences and uses the exact representation
identity theorem above. -/
noncomputable instance HamiltonCycle.fintype {G : SimpleGraph V}
    {hn : Fintype.card V = n} :
    Fintype (HamiltonCycle n hn_pos G hn) := by
  letI : Finite (Fin n → V) := Finite.of_fintype _
  letI : Finite (Fin n ≃ V) :=
    Finite.of_injective
      (fun equivalence : Fin n ≃ V => equivalence.toFun) (by
        intro first second equal
        ext index
        exact congrFun equal index)
  letI : Finite (HamiltonCycle n hn_pos G hn) :=
    Finite.of_injective (fun cycle => cycle.toEquiv) (by
      intro first second equal
      exact HamiltonCycle.eq_of_toEquiv_eq n hn_pos equal)
  exact Fintype.ofFinite _

variable {n hn_pos}

/-- The successor of a vertex on a Hamilton cycle (cyclically next vertex) -/
def HamiltonCycle.succ {G : SimpleGraph V} {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (v : V) : V :=
  C.toEquiv ⟨((C.toEquiv.symm v).val + 1) % n, Nat.mod_lt _ hn_pos⟩

/-- The predecessor of a vertex on a Hamilton cycle -/
def HamiltonCycle.pred {G : SimpleGraph V} {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (v : V) : V :=
  C.toEquiv ⟨((C.toEquiv.symm v).val + n - 1) % n, Nat.mod_lt _ hn_pos⟩

/-- The set of successors S⁺ for a set S -/
def HamiltonCycle.succSet {G : SimpleGraph V} {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (S : Finset V) : Finset V :=
  S.image C.succ

/-!
### Converting HamiltonCycle to Mathlib's Walk
-/

/-- Build a walk of length k starting from position i on the Hamilton cycle.
    walkFrom C i k visits: C.toEquiv i → C.toEquiv (i+1) → ... → C.toEquiv (i+k) -/
def HamiltonCycle.walkFrom {G : SimpleGraph V} {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (i : Fin n) :
    (k : ℕ) → G.Walk (C.toEquiv i) (C.toEquiv ⟨(i.val + k) % n, Nat.mod_lt _ hn_pos⟩)
  | 0 => by
    let endpoint : Fin n :=
      ⟨(i.val + 0) % n, Nat.mod_lt _ hn_pos⟩
    have endpoint_eq : C.toEquiv i = C.toEquiv endpoint := by
      apply congrArg C.toEquiv
      apply Fin.ext
      simp [endpoint, Nat.mod_eq_of_lt i.isLt]
    exact (SimpleGraph.Walk.nil : G.Walk (C.toEquiv i) (C.toEquiv i)).copy
      rfl endpoint_eq
  | k + 1 => by
    -- Walk from i to i+k, then add edge from i+k to i+k+1
    let w := C.walkFrom i k
    have hadj := C.adj_succ ⟨(i.val + k) % n, Nat.mod_lt _ hn_pos⟩
    -- The successor of position (i+k)%n is position ((i+k)%n + 1)%n = (i+k+1)%n
    have heq : ((i.val + k) % n + 1) % n = (i.val + (k + 1)) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    -- Need to convert hadj to use the right index
    have hadj' : G.Adj (C.toEquiv ⟨(i.val + k) % n, Nat.mod_lt _ hn_pos⟩)
                       (C.toEquiv ⟨(i.val + (k + 1)) % n, Nat.mod_lt _ hn_pos⟩) := by
      convert hadj using 2
      exact Fin.ext heq.symm
    exact w.concat hadj'

omit [DecidableEq V] in
@[simp]
lemma HamiltonCycle.walkFrom_length {G : SimpleGraph V}
    {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (i : Fin n) (k : ℕ) :
    (C.walkFrom i k).length = k := by
  induction k with
  | zero => simp [HamiltonCycle.walkFrom]
  | succ k ih =>
      simp only [HamiltonCycle.walkFrom, SimpleGraph.Walk.length_concat, ih]

omit [DecidableEq V] [Fintype V] in
private lemma getVert_concat_of_le {G : SimpleGraph V} {u v w : V}
    (walk : G.Walk u v) (adjacent : G.Adj v w) (index : ℕ)
    (atMost : index ≤ walk.length) :
    (walk.concat adjacent).getVert index = walk.getVert index := by
  rw [SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.getVert_append]
  by_cases before : index < walk.length
  · simp [before]
  · have equal : index = walk.length :=
      Nat.le_antisymm atMost (Nat.le_of_not_gt before)
    subst index
    simp

omit [DecidableEq V] in
lemma HamiltonCycle.walkFrom_getVert {G : SimpleGraph V}
    {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (i : Fin n) :
    ∀ k index : ℕ, index ≤ k →
      (C.walkFrom i k).getVert index =
        C.toEquiv ⟨(i.val + index) % n, Nat.mod_lt _ hn_pos⟩
  | 0, index, atMost => by
      have equal : index = 0 := Nat.eq_zero_of_le_zero atMost
      subst index
      simp only [SimpleGraph.Walk.getVert_zero]
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
  | k + 1, index, atMost => by
      by_cases earlier : index ≤ k
      · change ((C.walkFrom i k).concat _).getVert index = _
        have atMostLength : index ≤ (C.walkFrom i k).length := by
          simpa only [HamiltonCycle.walkFrom_length] using earlier
        rw [getVert_concat_of_le _ _ _ atMostLength]
        exact C.walkFrom_getVert i k index earlier
      · have equal : index = k + 1 := by omega
        subst index
        have endpoint := SimpleGraph.Walk.getVert_length (C.walkFrom i (k + 1))
        rw [HamiltonCycle.walkFrom_length] at endpoint
        exact endpoint

/-- The full Hamilton cycle as a walk returning to start -/
def HamiltonCycle.toWalk {G : SimpleGraph V} {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) :
    G.Walk (C.toEquiv ⟨0, hn_pos⟩) (C.toEquiv ⟨0, hn_pos⟩) := by
  let origin : Fin n := ⟨0, hn_pos⟩
  let endpoint : Fin n :=
    ⟨(origin.val + n) % n, Nat.mod_lt _ hn_pos⟩
  have endpoint_eq : C.toEquiv endpoint = C.toEquiv origin := by
    apply congrArg C.toEquiv
    apply Fin.ext
    simp [endpoint, origin]
  exact (C.walkFrom origin n).copy rfl endpoint_eq

omit [DecidableEq V] in
@[simp]
lemma HamiltonCycle.toWalk_length {G : SimpleGraph V}
    {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) :
    C.toWalk.length = n := by
  simp [HamiltonCycle.toWalk, HamiltonCycle.walkFrom_length]

omit [DecidableEq V] in
lemma HamiltonCycle.toWalk_getVert {G : SimpleGraph V}
    {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (index : ℕ) (atMost : index ≤ n) :
    C.toWalk.getVert index =
      C.toEquiv ⟨index % n, Nat.mod_lt _ hn_pos⟩ := by
  simp only [HamiltonCycle.toWalk, SimpleGraph.Walk.getVert_copy]
  simpa using C.walkFrom_getVert (⟨0, hn_pos⟩ : Fin n) n index atMost

/-- The walk from HamiltonCycle visits every vertex exactly once (in the non-closed part) -/
lemma HamiltonCycle.toWalk_isHamiltonianCycle {G : SimpleGraph V} {hn : Fintype.card V = n}
    (C : HamiltonCycle n hn_pos G hn) (hn3 : n ≥ 3) : C.toWalk.IsHamiltonianCycle := by
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, C.toWalk_length.trans hn.symm⟩
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_iff_injective_get_support]
    intro first second equalVertices
    have nonnil : ¬C.toWalk.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length, C.toWalk_length]
      exact hn_pos
    have tailSupportLength : C.toWalk.tail.support.length = n := by
      rw [C.toWalk.support_tail_of_not_nil nonnil, List.length_tail,
        SimpleGraph.Walk.length_support, C.toWalk_length]
      omega
    have firstLt : first.val < n := by
      simpa [tailSupportLength] using first.isLt
    have secondLt : second.val < n := by
      simpa [tailSupportLength] using second.isLt
    have firstAtMost : first.val + 1 ≤ n := by omega
    have secondAtMost : second.val + 1 ≤ n := by omega
    have tailEqual : C.toWalk.tail.getVert first.val =
        C.toWalk.tail.getVert second.val := by
      simpa only [List.get_eq_getElem,
        SimpleGraph.Walk.support_getElem_eq_getVert] using equalVertices
    let firstIndex : Fin n := ⟨first.val, firstLt⟩
    let secondIndex : Fin n := ⟨second.val, secondLt⟩
    let step : Fin n := ⟨1 % n, Nat.mod_lt _ hn_pos⟩
    have shiftedIndices : firstIndex + step = secondIndex + step := by
      apply C.toEquiv.injective
      rw [Fin.add_def, Fin.add_def]
      change C.toEquiv ⟨(first.val + 1 % n) % n, _⟩ =
        C.toEquiv ⟨(second.val + 1 % n) % n, _⟩
      have oneMod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      simpa only [oneMod] using
        (calc
          C.toEquiv ⟨(first.val + 1) % n, Nat.mod_lt _ hn_pos⟩ =
              C.toWalk.getVert (first.val + 1) :=
            (C.toWalk_getVert (first.val + 1) firstAtMost).symm
          _ = C.toWalk.tail.getVert first.val :=
            (SimpleGraph.Walk.getVert_tail C.toWalk).symm
          _ = C.toWalk.tail.getVert second.val := tailEqual
          _ = C.toWalk.getVert (second.val + 1) :=
            SimpleGraph.Walk.getVert_tail C.toWalk
          _ = C.toEquiv ⟨(second.val + 1) % n, Nat.mod_lt _ hn_pos⟩ :=
            C.toWalk_getVert (second.val + 1) secondAtMost)
    have baseIndices : firstIndex = secondIndex :=
      add_right_cancel shiftedIndices
    apply Fin.ext
    have vals := congrArg Fin.val baseIndices
    simpa [firstIndex, secondIndex] using vals
  · rw [C.toWalk_length]
    exact hn3

/-!
## Section 3: Dirac's Theorem

Dirac's theorem is obtained from the Mathlib-facing rotation-extension proof
in `HamiltonianDegree`.  This route constructs a longest path, proves that it
visits every vertex, and closes it by the Ore degree-sum argument.
-/

/-- Dirac's theorem: a finite graph on at least three vertices whose every
vertex has twice its degree at least the graph order is Hamiltonian. -/
theorem dirac_hamiltonian' (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn3 : Fintype.card V ≥ 3)
    (hdeg : ∀ v, 2 * G.degree v ≥ Fintype.card V) :
    G.IsHamiltonian := by
  apply HamiltonianDegree.ore_theorem G hn3
  intro u v _different _nonadjacent
  have degreeU := hdeg u
  have degreeV := hdeg v
  omega

/-!
## Section 4: Ore's Theorem
-/

/-- Ore's condition: all non-adjacent pairs have degree sum at least the
number of vertices. -/
def OreCondition (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v, u ≠ v → ¬G.Adj u v →
    Fintype.card V ≤ G.degree u + G.degree v

/-- Ore's theorem, exposed under the historical API of this module. -/
theorem ore_hamiltonian' (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V ≥ 3)
    (hore : OreCondition G) :
    G.IsHamiltonian := by
  apply HamiltonianDegree.ore_theorem G hn
  exact hore

end Mettapedia.GraphTheory.Hamiltonicity
