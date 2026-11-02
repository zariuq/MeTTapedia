import Mettapedia.Logic.ClarkCompletion
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Computed tightness and stratification certificates

Checking scans the original clauses independently of certificate finding.
Tightness reuses the certified dependency catalogue and its ordering measure.
Stratification uses bounded monotone propagation with weak positive edges and
strict negative edges. Rank compression proves completeness of the bound.
The procedures classify syntactic dependencies, including those in rules with
false static guards; they do not evaluate program models or probabilities.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.NormalProgramCertificates

open LP BDDCore NormalProgramSemantics ClarkCompletion
open Mettapedia.Algorithms.WellFoundedServices

variable {σ : LPSignature} [DecidableEq (GroundAtom σ)]

/-- Check the supplied ranks directly against positive body occurrences. -/
def checkTightRank (rules : List (NormalClause σ)) (rank : GroundAtom σ → Nat) : Bool :=
  rules.all fun c => (positiveBody c).all fun a => decide (rank a < rank c.head)

omit [DecidableEq (GroundAtom σ)] in
theorem checkTightRank_correct (rules : List (NormalClause σ)) (rank : GroundAtom σ → Nat) :
    checkTightRank rules rank = true ↔
      ∀ c ∈ rules, ∀ a, GoalLit.pos a ∈ c.body → rank a < rank c.head := by
  simp [checkTightRank]

/-- Check the supplied strata, rather than trusting how they were found. -/
def checkStratification (rules : List (NormalClause σ)) (s : Stratification σ) : Bool :=
  rules.all fun c => c.body.all fun g => match g with
    | .pos a => decide (s a ≤ s c.head)
    | .neg a => decide (s a < s c.head)
    | .neq _ _ => true

omit [DecidableEq (GroundAtom σ)] in
theorem checkStratification_correct (rules : List (NormalClause σ)) (s : Stratification σ) :
    checkStratification rules s = true ↔ ∀ c ∈ rules, respectsStratification c s := by
  simp only [checkStratification, List.all_eq_true, respectsStratification]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro _
  apply forall_congr'
  intro g
  cases g <;> simp

structure StratificationCertificate (rules : List (NormalClause σ)) where
  strata : Stratification σ
  respects : ∀ c ∈ rules, respectsStratification c strata

/-- The finite dependency carrier includes atoms occurring only in bodies. -/
def dependencyTable (rules : List (NormalClause σ)) : AtomTable (GroundAtom σ) :=
  programTable (n := 0) Fin.elim0 rules []

theorem head_mem_table {rules : List (NormalClause σ)} {c : NormalClause σ} (member : c ∈ rules) :
    c.head ∈ (dependencyTable rules).atoms :=
  (programTable_covers (n := 0) Fin.elim0 rules []).2 c member

theorem body_mem_table {rules : List (NormalClause σ)} {c : NormalClause σ} (member : c ∈ rules)
    {g : GoalLit σ} (body : g ∈ c.body) {a : GroundAtom σ} (atom : a ∈ goalAtoms g) :
    a ∈ (dependencyTable rules).atoms := by
  simp only [dependencyTable, programTable, List.mem_dedup, List.ofFn_zero,
    List.nil_append, List.flatMap_nil, List.append_nil]
  exact List.mem_flatMap.mpr ⟨c, member, List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, body, atom⟩)⟩

def positiveCatalogue (rules : List (NormalClause σ)) : Catalogue (GroundAtom σ) where
  items := (dependencyTable rules).atoms
  deps head := (rules.filter fun c => c.head = head).flatMap positiveBody

theorem catalogue_uses (rules : List (NormalClause σ)) (head body : GroundAtom σ) :
    (positiveCatalogue rules).Uses head body ↔ PositiveDependency rules body head := by
  have deps : body ∈ (positiveCatalogue rules).deps head ↔ PositiveDependency rules body head := by
    simp [positiveCatalogue, PositiveDependency, and_assoc]
  change head ∈ (dependencyTable rules).atoms ∧ body ∈ (positiveCatalogue rules).deps head ↔ _
  rw [deps]
  constructor
  · exact And.right
  · intro edge
    obtain ⟨c, member, rfl, bodyMember⟩ := edge
    exact ⟨head_mem_table member, c, member, rfl, bodyMember⟩

theorem catalogue_rank_checked (rules : List (NormalClause σ)) (order : (positiveCatalogue rules).Acyclic) :
    checkTightRank rules ((positiveCatalogue rules).orderMeasure order.order) = true := by
  apply (checkTightRank_correct _ _).mpr
  intro c hc a ha
  exact order.respects.orderMeasure_lt order.covers ((catalogue_uses rules c.head a).mpr ⟨c, hc, rfl, ha⟩)

/-- Find an ordering with the existing Kahn service, then independently check its ranks. -/
def findTight (rules : List (NormalClause σ)) : Option (TightCertificate rules) :=
  match (positiveCatalogue rules).acyclic? with
  | none => none
  | some order =>
    let rank := (positiveCatalogue rules).orderMeasure order.order
    if checked : checkTightRank rules rank = true then
      some ⟨rank, (checkTightRank_correct rules rank).mp checked⟩
    else none

theorem findTight_isSome (rules : List (NormalClause σ)) : (findTight rules).isSome ↔ Tight rules := by
  have same : (findTight rules).isSome = (positiveCatalogue rules).acyclic?.isSome := by
    cases found : (positiveCatalogue rules).acyclic? with
    | none => simp [findTight, found]
    | some order => simp [findTight, found, catalogue_rank_checked rules order]
  rw [same, Catalogue.acyclic?_isSome_iff, tight_iff_acyclic]
  have relation : (positiveCatalogue rules).Uses = Function.swap (PositiveDependency rules) := by
    funext a b
    exact propext (catalogue_uses rules a b)
  simp only [relation, Relation.transGen_swap, PositiveAcyclic]

namespace RankSolver

open scoped BigOperators

structure Edge (m : Nat) where
  source : Fin m
  target : Fin m
  strict : Bool
  deriving DecidableEq, Repr

def Edge.weight {m : Nat} (edge : Edge m) : Nat := if edge.strict then 1 else 0

abbrev Labels (m : Nat) := List.Vector Nat m

def Valid {m : Nat} (edges : List (Edge m)) (r : Labels m) : Prop :=
  ∀ edge ∈ edges, r.get edge.source + edge.weight ≤ r.get edge.target

instance validDecidable {m : Nat} (edges : List (Edge m)) (r : Labels m) : Decidable (Valid edges r) := by
  unfold Valid
  infer_instance

/-- Every round materializes its labels before the next round reads them. -/
def relax {m : Nat} (edges : List (Edge m)) (r : Labels m) : Labels m :=
  List.Vector.ofFn fun v => max (r.get v)
    (((edges.filter fun e => e.target = v).toFinset).sup fun e => r.get e.source + e.weight)

theorem le_relax {m : Nat} (edges : List (Edge m)) (r : Labels m) (v : Fin m) :
    r.get v ≤ (relax edges r).get v := by
  simp only [relax, List.Vector.get_ofFn]
  exact le_max_left _ _

theorem edge_le_relax {m : Nat} (edges : List (Edge m)) (r : Labels m) {edge : Edge m}
    (member : edge ∈ edges) : r.get edge.source + edge.weight ≤ (relax edges r).get edge.target := by
  simp only [relax, List.Vector.get_ofFn]
  apply le_trans ?_ (le_max_right _ _)
  exact Finset.le_sup (f := fun e : Edge m => r.get e.source + e.weight)
    (s := (edges.filter fun e => e.target = edge.target).toFinset) (by simp [member])

theorem relax_le_solution {m : Nat} (edges : List (Edge m)) (r solution : Labels m)
    (valid : Valid edges solution) (below : ∀ v, r.get v ≤ solution.get v) :
    ∀ v, (relax edges r).get v ≤ solution.get v := by
  intro v
  simp only [relax, List.Vector.get_ofFn]
  apply max_le (below v)
  apply Finset.sup_le
  intro edge member
  obtain ⟨member, target⟩ := List.mem_filter.mp (List.mem_toFinset.mp member)
  have target : edge.target = v := of_decide_eq_true target
  exact (Nat.add_le_add_right (below edge.source) edge.weight).trans (target ▸ valid edge member)

theorem relax_fixed_iff {m : Nat} (edges : List (Edge m)) (r : Labels m) :
    relax edges r = r ↔ Valid edges r := by
  constructor
  · intro fixed edge member
    simpa only [fixed] using edge_le_relax edges r member
  · intro valid
    apply List.Vector.ext
    intro v
    exact le_antisymm (relax_le_solution edges r r valid (fun _ => le_rfl) v) (le_relax edges r v)

def mass {m : Nat} (r : Labels m) : Nat := ∑ v, r.get v

theorem mass_relax_lt {m : Nat} (edges : List (Edge m)) (r : Labels m) (invalid : ¬ Valid edges r) :
    mass r < mass (relax edges r) := by
  apply Finset.sum_lt_sum (fun v _ => le_relax edges r v)
  by_contra none
  have fixed : relax edges r = r := by
    apply List.Vector.ext
    intro v
    apply le_antisymm ?_ (le_relax edges r v)
    exact Nat.le_of_not_gt (fun strict => none ⟨v, Finset.mem_univ v, strict⟩)
  exact invalid ((relax_fixed_iff edges r).mp fixed)

def compress {m : Nat} (r : Labels m) : Labels m :=
  List.Vector.ofFn fun v => (Finset.univ.filter fun u => r.get u < r.get v).card

theorem compress_bounded {m : Nat} (r : Labels m) (v : Fin m) : (compress r).get v ≤ m := by
  simpa only [compress, List.Vector.get_ofFn, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun u => r.get u < r.get v) Finset.univ)

theorem compress_mono {m : Nat} (r : Labels m) {a b : Fin m} (h : r.get a ≤ r.get b) :
    (compress r).get a ≤ (compress r).get b := by
  simp only [compress, List.Vector.get_ofFn]
  apply Finset.card_le_card
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hv).2 h⟩

theorem compress_strict {m : Nat} (r : Labels m) {a b : Fin m} (h : r.get a < r.get b) :
    (compress r).get a < (compress r).get b := by
  simp only [compress, List.Vector.get_ofFn]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hv).2 h⟩
  · intro equal
    have present : a ∈ Finset.univ.filter (fun v => r.get v < r.get b) := by simp [h]
    rw [← equal] at present
    simp at present

/-- Weak and strict comparisons survive compression to finitely bounded labels. -/
theorem compress_valid {m : Nat} (edges : List (Edge m)) (r : Labels m) (valid : Valid edges r) :
    Valid edges (compress r) := by
  intro edge member
  have old := valid edge member
  cases strict : edge.strict with
  | false =>
    simp only [Edge.weight, strict, Bool.false_eq_true, if_false, Nat.add_zero] at old ⊢
    exact compress_mono r old
  | true =>
    simp only [Edge.weight, strict, if_true] at old ⊢
    exact Nat.succ_le_of_lt (compress_strict r (by omega))

structure State (m : Nat) where
  labels : Labels m
  bounded : ∀ v, labels.get v ≤ m

def measure {m : Nat} (state : State m) : Nat := m*m - mass state.labels

theorem mass_bound {m : Nat} (state : State m) : mass state.labels ≤ m*m := by
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun v _ => state.bounded v)
  simpa [mass] using bound

theorem measure_drops {m : Nat} (edges : List (Edge m)) (state : State m)
    (invalid : ¬ Valid edges state.labels) (bounded : ∀ v, (relax edges state.labels).get v ≤ m) :
    measure (⟨relax edges state.labels, bounded⟩ : State m) < measure state := by
  have grows := mass_relax_lt edges state.labels invalid
  have bound := mass_bound (⟨relax edges state.labels, bounded⟩ : State m)
  change mass (relax edges state.labels) ≤ m*m at bound
  simp only [measure]
  change m*m - mass (relax edges state.labels) < m*m - mass state.labels
  omega

def solver {m : Nat} (edges : List (Edge m)) : MeasuredLoop (State m) (Option (Labels m)) where
  measure := measure
  step state :=
    if valid : Valid edges state.labels then .inr (some state.labels)
    else if bounded : ∀ v, (relax edges state.labels).get v ≤ m then
      .inl ⟨⟨relax edges state.labels, bounded⟩, measure_drops edges state valid bounded⟩
    else .inr none

def initial (m : Nat) : State m := ⟨List.Vector.ofFn (fun _ => 0), by simp⟩

def find {m : Nat} (edges : List (Edge m)) : Option (Labels m) := (solver edges).run (initial m)

theorem find_sound {m : Nat} (edges : List (Edge m)) {r : Labels m} (found : find edges = some r) :
    Valid edges r := by
  have result := (solver edges).run_induction
    (fun state => ∀ v, state.labels.get v ≤ m)
    (fun output => ∀ r, output = some r → Valid edges r)
    (fun _ next _ _ _ => next.bounded)
    (by
      intro state output _ step
      by_cases valid : Valid edges state.labels
      · simp only [solver, dif_pos valid] at step
        cases step
        intro r equal
        cases equal
        exact valid
      · by_cases bounded : ∀ v, (relax edges state.labels).get v ≤ m
        · simp only [solver, dif_neg valid, dif_pos bounded] at step
          cases step
        · simp only [solver, dif_neg valid, dif_neg bounded] at step
          cases step
          intro r equal
          cases equal)
    (initial m) (initial m).bounded
  exact result r found

theorem find_complete_bounded {m : Nat} (edges : List (Edge m)) (solution : Labels m)
    (valid : Valid edges solution) (bounded : ∀ v, solution.get v ≤ m) :
    (find edges).isSome = true := by
  apply (solver edges).run_induction
    (fun state => ∀ v, state.labels.get v ≤ solution.get v)
    (fun output => output.isSome = true)
  · intro state next decrease below step
    by_cases current : Valid edges state.labels
    · simp only [solver, dif_pos current] at step
      cases step
    · by_cases nextBound : ∀ v, (relax edges state.labels).get v ≤ m
      · simp only [solver, dif_neg current, dif_pos nextBound] at step
        cases step
        exact relax_le_solution edges state.labels solution valid below
      · simp only [solver, dif_neg current, dif_neg nextBound] at step
        cases step
  · intro state output below step
    by_cases current : Valid edges state.labels
    · simp only [solver, dif_pos current] at step
      cases step
      rfl
    · have nextBound : ∀ v, (relax edges state.labels).get v ≤ m :=
        fun v => (relax_le_solution edges state.labels solution valid below v).trans (bounded v)
      simp only [solver, dif_neg current, dif_pos nextBound] at step
      cases step
  · simp [initial]

theorem find_isSome_iff {m : Nat} (edges : List (Edge m)) :
    (find edges).isSome ↔ ∃ r, Valid edges r := by
  constructor
  · intro present
    cases found : find edges with
    | none => simp [found] at present
    | some r => exact ⟨r, find_sound edges found⟩
  · rintro ⟨r, valid⟩
    exact find_complete_bounded edges (compress r) (compress_valid edges r valid) (compress_bounded r)

end RankSolver

local instance : DecidableEq (GoalLit σ)
  | .pos a, .pos b => decidable_of_iff (a = b) (by simp)
  | .neg a, .neg b => decidable_of_iff (a = b) (by simp)
  | .neq a b, .neq c d => decidable_of_iff (a = c ∧ b = d) (by simp)
  | .pos _, .neg _ | .pos _, .neq _ _ | .neg _, .pos _ | .neg _, .neq _ _ |
      .neq _ _, .pos _ | .neq _ _, .neg _ => isFalse (by intro equal; cases equal)

def signedDependency (rules : List (NormalClause σ)) (body head : GroundAtom σ) (strict : Bool) : Prop :=
  ∃ c ∈ rules, c.head = head ∧ (if strict then GoalLit.neg body else GoalLit.pos body) ∈ c.body

instance signedDependencyDecidable (rules : List (NormalClause σ)) (body head : GroundAtom σ)
    (strict : Bool) : Decidable (signedDependency rules body head strict) := by
  unfold signedDependency
  infer_instance

/-- Materialize exactly the signed edges present in the finite program. -/
def signedEdges (rules : List (NormalClause σ)) : List (RankSolver.Edge (dependencyTable rules).atoms.length) :=
  let atoms := (dependencyTable rules).atoms
  ((List.finRange atoms.length).flatMap fun source =>
    (List.finRange atoms.length).flatMap fun target =>
      [⟨source, target, false⟩, ⟨source, target, true⟩]).filter fun edge =>
        decide (signedDependency rules (atoms.get edge.source) (atoms.get edge.target) edge.strict)

theorem signedEdges_mem (rules : List (NormalClause σ))
    (edge : RankSolver.Edge (dependencyTable rules).atoms.length) :
    edge ∈ signedEdges rules ↔ signedDependency rules
      ((dependencyTable rules).atoms.get edge.source) ((dependencyTable rules).atoms.get edge.target) edge.strict := by
  obtain ⟨source, target, strict⟩ := edge
  cases strict <;> simp [signedEdges]

/-- Extend finite labels by zero outside the dependency table. -/
def readLabels (rules : List (NormalClause σ)) (labels : RankSolver.Labels (dependencyTable rules).atoms.length) :
    Stratification σ := fun a =>
  if member : a ∈ (dependencyTable rules).atoms then labels.get ((dependencyTable rules).index a member) else 0

@[simp] theorem readLabels_index (rules : List (NormalClause σ))
    (labels : RankSolver.Labels (dependencyTable rules).atoms.length) (a : GroundAtom σ)
    (member : a ∈ (dependencyTable rules).atoms) :
    readLabels rules labels a = labels.get ((dependencyTable rules).index a member) := by
  rw [readLabels, dif_pos member]

@[simp] theorem readLabels_at (rules : List (NormalClause σ))
    (labels : RankSolver.Labels (dependencyTable rules).atoms.length) (i : Fin (dependencyTable rules).atoms.length) :
    readLabels rules labels ((dependencyTable rules).atoms.get i) = labels.get i := by
  rw [readLabels_index _ _ _ (List.get_mem _ _), AtomTable.index_at]

theorem signedEdges_valid (rules : List (NormalClause σ))
    (labels : RankSolver.Labels (dependencyTable rules).atoms.length) :
    RankSolver.Valid (signedEdges rules) labels ↔ ∀ c ∈ rules, respectsStratification c (readLabels rules labels) := by
  constructor
  · intro valid c member g body
    cases g with
    | pos a =>
      have atom := body_mem_table member body (a := a) (by simp [goalAtoms])
      let edge : RankSolver.Edge (dependencyTable rules).atoms.length :=
        ⟨(dependencyTable rules).index a atom, (dependencyTable rules).index c.head (head_mem_table member), false⟩
      have present : edge ∈ signedEdges rules := by
        rw [signedEdges_mem]
        simp only [edge, AtomTable.at_index, signedDependency, Bool.false_eq_true, if_false]
        exact ⟨c, member, rfl, body⟩
      have bound := valid edge present
      simpa only [edge, RankSolver.Edge.weight, Bool.false_eq_true, if_false, Nat.add_zero,
        readLabels_index _ _ _ atom, readLabels_index _ _ _ (head_mem_table member)] using bound
    | neg a =>
      have atom := body_mem_table member body (a := a) (by simp [goalAtoms])
      let edge : RankSolver.Edge (dependencyTable rules).atoms.length :=
        ⟨(dependencyTable rules).index a atom, (dependencyTable rules).index c.head (head_mem_table member), true⟩
      have present : edge ∈ signedEdges rules := by
        rw [signedEdges_mem]
        simp only [edge, AtomTable.at_index, signedDependency, if_true]
        exact ⟨c, member, rfl, body⟩
      have bound := valid edge present
      simpa only [edge, RankSolver.Edge.weight, if_true, Nat.succ_le_iff,
        readLabels_index _ _ _ atom, readLabels_index _ _ _ (head_mem_table member)] using bound
    | neq _ _ => trivial
  · intro valid edge member
    obtain ⟨c, hc, head, body⟩ := (signedEdges_mem rules edge).mp member
    have bound := valid c hc _ body
    rw [head] at bound
    cases strict : edge.strict <;>
      simpa only [strict, Bool.false_eq_true, if_false, if_true, RankSolver.Edge.weight,
        readLabels_at, Nat.add_zero, Nat.succ_le_iff] using bound

def restrictStrata (rules : List (NormalClause σ)) (s : Stratification σ) :
    RankSolver.Labels (dependencyTable rules).atoms.length :=
  List.Vector.ofFn fun i => s ((dependencyTable rules).atoms.get i)

theorem restrictStrata_valid (rules : List (NormalClause σ)) (s : Stratification σ)
    (valid : ∀ c ∈ rules, respectsStratification c s) :
    RankSolver.Valid (signedEdges rules) (restrictStrata rules s) := by
  intro edge member
  obtain ⟨c, hc, head, body⟩ := (signedEdges_mem rules edge).mp member
  have bound := valid c hc _ body
  rw [head] at bound
  cases strict : edge.strict <;>
    simpa only [strict, Bool.false_eq_true, if_false, if_true, RankSolver.Edge.weight,
      restrictStrata, List.Vector.get_ofFn, Nat.add_zero, Nat.succ_le_iff] using bound

/-- Propagate signed dependencies, then independently check the resulting strata. -/
def findStratification (rules : List (NormalClause σ)) : Option (StratificationCertificate rules) :=
  match RankSolver.find (signedEdges rules) with
  | none => none
  | some labels =>
    let strata := readLabels rules labels
    if checked : checkStratification rules strata = true then
      some ⟨strata, (checkStratification_correct rules strata).mp checked⟩
    else none

theorem findStratification_isSome (rules : List (NormalClause σ)) :
    (findStratification rules).isSome ↔ isStratifiable rules := by
  have same : (findStratification rules).isSome = (RankSolver.find (signedEdges rules)).isSome := by
    cases found : RankSolver.find (signedEdges rules) with
    | none => simp [findStratification, found]
    | some labels =>
      have checked := (checkStratification_correct rules _).mpr
        ((signedEdges_valid rules labels).mp (RankSolver.find_sound (signedEdges rules) found))
      simp [findStratification, found, checked]
  rw [same, RankSolver.find_isSome_iff]
  constructor
  · rintro ⟨labels, valid⟩
    exact ⟨readLabels rules labels, (signedEdges_valid rules labels).mp valid⟩
  · rintro ⟨s, valid⟩
    exact ⟨restrictStrata rules s, restrictStrata_valid rules s valid⟩

end Mettapedia.Logic.NormalProgramCertificates
