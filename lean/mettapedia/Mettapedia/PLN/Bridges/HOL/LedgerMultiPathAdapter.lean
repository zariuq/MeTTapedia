import Mathlib.Tactic
import Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency

/-!
# Ledger-backed HOL source supports as multipath source sets

`LedgerBackedTree` carries a finite evidence ledger whose source set is exactly
the `DerivationTree.sourceSupport` of a HOL proof tree.  The first-order
multi-path dependency theorems are stated over `Finset Nat` source indices, so
this module supplies the small adapter: choose an injective source-token code,
read each ledger as a finite set of source IDs, and reuse the proved T-A
source-overlap theorem.
-/

namespace Mettapedia.PLN.Bridges.HOL.LedgerMultiPathAdapter

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidentialLedger
open Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency
open scoped BigOperators ENNReal NNReal

noncomputable section

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

/-- A source-token coding used to feed HOL provenance into the first-order
`Finset Nat` source-overlap API.  Injectivity is required only for reflection
theorems. -/
abbrev SourceCode :=
  DerivationTree.SourceToken (Base := Base) Const → Nat

/-- The finite set of source IDs appearing in a ledger list. -/
def ledgerSourceIds {Source Candidate : Type*}
    (code : Source → Nat) (items : List (SourceItem Source Candidate)) :
    Finset Nat :=
  (items.map (fun item => code item.source)).toFinset

@[simp] theorem mem_ledgerSourceIds {Source Candidate : Type*}
    (code : Source → Nat) (items : List (SourceItem Source Candidate))
    (n : Nat) :
    n ∈ ledgerSourceIds code items ↔
      ∃ item, item ∈ items ∧ code item.source = n := by
  simp [ledgerSourceIds]

/-- The multipath source set extracted from one ledger-backed tree. -/
def ledgerBackedTreeSourceIds
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (code : SourceCode (Base := Base) (Const := Const))
    (x : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) :
    Finset Nat :=
  ledgerSourceIds code x.ledger

theorem mem_ledgerBackedTreeSourceIds_iff
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (code : SourceCode (Base := Base) (Const := Const))
    (x : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)
    (n : Nat) :
    n ∈ ledgerBackedTreeSourceIds code x ↔
      ∃ s ∈ x.tree.sourceSupport, code s = n := by
  constructor
  · intro hn
    rcases (mem_ledgerSourceIds code x.ledger n).mp hn with
      ⟨item, hitem, hcode⟩
    refine ⟨item.source, ?_, hcode⟩
    have hledger : item.source ∈ ledgerSourceSet x.ledger :=
      ⟨item, hitem, rfl⟩
    simpa [x.support_exact] using hledger
  · rintro ⟨s, hs, hcode⟩
    have hledger : s ∈ ledgerSourceSet x.ledger := by
      simpa [x.support_exact] using hs
    rcases hledger with ⟨item, hitem, hsource⟩
    exact (mem_ledgerSourceIds code x.ledger n).mpr
      ⟨item, hitem, by simpa [hsource] using hcode⟩

/-- If two proof trees share a HOL source token, their encoded multipath source
sets overlap at the token's source ID. -/
theorem sourceCode_mem_inter_of_shared_source
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (code : SourceCode (Base := Base) (Const := Const))
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (hx : s ∈ x.tree.sourceSupport) (hy : s ∈ y.tree.sourceSupport) :
    code s ∈ ledgerBackedTreeSourceIds code x ∩
      ledgerBackedTreeSourceIds code y := by
  exact Finset.mem_inter.mpr
    ⟨(mem_ledgerBackedTreeSourceIds_iff code x (code s)).mpr
        ⟨s, hx, rfl⟩,
      (mem_ledgerBackedTreeSourceIds_iff code y (code s)).mpr
        ⟨s, hy, rfl⟩⟩

/-- With an injective source code, encoded overlap reflects an actual shared
HOL source token. -/
theorem shared_source_of_sourceCode_mem_inter
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (code : SourceCode (Base := Base) (Const := Const))
    (hcode : Function.Injective code)
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)
    {n : Nat}
    (hn : n ∈ ledgerBackedTreeSourceIds code x ∩
      ledgerBackedTreeSourceIds code y) :
    ∃ s, s ∈ x.tree.sourceSupport ∧ s ∈ y.tree.sourceSupport ∧ code s = n := by
  rcases Finset.mem_inter.mp hn with ⟨hnx, hny⟩
  rcases (mem_ledgerBackedTreeSourceIds_iff code x n).mp hnx with
    ⟨sx, hsx, hcodex⟩
  rcases (mem_ledgerBackedTreeSourceIds_iff code y n).mp hny with
    ⟨sy, hsy, hcodey⟩
  have hxy : sx = sy := hcode (by rw [hcodex, hcodey])
  refine ⟨sx, hsx, ?_, hcodex⟩
  simpa [hxy] using hsy

/-- Source-disjoint HOL trees become disjoint first-order multipath source
sets under an injective code. -/
theorem ledgerBackedTreeSourceIds_disjoint_of_sourceDisjoint
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (code : SourceCode (Base := Base) (Const := Const))
    (hcode : Function.Injective code)
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)
    (hdisj : DerivationTree.SourceDisjoint x.tree y.tree) :
    Disjoint (ledgerBackedTreeSourceIds code x)
      (ledgerBackedTreeSourceIds code y) := by
  refine Finset.disjoint_left.mpr ?_
  intro n hnx hny
  rcases (mem_ledgerBackedTreeSourceIds_iff code x n).mp hnx with
    ⟨sx, hsx, hcodex⟩
  rcases (mem_ledgerBackedTreeSourceIds_iff code y n).mp hny with
    ⟨sy, hsy, hcodey⟩
  have hxy : sx = sy := hcode (by rw [hcodex, hcodey])
  have hsy' : sx ∈ y.tree.sourceSupport := by
    simpa [hxy] using hsy
  exact (Set.disjoint_left.mp hdisj hsx) hsy'

/-- The T-A dependency parameter induced by two ledger-backed HOL derivations:
the measured intersection of their encoded source events. -/
def ledgerBackedTreeDependencyParameter
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (p : Nat → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (code : SourceCode (Base := Base) (Const := Const))
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) : ℝ :=
  (infiniteFactMeasure p hp).real
    (sourceEvent (ledgerBackedTreeSourceIds code x) ∩
      sourceEvent (ledgerBackedTreeSourceIds code y))

theorem ledgerBackedTree_dependencyParameter_eq_overlapProduct
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (p : Nat → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (code : SourceCode (Base := Base) (Const := Const))
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) :
    ledgerBackedTreeDependencyParameter p hp code x y =
      ∏ s ∈ ledgerBackedTreeSourceIds code x ∪
          ledgerBackedTreeSourceIds code y,
        ((p s : ℝ≥0) : ℝ) := by
  unfold ledgerBackedTreeDependencyParameter
  rw [sourcePair_intersection_measureReal]

/-- The ledger-backed HOL source readout instantiates the T-A two-path union
equation: the union score subtracts the measured dependency parameter computed
from the encoded ledger supports. -/
theorem ledgerBackedTree_unionMeasure_eq_add_sub_dependency
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (p : Nat → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (code : SourceCode (Base := Base) (Const := Const))
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) :
    (infiniteFactMeasure p hp).real
        (sourceEvent (ledgerBackedTreeSourceIds code x) ∪
          sourceEvent (ledgerBackedTreeSourceIds code y)) =
      (infiniteFactMeasure p hp).real
          (sourceEvent (ledgerBackedTreeSourceIds code x)) +
        (infiniteFactMeasure p hp).real
          (sourceEvent (ledgerBackedTreeSourceIds code y)) -
          ledgerBackedTreeDependencyParameter p hp code x y := by
  rw [sourcePair_union_eq_add_sub_intersection]
  rfl

theorem ledgerBackedTree_unionMeasure_eq_add_sub_overlapProduct
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (p : Nat → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (code : SourceCode (Base := Base) (Const := Const))
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) :
    (infiniteFactMeasure p hp).real
        (sourceEvent (ledgerBackedTreeSourceIds code x) ∪
          sourceEvent (ledgerBackedTreeSourceIds code y)) =
      (infiniteFactMeasure p hp).real
          (sourceEvent (ledgerBackedTreeSourceIds code x)) +
        (infiniteFactMeasure p hp).real
          (sourceEvent (ledgerBackedTreeSourceIds code y)) -
          (∏ s ∈ ledgerBackedTreeSourceIds code x ∪
              ledgerBackedTreeSourceIds code y,
            ((p s : ℝ≥0) : ℝ)) := by
  rw [ledgerBackedTree_unionMeasure_eq_add_sub_dependency,
    ledgerBackedTree_dependencyParameter_eq_overlapProduct]

end

end Mettapedia.PLN.Bridges.HOL.LedgerMultiPathAdapter
