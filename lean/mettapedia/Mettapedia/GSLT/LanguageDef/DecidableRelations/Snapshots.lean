import Mettapedia.GSLT.LanguageDef.DecidableRelations.Core
import Mettapedia.KR.ConceptOntology.ConstructionBase

/-!
# Snapshots: closed-world verdicts and "that's all"

A store at a snapshot holds the phenomena visible from one vantage of a construction base
(`KR.ConceptOntology.ConstructionBase`). Inside the snapshot the world is closed. The universal claim "every visible
phenomenon with the premise's attributes has attribute `a`" is a `forAll` over the store's elements. It is membership
of `a` in the closure computed at the vantage (`forAll_iff_mem_closureAt`). A visible counterexample complements it
(`snapshot_complemented`).

The two verdicts behave differently once the world is read beyond the snapshot:
- **a counterexample persists**: a visible phenomenon that refutes `a` refutes it in the full world
  (`not_mem_fullClosure_of_counterexample`);
- **a universal verdict is provisional**: it holds in the full world exactly where the vantage has reached the full
  closure, `ConstructionBase.thatsAllAt` (`mem_fullClosure_iff_of_thatsAllAt`). Chalmers's scrutability base needs
  its "that's all" clause for the same reason.

"That's all" at a vantage is exactly the condition under which the snapshot's counterexamples certify the complement
of membership in the full closure (`thatsAllAt_iff_full_complemented`). Where it fails, the frontier is nonempty
(`ConstructionBase.openWorldAt_iff_not_thatsAllAt`), and only the counterexamples are final.

`Controls` gives a base where a narrow vantage holds a provisional universal verdict that the full world refutes, and
the full vantage holds "that's all".
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.KR.ConceptOntology

universe u v w

variable (B : ConstructionBase.{u, v, w}) (ι : B.Indexicality) (premise : Set B.Abstract)

/-- A phenomenon has every attribute of the premise. -/
def HasAll (x : B.Phenomena) : Prop := ∀ b ∈ premise, B.incidence x b

/-- **A visible counterexample** to attribute `a`: a phenomenon visible at the vantage with the premise's attributes
and without `a`. -/
def Counterexample (a : B.Abstract) : Prop := ∃ x ∈ B.visibleAt ι, HasAll B premise x ∧ ¬ B.incidence x a

/-- A snapshot lists exactly the phenomena visible at the vantage. -/
def Lists (snapshot : List B.Phenomena) : Prop := ∀ x, x ∈ snapshot ↔ x ∈ B.visibleAt ι

/-- **A universal claim over the snapshot is membership in the closure at the vantage.** -/
theorem forAll_iff_mem_closureAt {snapshot : List B.Phenomena} (listed : Lists B ι snapshot) (a : B.Abstract) :
    (∀ x ∈ snapshot, HasAll B premise x → B.incidence x a) ↔ a ∈ B.closureAt ι premise := by
  rw [B.mem_closureAt_iff]
  constructor
  · intro holds x visible hasAll
    exact holds x ((listed x).mpr visible) (fun b member => hasAll b member)
  · intro holds x member hasAll
    exact holds x ((listed x).mp member) (fun b inPremise => hasAll b inPremise)

/-- **Inside the snapshot the world is closed**: membership in the closure at the vantage is complemented by a visible
counterexample. -/
theorem snapshot_complemented :
    Complemented (fun a => a ∈ B.closureAt ι premise) (Counterexample B ι premise) (fun _ => True) where
  disjoint a _ held failed := by
    obtain ⟨x, visible, hasAll, notA⟩ := failed
    exact notA (((B.mem_closureAt_iff ι premise a).mp held) x visible hasAll)
  exhaustive a _ := by
    by_cases counter : Counterexample B ι premise a
    · exact .inr counter
    · left
      rw [B.mem_closureAt_iff]
      intro x visible hasAll
      by_contra notA
      exact counter ⟨x, visible, hasAll, notA⟩

/-- **A counterexample persists**: a visible phenomenon that refutes `a` refutes it in the full world. -/
theorem not_mem_fullClosure_of_counterexample {a : B.Abstract} (counter : Counterexample B ι premise a) :
    a ∉ B.fullClosure premise := by
  obtain ⟨x, _, hasAll, notA⟩ := counter
  intro member
  exact notA (((B.mem_fullClosure_iff premise a).mp member) x hasAll)

/-- **A universal verdict holds in the full world where "that's all" holds at the vantage.** -/
theorem mem_fullClosure_iff_of_thatsAllAt (all : B.thatsAllAt ι premise) (a : B.Abstract) :
    a ∈ B.fullClosure premise ↔ a ∈ B.closureAt ι premise := by
  rw [ConstructionBase.thatsAllAt] at all
  rw [all]

/-- **"That's all" is exactly what makes the snapshot decide the full world**: it holds at a vantage if and only if
the visible counterexamples complement membership in the full closure. -/
theorem thatsAllAt_iff_full_complemented :
    B.thatsAllAt ι premise ↔
      Complemented (fun a => a ∈ B.fullClosure premise) (Counterexample B ι premise) (fun _ => True) := by
  constructor
  · intro all
    have closed := snapshot_complemented B ι premise
    rw [ConstructionBase.thatsAllAt] at all
    rw [all] at closed
    exact closed
  · intro decided
    apply Set.Subset.antisymm
    · intro a atVantage
      refine (decided.exhaustive a trivial).resolve_right fun counter => ?_
      exact (snapshot_complemented B ι premise).disjoint a trivial atVantage counter
    · exact B.fullClosure_subset_closureAt ι premise

/-! ## Controls -/

namespace Controls

/-- Two phenomena, each with the attribute of its own name; the narrow vantage sees only `true`. -/
def base : ConstructionBase.{0, 0, 0} where
  Phenomena := Bool
  Abstract := Bool
  Indexicality := Bool
  incidence x a := x = a
  visibleAt wide := if wide then Set.univ else {true}

/-- Positive: the narrow vantage holds the universal verdict that everything has attribute `true`. -/
theorem narrow_verdict : (true : base.Abstract) ∈ base.closureAt (false : base.Indexicality) ∅ :=
  (base.mem_closureAt_iff false ∅ true).mpr fun _ visible _ => visible

/-- Negative: the full world refutes it, by the phenomenon the narrow vantage does not see. -/
theorem full_refutes : (true : base.Abstract) ∉ base.fullClosure ∅ := fun member =>
  Bool.false_ne_true ((base.mem_fullClosure_iff ∅ true).mp member (false : base.Phenomena)
    (fun _ inEmpty => by simp at inEmpty))

/-- Negative: "that's all" fails at the narrow vantage. -/
theorem narrow_not_thatsAll : ¬ base.thatsAllAt (false : base.Indexicality) ∅ := fun all =>
  full_refutes ((mem_fullClosure_iff_of_thatsAllAt base false ∅ all true).mpr narrow_verdict)

/-- Positive: "that's all" holds at the full vantage, which sees every phenomenon. -/
theorem wide_thatsAll : base.thatsAllAt (true : base.Indexicality) ∅ := by
  apply Set.Subset.antisymm
  · intro a atVantage
    exact (base.mem_fullClosure_iff ∅ a).mpr fun x hasAll =>
      (base.mem_closureAt_iff true ∅ a).mp atVantage x (Set.mem_univ x) hasAll
  · exact base.fullClosure_subset_closureAt true ∅

/-- Positive: at the full vantage, the counterexample `false` certifies that not everything has attribute `true`. -/
theorem wide_counterexample : Counterexample base (true : base.Indexicality) ∅ (true : base.Abstract) :=
  ⟨(false : base.Phenomena), Set.mem_univ _, fun _ inEmpty => by simp at inEmpty, Bool.false_ne_true⟩

end Controls

end Mettapedia.GSLT.LanguageDef.DecidableRelations
