import Mettapedia.SetTheory.AntiFoundation.Core
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph

/-!
# One labelled consumer

Five processes. Two are loops labelled `a`, one is a loop labelled `b`, and
two form a cycle labelled `a` on both steps. Unlabelled bisimilarity identifies
all five: it forgets the label. Labelled bisimilarity keeps `a` apart from `b`
and identifies the two `a`-loops with each other and with the cycle. The first
label respects the labelled relation and does not respect the unlabelled one.

A Boffa-style observer that sends the two `a`-loops to different atoms does not
respect labelled bisimilarity. Labelled processes ask for the labelled
relation, not for Boffa's. Unlabelled bisimilarity of accessible pointed graphs
also forgets multiplicity: two edges to a childless node match one edge.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.GSLT.QuotientObservers
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open AccessiblePointedGraph

inductive Lab where
  | a
  | b
  deriving DecidableEq

inductive Proc where
  | loopA
  | loopA2
  | loopB
  | cycL
  | cycR
  deriving DecidableEq

def step : Proc → Lab → Proc → Prop
  | .loopA, .a, .loopA => True
  | .loopA2, .a, .loopA2 => True
  | .loopB, .b, .loopB => True
  | .cycL, .a, .cycR => True
  | .cycR, .a, .cycL => True
  | _, _, _ => False

def next : Proc → Lab × Proc
  | .loopA => (.a, .loopA)
  | .loopA2 => (.a, .loopA2)
  | .loopB => (.b, .loopB)
  | .cycL => (.a, .cycR)
  | .cycR => (.a, .cycL)

theorem step_iff (p : Proc) (lab : Lab) (q : Proc) : step p lab q ↔ next p = (lab, q) := by
  cases p <;> cases lab <;> cases q <;> constructor <;> intro h <;>
    first | rfl | exact trivial | exact h.elim | cases h

def ustep (p q : Proc) : Prop := ∃ lab, step p lab q

def firstLabel : Proc → Lab
  | .loopB => .b
  | _ => .a

theorem firstLabel_next (p : Proc) : (next p).1 = firstLabel p := by
  cases p <;> rfl

theorem ustep_next (p : Proc) : ustep p (next p).2 :=
  ⟨(next p).1, (step_iff p (next p).1 (next p).2).mpr rfl⟩

theorem unlabelled_total : IsBisimulation ustep ustep (fun _ _ => True) := by
  intro a b _
  constructor
  · intro _ _
    exact ⟨(next b).2, ustep_next b, trivial⟩
  · intro _ _
    exact ⟨(next a).2, ustep_next a, trivial⟩

def sameA : Proc → Proc → Prop
  | .loopA, .loopA => True
  | .loopA, .loopA2 => True
  | .loopA, .cycL => True
  | .loopA, .cycR => True
  | .loopA2, .loopA => True
  | .loopA2, .loopA2 => True
  | .loopA2, .cycL => True
  | .loopA2, .cycR => True
  | .cycL, .loopA => True
  | .cycL, .loopA2 => True
  | .cycL, .cycL => True
  | .cycL, .cycR => True
  | .cycR, .loopA => True
  | .cycR, .loopA2 => True
  | .cycR, .cycL => True
  | .cycR, .cycR => True
  | .loopB, .loopB => True
  | _, _ => False

theorem sameA_next (p q : Proc) (h : sameA p q) :
    (next p).1 = (next q).1 ∧ sameA (next p).2 (next q).2 := by
  cases p <;> cases q <;> first | exact ⟨rfl, trivial⟩ | exact h.elim

def IsLabelledBisimulation (R : Proc → Proc → Prop) : Prop :=
  ∀ p q, R p q →
    (∀ lab p', step p lab p' → ∃ q', step q lab q' ∧ R p' q') ∧
    (∀ lab q', step q lab q' → ∃ p', step p lab p' ∧ R p' q')

def LabelledBisimilar (p q : Proc) : Prop :=
  ∃ R, IsLabelledBisimulation R ∧ R p q

theorem sameA_labelled : IsLabelledBisimulation sameA := by
  intro p q h
  obtain ⟨labEq, relNext⟩ := sameA_next p q h
  constructor
  · intro lab p' hp
    have hn : next p = (lab, p') := (step_iff p lab p').mp hp
    have hfst : (next p).1 = lab := congrArg Prod.fst hn
    have hsnd : (next p).2 = p' := congrArg Prod.snd hn
    refine ⟨(next q).2, ?_, ?_⟩
    · exact (step_iff q lab (next q).2).mpr (Prod.ext (labEq.symm.trans hfst) rfl)
    · exact hsnd ▸ relNext
  · intro lab q' hq
    have hn : next q = (lab, q') := (step_iff q lab q').mp hq
    have hfst : (next q).1 = lab := congrArg Prod.fst hn
    have hsnd : (next q).2 = q' := congrArg Prod.snd hn
    refine ⟨(next p).2, ?_, ?_⟩
    · exact (step_iff p lab (next p).2).mpr (Prod.ext (labEq.trans hfst) rfl)
    · exact hsnd.symm ▸ relNext

theorem step_label (p : Proc) (lab : Lab) (q : Proc) (h : step p lab q) :
    lab = firstLabel p :=
  (congrArg Prod.fst ((step_iff p lab q).mp h)).symm.trans (firstLabel_next p)

theorem label_respects_labelled : Respects LabelledBisimilar firstLabel := by
  intro p q ⟨R, hR, h⟩
  have stepP : step p (firstLabel p) (next p).2 :=
    (step_iff p (firstLabel p) (next p).2).mpr (Prod.ext (firstLabel_next p) rfl)
  obtain ⟨q', hq, _⟩ := (hR p q h).1 (firstLabel p) (next p).2 stepP
  exact step_label q (firstLabel p) q' hq

theorem label_not_respects_unlabelled :
    ¬ Respects (Bisimilar ustep ustep) firstLabel := by
  intro h
  cases h .loopA .loopB (unlabelled_total.bisimilar trivial)

/-- Unlabelled collapse: every process denotes the same point. -/
def unlabelledView : Proc → Unit := fun _ => ()

/-- The labelled view is the first label. -/
def labelledView : Proc → Lab := firstLabel

inductive ProcAtom where
  | one
  | two
  deriving DecidableEq

/-- A Boffa-style name: the two `a`-loops are different atoms. -/
def bafaProc : Proc → ProcAtom
  | .loopA2 => .two
  | .cycR => .two
  | _ => .one

theorem loopA_labelled_loopA2 : LabelledBisimilar .loopA .loopA2 :=
  ⟨sameA, sameA_labelled, trivial⟩

theorem bafa_not_respects_labelled : ¬ Respects LabelledBisimilar bafaProc := by
  intro h
  cases h .loopA .loopA2 loopA_labelled_loopA2

def label_fiber : NonTrivialFiber unlabelledView firstLabel where
  left := .loopA
  right := .loopB
  sameShadow := rfl
  differentValue := by intro h; cases h

theorem not_factors_label_unlabelled : ¬ Factors unlabelledView firstLabel :=
  label_fiber.not_factors

theorem factors_label_labelled : Factors labelledView firstLabel :=
  ⟨id, fun _ => rfl⟩

def bafa_fiber : NonTrivialFiber labelledView bafaProc where
  left := .loopA
  right := .loopA2
  sameShadow := rfl
  differentValue := by intro h; cases h

theorem not_factors_bafa_labelled : ¬ Factors labelledView bafaProc :=
  bafa_fiber.not_factors

/-- Unlabelled bisimilarity identifies two edges to a childless node with one edge. -/
theorem unlabelled_forgets_multiplicity.{u} :
    sup (fun _ : ULift.{u} Bool => empty.{u}) ≈
      sup (fun _ : PUnit.{u + 1} => empty.{u}) :=
  sup_bool_equiv_sup_unit

end Mettapedia.SetTheory.AntiFoundation
