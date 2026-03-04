import Mettapedia.CategoryTheory.GeneralizedOpenMaps
import Mettapedia.Logic.OSLFDistinctionGraph

/-!
# OSLF ↔ Generalized Open-Map Bridge

Connects generalized open-map witnesses to existing OSLF bisimulation and
distinction-graph theorems.
-/

namespace Mettapedia.Logic.OSLFOpenMapBridge

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.Logic.OSLFKSUnificationSketch
open Mettapedia.Logic.OSLFDistinctionGraph

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- OSLF instantiation of the generalized open-map kit for a fixed step relation
and atom semantics. -/
def OSLFInst (R : Pat → Pat → Prop) (I : Mettapedia.OSLF.Formula.AtomSem) :
    BisimulationKit Pat String where
  step := R
  stepStar := R
  step_sub_star := by
    intro _ _ h
    exact h
  observable := fun p a => I a p

private theorem pathWitness_stepBisimulation
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : PathWitness (OSLFInst R I)) :
    StepBisimulation R w.rel := by
  constructor
  · intro p q hpq p' hpp'
    obtain ⟨q', hqq', hp'q'⟩ := w.lift hpq hpp'
    exact ⟨q', hqq', hp'q'⟩
  · intro p q hpq q' hqq'
    have hqp : w.rel q p := w.symm hpq
    obtain ⟨p', hpp', hq'p'⟩ := w.lift hqp hqq'
    exact ⟨p', hpp', w.symm hq'p'⟩

/-- One-direction generalized open-map path bisim gives OSLF `Bisimilar`. -/
theorem pathBisim_implies_bisimilar
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem} {p q : Pat} :
    PathBisim (OSLFInst R I) p q → Bisimilar R p q := by
  rintro ⟨w, hpq⟩
  exact ⟨w.rel, pathWitness_stepBisimulation w, hpq⟩

/-- Two-direction generalized open-map witness for full OSLF modal invariance
(`◇` and `□` sides). -/
structure FullOpenWitness (R : Pat → Pat → Prop) (I : Mettapedia.OSLF.Formula.AtomSem) where
  rel : Pat → Pat → Prop
  symm : ∀ ⦃p q : Pat⦄, rel p q → rel q p
  open_fwd : GOpen (OSLFInst R I) rel
  open_rev : GOpen (OSLFInst (fun a b => R b a) I) rel
  atom : ObsPreserving (OSLFInst R I) rel

private theorem fullOpenWitness_fullBisimilar
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem} (w : FullOpenWitness R I) {p q : Pat}
    (hpq : w.rel p q) : FullBisimilar R I p q := by
  refine ⟨w.rel, ?_, ?_, ?_, hpq⟩
  · constructor
    · intro a b hab a' haa'
      obtain ⟨b', hbb', ha'b'⟩ := w.open_fwd hab haa'
      exact ⟨b', hbb', ha'b'⟩
    · intro a b hab b' hbb'
      have hba : w.rel b a := w.symm hab
      obtain ⟨a', haa', hb'a'⟩ := w.open_fwd hba hbb'
      exact ⟨a', haa', w.symm hb'a'⟩
  · constructor
    · intro a b hab a' haa'
      obtain ⟨b', hbb', ha'b'⟩ := w.open_rev hab haa'
      exact ⟨b', hbb', ha'b'⟩
    · intro a b hab b' hbb'
      have hba : w.rel b a := w.symm hab
      obtain ⟨a', haa', hb'a'⟩ := w.open_rev hba hbb'
      exact ⟨a', haa', w.symm hb'a'⟩
  · intro atom p' q' hp'q'
    constructor
    · intro hpAtom
      exact w.atom hp'q' atom hpAtom
    · intro hqAtom
      have hqp : w.rel q' p' := w.symm hp'q'
      exact w.atom hqp atom hqAtom

/-- Full generalized open-map witness implies OSLF observational equivalence. -/
theorem fullOpenWitness_implies_obsEq
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    OSLFObsEq R I p q :=
  fullBisim_implies_indist (fullOpenWitness_fullBisimilar w hpq)

/-- Distinction-graph compatibility: full open-map witness implies indistinguishability. -/
theorem fullOpenWitness_implies_indistObs
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    indistObs R I p q :=
  fullOpenWitness_implies_obsEq w hpq

theorem fullOpenWitness_not_distinguished
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    ¬ distinguished R I p q := by
  intro hdist
  exact hdist (fullOpenWitness_implies_indistObs w hpq)

end Mettapedia.Logic.OSLFOpenMapBridge
