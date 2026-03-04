import Mathlib.Logic.Relation

/-!
# Generalized Open Maps (Minimal Core)

Minimal, implementation-oriented core for generalized open-map style reasoning.
The design is intentionally light: we expose a path-style bisimulation interface
that can be instantiated by existing process-calculus and OSLF relations.
-/

namespace Mettapedia.CategoryTheory.GeneralizedOpenMaps

universe u v

/-- Operational kit used by generalized open-map style definitions. -/
structure BisimulationKit (α : Type u) (Obs : Type v) where
  /-- One-step transition relation. -/
  step : α → α → Prop
  /-- Saturated/weak transition relation. -/
  stepStar : α → α → Prop
  /-- Every one-step transition is a saturated transition. -/
  step_sub_star : ∀ {x y : α}, step x y → stepStar x y
  /-- Observable predicate family. -/
  observable : α → Obs → Prop

section CoreDefs

variable {α : Type u} {Obs : Type v} (K : BisimulationKit α Obs)

/-- A run is a source/target pair justified by saturated reachability. -/
structure Run (K : BisimulationKit α Obs) where
  src : α
  dst : α
  reaches : K.stepStar src dst

/-- Extension of runs: same source, larger saturated target. -/
def Extension (r r' : Run K) : Prop :=
  r.src = r'.src ∧ K.stepStar r.dst r'.dst

/-- Generalized-open lifting for a relation witness. -/
def GOpen (R : α → α → Prop) : Prop :=
  ∀ ⦃p q : α⦄, R p q → ∀ ⦃p' : α⦄, K.step p p' →
    ∃ q' : α, K.stepStar q q' ∧ R p' q'

/-- Strong (non-saturated) open lifting for a relation witness. -/
def GOpenStrong (R : α → α → Prop) : Prop :=
  ∀ ⦃p q : α⦄, R p q → ∀ ⦃p' : α⦄, K.step p p' →
    ∃ q' : α, K.step q q' ∧ R p' q'

/-- Observable preservation along a relation witness. -/
def ObsPreserving (R : α → α → Prop) : Prop :=
  ∀ ⦃p q : α⦄, R p q → ∀ o : Obs, K.observable p o → K.observable q o

/-- Path-bisimulation witness: symmetry + weak/open lifting + observables. -/
structure PathWitness where
  rel : α → α → Prop
  symm : ∀ ⦃p q : α⦄, rel p q → rel q p
  lift : GOpen K rel
  obs : ObsPreserving K rel

/-- Strong-path witness: symmetry + strong/open lifting + observables. -/
structure StrongPathWitness where
  rel : α → α → Prop
  symm : ∀ ⦃p q : α⦄, rel p q → rel q p
  lift : GOpenStrong K rel
  obs : ObsPreserving K rel

/-- Existence form of path bisimilarity. -/
def PathBisim (p q : α) : Prop :=
  ∃ w : PathWitness K, w.rel p q

/-- Existence form of strong-path bisimilarity. -/
def StrongPathBisim (p q : α) : Prop :=
  ∃ w : StrongPathWitness K, w.rel p q

/-- Explicit "(E,S)-bisimilarity via span witness". In this minimal core it is
representation-equivalent to `PathBisim`. -/
structure GOpenSpanWitness where
  rel : α → α → Prop
  symm : ∀ ⦃p q : α⦄, rel p q → rel q p
  left_open : GOpen K rel
  left_obs : ObsPreserving K rel

/-- "(E,S)-bisimilarity" as a rooted span witness. -/
def ESBisimilar (p q : α) : Prop :=
  ∃ w : GOpenSpanWitness K, w.rel p q

end CoreDefs

section CoreLemmas

variable {α : Type u} {Obs : Type v} {K : BisimulationKit α Obs}

theorem PathWitness.open_symm (w : PathWitness K) :
    GOpen K (fun p q => w.rel q p) := by
  intro p q hpq p' hstep
  have hpq' : w.rel p q := w.symm hpq
  obtain ⟨q', hq', hp'q'⟩ := w.lift hpq' hstep
  exact ⟨q', hq', w.symm hp'q'⟩

theorem PathWitness.obs_symm (w : PathWitness K) :
    ObsPreserving K (fun p q => w.rel q p) := by
  intro p q hpq o hObs
  have hpq' : w.rel p q := w.symm hpq
  have hObs' : K.observable q o := w.obs hpq' o hObs
  exact hObs'

def PathWitness.toSpan (w : PathWitness K) : GOpenSpanWitness K :=
  { rel := w.rel
    symm := w.symm
    left_open := w.lift
    left_obs := w.obs }

def GOpenSpanWitness.toPath (w : GOpenSpanWitness K) : PathWitness K :=
  { rel := w.rel
    symm := w.symm
    lift := w.left_open
    obs := w.left_obs }

theorem pathBisim_iff_esBisimilar (K : BisimulationKit α Obs) (p q : α) :
    PathBisim K p q ↔ ESBisimilar K p q := by
  constructor
  · rintro ⟨w, hpq⟩
    exact ⟨w.toSpan, hpq⟩
  · rintro ⟨w, hpq⟩
    exact ⟨w.toPath, hpq⟩

theorem strongPathBisim_implies_pathBisim (K : BisimulationKit α Obs) {p q : α} :
    StrongPathBisim K p q → PathBisim K p q := by
  rintro ⟨w, hpq⟩
  refine ⟨{ rel := w.rel, symm := w.symm, lift := ?_, obs := w.obs }, hpq⟩
  intro a b hab a' hstep
  obtain ⟨b', hb', ha'b'⟩ := w.lift hab hstep
  exact ⟨b', K.step_sub_star hb', ha'b'⟩

end CoreLemmas

end Mettapedia.CategoryTheory.GeneralizedOpenMaps
