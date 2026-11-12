import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Interchange

/-!
# Models that respect interchange

A proof-relevant model receives exactly one map from the witnessed runs (`paths_initial`). This
module says when that map is constant along interchange cells.

* `RespectsSwaps`: a model **respects swaps** when, at every state, the two witnessed runs of an
  independent pair, one in each order, have one interpretation.
* `interp_cell`: **a model that respects swaps gives one interpretation to any two witnessed runs
  joined by a cell.** So it factors through the runs modulo the cells, the trace category; the
  generating swaps are enough.
* `weights_respectSwaps`: a commutative monoid of weights respects swaps. The free monoid does not
  (`InterchangeControls.free_weights_separate`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

open Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule uM

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  {sys : System K Atom Rule}

/-- A model **respects swaps** when the two orders of an independent pair, at any state, have one
interpretation. -/
def RespectsSwaps (M : RelevantModel.{uK, uAtom, uRule, uM} sys) : Prop :=
  ∀ {k k' : K} {Γ Γ' : Multiset Atom} {a b : Rule} (p q : Path sys k Γ k' Γ'),
    p.uses = [a, b] → q.uses = [b, a] → sys.Independent a b k Γ → interp M p = interp M q

section Split

variable [DecidableEq Atom]

/-- A witnessed run whose word is a concatenation is the cut of the witnessed runs of the parts. -/
theorem Path.split {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ') (first second : List Rule)
    (shape : p.uses = first ++ second) :
    ∃ (k₁ : K) (Γ₁ : Multiset Atom) (one : Path sys k Γ k₁ Γ₁) (two : Path sys k₁ Γ₁ k' Γ'),
      one.uses = first ∧ two.uses = second ∧ p = Path.cut one two := by
  have run := p.run
  rw [shape] at run
  obtain ⟨k₁, Γ₁, early, late⟩ := System.Run.split first run
  refine ⟨k₁, Γ₁, Path.ofRun first early, Path.ofRun second late, Path.uses_ofRun _ _,
    Path.uses_ofRun _ _, Path.eq_of_uses _ _ ?_⟩
  rw [Path.uses_cut, Path.uses_ofRun, Path.uses_ofRun, shape]

/-- **A model that respects swaps gives one interpretation to witnessed runs joined by a cell.** -/
theorem interp_cell (M : RelevantModel.{uK, uAtom, uRule, uM} sys) (respects : RespectsSwaps M)
    {k : K} {Γ : Multiset Atom} {w w' : List Rule} (cell : Cell sys (k, Γ) w w') :
    ∀ {k' : K} {Γ' : Multiset Atom} (p q : Path sys k Γ k' Γ'), p.uses = w → q.uses = w' →
      interp M p = interp M q := by
  induction cell with
  | refl w =>
      intro k' Γ' p q hp hq
      rw [Path.eq_of_uses p q (hp.trans hq.symm)]
  | swap before mid a b after reach admissible rest ih =>
      intro k' Γ' p q hp hq
      obtain ⟨k₁, Γ₁, head, tail, headUses, tailUses, rfl⟩ :=
        Path.split p before (a :: b :: after) hp
      obtain ⟨k₂, Γ₂, pair, last, pairUses, lastUses, rfl⟩ :=
        Path.split tail [a, b] after tailUses
      have headRun : Runs (fires sys) (k, Γ) before (k₁, Γ₁) := by
        have inner := head.run
        rw [headUses] at inner
        exact runs_iff_run.mpr inner
      have here : mid = (k₁, Γ₁) :=
        Runs.unique (step := fires sys) fires_deterministic reach headRun
      subst here
      have independent' : sys.Independent a b k₁ Γ₁ := admissible
      obtain ⟨k₃, Γ₃, straight, swapped⟩ := System.Independent.diamond independent'
      have pairRun : sys.Run k₁ Γ₁ [a, b] k₂ Γ₂ := by
        have inner := pair.run
        rw [pairUses] at inner
        exact inner
      obtain ⟨rfl, rfl⟩ := System.Run.deterministic straight pairRun
      have crossedUses : (Path.ofRun [b, a] swapped).uses = [b, a] := Path.uses_ofRun _ _
      have local' : interp M pair = interp M (Path.ofRun [b, a] swapped) :=
        respects pair (Path.ofRun [b, a] swapped) pairUses crossedUses independent'
      have moved : interp M (Path.cut head (Path.cut pair last)) =
          interp M (Path.cut head (Path.cut (Path.ofRun [b, a] swapped) last)) := by
        rw [interp_cut, interp_cut, interp_cut, interp_cut, local']
      rw [moved]
      refine ih _ q ?_ hq
      rw [Path.uses_cut, Path.uses_cut, headUses, crossedUses, lastUses]
      rfl

end Split

/-- **A commutative monoid of weights respects swaps.** -/
theorem weights_respectSwaps {N : Type uM} [CommMonoid N] (weight : Rule → N) :
    RespectsSwaps (weights (sys := sys) N weight) := by
  intro k k' Γ Γ' a b p q hp hq _
  rw [interp_weights, interp_weights, hp, hq]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact mul_comm _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
