import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.DistinctionGraph

/-!
# Simulation Maps Preserve Modal Semantics

Proves that maps between reduction systems which respect the transition
structure also preserve the OSLF modal semantics:

- **Forward simulation** preserves the positive fragment (atoms, top, bot,
  and, or, diamond) in one direction.
- **Bisimulation maps** preserve the full formula language (all connectives
  including implication and box) as an iff.

## Key Theorems

- `forward_sim_preserves_positive` : forward simulation + atom preservation
    implies `sem R₁ I₁ φ p → sem R₂ I₂ φ (f p)` for positive φ
- `bisimulation_map_preserves_sem` : bisimulation map implies
    `sem R₁ I₁ φ p ↔ sem R₂ I₂ φ (f p)` for all φ
- `bisimulation_map_preserves_indistObs` : bisimulation map preserves
    observational equivalence

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
- van Glabbeek, "The Linear Time – Branching Time Spectrum"
-/

namespace Mettapedia.OSLF.Framework.SimulationPreservation

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DistinctionGraph
open Mettapedia.OSLF.Framework.KSUnificationSketch

/-! ## Simulation Map Structures -/

/-- A forward simulation map from reduction system (R₁, I₁) to (R₂, I₂).

    Maps states via `f : Pattern → Pattern` such that:
    - every R₁-step lifts to an R₂-step on the images
    - atom satisfaction is preserved forward -/
structure ForwardSimulationMap
    (R₁ R₂ : Pattern → Pattern → Prop) (I₁ I₂ : AtomSem) where
  /-- The underlying state map. -/
  f : Pattern → Pattern
  /-- Forward simulation: R₁-steps lift to R₂-steps. -/
  forward : ∀ p p', R₁ p p' → R₂ (f p) (f p')
  /-- Atom preservation (forward direction). -/
  atoms : ∀ a p, I₁ a p → I₂ a (f p)

/-- A bisimulation map from (R₁, I₁) to (R₂, I₂): both forward and backward
    simulation conditions hold, sufficient for full formula preservation.

    - `forward`: R₁-steps lift to R₂-steps
    - `backward_succ`: every R₂-successor of `f p` is the image of some
      R₁-successor of `p`
    - `backward_pred`: every R₂-predecessor of `f p` is the image of some
      R₁-predecessor of `p`
    - `atoms`: atom satisfaction is preserved as an iff -/
structure BisimulationMap
    (R₁ R₂ : Pattern → Pattern → Prop) (I₁ I₂ : AtomSem) where
  /-- The underlying state map. -/
  f : Pattern → Pattern
  /-- Forward simulation: R₁-steps lift to R₂-steps. -/
  forward : ∀ p p', R₁ p p' → R₂ (f p) (f p')
  /-- Backward on successors: every R₂-successor of f(p) is the image of
      an R₁-successor of p. Needed for ◇ backward direction. -/
  backward_succ : ∀ p q₂, R₂ (f p) q₂ → ∃ q₁, R₁ p q₁ ∧ f q₁ = q₂
  /-- Backward on predecessors: every R₂-predecessor of f(p) is the image
      of an R₁-predecessor of p. Needed for □ forward direction. -/
  backward_pred : ∀ p q₂, R₂ q₂ (f p) → ∃ q₁, R₁ q₁ p ∧ f q₁ = q₂
  /-- Atom preservation (both directions). -/
  atoms : ∀ a p, I₁ a p ↔ I₂ a (f p)

/-- Extract a forward simulation from a bisimulation map. -/
def BisimulationMap.toForwardSim {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem} (sim : BisimulationMap R₁ R₂ I₁ I₂) :
    ForwardSimulationMap R₁ R₂ I₁ I₂ where
  f := sim.f
  forward := sim.forward
  atoms a p h := (sim.atoms a p).mp h

/-! ## Formula Fragment Predicates -/

/-- The positive fragment: formulas built from top, bot, atoms, and, or, diamond.
    No implication, no box. These are the formulas preserved forward by a
    forward simulation map. -/
def IsPositive : OSLFFormula → Prop
  | .top => True
  | .bot => True
  | .atom _ => True
  | .and φ ψ => IsPositive φ ∧ IsPositive ψ
  | .or φ ψ => IsPositive φ ∧ IsPositive ψ
  | .imp _ _ => False
  | .dia φ => IsPositive φ
  | .box _ => False

/-- Decidability of `IsPositive`. -/
def decideIsPositive : (φ : OSLFFormula) → Decidable (IsPositive φ)
  | .top | .bot | .atom _ => isTrue trivial
  | .and φ ψ =>
    match decideIsPositive φ, decideIsPositive ψ with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h, _ => isFalse fun ⟨h₁, _⟩ => h h₁
    | _, isFalse h => isFalse fun ⟨_, h₂⟩ => h h₂
  | .or φ ψ =>
    match decideIsPositive φ, decideIsPositive ψ with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h, _ => isFalse fun ⟨h₁, _⟩ => h h₁
    | _, isFalse h => isFalse fun ⟨_, h₂⟩ => h h₂
  | .imp _ _ => isFalse not_false
  | .dia φ => decideIsPositive φ
  | .box _ => isFalse not_false

instance : DecidablePred IsPositive := decideIsPositive

/-! ## Positive-Fragment Forward Preservation -/

/-- Forward simulation maps preserve the positive fragment of modal semantics.

    If `sim` is a forward simulation from (R₁, I₁) to (R₂, I₂), then for
    any positive formula φ:
      `sem R₁ I₁ φ p → sem R₂ I₂ φ (sim.f p)` -/
theorem forward_sim_preserves_positive
    {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem}
    (sim : ForwardSimulationMap R₁ R₂ I₁ I₂)
    (φ : OSLFFormula) (hpos : IsPositive φ) (p : Pattern) :
    sem R₁ I₁ φ p → sem R₂ I₂ φ (sim.f p) := by
  induction φ generalizing p with
  | top => intro _; trivial
  | bot => intro h; exact h
  | atom a => intro h; exact sim.atoms a p h
  | and φ ψ ihφ ihψ =>
    intro ⟨h₁, h₂⟩
    exact ⟨ihφ hpos.1 p h₁, ihψ hpos.2 p h₂⟩
  | or φ ψ ihφ ihψ =>
    intro h
    exact h.elim (fun h₁ => Or.inl (ihφ hpos.1 p h₁))
                  (fun h₂ => Or.inr (ihψ hpos.2 p h₂))
  | imp _ _ => exact absurd hpos not_false
  | dia φ ih =>
    intro ⟨q, hR, hq⟩
    exact ⟨sim.f q, sim.forward p q hR, ih hpos q hq⟩
  | box _ => exact absurd hpos not_false

/-! ## Full Bisimulation-Map Preservation -/

/-- Bisimulation maps preserve the full OSLF modal semantics as an iff.

    If `sim` is a bisimulation map from (R₁, I₁) to (R₂, I₂), then for
    any formula φ and state p:
      `sem R₁ I₁ φ p ↔ sem R₂ I₂ φ (sim.f p)`

    This is the main theorem: simulation-style maps between reduction
    systems preserve modal meaning. -/
theorem bisimulation_map_preserves_sem
    {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂)
    (φ : OSLFFormula) (p : Pattern) :
    sem R₁ I₁ φ p ↔ sem R₂ I₂ φ (sim.f p) := by
  induction φ generalizing p with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | atom a => exact sim.atoms a p
  | and φ ψ ihφ ihψ => exact and_congr (ihφ p) (ihψ p)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ p) (ihψ p)
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ p) (ihψ p)
  | dia φ ih =>
    constructor
    · rintro ⟨q, hR, hq⟩
      exact ⟨sim.f q, sim.forward p q hR, (ih q).mp hq⟩
    · rintro ⟨q₂, hR₂, hq₂⟩
      obtain ⟨q₁, hR₁, hfq⟩ := sim.backward_succ p q₂ hR₂
      exact ⟨q₁, hR₁, (ih q₁).mpr (hfq ▸ hq₂)⟩
  | box φ ih =>
    constructor
    · intro h q₂ hR₂
      obtain ⟨q₁, hR₁, hfq⟩ := sim.backward_pred p q₂ hR₂
      exact hfq ▸ (ih q₁).mp (h q₁ hR₁)
    · intro h q₁ hR₁
      exact (ih q₁).mpr (h (sim.f q₁) (sim.forward q₁ p hR₁))

/-! ## Corollaries -/

/-- Bisimulation maps preserve observational equivalence:
    if p and q are indistinguishable under (R₁, I₁), then f(p) and f(q) are
    indistinguishable under (R₂, I₂). -/
theorem bisimulation_map_preserves_indistObs
    {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂)
    (p q : Pattern) :
    indistObs R₁ I₁ p q → indistObs R₂ I₂ (sim.f p) (sim.f q) := by
  intro hind φ
  have hp := bisimulation_map_preserves_sem sim φ p
  have hq := bisimulation_map_preserves_sem sim φ q
  exact hp.symm.trans ((hind φ).trans hq)

/-- The positive-fragment theorem as a special case of the full theorem. -/
theorem bisimulation_map_preserves_positive
    {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂)
    (φ : OSLFFormula) (_hpos : IsPositive φ) (p : Pattern) :
    sem R₁ I₁ φ p → sem R₂ I₂ φ (sim.f p) :=
  (bisimulation_map_preserves_sem sim φ p).mp

/-! ## Categorical Structure: Identity and Composition

    Simulation maps form a category: identity maps are (bi)simulation maps,
    and (bi)simulation maps compose. This gives the semantic preservation
    theorems a functorial character. -/

/-- The identity map is a forward simulation from any system to itself. -/
def ForwardSimulationMap.id (R : Pattern → Pattern → Prop) (I : AtomSem) :
    ForwardSimulationMap R R I I where
  f := _root_.id
  forward _ _ h := h
  atoms _ _ h := h

/-- Composition of forward simulation maps. -/
def ForwardSimulationMap.comp
    {R₁ R₂ R₃ : Pattern → Pattern → Prop}
    {I₁ I₂ I₃ : AtomSem}
    (sim₁ : ForwardSimulationMap R₁ R₂ I₁ I₂)
    (sim₂ : ForwardSimulationMap R₂ R₃ I₂ I₃) :
    ForwardSimulationMap R₁ R₃ I₁ I₃ where
  f := sim₂.f ∘ sim₁.f
  forward p p' h := sim₂.forward _ _ (sim₁.forward p p' h)
  atoms a p h := sim₂.atoms a _ (sim₁.atoms a p h)

/-- The identity map is a bisimulation map from any system to itself. -/
def BisimulationMap.id (R : Pattern → Pattern → Prop) (I : AtomSem) :
    BisimulationMap R R I I where
  f := _root_.id
  forward _ _ h := h
  backward_succ _ _ h := ⟨_, h, rfl⟩
  backward_pred _ _ h := ⟨_, h, rfl⟩
  atoms _ _ := Iff.rfl

/-- Composition of bisimulation maps. -/
def BisimulationMap.comp
    {R₁ R₂ R₃ : Pattern → Pattern → Prop}
    {I₁ I₂ I₃ : AtomSem}
    (sim₁ : BisimulationMap R₁ R₂ I₁ I₂)
    (sim₂ : BisimulationMap R₂ R₃ I₂ I₃) :
    BisimulationMap R₁ R₃ I₁ I₃ where
  f := sim₂.f ∘ sim₁.f
  forward p p' h := sim₂.forward _ _ (sim₁.forward p p' h)
  backward_succ p q₃ h := by
    obtain ⟨q₂, hR₂, hfq₂⟩ := sim₂.backward_succ (sim₁.f p) q₃ h
    obtain ⟨q₁, hR₁, hfq₁⟩ := sim₁.backward_succ p q₂ hR₂
    exact ⟨q₁, hR₁, show sim₂.f (sim₁.f q₁) = q₃ by rw [hfq₁, hfq₂]⟩
  backward_pred p q₃ h := by
    obtain ⟨q₂, hR₂, hfq₂⟩ := sim₂.backward_pred (sim₁.f p) q₃ h
    obtain ⟨q₁, hR₁, hfq₁⟩ := sim₁.backward_pred p q₂ hR₂
    exact ⟨q₁, hR₁, show sim₂.f (sim₁.f q₁) = q₃ by rw [hfq₁, hfq₂]⟩
  atoms a p := (sim₁.atoms a p).trans (sim₂.atoms a (sim₁.f p))

/-- Composition respects preservation: composing two bisimulation maps and then
    applying the preservation theorem gives the same result as chaining
    preservation through the intermediate system. -/
theorem comp_preserves_sem
    {R₁ R₂ R₃ : Pattern → Pattern → Prop}
    {I₁ I₂ I₃ : AtomSem}
    (sim₁ : BisimulationMap R₁ R₂ I₁ I₂)
    (sim₂ : BisimulationMap R₂ R₃ I₂ I₃)
    (φ : OSLFFormula) (p : Pattern) :
    (bisimulation_map_preserves_sem (sim₁.comp sim₂) φ p).mp =
      (bisimulation_map_preserves_sem sim₂ φ (sim₁.f p)).mp ∘
        (bisimulation_map_preserves_sem sim₁ φ p).mp := by
  ext; rfl

/-! ## Bridge to Single-System Bisimulation

    The existing `bisimulation_invariant_sem` (in `OSLFKSUnificationSketch`)
    proves that a bisimulation equivalence within a single system preserves
    all formulas. That theorem uses a *relation* between states, while
    `bisimulation_map_preserves_sem` uses a *function*.

    These are complementary:
    - Relational bisimulation: `equiv p q → ∀ φ, sem R I φ p ↔ sem R I φ q`
    - Functional simulation:   `∀ φ p, sem R₁ I₁ φ p ↔ sem R₂ I₂ φ (f p)`

    The identity bisimulation map recovers the trivial case `p = p`. For the
    full relational case (arbitrary `equiv p q`), the relational theorem is
    the natural statement — converting it to a functional map would require
    `Choice` to pick canonical representatives, which is mathematically
    unnatural.

    Instead, we provide a clean bridge showing both theorems compose:
    a bisimulation map followed by relational bisimulation still preserves
    all formulas. -/

/-- Composition of functional and relational preservation: if a bisimulation
    map sends (R₁, I₁) to (R₂, I₂), and `equiv` is a bisimulation on
    (R₂, I₂), then `equiv (f p) q₂` implies formulas transfer from p to q₂.

    This bridges `bisimulation_map_preserves_sem` with
    `bisimulation_invariant_sem`. -/
theorem map_then_bisim_preserves_sem
    {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂)
    {equiv : Pattern → Pattern → Prop}
    (hBisim : StepBisimulation R₂ equiv)
    (hBisimRev : StepBisimulation (fun a b => R₂ b a) equiv)
    (hAtom : ∀ a p q, equiv p q → (I₂ a p ↔ I₂ a q))
    (φ : OSLFFormula) (p : Pattern) (q₂ : Pattern)
    (hequiv : equiv (sim.f p) q₂) :
    sem R₁ I₁ φ p ↔ sem R₂ I₂ φ q₂ :=
  (bisimulation_map_preserves_sem sim φ p).trans
    (bisimulation_invariant_sem hBisim hBisimRev hAtom hequiv φ)

end Mettapedia.OSLF.Framework.SimulationPreservation
