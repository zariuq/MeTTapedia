import Mettapedia.Cybernetics.ApproximateAdequacy.CouplingBound
import Mettapedia.Cybernetics.ApproximateAdequacy.SquareIteration

/-!
# Probabilistic update squares give coupling bounds

W11's update squares certify one-step predictions of deterministic updates.
Their probabilistic form compares distributions: a **probabilistic update
square** with error `δ`, for a view `v` from world states to model states and
a pseudometric `ρ` on model states, gives for every action and world state `s`
a coupling of the world's successor distribution with the model's successor
distribution from `v s` whose expected distance, `ρ (v x) y`, is at most `δ`
(`ProbabilisticSquare`).  The model is `κ`-Lipschitz when every pair of its
states has successor distributions coupled within `κ` times their distance
(`KantorovichLipschitz`).

**Theorem** (`couplingBound_of_squares`).  If the observables are
`1`-Lipschitz along the view, the discount satisfies `c < 1` and `c κ ≤ 1`,
then `ρ (v s) t + c δ / (1 - c)` is a coupling bound.  In particular every
world state is within `c δ / (1 - c)` of its view in the bisimulation metric
(`couplingBound_view`): the discount plays the part that the contraction plays
in lane A's `isApproxBisimulation_of_contraction`, where `δ + κ ε ≤ ε`.  A
per-step distributional error accumulates, discounted, to a behavioural
distance.

The proof glues the square's coupling with the model's Lipschitz coupling
(`Coupling.glue`), which is how the sequential composition law of coupling
bounds is proved as well.

**Parallel composition of squares** (`ApproxSquare.prod`): deterministic
squares on products add their errors for the sum of the distances.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset
open Mettapedia.GSLT.Scope

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {A Atom S T : Type*} [Fintype S] [Fintype T]

/-- **A probabilistic update square** with error `δ`. -/
def ProbabilisticSquare (P : LabelledMarkovChain 𝕜 A Atom S) (Q : LabelledMarkovChain 𝕜 A Atom T)
    (ρ : T → T → 𝕜) (v : S → T) (δ : 𝕜) : Prop :=
  ∀ a s, ∃ ω : Coupling (P.trans a s) (Q.trans a (v s)), ω.cost (fun x y => ρ (v x) y) ≤ δ

/-- **The model's transitions are `κ`-Lipschitz** for `ρ`, in the Kantorovich
sense. -/
def KantorovichLipschitz (Q : LabelledMarkovChain 𝕜 A Atom T) (ρ : T → T → 𝕜) (κ : 𝕜) : Prop :=
  ∀ a y y', ∃ ω : Coupling (Q.trans a y) (Q.trans a y'), ω.cost ρ ≤ κ * ρ y y'

variable {P : LabelledMarkovChain 𝕜 A Atom S} {Q : LabelledMarkovChain 𝕜 A Atom T}
  {ρ : T → T → 𝕜} {v : S → T} {δ κ c : 𝕜}

/-- **Probabilistic update squares, discounted, give a coupling bound.** -/
theorem couplingBound_of_squares (ρ_nonneg : ∀ y y', 0 ≤ ρ y y')
    (triangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (observe_le : ∀ i s t, |P.observe i s - Q.observe i t| ≤ ρ (v s) t)
    (square : ProbabilisticSquare P Q ρ v δ) (lipschitz : KantorovichLipschitz Q ρ κ)
    (δ_nonneg : 0 ≤ δ) (c_nonneg : 0 ≤ c) (c_lt : c < 1) (contracting : c * κ ≤ 1) :
    CouplingBound P Q c fun s t => ρ (v s) t + c * δ / (1 - c) := by
  have gap : 0 < 1 - c := sub_pos.mpr c_lt
  have B_nonneg : 0 ≤ c * δ / (1 - c) := div_nonneg (mul_nonneg c_nonneg δ_nonneg) gap.le
  have B_eq : c * δ + c * (c * δ / (1 - c)) = c * δ / (1 - c) := by
    field_simp
    ring
  refine ⟨fun s t => add_nonneg (ρ_nonneg _ _) B_nonneg,
    fun i s t => (observe_le i s t).trans (le_add_of_nonneg_right B_nonneg), fun a s t => ?_⟩
  obtain ⟨ω₁, le₁⟩ := square a s
  obtain ⟨ω₂, le₂⟩ := lipschitz a (v s) t
  refine ⟨ω₁.glue ω₂, ?_⟩
  have glued := ω₁.cost_glue_le ω₂ (m₁ := fun x y => ρ (v x) y) (m₂ := ρ)
    (m₃ := fun x z => ρ (v x) z) fun x y z => triangle (v x) y z
  have split := (ω₁.glue ω₂).cost_add (fun x z => ρ (v x) z) (fun _ _ => c * δ / (1 - c))
  rw [(ω₁.glue ω₂).cost_const (P.isDistribution a s)] at split
  rw [split]
  have lipschitz_step : c * (κ * ρ (v s) t) ≤ ρ (v s) t := by
    rw [← mul_assoc]
    exact mul_le_of_le_one_left (ρ_nonneg _ _) contracting
  calc c * ((ω₁.glue ω₂).cost (fun x z => ρ (v x) z) + c * δ / (1 - c))
      ≤ c * (δ + κ * ρ (v s) t + c * δ / (1 - c)) :=
        mul_le_mul_of_nonneg_left (add_le_add (glued.trans (add_le_add le₁ le₂)) le_rfl) c_nonneg
    _ = c * (κ * ρ (v s) t) + (c * δ + c * (c * δ / (1 - c))) := by ring
    _ ≤ ρ (v s) t + c * δ / (1 - c) := by rw [B_eq]; exact add_le_add lipschitz_step le_rfl

/-- **Every world state is within `c δ / (1 - c)` of its view.** -/
theorem couplingBound_view (ρ_nonneg : ∀ y y', 0 ≤ ρ y y') (ρ_self : ∀ y, ρ y y = 0)
    (triangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (observe_le : ∀ i s t, |P.observe i s - Q.observe i t| ≤ ρ (v s) t)
    (square : ProbabilisticSquare P Q ρ v δ) (lipschitz : KantorovichLipschitz Q ρ κ)
    (δ_nonneg : 0 ≤ δ) (c_nonneg : 0 ≤ c) (c_lt : c < 1) (contracting : c * κ ≤ 1) (s : S) :
    ∃ m : S → T → 𝕜, CouplingBound P Q c m ∧ m s (v s) = c * δ / (1 - c) :=
  ⟨_, couplingBound_of_squares ρ_nonneg triangle observe_le square lipschitz δ_nonneg c_nonneg c_lt
    contracting, by rw [ρ_self, zero_add]⟩

/-! ## Parallel composition of deterministic squares -/

section Parallel

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ D : Type*} [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D]
  {dist₁ : Z₁ → Z₁ → D} {dist₂ : Z₂ → Z₂ → D} {view₁ : X₁ → Y₁} {view₂ : X₂ → Y₂}
  {view₁' : X₁ → Z₁} {view₂' : X₂ → Z₂} {f₁ : X₁ → X₁} {f₂ : X₂ → X₂}
  {f₁' : Y₁ → Z₁} {f₂' : Y₂ → Z₂} {ε₁ ε₂ : D}

/-- **Squares on products add their errors.** -/
theorem ApproxSquare.prod (first : ApproxSquare dist₁ view₁ view₁' f₁ f₁' ε₁)
    (second : ApproxSquare dist₂ view₂ view₂' f₂ f₂' ε₂) :
    ApproxSquare (sumDistance dist₁ dist₂) (Prod.map view₁ view₂) (Prod.map view₁' view₂')
      (Prod.map f₁ f₂) (Prod.map f₁' f₂') (ε₁ + ε₂) :=
  fun x => add_le_add (first x.1) (second x.2)

end Parallel

end Mettapedia.Cybernetics.ApproximateAdequacy
