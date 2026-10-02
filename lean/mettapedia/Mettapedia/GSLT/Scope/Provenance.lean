import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Tropical.Basic
import Mettapedia.GSLT.Scope.RevisionWorkflow

/-!
# One program, many interpretations: provenance semirings

A path program on the road map of `Mettapedia.GSLT.Scope.RoadMap`, run over
an arbitrary commutative semiring `K`: roads carry tags in `K`
(`edges`), and routes of two roads are the join of the road relation with
itself, projected to its endpoints (`twoRoads`).  Following T. J. Green,
G. Karvounarakis and V. Tannen (*Provenance semirings*, PODS 2007):
* **homomorphisms commute with the program** (`map_twoRoads`, the direction
  of their Proposition 3.5 that holds for every semiring homomorphism);
* **the provenance polynomials `ℕ[X]` are universal**: for every tagging
  there is exactly one semiring homomorphism out of `ℕ[X]` extending it
  (`universal`, their Proposition 4.2);
* **every interpretation factors through provenance**: running the program
  in `K` is evaluating its provenance polynomial (`twoRoads_eq_evaluate`,
  their Theorem 4.3).  The provenance of a route from `a` to `d` is
  `ab · bd + ac · cd` (`provenance_a_d`).

**Three homomorphic images**, with every road usable:
* Boolean, disjunction and conjunction (`Reach`): reachability
  (`reachImage`, `reach_a_d`);
* tropical, minimum and addition: the cheapest cost (`costImage`,
  `cost_a_d`);
* natural numbers: the number of routes (`countImage`, `count_a_d`).

**Consumer descent.**  A consumer of provenance descends to an image exactly
when it factors through the image homomorphism.  Reachability descends to
counting (`reach_factors_count`) and to cost (`reach_factors_cost`); counting
and cost do not descend to reachability (`count_not_factors_reach`,
`cost_not_factors_reach`), and neither descends to the other
(`count_not_factors_cost`, `cost_not_factors_count`).  The images form the
diamond `ℕ[X] ↠ ℕ, Trop ↠ 𝔹`.

The polynomial semiring is Mathlib's `MvPolynomial`, whose finitely supported
functions use `Classical.choice`; every statement about provenance inherits
it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.Provenance

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Scope.RoadMap
open MvPolynomial

/-! ## The Boolean semiring -/

/-- The Boolean semiring: disjunction as addition, conjunction as
multiplication. -/
@[ext]
structure Reach where
  /-- Whether a route exists. -/
  reachable : Bool
  deriving DecidableEq

instance : Zero Reach := ⟨⟨false⟩⟩
instance : One Reach := ⟨⟨true⟩⟩
instance : Add Reach := ⟨fun a b => ⟨a.reachable || b.reachable⟩⟩
instance : Mul Reach := ⟨fun a b => ⟨a.reachable && b.reachable⟩⟩

instance : CommSemiring Reach where
  add_assoc := by rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ <;> rfl
  zero_add := by rintro ⟨_ | _⟩ <;> rfl
  add_zero := by rintro ⟨_ | _⟩ <;> rfl
  add_comm := by rintro ⟨_ | _⟩ ⟨_ | _⟩ <;> rfl
  mul_assoc := by rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ <;> rfl
  one_mul := by rintro ⟨_ | _⟩ <;> rfl
  mul_one := by rintro ⟨_ | _⟩ <;> rfl
  zero_mul := by rintro ⟨_ | _⟩ <;> rfl
  mul_zero := by rintro ⟨_ | _⟩ <;> rfl
  left_distrib := by rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ <;> rfl
  right_distrib := by rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ <;> rfl
  mul_comm := by rintro ⟨_ | _⟩ ⟨_ | _⟩ <;> rfl
  nsmul := nsmulRec

/-! ## The program -/

section Program

variable {K : Type*} [CommSemiring K] {K' : Type*} [CommSemiring K']

/-- The road relation as a `K`-relation: the road from `s` to `t` carries its
tag. -/
def edges (tag : Road → K) (s t : Town) : K :=
  (roads.map fun r => if r.ends = (s, t) then tag r else 0).sum

/-- **The path program**: routes of two roads, the join of the road relation
with itself projected to its endpoints. -/
def twoRoads (edge : Town → Town → K) (s t : Town) : K :=
  (towns.map fun m => edge s m * edge m t).sum

/-- **Homomorphisms commute with tagging.** -/
theorem map_edges (h : K →+* K') (tag : Road → K) (s t : Town) :
    h (edges tag s t) = edges (fun r => h (tag r)) s t := by
  simp only [edges, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  split <;> simp

/-- **Homomorphisms commute with the program.** -/
theorem map_twoRoads (h : K →+* K') (edge : Town → Town → K) (s t : Town) :
    h (twoRoads edge s t) = twoRoads (fun source target => h (edge source target)) s t := by
  simp only [twoRoads, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro middle _
  simp only [Function.comp_apply, map_mul]

end Program

/-! ## Provenance polynomials -/

section Universal

variable {K : Type*} [CommSemiring K]

/-- **The provenance of a route**: the program run on roads tagged by
themselves, in `ℕ[roads]`. -/
noncomputable def provenance (s t : Town) : MvPolynomial Road ℕ :=
  twoRoads (edges X) s t

/-- The provenance of a route from `a` to `d`: through `b` or through `c`. -/
theorem provenance_a_d :
    provenance .a .d = X .ab * X .bd + X .ac * X .cd := by
  simp [provenance, twoRoads, edges, towns, roads, Road.ends]

/-- Evaluation of provenance at a tagging. -/
noncomputable def evaluate (tag : Road → K) : MvPolynomial Road ℕ →+* K :=
  eval₂Hom (Nat.castRingHom K) tag

@[simp] theorem evaluate_X (tag : Road → K) (r : Road) : evaluate tag (X r) = tag r :=
  eval₂Hom_X' _ _ r

/-- Semiring homomorphisms out of `ℕ[X]` agree when they agree on the
variables. -/
theorem hom_ext {f g : MvPolynomial Road ℕ →+* K} (agree : ∀ r, f (X r) = g (X r)) : f = g :=
  ringHom_ext' (ext_nat _ _) agree

/-- **Universality of provenance polynomials**: every tagging extends to
exactly one semiring homomorphism. -/
theorem universal (tag : Road → K) :
    ∃! h : MvPolynomial Road ℕ →+* K, ∀ r, h (X r) = tag r :=
  ⟨evaluate tag, evaluate_X tag, fun _ agree => hom_ext fun r => (agree r).trans
    (evaluate_X tag r).symm⟩

/-- **Every interpretation factors through provenance**: running the program in
`K` is evaluating its provenance. -/
theorem twoRoads_eq_evaluate (tag : Road → K) (s t : Town) :
    twoRoads (edges tag) s t = evaluate tag (provenance s t) := by
  rw [provenance, map_twoRoads]
  congr 1
  funext source target
  rw [map_edges]
  congr 1
  funext r
  exact (evaluate_X tag r).symm

end Universal

/-! ## Three images -/

/-- The costs of the roads. -/
def cost : Road → ℕ
  | .ab => 1
  | .bd => 5
  | .ac => 2
  | .cd => 2

/-- **Counting**: every road usable once. -/
noncomputable def countImage : MvPolynomial Road ℕ →+* ℕ :=
  evaluate fun _ => 1

/-- **Reachability**: every road open. -/
noncomputable def reachImage : MvPolynomial Road ℕ →+* Reach :=
  evaluate fun _ => 1

/-- **Cheapest cost**. -/
noncomputable def costImage : MvPolynomial Road ℕ →+* Tropical (WithTop ℕ) :=
  evaluate fun r => Tropical.trop (cost r : WithTop ℕ)

/-- Two routes lead from `a` to `d`. -/
theorem count_a_d : countImage (provenance .a .d) = 2 := by
  rw [provenance_a_d]
  simp [countImage]

/-- `d` is reachable from `a`. -/
theorem reach_a_d : reachImage (provenance .a .d) = 1 := by
  rw [provenance_a_d]
  simp only [reachImage, map_add, map_mul, evaluate_X]
  rfl

/-- The cheapest route from `a` to `d` costs `4`, through `c`. -/
theorem cost_a_d : costImage (provenance .a .d) = Tropical.trop (4 : WithTop ℕ) := by
  rw [provenance_a_d]
  simp only [costImage, map_add, map_mul, evaluate_X, cost, ← Tropical.trop_add,
    Tropical.trop_add_def, Tropical.untrop_trop]
  rfl

/-! ## Consumer descent -/

/-- **Reachability descends to counting**: it factors through the count, by
the homomorphism sending a count to whether it is nonzero. -/
theorem reach_factors_count : Factors countImage reachImage := by
  refine ⟨Nat.castRingHom Reach, fun p => ?_⟩
  have equal : (Nat.castRingHom Reach).comp countImage = reachImage :=
    hom_ext fun r => by simp [countImage, reachImage]
  exact congrArg (fun h : MvPolynomial Road ℕ →+* Reach => h p) equal

/-- Whether a tropical cost is finite: a semiring homomorphism to the Boolean
semiring. -/
def finite : Tropical (WithTop ℕ) →+* Reach where
  toFun x := ⟨decide (Tropical.untrop x ≠ ⊤)⟩
  map_one' := rfl
  map_mul' x y := by
    ext
    change decide (Tropical.untrop x + Tropical.untrop y ≠ ⊤) =
      (decide (Tropical.untrop x ≠ ⊤) && decide (Tropical.untrop y ≠ ⊤))
    simp [WithTop.add_eq_top]
  map_zero' := rfl
  map_add' x y := by
    ext
    change decide (min (Tropical.untrop x) (Tropical.untrop y) ≠ ⊤) =
      (decide (Tropical.untrop x ≠ ⊤) || decide (Tropical.untrop y ≠ ⊤))
    simp

/-- **Reachability descends to cost.** -/
theorem reach_factors_cost : Factors costImage reachImage := by
  refine ⟨finite, fun p => ?_⟩
  have equal : finite.comp costImage = reachImage :=
    hom_ext fun r => by
      simp only [RingHom.comp_apply, costImage, reachImage, evaluate_X]
      cases r <;> rfl
  exact congrArg (fun h : MvPolynomial Road ℕ →+* Reach => h p) equal

/-- **Control: counting does not descend to reachability.** -/
theorem count_not_factors_reach : ¬ Factors reachImage countImage := by
  apply NonTrivialFiber.not_factors
  refine ⟨X .ab, X .ab + X .bd, ?_, ?_⟩
  · simp only [reachImage, map_add, evaluate_X]
    rfl
  · simp [countImage]

/-- **Control: cost does not descend to reachability.** -/
theorem cost_not_factors_reach : ¬ Factors reachImage costImage := by
  apply NonTrivialFiber.not_factors
  refine ⟨X .ab, X .bd, ?_, ?_⟩
  · simp only [reachImage, evaluate_X]
  · simp only [costImage, evaluate_X, cost]
    intro equal
    have := congrArg Tropical.untrop equal
    simp at this

/-- **Control: counting does not descend to cost**: one route and the same
route twice cost the same. -/
theorem count_not_factors_cost : ¬ Factors costImage countImage := by
  apply NonTrivialFiber.not_factors
  refine ⟨X .ab, X .ab + X .ab, ?_, ?_⟩
  · simp only [costImage, map_add, evaluate_X, Tropical.add_self]
  · simp [countImage]

/-- **Control: cost does not descend to counting**: two single roads of
different costs. -/
theorem cost_not_factors_count : ¬ Factors countImage costImage := by
  apply NonTrivialFiber.not_factors
  refine ⟨X .ab, X .bd, ?_, ?_⟩
  · simp [countImage]
  · simp only [costImage, evaluate_X, cost]
    intro equal
    have := congrArg Tropical.untrop equal
    simp at this

end Mettapedia.GSLT.Scope.Provenance
