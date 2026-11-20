import Mettapedia.ProbabilityTheory.ImpreciseProbability.AnytimeConditional
import Mettapedia.InformationTheory.FiniteProbability

/-!
# Scope-limited computation of coherent probability bounds

A view carries the same query and evidence event into a smaller world space.
Every retained constraint is justified by its pullback to the original
knowledge base. Solving the view gives an outer bound. For a disconnected
consistent component the view is exact, via a product witness for every
admissible marginal.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalScope

open FiniteConditionalConstraints FiniteEventMass AnytimeConditional
open Mettapedia.InformationTheory.FiniteRV
open scoped BigOperators

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def pullback (view : Ω → Ξ) (c : Constraint Ξ) : Constraint Ω where
  event := c.event ∘ view
  condition := c.condition ∘ view
  lower := c.lower
  upper := c.upper
  nonneg := c.nonneg
  ordered := c.ordered
  bounded := c.bounded

noncomputable def marginal [DecidableEq Ξ] (view : Ω → Ξ) (p : Distribution Ω) : Distribution Ξ where
  weight := pushforward p.weight view
  nonneg := pushforward_nonneg p.weight p.nonneg view
  total := (sum_pushforward p.weight view).trans p.total

theorem mass_marginal [DecidableEq Ξ] (view : Ω → Ξ) (p : Distribution Ω) (event : Event Ξ) :
    mass (marginal view p).weight event = mass p.weight (event ∘ view) := by
  simpa only [marginal, mass, Function.comp_def, mul_ite, mul_one, mul_zero] using
    sum_pushforward_mul p.weight view (fun x => if event x then 1 else 0)

theorem holds_marginal [DecidableEq Ξ] (view : Ω → Ξ) (p : Distribution Ω) (c : Constraint Ξ) :
    c.Holds (marginal view p).weight ↔ (pullback view c).Holds p.weight := by
  simp only [Constraint.Holds, mass_marginal, pullback, Function.comp_def]

structure View (base : KnowledgeBase Ω) (event condition : Event Ω) where
  worlds : Nat
  project : Ω → Fin worlds
  constraints : KnowledgeBase (Fin worlds)
  query : Event (Fin worlds)
  support : Event (Fin worlds)
  query_eq : ∀ world, query (project world) = event world
  support_eq : ∀ world, support (project world) = condition world
  retained : ∀ c ∈ constraints, pullback project c ∈ base

namespace View

variable {base : KnowledgeBase Ω} {event condition : Event Ω}

theorem queryValues_subset (view : View base event condition) :
    queryValues base event condition ⊆ queryValues view.constraints view.query view.support := by
  rintro val ⟨p, admissible, positive, same⟩
  have ev : view.support ∘ view.project = condition := funext view.support_eq
  have joint : (fun w => view.query w && view.support w) ∘ view.project =
      (fun w => event w && condition w) := by
    funext world
    simp only [Function.comp_apply, view.query_eq, view.support_eq]
  refine ⟨marginal view.project p, ?_, ?_, ?_⟩
  · intro c member
    exact (holds_marginal view.project p c).mpr (admissible _ (view.retained c member))
  · rwa [mass_marginal, ev]
  · unfold conditionalValue at same ⊢
    rwa [mass_marginal, mass_marginal, ev, joint]

def solve (view : View base event condition) (fuel : Nat) : Answer :=
  queryAt fuel view.constraints view.query view.support

theorem solve_sound (view : View base event condition) (fuel : Nat) :
    queryValues base event condition ⊆ range (view.solve fuel) :=
  view.queryValues_subset.trans (queryAt_sound fuel _ _ _)

end View

def disjointBase (left : KnowledgeBase Ω) (right : KnowledgeBase Ξ) : KnowledgeBase (Ω × Ξ) :=
  left.map (pullback Prod.fst) ++ right.map (pullback Prod.snd)

noncomputable def product (left : Distribution Ω) (right : Distribution Ξ) : Distribution (Ω × Ξ) where
  weight pair := left.weight pair.1 * right.weight pair.2
  nonneg pair := mul_nonneg (left.nonneg _) (right.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, right.total, mul_one, left.total]

theorem product_mass_left (left : Distribution Ω) (right : Distribution Ξ) (event : Event Ω) :
    mass (product left right).weight (event ∘ Prod.fst) = mass left.weight event := by
  rw [mass, Fintype.sum_prod_type, mass]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Function.comp_apply, product]
  by_cases inside : event x = true
  · simp [inside, ← Finset.mul_sum, right.total]
  · simp [inside]

theorem product_mass_right (left : Distribution Ω) (right : Distribution Ξ) (event : Event Ξ) :
    mass (product left right).weight (event ∘ Prod.snd) = mass right.weight event := by
  rw [mass, Fintype.sum_prod_type, Finset.sum_comm, mass]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Function.comp_apply, product]
  by_cases inside : event x = true
  · simp [inside, ← Finset.sum_mul, left.total]
  · simp [inside]

/-- A model in a larger disconnected component imposes no further
restrictions. The product is an extension witness. The joint models in
the knowledge base may also include correlated couplings. -/
theorem disjoint_query_exact [DecidableEq Ω] (left : KnowledgeBase Ω) (right : KnowledgeBase Ξ)
    (consistent : Consistent right) (query condition : Event Ω) :
    queryValues (disjointBase left right) (query ∘ Prod.fst) (condition ∘ Prod.fst) =
      queryValues left query condition := by
  ext val
  constructor
  · rintro ⟨model, satisfies, positive, value⟩
    refine ⟨marginal Prod.fst model, ?_, ?_, ?_⟩
    · intro c member
      exact (holds_marginal Prod.fst model c).mpr
        (satisfies _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, member, rfl⟩)))
    · rwa [mass_marginal]
    · simpa only [conditionalValue, mass_marginal, Function.comp_def] using value
  · rintro ⟨model, satisfies, positive, value⟩
    obtain ⟨background, allowed⟩ := consistent
    refine ⟨product model background, ?_, ?_, ?_⟩
    · intro c member
      rcases List.mem_append.mp member with l | r
      · obtain ⟨source, present, rfl⟩ := List.mem_map.mp l
        simpa only [pullback, Constraint.Holds, show
          (fun x : Ω × Ξ => (source.event ∘ Prod.fst) x && (source.condition ∘ Prod.fst) x) =
            (fun x => source.event x && source.condition x) ∘ Prod.fst from rfl,
          product_mass_left] using satisfies source present
      · obtain ⟨source, present, rfl⟩ := List.mem_map.mp r
        simpa only [pullback, Constraint.Holds, show
          (fun x : Ω × Ξ => (source.event ∘ Prod.snd) x && (source.condition ∘ Prod.snd) x) =
            (fun x => source.event x && source.condition x) ∘ Prod.snd from rfl,
          product_mass_right] using allowed source present
    · rwa [product_mass_left]
    · unfold conditionalValue
      rw [show (fun x : Ω × Ξ => (query ∘ Prod.fst) x && (condition ∘ Prod.fst) x) =
          (fun x => query x && condition x) ∘ Prod.fst from rfl,
        product_mass_left, product_mass_left]
      exact value

/-- Each solver step examines only the local component. The background
component need only supply a consistency witness for the exactness result. -/
def disjointView {n : Nat} (left : KnowledgeBase (Fin n)) (right : KnowledgeBase Ξ)
    (query condition : Event (Fin n)) :
    View (disjointBase left right) (query ∘ Prod.fst) (condition ∘ Prod.fst) where
  worlds := n
  project := Prod.fst
  constraints := left
  query := query
  support := condition
  query_eq _ := rfl
  support_eq _ := rfl
  retained c member := List.mem_append_left _ (List.mem_map.mpr ⟨c, member, rfl⟩)

theorem disjointView_eventually_exact {n : Nat} (left : KnowledgeBase (Fin n))
    (right : KnowledgeBase Ξ) (consistent : Consistent right) (query condition : Event (Fin n)) :
    ∃ sufficient, ∀ fuel ≥ sufficient,
      range ((disjointView left right query condition).solve fuel) =
        queryValues (disjointBase left right) (query ∘ Prod.fst) (condition ∘ Prod.fst) := by
  rw [disjoint_query_exact left right consistent]
  exact queryAt_eventually_exact left query condition

end Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalScope
