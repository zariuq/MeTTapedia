import Mettapedia.Logic.ConstraintTypes.OpenMembership

/-!
# Predicate languages, reindexing and existential hiding

A type or constraint denotes a predicate. Restricting a solution set is an
idempotent projection; independent restrictions commute. Hiding is existential
image, left adjoint to substitution/preimage. Dropping hidden delayed goals is
an operational policy; the fibre theorem below states exactly when it is also
an exact existential projection. No satisfiability test is added to collection.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.Semantics

universe u v w

abbrev Language (Value : Type u) := Value → Prop

def Entails {V : Type u} (left right : Language V) : Prop := ∀ v, left v → right v

def restrict {V : Type u} (predicate solutions : Language V) : Language V :=
  fun v => solutions v ∧ predicate v

theorem restrict_idempotent {V : Type u} (predicate solutions : Language V) :
    restrict predicate (restrict predicate solutions) = restrict predicate solutions := by
  funext v
  apply propext
  simp [restrict]

theorem restrictions_commute {V : Type u} (left right solutions : Language V) :
    restrict left (restrict right solutions) = restrict right (restrict left solutions) := by
  funext v
  apply propext
  simp only [restrict]
  exact ⟨fun ⟨⟨hs, hr⟩, hl⟩ => ⟨⟨hs, hl⟩, hr⟩,
    fun ⟨⟨hs, hl⟩, hr⟩ => ⟨⟨hs, hr⟩, hl⟩⟩

theorem restriction_erasure_iff_entails {V : Type u} (predicate solutions : Language V) :
    restrict predicate solutions = solutions ↔ Entails solutions predicate := by
  constructor
  · intro same v hs
    have : restrict predicate solutions v := by rw [same]; exact hs
    exact this.2
  · intro establishes
    funext v
    apply propext
    exact ⟨And.left, fun hs => ⟨hs, establishes v hs⟩⟩

def reindex {X : Type u} {Y : Type v} (map : X → Y) (predicate : Language Y) : Language X :=
  fun x => predicate (map x)

def image {X : Type u} {Y : Type v} (map : X → Y) (predicate : Language X) : Language Y :=
  fun y => ∃ x, predicate x ∧ map x = y

/-- Existential projection and substitution form a Galois connection. -/
theorem image_reindex_adjunction {X : Type u} {Y : Type v} (map : X → Y)
    (source : Language X) (target : Language Y) :
    Entails (image map source) target ↔ Entails source (reindex map target) := by
  constructor
  · intro h x hx
    exact h (map x) ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h x hx

theorem image_comp {X : Type u} {Y : Type v} {Z : Type w}
    (first : X → Y) (second : Y → Z) (predicate : Language X) :
    image second (image first predicate) = image (second ∘ first) predicate := by
  funext z
  apply propext
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, hx, hz⟩
  · rintro ⟨x, hx, hz⟩
    exact ⟨first x, ⟨x, hx, rfl⟩, hz⟩

/-- The existential projection law for conjoining a visible predicate. -/
theorem image_restrict {X : Type u} {Y : Type v} (map : X → Y)
    (visible : Language Y) (source : Language X) :
    image map (restrict (reindex map visible) source) = restrict visible (image map source) := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, ⟨hx, hv⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hv⟩
  · rintro ⟨⟨x, hx, rfl⟩, hv⟩
    exact ⟨x, ⟨hx, hv⟩, rfl⟩

/-- Exactness criterion for forgetting the hidden component. Each admitted
visible value must have a hidden extension satisfying the discarded checks. -/
theorem discard_hidden_iff_fibres_inhabited {X : Type u} {Y : Type v}
    (map : X → Y) (visible : Language Y) (hidden : Language X) :
    image map (restrict (reindex map visible) hidden) = visible ↔
      ∀ y, visible y → ∃ x, hidden x ∧ map x = y := by
  constructor
  · intro same y hy
    have : image map (restrict (reindex map visible) hidden) y := by rw [same]; exact hy
    obtain ⟨x, ⟨hx, _⟩, hxy⟩ := this
    exact ⟨x, hx, hxy⟩
  · intro witnesses
    funext y
    apply propext
    constructor
    · rintro ⟨x, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro hy
      obtain ⟨x, hx, hxy⟩ := witnesses y hy
      exact ⟨x, ⟨hx, by simpa [reindex, hxy] using hy⟩, hxy⟩

theorem independent_hidden_projection {X : Type u} {Y : Type v}
    (visible : Language X) (hidden : Language Y) (x : X) :
    image Prod.fst (fun pair : X × Y => visible pair.1 ∧ hidden pair.2) x ↔
      visible x ∧ ∃ y, hidden y := by
  constructor
  · rintro ⟨⟨x', y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨hx, y, hy⟩
  · rintro ⟨hx, y, hy⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

/-- Connection to the emitted residual language. -/
def formulaLanguage {X Q V : Type} (member : Q → V → Bool) (formula : Formula X Q) :
    Language (X → V) := fun valuation => formula.evaluate (fun x q => member q (valuation x)) = true

theorem formula_conjunction_is_intersection {X Q V : Type} (member : Q → V → Bool)
    (left right : Formula X Q) :
    formulaLanguage member (.both left right) =
      restrict (formulaLanguage member left) (formulaLanguage member right) := by
  funext valuation
  apply propext
  simp [formulaLanguage, Formula.evaluate, restrict, and_comm]

theorem residual_substitution_is_reindex {X Y Q S : Type} {arity : S → Nat}
    (grammar : Grammar Q S arity) (substitution : X → OpenTree Y S arity) (formula : Formula X Q) :
    formulaLanguage (fun q value => grammar.accepts value q) (formula.substitute grammar substitution) =
      reindex (fun valuation x => (substitution x).evaluate valuation)
        (formulaLanguage (fun q value => grammar.accepts value q) formula) := by
  funext valuation
  apply propext
  exact Eq.to_iff (congrArg (fun b => b = true)
    (Formula.evaluate_substitute grammar substitution valuation formula))

end Mettapedia.Logic.ConstraintTypes.Semantics
