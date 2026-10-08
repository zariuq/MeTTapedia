import Mathlib.Logic.Equiv.Basic

/-!
# Uniform origins in dependent sum/product exchange

Summing a family of functions keeps one origin for all arguments.
A function into a summed family may select a different origin at every
argument. The canonical exchange map retains the former discipline; its
image is exactly the functions with a common origin. Thus the universal
property of forward dependent-sum transport does not make that forward
functor preserve dependent products.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentSumProductExchange

universe u v w
variable {Origin : Type u} {Input : Type v} {Evidence : Origin → Input → Type w}

def exchange (uniform : Σ origin, ∀ input, Evidence origin input) :
    ∀ input, Σ origin, Evidence origin input :=
  fun input => ⟨uniform.1, uniform.2 input⟩

theorem common_origin (uniform : Σ origin, ∀ input, Evidence origin input)
    (first second : Input) : (exchange uniform first).1 = (exchange uniform second).1 := rfl

theorem exchange_injective [Nonempty Input] : Function.Injective (@exchange Origin Input Evidence) := by
  intro first second same
  obtain ⟨input⟩ := ‹Nonempty Input›
  have origins := congrArg (fun value => (value input).1) same
  rcases first with ⟨origin, first⟩
  rcases second with ⟨other, second⟩
  dsimp [exchange] at origins
  cases origins
  congr 1
  funext input
  exact eq_of_heq (Sigma.mk.inj_iff.mp (congrFun same input)).2

def recover (value : ∀ input, Σ origin, Evidence origin input)
    (origin : Origin) (same : ∀ input, (value input).1 = origin) :
    Σ origin, ∀ input, Evidence origin input :=
  ⟨origin, fun input => by rw [← same input]; exact (value input).2⟩

theorem recover_computes (value : ∀ input, Σ origin, Evidence origin input)
    (origin : Origin) (same : ∀ input, (value input).1 = origin) :
    exchange (recover value origin same) = value := by
  funext input
  apply Sigma.ext (same input).symm
  dsimp [exchange, recover]
  exact cast_heq _ _

/-- This criterion retains actual evidence in each dependent codomain;
it is not a claim about the support predicates alone. -/
theorem in_image_iff_common_origin (value : ∀ input, Σ origin, Evidence origin input) :
    (∃ uniform, exchange uniform = value) ↔ ∃ origin, ∀ input, (value input).1 = origin := by
  constructor
  · rintro ⟨uniform, rfl⟩
    exact ⟨uniform.1, fun _ => rfl⟩
  · rintro ⟨origin, same⟩
    exact ⟨recover value origin same, recover_computes value origin same⟩

namespace Controls

def mixedOrigins : Bool → Σ _ : Bool, Unit := fun input => ⟨input, ()⟩

theorem mixed_origins_not_uniform :
    ¬ ∃ uniform : Σ _ : Bool, Bool → Unit, exchange uniform = mixedOrigins := by
  rintro ⟨uniform, same⟩
  have common := common_origin uniform false true
  rw [same] at common
  exact Bool.false_ne_true common

theorem exchange_not_surjective :
    ¬ Function.Surjective (@exchange Bool Bool (fun _ _ => Unit)) := by
  intro onto
  exact mixed_origins_not_uniform (onto mixedOrigins)

def dependentUniform : Σ origin : Nat, ∀ input : Nat, Fin (origin + input + 1) :=
  ⟨2, fun input => ⟨input, by omega⟩⟩

theorem varying_codomain_retained (input : Nat) :
    (exchange dependentUniform input).1 = 2 ∧
      (exchange dependentUniform input).2.val = input := ⟨rfl, rfl⟩

theorem dependent_functions_not_collapsed :
    Function.Injective (@exchange Nat Nat (fun origin input => Fin (origin + input + 1))) :=
  exchange_injective

end Controls

end Mettapedia.TypeTheory.DependentSumProductExchange
