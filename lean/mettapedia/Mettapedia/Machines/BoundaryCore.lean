import Mathlib.Data.Multiset.Functor

/-!
# A carrier-parametric call boundary

The answer carrier is a parameter. Ordered lists and occurrence multisets
share the sequencing laws, but their observations need not be interchangeable.
Batch selection stays outside continuation composition: success-priority
selection need not distribute over alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundaryCore

universe u

/-- Entry frames retain shared type/binding state. `merge` combines early
answers with body returns in the chosen carrier. -/
structure Protocol (M : Type u → Type u) (I F V O : Type u)
    (merge : M O → M O → M O) where
  early : I → M O
  enter : I → M F
  leave : F → V → M O
  select : M O → M O

variable {M : Type u → Type u} {I F V W O : Type u}
variable {merge : M O → M O → M O}

def Protocol.run [Monad M] (p : Protocol M I F V O merge)
    (body : F → M V) (input : I) : M O :=
  p.select (merge (p.early input)
    (p.enter input >>= fun frame => body frame >>= p.leave frame))

/-- Move a post-body computation into the return boundary. No result
selection, argument demand or shared frame is moved across this boundary. -/
def Protocol.after [Monad M] (p : Protocol M I F W O merge) (next : V → M W) :
    Protocol M I F V O merge where
  early := p.early
  enter := p.enter
  leave := fun frame value => next value >>= p.leave frame
  select := p.select

theorem Protocol.run_after [Monad M] [LawfulMonad M]
    (p : Protocol M I F W O merge) (next : V → M W) (body : F → M V) (input : I) :
    (p.after next).run body input =
      p.run (fun frame => body frame >>= next) input := by
  simp only [Protocol.run, Protocol.after, bind_assoc]

theorem Protocol.run_congr_body [Monad M]
    (p : Protocol M I F V O merge) (left right : F → M V)
    (same : ∀ frame, left frame = right frame) (input : I) :
    p.run left input = p.run right input := by
  have functions : left = right := funext same
  rw [functions]

end Mettapedia.Machines.BoundaryCore
