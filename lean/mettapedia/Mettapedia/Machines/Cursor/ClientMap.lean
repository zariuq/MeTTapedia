import Mettapedia.Machines.Cursor.Protocol

/-!
# Changing the client control representation

Cursor providers need not impose one physical continuation layout. A
coalgebra morphism between existing client realizations preserves each
request and its reply-indexed continuation. Consequently it preserves
execution on every provider, including the exact retained control at a
suspension point and all operation receipts.

This law complements provider refinement: a compiler can establish its
control translation locally, while a storage backend establishes its own
step law independently. It does not assert that an arbitrary C compiler or
resume table implements a coalgebra morphism.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ClientMap

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable {first second : Client (P := P) (Return := Return)}

def packet (M : Provider P) (h : first ⟶ second) {base : Base}
    (value : Packet M first base) : Packet M second base :=
  ⟨value.1, h.f base value.1 value.2.1, value.2.2⟩

def outcome (M : Provider P) (h : first ⟶ second) {base : Base} :
    Outcome M first base → Outcome M second base
  | .paused value => .paused (packet M h value)
  | .done value => .done value

/-- A local control translation preserves actual provider execution, rather
than unfolding a fresh copy of the original query when it resumes. -/
theorem advance (M : Provider P) (h : first ⟶ second) (charge : Charge M)
    (budget : Nat) {base : Base} (value : Packet M first base) :
    ((Cursor.advance M first charge budget value).1,
        outcome M h (Cursor.advance M first charge budget value).2) =
      Cursor.advance M second charge budget (packet M h value) := by
  induction budget generalizing value with
  | zero => rfl
  | succ budget ih =>
      rcases value with ⟨index, control, state⟩
      have law := congrArg (fun mapping => mapping base index control) h.h
      change Extension.map (P.withHoles Return) (fun b i => h.f b i)
          (first.str base index control) =
        second.str base index (h.f base index control) at law
      change ((Cursor.advance M first charge (budget + 1)
          ⟨index, control, state⟩).1,
        outcome M h (Cursor.advance M first charge (budget + 1)
          ⟨index, control, state⟩).2) =
        Cursor.advance M second charge (budget + 1)
          ⟨index, h.f base index control, state⟩
      simp only [Cursor.advance]
      rw [← law]
      cases layer : first.str base index control with
      | mk shape children =>
          cases shape with
          | inl returned => rfl
          | inr request =>
              dsimp only [withHoles] at children
              change (charge state request +
                  (Cursor.advance M first charge budget
                    ⟨_, children (M.step state request).1, (M.step state request).2⟩).1,
                outcome M h (Cursor.advance M first charge budget
                  ⟨_, children (M.step state request).1, (M.step state request).2⟩).2) = _
              have rest := ih ⟨_, children (M.step state request).1,
                (M.step state request).2⟩
              exact congrArg (fun result => (charge state request + result.1, result.2)) rest

end Mettapedia.Machines.Cursor.ClientMap
