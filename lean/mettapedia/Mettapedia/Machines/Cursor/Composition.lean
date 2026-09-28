import Mettapedia.Machines.Cursor.Protocol

/-!
# Independent cursor composition

Two indexed protocols can be interleaved while retaining separate capability
indices and provider states. A request to one side cannot mutate the other.
Local implementation refinements compose without reproving the client.

This construction requires independent state. Aliased cursors, shared mutable
spaces, and externally visible effects require a joint provider with its own
laws; independence must not be inferred from the names of operations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory

universe u

variable {Base : Type u} {Left Right : Base → Type u}

def interleave (P : IndexedPolynomial.{u,u,u,u} Base Left)
    (Q : IndexedPolynomial.{u,u,u,u} Base Right) :
    IndexedPolynomial Base (fun base => Left base × Right base) where
  Shape base index := P.Shape base index.1 ⊕ Q.Shape base index.2
  Position request := match request with
    | .inl left => P.Position left
    | .inr right => Q.Position right
  next {_ index} request reply := match request with
    | .inl left => (P.next left reply, index.2)
    | .inr right => (index.1, Q.next right reply)

variable {P : IndexedPolynomial.{u,u,u,u} Base Left}
variable {Q : IndexedPolynomial.{u,u,u,u} Base Right}

def pairedProvider (left : Provider P) (right : Provider Q) :
    Provider (interleave P Q) where
  State base index := left.State base index.1 × right.State base index.2
  step state request := match request with
    | .inl operation =>
        let response := left.step state.1 operation
        ⟨response.1, response.2, state.2⟩
    | .inr operation =>
        let response := right.step state.2 operation
        ⟨response.1, state.1, response.2⟩

def pairedHom {left left' : Provider P} {right right' : Provider Q}
    (first : Hom left left') (second : Hom right right') :
    Hom (pairedProvider left right) (pairedProvider left' right') where
  map state := (first.map state.1, second.map state.2)
  step state request := by
    cases request with
    | inl operation =>
        have law := first.step state.1 operation
        dsimp only [pairedProvider]
        rw [← law]
        rfl
    | inr operation =>
        have law := second.step state.2 operation
        dsimp only [pairedProvider]
        rw [← law]
        rfl

/-- Each operation keeps the other component's state exactly, rather than
reconstructing it from its observed answers. -/
theorem paired_left_keeps_right (left : Provider P) (right : Provider Q)
    {base : Base} {index : Left base × Right base}
    (state : (pairedProvider left right).State base index)
    (request : P.Shape base index.1) :
    ((pairedProvider left right).step state (.inl request)).2.2 = state.2 := rfl

theorem paired_right_keeps_left (left : Provider P) (right : Provider Q)
    {base : Base} {index : Left base × Right base}
    (state : (pairedProvider left right).State base index)
    (request : Q.Shape base index.2) :
    ((pairedProvider left right).step state (.inr request)).2.1 = state.1 := rfl

namespace Hom

variable {Index : Base → Type u}
variable {R : IndexedPolynomial.{u,u,u,u} Base Index}
variable {A B C D : Provider R}

@[simp] theorem id_comp (h : Hom A B) : (Hom.id A).comp h = h := by cases h; rfl
@[simp] theorem comp_id (h : Hom A B) : h.comp (Hom.id B) = h := by cases h; rfl

theorem comp_assoc (first : Hom A B) (second : Hom B C) (third : Hom C D) :
    (first.comp second).comp third = first.comp (second.comp third) := rfl

end Hom

end Mettapedia.Machines.Cursor
