import Mettapedia.TypeTheory.IndexedPolynomialFree

/-!
# Injective relabeling of typed holes

A free indexed tree remembers each constructor, recursive position and typed
hole. Injectively relabeling the holes therefore preserves the entire tree.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory

namespace Mettapedia.TypeTheory.IndexedPolynomial.Free

universe uBase uIndex uShape uPosition uHole uNext

variable {Base : Type uBase} {Index : Base → Type uIndex}
variable (P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
variable {H : (b : Base) → Index b → Type uHole}
variable {K : (b : Base) → Index b → Type uNext}

/-- Injective maps of typed holes induce injective maps of free indexed
polynomial trees, without any injectivity assumption on constructor data. -/
theorem map_injective
    (f : ∀ b i, H b i → K b i)
    (injective : ∀ b i, Function.Injective (f b i))
    (b : Base) (i : Index b) :
    Function.Injective (map P f b i) := by
  intro first second same
  induction first with
  | roll shape children ih =>
      cases second with
      | roll otherShape otherChildren =>
          cases shape with
          | inl seed =>
              have empty : children = fun position => position.elim := by
                funext position
                exact position.elim
              subst children
              cases otherShape with
              | inl otherSeed =>
                  have otherEmpty : otherChildren = fun position => position.elim := by
                    funext position
                    exact position.elim
                  subst otherChildren
                  change map P f b _ (pure P seed) =
                    map P f b _ (pure P otherSeed) at same
                  rw [map_pure, map_pure] at same
                  have sameSeed : seed = otherSeed := by
                    apply injective b _
                    injection same with _ h _
                    exact Sum.inl.inj h
                  subst otherSeed
                  rfl
              | inr other =>
                  change (position : P.Position other) →
                    P.Free H b (P.next other position) at otherChildren
                  change map P f b _ (pure P seed) =
                    map P f b _ (node P other otherChildren) at same
                  rw [map_pure, map_node] at same
                  cases same
          | inr ctor =>
              change (position : P.Position ctor) →
                P.Free H b (P.next ctor position) at children
              change ∀ position, ∀ {second : P.Free H b (P.next ctor position)},
                map P f b _ (children position) = map P f b _ second →
                children position = second at ih
              cases otherShape with
              | inl otherSeed =>
                  have otherEmpty : otherChildren = fun position => position.elim := by
                    funext position
                    exact position.elim
                  subst otherChildren
                  change map P f b _ (node P ctor children) =
                    map P f b _ (pure P otherSeed) at same
                  rw [map_node, map_pure] at same
                  cases same
              | inr otherCtor =>
                  change (position : P.Position otherCtor) →
                    P.Free H b (P.next otherCtor position) at otherChildren
                  change map P f b _ (node P ctor children) =
                    map P f b _ (node P otherCtor otherChildren) at same
                  rw [map_node, map_node] at same
                  have sameCtor : ctor = otherCtor := by
                    injection same with _ h _
                    exact Sum.inr.inj h
                  subst sameCtor
                  have sameChildren : children = otherChildren := by
                    funext position
                    apply ih position
                    injection same with _ _ h
                    exact congrFun h position
                  subst sameChildren
                  rfl

end Mettapedia.TypeTheory.IndexedPolynomial.Free
