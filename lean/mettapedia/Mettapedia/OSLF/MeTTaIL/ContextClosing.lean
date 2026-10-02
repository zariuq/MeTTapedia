import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Binding a free name in a plugged context

Closing a free name into a bound variable acts on a plugged context piece by
piece: on the siblings of the hole at the depth they sit at, and on what is
plugged at the depth of the hole.  The depth of the hole is the number of
binders above it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.DerivedContexts

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)

namespace OneHoleContext

/-- The number of binders above the hole. -/
def binders : OneHoleContext → Nat
  | .hole => 0
  | .apply _ _ inner _ => inner.binders
  | .lambda _ inner => inner.binders + 1
  | .multiLambda arity _ inner => inner.binders + arity
  | .substBody inner _ => inner.binders + 1
  | .substReplacement _ inner => inner.binders
  | .collection _ _ inner _ _ => inner.binders

/-- Close a free name in every sibling of the hole. -/
def closeName (name : String) : Nat → OneHoleContext → OneHoleContext
  | _, .hole => .hole
  | depth, .apply constructor before inner after =>
      .apply constructor (before.map (closeFVar depth name)) (inner.closeName name depth)
        (after.map (closeFVar depth name))
  | depth, .lambda binderName inner => .lambda binderName (inner.closeName name (depth + 1))
  | depth, .multiLambda arity binderNames inner =>
      .multiLambda arity binderNames (inner.closeName name (depth + arity))
  | depth, .substBody inner replacement =>
      .substBody (inner.closeName name (depth + 1)) (closeFVar depth name replacement)
  | depth, .substReplacement body inner =>
      .substReplacement (closeFVar (depth + 1) name body) (inner.closeName name depth)
  | depth, .collection collectionType before inner after rest =>
      .collection collectionType (before.map (closeFVar depth name)) (inner.closeName name depth)
        (after.map (closeFVar depth name)) rest

/-- Closing a name in the siblings does not move the hole. -/
theorem binders_closeName (name : String) :
    ∀ (context : OneHoleContext) (depth : Nat), (context.closeName name depth).binders =
      context.binders
  | .hole, _ => rfl
  | .apply _ _ inner _, depth => by simp only [closeName, binders, binders_closeName name inner]
  | .lambda _ inner, depth => by simp only [closeName, binders, binders_closeName name inner]
  | .multiLambda _ _ inner, depth => by
      simp only [closeName, binders, binders_closeName name inner]
  | .substBody inner _, depth => by simp only [closeName, binders, binders_closeName name inner]
  | .substReplacement _ inner, depth => by
      simp only [closeName, binders, binders_closeName name inner]
  | .collection _ _ inner _ _, depth => by
      simp only [closeName, binders, binders_closeName name inner]

/-- **Closing a name in a plugged context** closes it in the context and, at
the depth of the hole, in what is plugged. -/
theorem closeFVar_fill (name : String) :
    ∀ (context : OneHoleContext) (depth : Nat) (pattern : Pattern),
      closeFVar depth name (context.fill pattern) =
        (context.closeName name depth).fill (closeFVar (depth + context.binders) name pattern)
  | .hole, depth, pattern => by simp [fill, closeName, binders]
  | .apply constructor before inner after, depth, pattern => by
      rw [fill, closeFVar]
      simp only [List.map_append, List.map_cons, closeFVar_fill name inner depth pattern,
        closeName, fill, binders]
  | .lambda binderName inner, depth, pattern => by
      rw [fill, closeFVar, closeFVar_fill name inner (depth + 1) pattern]
      simp only [closeName, fill, binders]
      congr 3
      omega
  | .multiLambda arity binderNames inner, depth, pattern => by
      rw [fill, closeFVar, closeFVar_fill name inner (depth + arity) pattern]
      simp only [closeName, fill, binders]
      congr 3
      omega
  | .substBody inner replacement, depth, pattern => by
      rw [fill, closeFVar, closeFVar_fill name inner (depth + 1) pattern]
      simp only [closeName, fill, binders]
      congr 3
      omega
  | .substReplacement body inner, depth, pattern => by
      rw [fill, closeFVar, closeFVar_fill name inner depth pattern]
      simp only [closeName, fill, binders]
  | .collection collectionType before inner after rest, depth, pattern => by
      rw [fill, closeFVar]
      simp only [List.map_append, List.map_cons, closeFVar_fill name inner depth pattern,
        closeName, fill, binders]

end OneHoleContext

end Mettapedia.OSLF.MeTTaIL.DerivedContexts
