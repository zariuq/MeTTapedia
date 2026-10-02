import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.UniverseLevel.Extension

/-!
# The tower along embeddings of level orders

An embedding of level orders maps the level constants of the tower's heads. It is a
morphism of the towers' rule packages: head typing, universes and joins are preserved
by construction, and the order and the equality of universes are preserved because
comparisons of level expressions are conservative along an embedding. So every derivable
statement of the tower over the smaller level order is derivable in the tower over the
larger one, with its level constants mapped. The order and the equality of universes are
also reflected.

The finite levels embed into every level order, so every derivation of the tower over the
natural numbers is a derivation of the tower over any level order.

Positive example: the typing of the first universe in the second one, over the natural
numbers, is a typing over every level order. Negative example: the map of heads that
sends every level constant to the least level does not reflect the order of universes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

open Mettapedia.TypeTheory.UniverseLevel
open TypedEquality

namespace LevelTower

variable {L L' : Type}

/-- Map the level constants of a head. -/
def Head.map (f : L → L') : Head L → Head L'
  | .legacyGround => .legacyGround
  | .sort e => .sort (e.map f)

variable [LevelOrder L] [LevelOrder L']

/-- An embedding fixes the least level expression. -/
theorem map_zero (f : LevelOrder.Embedding L L') :
    (zero : LevelExpr L).map f = (zero : LevelExpr L') := by
  show LevelExpr.const (f LevelOrder.bot) = LevelExpr.const LevelOrder.bot
  rw [f.map_bot]

/-- The order of universes is preserved and reflected by an embedding. -/
theorem cumulative_map_iff (f : LevelOrder.Embedding L L') {u v : Head L} :
    Cumulative (Head.map f u) (Head.map f v) ↔ Cumulative u v := by
  cases u with
  | legacyGround => exact Iff.rfl
  | sort l =>
    cases v with
    | legacyGround => exact Iff.rfl
    | sort r => exact LevelNF.level_le_conservative f l r

/-- The equality of heads is preserved and reflected by an embedding. -/
theorem headEq_map_iff (f : LevelOrder.Embedding L L') {u v : Head L} :
    HeadEq (Head.map f u) (Head.map f v) ↔ HeadEq u v := by
  cases u with
  | legacyGround =>
    cases v with
    | legacyGround => exact Iff.rfl
    | sort _ => exact Iff.rfl
  | sort l =>
    cases v with
    | legacyGround => exact Iff.rfl
    | sort r => exact LevelNF.level_eq_conservative f l r

/-- **An embedding of level orders is a morphism of towers.** -/
theorem morphism (f : LevelOrder.Embedding L L') :
    (rules L).Morphism (rules L') (Head.map f) where
  headTyping := by
    intro head universeHead typing
    cases typing with
    | legacyGround =>
      show HeadTyping (Head.legacyGround) (.sort ((zero : LevelExpr L).map f))
      rw [map_zero f]
      exact .legacyGround
    | sort level => exact .sort _
  isUniverse := by
    intro head isUniverse
    cases isUniverse with
    | sort level => exact .sort _
  join := by
    intro left right result joined
    cases joined with
    | sorts l r => exact .sorts _ _
  cumulative := fun below => (cumulative_map_iff f).mpr below
  headEq := fun same => (headEq_map_iff f).mpr same
  constantType := by
    intro name type known
    exact nomatch known
  computation := by
    intro n left right step
    exact step.elim

/-- **Every derivable statement of the tower over `L` is derivable in the tower over `L'`**,
with its level constants mapped along the embedding. -/
theorem derivable_map (f : LevelOrder.Embedding L L') {st : Statement (Head L)}
    (derivation : Derivable (rules L) st) :
    Derivable (rules L') (st.mapHead (Head.map f)) :=
  derivation.mapHead (morphism f)

/-- Every derivable statement of the tower over the natural numbers is derivable in the
tower over any level order. -/
theorem derivable_ofNat (L : Type) [LevelOrder L] {st : Statement (Head Nat)}
    (derivation : Derivable (rules Nat) st) :
    Derivable (rules L) (st.mapHead (Head.map (LevelOrder.Embedding.ofNat L))) :=
  derivable_map (LevelOrder.Embedding.ofNat L) derivation

/-! ## Examples -/

/-- The first universe is a type of the second one, over the natural numbers. -/
theorem first_in_second :
    Derivable (rules Nat)
      (.typing (.nil : Ctx Nat 0) (.head (.sort (.const 0)))
        (.head (.sort (.succ (.const 0))))) :=
  .headType (HeadTyping.sort _)

/-- The same typing, over any level order. -/
example (L : Type) [LevelOrder L] :
    Derivable (rules L)
      (.typing (.nil : Ctx L 0) (.head (.sort (.const (LevelOrder.ofNat 0))))
        (.head (.sort (.succ (.const (LevelOrder.ofNat 0)))))) :=
  derivable_ofNat L first_in_second

/-- The map that sends every level constant to the least level is not an embedding, and it
does not reflect the order of universes: `(u 1) ⊑ (u 0)` fails, while its image
`(u 0) ⊑ (u 0)` holds. -/
theorem collapse_not_reflecting :
    Cumulative (Head.map (fun _ : Nat => (0 : Nat)) (.sort (.const 1)))
        (Head.map (fun _ : Nat => (0 : Nat)) (.sort (.const 0))) ∧
      ¬ Cumulative (Head.sort (.const (1 : Nat))) (Head.sort (.const (0 : Nat))) := by
  constructor
  · intro _
    exact le_refl _
  · intro below
    exact absurd (below fun _ => 0) (by decide)

end LevelTower

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
