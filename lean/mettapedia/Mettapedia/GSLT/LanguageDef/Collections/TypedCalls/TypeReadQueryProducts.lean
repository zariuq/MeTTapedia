import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRows

/-! # Ordered Cartesian type families under one growing coordinate world -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryProducts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQueryWorldRelation (Related)
open TypeReadQueryWorlds

def ProductsRelated (world : Coordinates) : List (List Atom) → List (List Atom) → Prop :=
  List.Forall₂ (TypesRelated world)

def ProductAnswers (world : Coordinates) : Except Unit (List (List Atom)) → Except Unit (List (List Atom)) → Prop :=
  CheckedRelated (ProductsRelated world)

theorem prepend (world : Coordinates) {first second : Atom} (head : AtomRelated world first second)
    {left right : List (List Atom)} (tails : ProductsRelated world left right) :
    ProductsRelated world (left.map (first :: ·)) (right.map (second :: ·)) := by
  induction tails with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (types_cons head pair) ih

theorem product (world : Coordinates) {first second : List Atom} (heads : TypesRelated world first second)
    {left right : List (List Atom)} (tails : ProductsRelated world left right) :
    ProductsRelated world (first.flatMap fun head => left.map (head :: ·))
      (second.flatMap fun head => right.map (head :: ·)) := by
  induction first generalizing second with
  | nil => rw [heads.2.2]; exact .nil
  | cons head rest ih =>
      rw [heads.2.2]
      simp only [List.map_cons, List.flatMap_cons]
      exact List.rel_append (prepend world (types_member heads List.mem_cons_self) tails)
        (ih (types_tail heads))

theorem expression (world : Coordinates) {first second : List Atom} (types : TypesRelated world first second) :
    AtomRelated world (.expression first) (.expression second) := by
  refine ⟨types.1, types.2.1, ?_⟩
  simpa only [renameAtom, renameAtomList_eq_map] using congrArg Atom.expression types.2.2

theorem tuple_families (world : Coordinates) {first second : List (List Atom)}
    (products : ProductsRelated world first second) :
    TypesRelated world (first.map Atom.expression) (second.map Atom.expression) := by
  induction products with
  | nil => exact ⟨rfl, by simp [atomListVariables], rfl⟩
  | cons pair rest ih => exact types_cons (expression world pair) ih

theorem productPlan (keys : List (NativeTypeDemand.Question Atom)) :
    ∀ world : Coordinates, (∀ key ∈ keys, viewWorlds.keys world key key) →
      Related viewWorlds ProductAnswers world (NativeTypeDemand.productPlan keys) (NativeTypeDemand.productPlan keys) := by
  induction keys with
  | nil => intro world _; exact .pure (.ok (.cons ⟨rfl, by simp [atomListVariables], rfl⟩ .nil))
  | cons key keys ih =>
      intro world safeKeys
      apply Related.read (safeKeys key List.mem_cons_self)
      intro next grown firstReply secondReply replies
      cases replies with
      | class_ _ | kind _ => exact .pure .error
      | types types =>
          rename_i firstTypes secondTypes
          have sameEmpty : secondTypes.isEmpty = firstTypes.isEmpty := by rw [types.2.2, List.isEmpty_map]
          dsimp only
          rw [sameEmpty]
          by_cases empty : firstTypes.isEmpty = true
          · simp only [empty, if_true]
            exact .pure (.ok .nil)
          · simp only [empty]
            apply Mettapedia.Machines.ReadOnlyQueryWorldRelation.map_related viewWorlds ProductAnswers ProductAnswers
            · exact ih next (fun key member => viewWorlds.keys_mono grown (safeKeys key (List.mem_cons_of_mem _ member)))
            · intro last extended left right related
              cases related with
              | error => exact .error
              | ok tails => exact .ok (product last (types_mono extended types) tails)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryProducts
