import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Ground binding application is stable under consistent extension

Adding bindings for other schema parameters does not change an already-ground
instance of a constructor schema. The existing `isMatchCorrect` predicate
specifies the binder-free constructor fragment; the result does not assume
that the bindings originated from a particular matching derivation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.MatchBindingExtension

open Syntax Match MatchSpec

/-- The first selected binding, including its key, is preserved by extension. -/
theorem find_preserved {initial final : Bindings} (extension : BindingsExtends initial final)
    {name : String} {entry : String × Pattern}
    (found : initial.find? (·.1 == name) = some entry) :
    final.find? (·.1 == name) = some entry := by
  have tested := List.find?_some found
  have key : entry.1 = name := beq_iff_eq.mp tested
  cases entry with
  | mk keyName value =>
    simp only at key
    subst keyName
    exact extension name value found

/-- Binding lookup preserves every previously selected value. -/
theorem lookup_preserved {initial final : Bindings} (extension : BindingsExtends initial final)
    {name : String} {value : Pattern} (found : initial.lookup name = some value) :
    final.lookup name = some value := by
  simp only [Bindings.lookup] at found ⊢
  obtain ⟨entry, foundEntry, valueEq⟩ := Option.map_eq_some_iff.mp found
  rw [find_preserved extension foundEntry]
  simpa only [Option.map_some, Option.some.injEq] using valueEq

private theorem matchCorrectList_member {patterns : List Pattern} {pattern : Pattern}
    (correct : isMatchCorrectListAux patterns = true) (member : pattern ∈ patterns) :
    Match.Pattern.isMatchCorrect pattern = true := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
    simp only [isMatchCorrectListAux, Bool.and_eq_true] at correct
    rcases List.mem_cons.mp member with rfl | later
    · exact correct.1
    · exact ih correct.2 later

private theorem groundList_member {depth : Nat} {patterns : List Pattern} {pattern : Pattern}
    (ground : Pattern.isGroundListAt depth patterns = true) (member : pattern ∈ patterns) :
    pattern.isGroundAt depth = true := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
    simp only [Pattern.isGroundListAt, Bool.and_eq_true] at ground
    rcases List.mem_cons.mp member with rfl | later
    · exact ground.1
    · exact ih ground.2 later

/-- A ground constructor-schema instance is unchanged when the binding map
is consistently extended. Values may themselves contain binders. -/
theorem applyBindings_eq_of_extends_of_ground {initial final : Bindings} {pat : Pattern}
    (correct : Match.Pattern.isMatchCorrect pat = true) (extension : BindingsExtends initial final)
    (ground : (applyBindings initial pat).isGround = true) :
    applyBindings final pat = applyBindings initial pat := by
  revert correct ground
  induction pat using Pattern.inductionOn with
  | hbvar index => intro _ _; simp only [applyBindings]
  | hfvar name =>
    intro _ ground
    cases found : initial.find? (·.1 == name) with
    | none => simp [applyBindings, found, Pattern.isGround, Pattern.isGroundAt] at ground
    | some entry =>
      simp only [applyBindings, found, find_preserved extension found]
  | happly constructor arguments ih =>
    intro correct ground
    simp only [Match.Pattern.isMatchCorrect, isMatchCorrectAux] at correct
    simp only [applyBindings, Pattern.isGround, Pattern.isGroundAt] at ground
    simp only [applyBindings]
    apply congrArg (Pattern.apply constructor)
    exact List.map_congr_left (fun argument member =>
      ih argument member (matchCorrectList_member correct member)
        (groundList_member ground (List.mem_map.mpr ⟨argument, member, rfl⟩)))
  | hlambda => intro correct _; simp [Match.Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hmultiLambda => intro correct _; simp [Match.Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hsubst => intro correct _; simp [Match.Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hcollection => intro correct _; simp [Match.Pattern.isMatchCorrect, isMatchCorrectAux] at correct

/-- Additional captures leave a nested constructor instance unchanged, even
when one captured value is itself a closed binder. -/
theorem control_nested_constructor_closed_binder :
    applyBindings [("x", .lambda "bound" (.bvar 0))]
        (.apply "wrap" [.fvar "x", .apply "zero" []]) =
      applyBindings [("x", .lambda "bound" (.bvar 0)), ("unused", .apply "unit" [])]
        (.apply "wrap" [.fvar "x", .apply "zero" []]) := by
  symm
  apply applyBindings_eq_of_extends_of_ground
  · rfl
  · intro name value found
    simp only [List.find?_cons, List.find?_nil] at found
    split at found <;> simp_all
  · simp [applyBindings, Pattern.isGround, Pattern.isGroundAt, Pattern.isGroundListAt]

/-- A consistent extension can change a schema that was not yet ground. -/
theorem control_groundness_required :
    BindingsExtends [] [("x", .apply "unit" [])] ∧
      (applyBindings [] (.apply "wrap" [.fvar "x"])).isGround = false ∧
      applyBindings [] (.apply "wrap" [.fvar "x"]) ≠
        applyBindings [("x", .apply "unit" [])] (.apply "wrap" [.fvar "x"]) := by
  constructor
  · intro name value found
    cases found
  · constructor
    · simp [applyBindings, Pattern.isGround, Pattern.isGroundAt, Pattern.isGroundListAt]
    · simp [applyBindings]

/-- Groundness alone does not protect an instance from overwriting a capture. -/
theorem control_consistent_extension_required :
    ¬ BindingsExtends [("x", .apply "one" [])] [("x", .apply "two" [])] ∧
      (applyBindings [("x", .apply "one" [])] (.fvar "x")).isGround = true ∧
      applyBindings [("x", .apply "one" [])] (.fvar "x") ≠
        applyBindings [("x", .apply "two" [])] (.fvar "x") := by
  constructor
  · intro extension
    have preserved := extension "x" (.apply "one" []) (by rfl)
    simp at preserved
  · constructor
    · simp [applyBindings, Pattern.isGround, Pattern.isGroundAt, Pattern.isGroundListAt]
    · simp [applyBindings]

end Mettapedia.OSLF.MeTTaIL.MatchBindingExtension
