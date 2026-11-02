import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternReadback

/-! Source values and captured environments have injective encodings.
Closures retain their lambda/group/slot references and captured values.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem environment_as_linked (items : List OCaml.Value) :
    environment items = linked "MlEnvironmentCons" "MlEnvironmentNil" (items.map value) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simpa only [environment, linked, List.map_cons, List.foldr_cons] using
        congrArg (fun tail => node "MlEnvironmentCons" [value first, tail]) ih

theorem linked_injective (cons nil : String) (different : cons ≠ nil) :
    Function.Injective (linked cons nil) := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons _ _ => simp [linked, node, Ne.symm different] at same
  | cons head rest ih =>
      intro second same
      cases second with
      | nil => simp [linked, node, different] at same
      | cons other tail =>
          have arguments := (Pattern.apply.inj same).2
          have both := List.cons.inj arguments
          have suffix := (List.cons.inj both.2).1
          exact congrArg₂ List.cons both.1 (ih suffix)

theorem value_injective : Function.Injective value := by
  intro first
  refine OCaml.Value.rec
    (motive_1 := fun first => ∀ second, value first = value second → first = second)
    (motive_2 := fun first => ∀ second, first.map value = second.map value → first = second)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ first
  · intro datum second same
    exact (literal_instance_source same).symm
  · intro fields ih second same
    cases second with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        rw [literal_read_value, literal_read_value] at impossible
        cases impossible
    | tuple actuals =>
        have fieldsSame := (List.cons.inj (Pattern.apply.inj same).2).1
        rw [valueList_as_values, valueList_as_values] at fieldsSame
        exact congrArg OCaml.Value.tuple (ih actuals (values_injective fieldsSame))
    | cons | variant => simp [value, node] at same
    | closure function captured => cases function <;> simp [value, node] at same
  · intro head tail headIH tailIH second same
    cases second with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        rw [literal_read_value, literal_read_value] at impossible
        cases impossible
    | cons first rest =>
        have arguments := (Pattern.apply.inj same).2
        have both := List.cons.inj arguments
        exact congrArg₂ OCaml.Value.cons (headIH first both.1) (tailIH rest (List.cons.inj both.2).1)
    | tuple | variant => simp [value, node] at same
    | closure function captured => cases function <;> simp [value, node] at same
  · intro typeId constructor fields ih second same
    cases second with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        rw [literal_read_value, literal_read_value] at impossible
        cases impossible
    | variant actualType actualConstructor actuals =>
        have arguments := List.cons.inj (Pattern.apply.inj same).2
        obtain ⟨rfl, rfl⟩ := tag_injective arguments.1
        have fieldsSame := (List.cons.inj arguments.2).1
        rw [valueList_as_values, valueList_as_values] at fieldsSame
        exact congrArg (OCaml.Value.variant typeId constructor) (ih actuals (values_injective fieldsSame))
    | tuple | cons => simp [value, node] at same
    | closure function captured => cases function <;> simp [value, node] at same
  · intro function captured ih second same
    cases second with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        rw [literal_read_value, literal_read_value] at impossible
        cases impossible
    | tuple | cons | variant => cases function <;> simp [value, node] at same
    | closure other actuals =>
        cases function with
        | lambda reference =>
            cases other with
            | recursive group slot => simp [value, node] at same
            | lambda actualReference =>
                have arguments := List.cons.inj (Pattern.apply.inj same).2
                have referenceSame := code_injective (List.cons.inj (Pattern.apply.inj arguments.1).2).1
                have environmentSame := (List.cons.inj arguments.2).1
                rw [environment_as_linked, environment_as_linked] at environmentSame
                have capturedSame := ih actuals (linked_injective _ _ (by decide) environmentSame)
                subst actualReference
                subst actuals
                rfl
        | recursive group slot =>
            cases other with
            | lambda reference => simp [value, node] at same
            | recursive actualGroup actualSlot =>
                have arguments := List.cons.inj (Pattern.apply.inj same).2
                have indices := List.cons.inj (Pattern.apply.inj arguments.1).2
                have groupSame := code_injective indices.1
                have slotSame := code_injective (List.cons.inj indices.2).1
                have environmentSame := (List.cons.inj arguments.2).1
                rw [environment_as_linked, environment_as_linked] at environmentSame
                have capturedSame := ih actuals (linked_injective _ _ (by decide) environmentSame)
                subst actualGroup
                subst actualSlot
                subst actuals
                rfl
  · intro second same
    cases second with
    | nil => rfl
    | cons _ _ => cases same
  · intro head rest headIH restIH second same
    cases second with
    | nil => cases same
    | cons other tail =>
        have both := List.cons.inj same
        exact congrArg₂ List.cons (headIH other both.1) (restIH tail both.2)

theorem environment_injective : Function.Injective environment := by
  intro first second same
  rw [environment_as_linked, environment_as_linked] at same
  have mapped := linked_injective "MlEnvironmentCons" "MlEnvironmentNil" (by decide) same
  exact List.map_injective_iff.mpr value_injective mapped

#print axioms value_injective
#print axioms environment_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
