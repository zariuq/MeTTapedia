import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagQueryReadout
import Mettapedia.Languages.Maude.ACUFoldControls

/-! A middle-position residual variable retains duplicate resources.
Static negatives distinguish one bag variable from repeated or nested
variables, which require a stronger query profile.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery.Controls

open Mettapedia.Languages
open Maude.ACUFoldControls

def base? := (ACUBagCompilation.prepare operation).toOption
def apple : Maude.Term := .app "vending.a" []
def middle : Maude.Term := operation.merge apple (operation.merge (.var "M") coffee)
def atEnd : Maude.Term := operation.merge apple (operation.merge coffee (.var "M"))

#guard base?.isSome
#guard (base?.bind fun base => (prepare operation base middle).toOption).isSome
#guard (base?.bind fun base => (prepare operation base atEnd).toOption).isSome
#guard ((base?.bind fun base => (prepare operation base middle).toOption).map
    (fun prepared => (prepared.heads, prepared.variableName))) ==
  some ([apple, coffee], "M")
#guard (base?.bind fun base => (prepare operation base (operation.merge (.var "M") (.var "M"))).toOption).isNone
#guard (base?.bind fun base => (prepare operation base (operation.merge (.var "M") (.var "N"))).toOption).isNone
#guard (base?.bind fun base =>
    (prepare operation base (operation.merge (.app "nested" [.var "M"]) (.var "N"))).toOption).isNone

private theorem apple_sorted : Maude.HasSort Maude.Examples.vending.signature [] apple "Marking" :=
  .app (declaration := ⟨"vending.a", "a", [], "Marking", {constructor := true}⟩)
    (by simp [Maude.Examples.vending, Maude.Examples.markingOperators]) .nil

private theorem lift_atom {context : Maude.VariableContext} {label sort : String}
    (typed : Maude.HasSort Maude.Examples.vending.signature [] (.app label []) sort) :
    Maude.HasSort Maude.Examples.vending.signature context (.app label []) sort := by
  cases typed with
  | @app declaration _ member arguments =>
    have noArguments : declaration.arguments = [] := by
      apply List.length_eq_zero_iff.mp
      simpa only [List.length_nil] using arguments.length_eq.symm
    exact .app member (by rw [noArguments]; exact .nil)

private theorem merge_context {context : Maude.VariableContext} {left right : Maude.Term}
    (first : Maude.HasSort Maude.Examples.vending.signature context left "Marking")
    (second : Maude.HasSort Maude.Examples.vending.signature context right "Marking") :
    Maude.HasSort Maude.Examples.vending.signature context (operation.merge left right) "Marking" := by
  have children : List.Forall₂ (Maude.HasSort Maude.Examples.vending.signature context)
      [left, right] operation.declaration.arguments := by
    rw [operation.arguments]
    exact .cons (by simpa only [operation] using first) (.cons (by simpa only [operation] using second) .nil)
  simpa only [operation, Maude.ACUOperation.merge] using Maude.HasSort.app operation.declared children

theorem middle_sorted : Maude.HasSort Maude.Examples.vending.signature [("M", "Marking")] middle "Marking" := by
  apply merge_context (lift_atom apple_sorted)
  exact merge_context (.var (by simp [List.lookup])) (lift_atom coffee_sorted)

theorem middle_binding_preserves_duplicates :
    Maude.Equivalent Maude.Examples.vending [] "Marking"
      (operation.fold [quarter, apple, coffee, quarter])
      (middle.substitute (assignment operation "M" [quarter, quarter])) := by
  have sourceSorted : operation.Sorted [quarter, apple, coffee, quarter] := by
    intro term member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact quarter_sorted
    · exact apple_sorted
    · exact coffee_sorted
    · exact quarter_sorted
  have ground : ∀ head ∈ [apple, coffee], head.variables = [] := by
    intro head member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [apple, Maude.Term.variables, List.flatMap_nil]
    · cases List.mem_singleton.mp member
      simp only [coffee, Maude.Term.variables, List.flatMap_nil]
  have meaning := residual_authorizes_target operation (by decide_cbv) middle [apple, coffee]
    [quarter, quarter] "M" (operation.fold_sorted _ sourceSorted)
    (by simpa only [operation] using middle_sorted) (by decide_cbv) ground (by decide_cbv)
  simpa only [operation] using meaning

#print axioms middle_binding_preserves_duplicates

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery.Controls
