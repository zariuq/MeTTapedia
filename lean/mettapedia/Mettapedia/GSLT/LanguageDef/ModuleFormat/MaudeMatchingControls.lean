import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeEquationInstances
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatchReadback
import Mettapedia.Languages.Maude.SortedControls

/-! A nonlinear authored equation is prepared and instantiated by the real
matcher. Raw matching checks repeated-variable consistency; its sorted
binding check additionally rejects a Nat captured for an Element variable.
These are row-instance controls, not ACU normalization certificates. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.MatchingControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def row : Maude.Row := ⟨"idempotent", [("X", "Element")], [],
  .app "combine" [.var "X", .var "X"], .var "X"⟩
def theory : Maude.Theory := {Maude.SortedControls.theory with equations := [row]}
def prepared : Prepared := (prepare theory).toOption.get (by decide_cbv)
def e0 : Maude.Term := .app "e0" []
def zero : Maude.Term := .app "zero" []
def same : Maude.Term := .app "combine" [e0, e0]
def different : Maude.Term := .app "combine" [e0, zero]
def wrongSort : Maude.Term := .app "combine" [zero, zero]

theorem preparation : prepare theory = .ok prepared := by
  have accepted : (prepare theory).toOption.isSome = true := by decide_cbv
  cases result : prepare theory with
  | error message => simp [result, Except.toOption] at accepted
  | ok value =>
      have selected : prepared = value := by simp [prepared, result, Except.toOption]
      exact congrArg Except.ok selected.symm
theorem context_exact : row.usedContext = [("X", "Element")] := by decide_cbv

#guard (matchPattern (encode row.left) (encode same)).length == 1
#guard (matchPattern (encode row.left) (encode different)).isEmpty
#guard (matchPattern (encode row.left) (encode wrongSort)).length == 1

theorem e0_typed : Maude.HasSort theory.signature [] e0 "Element" :=
  .app (declaration := Maude.SortedControls.unit)
    (by simp [theory, Maude.SortedControls.theory, Maude.SortedControls.signature]) .nil

theorem source_valuation_typed :
    Maude.TypedValuation theory.signature [] row.usedContext (fun _ => e0) := by
  intro name sort found
  rw [context_exact] at found
  by_cases same : name = "X"
  · subst name
    have selected : "Element" = sort := by simpa using found
    rw [← selected]
    exact e0_typed
  · have different : (name == "X") = false := beq_eq_false_iff_ne.mpr same
    simp [List.lookup, different] at found

theorem prepared_sorted_firing :
    OpenSortedEquationInstance (freeContext []) (engineBasePremises Engine.RelationEnv.empty)
      prepared.language (encode same) (encode e0) := by
  have fired := prepared_unconditional_sorted_instance (engineBasePremises Engine.RelationEnv.empty)
    preparation [] (row := row) (index := 0) (by simp [theory]) (fun _ => e0)
    rfl (by decide_cbv) source_valuation_typed
  simpa only [row, same, Maude.Term.substitute, List.map_cons, List.map_nil] using fired

theorem zero_not_element : ¬ Maude.HasSort theory.signature [] zero "Element" := by
  intro typed
  obtain ⟨declaration, member, label, result⟩ := Maude.HasSort.operator_origin typed rfl
  simp [theory, Maude.SortedControls.theory, Maude.SortedControls.signature] at member
  rcases member with rfl | rfl | rfl <;>
    simp_all [Maude.SortedControls.zero, Maude.SortedControls.unit, Maude.SortedControls.combine]

theorem wrong_sort_bindings_refused :
    ¬ SortedBindingsIn prepared.language (freeContext []) (context row) [("X", encode zero)] := by
  intro sorted
  have valueTyped := (sorted "X" (.base "Element") (by decide_cbv)).2
  have applied : applyBindings [("X", encode zero)] (.fvar "X") = encode zero := by rw [applyBindings]; rfl
  rw [applied] at valueTyped
  have sourceTyped := (prepared_typing_iff prepared [] zero "Element").mp valueTyped
  have sourceExact := prepare_source preparation
  rw [sourceExact] at sourceTyped
  exact zero_not_element sourceTyped

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.MatchingControls
