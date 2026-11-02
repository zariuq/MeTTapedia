import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

/-! Sort preservation and reflection at the independent Maude IR boundary.
These are properties of arbitrary constructor terms and contexts, not just
the prepared acceptance examples. Equational and operational correspondence
are separate obligations. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def freeContext (context : Maude.VariableContext) : FreeTypeContext :=
  fun name => TypeExpr.base <$> context.lookup name

private def parameters (sorts : List String) (offset : Nat) : List TermParam :=
  (sorts.zipIdx offset).map fun (sort, index) => .simple ("p" ++ toString index) (.base sort)

theorem typing_preserved {signature : Maude.Signature} {context : Maude.VariableContext}
    {language : LanguageDef}
    (declared : ∀ declaration ∈ signature.operators, operator declaration ∈ language.terms)
    {term : Maude.Term} {sort : String} (typed : Maude.HasSort signature context term sort) :
    HasType language (freeContext context) [] (encode term) (.base sort) := by
  refine Maude.HasSort.rec
    (motive_1 := fun term sort _ => HasType language (freeContext context) [] (encode term) (.base sort))
    (motive_2 := fun terms sorts _ => ∀ offset,
      ArgumentsHaveTypes language (freeContext context) [] (terms.map encode) (parameters sorts offset))
    ?_ ?_ ?_ ?_ typed
  · intro name sort bound
    rw [encode]
    apply HasType.fvar
    simp [freeContext, bound]
  · intro declaration arguments member _ ih
    rw [encode]
    apply HasType.constructor (rule := operator declaration)
    · exact declared declaration member
    · simp [UsesBareCollection, GrammarRule.bareParams, operator]
    · exact ih 0
  · intro offset
    exact .nil
  · intro first sort rest sorts _ _ firstIH restIH offset
    simp only [parameters, List.zipIdx_cons, List.map_cons]
    exact .cons trivial rfl firstIH (restIH (offset + 1))

theorem typing_reflected {signature : Maude.Signature} {context : Maude.VariableContext}
    {language : LanguageDef} (declarations : language.terms = signature.operators.map operator)
    (term : Maude.Term) : ∀ sort,
    HasType language (freeContext context) [] (encode term) (.base sort) → Maude.HasSort signature context term sort := by
  refine Maude.Term.rec
    (motive_1 := fun term => ∀ sort,
      HasType language (freeContext context) [] (encode term) (.base sort) → Maude.HasSort signature context term sort)
    (motive_2 := fun terms => ∀ sorts offset,
      ArgumentsHaveTypes language (freeContext context) [] (terms.map encode) (parameters sorts offset) →
        List.Forall₂ (Maude.HasSort signature context) terms sorts)
    ?_ ?_ ?_ ?_ term
  · intro name sort typed
    rw [encode] at typed
    cases typed with
    | fvar found =>
        apply Maude.HasSort.var
        cases lookup : context.lookup name with
        | none => simp [freeContext, lookup] at found
        | some actual =>
            have same : actual = sort := by simpa [freeContext, lookup] using found
            exact congrArg some same
  · intro id arguments ih sort typed
    rw [encode] at typed
    cases typed with
    | @constructor _ rule _ membership _ argumentsTyped =>
        rw [declarations] at membership
        obtain ⟨declaration, member, same⟩ := List.mem_map.mp membership
        subst rule
        exact .app member (ih declaration.arguments 0 argumentsTyped)
  · intro sorts offset typed
    cases sorts with
    | nil => exact .nil
    | cons head tail =>
        simp only [parameters, List.zipIdx_cons, List.map_cons] at typed
        cases typed
  · intro first rest firstIH restIH sorts offset typed
    cases sorts with
    | nil =>
        simp only [parameters, List.zipIdx_nil, List.map_nil] at typed
        cases typed
    | cons sort sorts =>
        simp only [parameters, List.zipIdx_cons, List.map_cons] at typed
        obtain ⟨head, tail⟩ := ArgumentsHaveTypes.simple_cons_inv typed
        exact .cons (firstIH sort head) (restIH sorts (offset + 1) tail)

theorem prepared_typing_iff (prepared : Prepared) (context : Maude.VariableContext) (term : Maude.Term) (sort : String) :
    HasType prepared.language (freeContext context) [] (encode term) (.base sort) ↔
      Maude.HasSort prepared.source.signature context term sort := by
  constructor
  · exact typing_reflected prepared.terms_exact term sort
  · apply typing_preserved
    intro declaration member
    rw [prepared.terms_exact]
    exact List.mem_map.mpr ⟨declaration, member, rfl⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
