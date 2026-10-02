import Mettapedia.OSLF.MeTTaIL.MultiHoleContext
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# The action of a symbol map on contexts

A map of declaration symbols renames the constructors of a pattern.  It acts
in the same way on a pattern with holes, leaving the holes where they are.
The action commutes with filling, with plugging and with renaming of holes,
so it is a strict map of the syntax of contexts; on patterns and on one-hole
contexts it is the existing action.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext

variable {ι κ : Type}

mutual
/-- Rename the constructors of a pattern with holes. -/
def mapContextSymbols (symbols : LanguageDefSymbolMap) : MultiHoleContext ι → MultiHoleContext ι
  | .hole index => .hole index
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply (symbols.constructor constructor) (mapContextSymbolsList symbols arguments)
  | .lambda binderName body => .lambda binderName (mapContextSymbols symbols body)
  | .multiLambda arity binderNames body =>
      .multiLambda arity binderNames (mapContextSymbols symbols body)
  | .subst body replacement =>
      .subst (mapContextSymbols symbols body) (mapContextSymbols symbols replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (mapContextSymbolsList symbols elements) rest

/-- The action along a list of contexts. -/
def mapContextSymbolsList (symbols : LanguageDefSymbolMap) :
    List (MultiHoleContext ι) → List (MultiHoleContext ι)
  | [] => []
  | context :: contexts =>
      mapContextSymbols symbols context :: mapContextSymbolsList symbols contexts
end

@[simp] theorem mapContextSymbolsList_eq_map (symbols : LanguageDefSymbolMap) :
    ∀ contexts : List (MultiHoleContext ι),
      mapContextSymbolsList symbols contexts = contexts.map (mapContextSymbols symbols)
  | [] => rfl
  | context :: contexts => by
      simp only [mapContextSymbolsList, List.map_cons,
        mapContextSymbolsList_eq_map symbols contexts]

mutual
/-- **Filling commutes with the action.**  The renamed context filled with
renamed patterns is the renamed filled context. -/
theorem fill_mapContextSymbols (symbols : LanguageDefSymbolMap) (filling : ι → Pattern) :
    ∀ context : MultiHoleContext ι,
      fill (fun index => mapPattern symbols (filling index)) (mapContextSymbols symbols context) =
        mapPattern symbols (fill filling context)
  | .hole _ => rfl
  | .bvar _ => by simp [mapContextSymbols, fill, mapPattern]
  | .fvar _ => by simp [mapContextSymbols, fill, mapPattern]
  | .apply _ arguments => by
      simp only [mapContextSymbols, fill, mapPattern,
        fillList_mapContextSymbolsList symbols filling arguments]
  | .lambda _ body => by
      simp only [mapContextSymbols, fill, mapPattern, fill_mapContextSymbols symbols filling body]
  | .multiLambda _ _ body => by
      simp only [mapContextSymbols, fill, mapPattern, fill_mapContextSymbols symbols filling body]
  | .subst body replacement => by
      simp only [mapContextSymbols, fill, mapPattern,
        fill_mapContextSymbols symbols filling body,
        fill_mapContextSymbols symbols filling replacement]
  | .collection _ elements _ => by
      simp only [mapContextSymbols, fill, mapPattern,
        fillList_mapContextSymbolsList symbols filling elements]

theorem fillList_mapContextSymbolsList (symbols : LanguageDefSymbolMap)
    (filling : ι → Pattern) :
    ∀ contexts : List (MultiHoleContext ι),
      fillList (fun index => mapPattern symbols (filling index))
          (mapContextSymbolsList symbols contexts) =
        mapPatternList symbols (fillList filling contexts)
  | [] => rfl
  | context :: contexts => by
      simp only [mapContextSymbolsList, fillList, mapPatternList,
        fill_mapContextSymbols symbols filling context,
        fillList_mapContextSymbolsList symbols filling contexts]
end

mutual
/-- **Plugging commutes with the action.** -/
theorem mapContextSymbols_bind (symbols : LanguageDefSymbolMap)
    (assignment : ι → MultiHoleContext κ) :
    ∀ context : MultiHoleContext ι,
      mapContextSymbols symbols (bind assignment context) =
        bind (fun index => mapContextSymbols symbols (assignment index))
          (mapContextSymbols symbols context)
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by
      simp only [mapContextSymbols, MultiHoleContext.bind, mapContextSymbolsList_bindList symbols assignment arguments]
  | .lambda _ body => by
      simp only [mapContextSymbols, MultiHoleContext.bind, mapContextSymbols_bind symbols assignment body]
  | .multiLambda _ _ body => by
      simp only [mapContextSymbols, MultiHoleContext.bind, mapContextSymbols_bind symbols assignment body]
  | .subst body replacement => by
      simp only [mapContextSymbols, MultiHoleContext.bind, mapContextSymbols_bind symbols assignment body,
        mapContextSymbols_bind symbols assignment replacement]
  | .collection _ elements _ => by
      simp only [mapContextSymbols, MultiHoleContext.bind, mapContextSymbolsList_bindList symbols assignment elements]

theorem mapContextSymbolsList_bindList (symbols : LanguageDefSymbolMap)
    (assignment : ι → MultiHoleContext κ) :
    ∀ contexts : List (MultiHoleContext ι),
      mapContextSymbolsList symbols (bindList assignment contexts) =
        bindList (fun index => mapContextSymbols symbols (assignment index))
          (mapContextSymbolsList symbols contexts)
  | [] => rfl
  | context :: contexts => by
      simp only [MultiHoleContext.bindList, mapContextSymbolsList,
        mapContextSymbols_bind symbols assignment context,
        mapContextSymbolsList_bindList symbols assignment contexts]
end

theorem mapContextSymbols_relabel (symbols : LanguageDefSymbolMap) (rename : ι → κ)
    (context : MultiHoleContext ι) :
    mapContextSymbols symbols (relabel rename context) =
      relabel rename (mapContextSymbols symbols context) :=
  mapContextSymbols_bind symbols _ context

theorem mapContextSymbols_plug (symbols : LanguageDefSymbolMap) {arity : ι → Type}
    (context : MultiHoleContext ι) (inner : (index : ι) → MultiHoleContext (arity index)) :
    mapContextSymbols symbols (plug context inner) =
      plug (mapContextSymbols symbols context) fun index =>
        mapContextSymbols symbols (inner index) := by
  rw [MultiHoleContext.plug, mapContextSymbols_bind]
  congr 1
  funext index
  exact mapContextSymbols_relabel symbols (Sigma.mk index) (inner index)

mutual
/-- The action leaves the holes where they are. -/
theorem holes_mapContextSymbols (symbols : LanguageDefSymbolMap) :
    ∀ context : MultiHoleContext ι, holes (mapContextSymbols symbols context) = holes context
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by
      simp only [mapContextSymbols, holes, holesList_mapContextSymbolsList symbols arguments]
  | .lambda _ body => by simp only [mapContextSymbols, holes, holes_mapContextSymbols symbols body]
  | .multiLambda _ _ body => by
      simp only [mapContextSymbols, holes, holes_mapContextSymbols symbols body]
  | .subst body replacement => by
      simp only [mapContextSymbols, holes, holes_mapContextSymbols symbols body,
        holes_mapContextSymbols symbols replacement]
  | .collection _ elements _ => by
      simp only [mapContextSymbols, holes, holesList_mapContextSymbolsList symbols elements]

theorem holesList_mapContextSymbolsList (symbols : LanguageDefSymbolMap) :
    ∀ contexts : List (MultiHoleContext ι),
      holesList (mapContextSymbolsList symbols contexts) = holesList contexts
  | [] => rfl
  | context :: contexts => by
      simp only [mapContextSymbolsList, holesList, holes_mapContextSymbols symbols context,
        holesList_mapContextSymbolsList symbols contexts]
end

/-- The action keeps a context linear. -/
theorem linear_mapContextSymbols {context : MultiHoleContext ι} (linear : Linear context)
    (symbols : LanguageDefSymbolMap) : Linear (mapContextSymbols symbols context) := by
  rw [Linear, holes_mapContextSymbols]
  exact linear

mutual
/-- On a pattern the action is the existing one. -/
theorem mapContextSymbols_ofPattern (symbols : LanguageDefSymbolMap) :
    ∀ pattern : Pattern,
      mapContextSymbols symbols (ofPattern pattern : MultiHoleContext ι) =
        ofPattern (mapPattern symbols pattern)
  | .bvar _ => by simp [ofPattern, mapContextSymbols, mapPattern]
  | .fvar _ => by simp [ofPattern, mapContextSymbols, mapPattern]
  | .apply _ arguments => by
      simp only [ofPattern, mapContextSymbols, mapPattern,
        mapContextSymbolsList_ofPatternList symbols arguments]
  | .lambda _ body => by
      simp only [ofPattern, mapContextSymbols, mapPattern, mapContextSymbols_ofPattern symbols body]
  | .multiLambda _ _ body => by
      simp only [ofPattern, mapContextSymbols, mapPattern, mapContextSymbols_ofPattern symbols body]
  | .subst body replacement => by
      simp only [ofPattern, mapContextSymbols, mapPattern,
        mapContextSymbols_ofPattern symbols body, mapContextSymbols_ofPattern symbols replacement]
  | .collection _ elements _ => by
      simp only [ofPattern, mapContextSymbols, mapPattern,
        mapContextSymbolsList_ofPatternList symbols elements]

theorem mapContextSymbolsList_ofPatternList (symbols : LanguageDefSymbolMap) :
    ∀ patterns : List Pattern,
      mapContextSymbolsList symbols (ofPatternList patterns : List (MultiHoleContext ι)) =
        ofPatternList (mapPatternList symbols patterns)
  | [] => rfl
  | pattern :: patterns => by
      simp only [ofPatternList, mapContextSymbolsList, mapPatternList,
        mapContextSymbols_ofPattern symbols pattern,
        mapContextSymbolsList_ofPatternList symbols patterns]
end

mutual
/-- The identity symbol map acts as the identity. -/
theorem mapContextSymbols_id :
    ∀ context : MultiHoleContext ι, mapContextSymbols LanguageDefSymbolMap.id context = context
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by
      rw [mapContextSymbols, mapContextSymbolsList_id arguments]
      rfl
  | .lambda _ body => by simp only [mapContextSymbols, mapContextSymbols_id body]
  | .multiLambda _ _ body => by simp only [mapContextSymbols, mapContextSymbols_id body]
  | .subst body replacement => by
      simp only [mapContextSymbols, mapContextSymbols_id body, mapContextSymbols_id replacement]
  | .collection _ elements _ => by
      simp only [mapContextSymbols, mapContextSymbolsList_id elements]

theorem mapContextSymbolsList_id :
    ∀ contexts : List (MultiHoleContext ι),
      mapContextSymbolsList LanguageDefSymbolMap.id contexts = contexts
  | [] => rfl
  | context :: contexts => by
      simp only [mapContextSymbolsList, mapContextSymbols_id context,
        mapContextSymbolsList_id contexts]
end

mutual
/-- The action of a composite is the composite of the actions. -/
theorem mapContextSymbols_comp (first second : LanguageDefSymbolMap) :
    ∀ context : MultiHoleContext ι,
      mapContextSymbols (first.comp second) context =
        mapContextSymbols second (mapContextSymbols first context)
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by
      rw [mapContextSymbols, mapContextSymbolsList_comp first second arguments]
      simp only [mapContextSymbols, LanguageDefSymbolMap.comp, Function.comp_apply]
  | .lambda _ body => by simp only [mapContextSymbols, mapContextSymbols_comp first second body]
  | .multiLambda _ _ body => by
      simp only [mapContextSymbols, mapContextSymbols_comp first second body]
  | .subst body replacement => by
      simp only [mapContextSymbols, mapContextSymbols_comp first second body,
        mapContextSymbols_comp first second replacement]
  | .collection _ elements _ => by
      simp only [mapContextSymbols, mapContextSymbolsList_comp first second elements]

theorem mapContextSymbolsList_comp (first second : LanguageDefSymbolMap) :
    ∀ contexts : List (MultiHoleContext ι),
      mapContextSymbolsList (first.comp second) contexts =
        mapContextSymbolsList second (mapContextSymbolsList first contexts)
  | [] => rfl
  | context :: contexts => by
      simp only [mapContextSymbolsList, mapContextSymbols_comp first second context,
        mapContextSymbolsList_comp first second contexts]
end

/-- On a one-hole context the action is the existing one. -/
theorem mapContextSymbols_ofOneHole (symbols : LanguageDefSymbolMap) :
    ∀ context : OneHoleContext,
      mapContextSymbols symbols (ofOneHole context) =
        ofOneHole (CIGSLT.mapOneHoleContext symbols context)
  | .hole => rfl
  | .apply _ before inner after => by
      simp only [ofOneHole, mapContextSymbols, mapContextSymbolsList_eq_map, List.map_append,
        List.map_cons, List.map_map, CIGSLT.mapOneHoleContext,
        mapContextSymbols_ofOneHole symbols inner]
      congr 2 <;> first
        | rfl
        | (apply List.map_congr_left; intro pattern _; exact mapContextSymbols_ofPattern symbols pattern)
        | (congr 1; apply List.map_congr_left; intro pattern _
           exact mapContextSymbols_ofPattern symbols pattern)
  | .lambda _ inner => by
      simp only [ofOneHole, mapContextSymbols, CIGSLT.mapOneHoleContext,
        mapContextSymbols_ofOneHole symbols inner]
  | .multiLambda _ _ inner => by
      simp only [ofOneHole, mapContextSymbols, CIGSLT.mapOneHoleContext,
        mapContextSymbols_ofOneHole symbols inner]
  | .substBody inner replacement => by
      simp only [ofOneHole, mapContextSymbols, CIGSLT.mapOneHoleContext,
        mapContextSymbols_ofOneHole symbols inner, mapContextSymbols_ofPattern]
  | .substReplacement body inner => by
      simp only [ofOneHole, mapContextSymbols, CIGSLT.mapOneHoleContext,
        mapContextSymbols_ofOneHole symbols inner, mapContextSymbols_ofPattern]
  | .collection _ before inner after _ => by
      simp only [ofOneHole, mapContextSymbols, mapContextSymbolsList_eq_map, List.map_append,
        List.map_cons, List.map_map, CIGSLT.mapOneHoleContext,
        mapContextSymbols_ofOneHole symbols inner]
      congr 2 <;> first
        | rfl
        | (apply List.map_congr_left; intro pattern _; exact mapContextSymbols_ofPattern symbols pattern)
        | (congr 1; apply List.map_congr_left; intro pattern _
           exact mapContextSymbols_ofPattern symbols pattern)

end Mettapedia.GSLT.LanguageDef
