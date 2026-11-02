import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReferenceTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPhysicalInstances

/-! Encoded facts and requests inhabit the actual query grammar. Their
typing is derived from the registered reference context and authored
constructors, independently of matching or receipt validation. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PhysicalTyping

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem constructor_typed (language : LanguageDef)
    (terms : language.terms = Query.baseLanguage.terms)
    (free : FreeTypeContext) (index : Fin Query.baseLanguage.terms.length)
    (arguments : List Pattern)
    (ordinary : ¬ UsesBareCollection (Query.baseLanguage.terms.get index))
    (typed : ArgumentsHaveTypes language free [] arguments (Query.baseLanguage.terms.get index).params) :
    HasType language free [] (.apply (Query.baseLanguage.terms.get index).label arguments)
      (.base (Query.baseLanguage.terms.get index).category) := by
  apply HasType.constructor ?_ ordinary typed
  rw [terms]
  exact List.get_mem _ index

private theorem node_open {language : LanguageDef} {free : FreeTypeContext}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free [] (.apply label arguments) type)
    (children : ∀ child ∈ arguments,
      child.hasCanonicalBinderMetadata = true ∧ isObjectPattern child = true) :
    OpenPatternWellSorted language free [] type (.apply label arguments) := by
  have metadata : Pattern.hasCanonicalBinderMetadataList arguments = true ∧
      isObjectPatternList arguments = true := by
    clear typed
    induction arguments with
    | nil => exact ⟨rfl,rfl⟩
    | cons head tail ih =>
      have first := children head List.mem_cons_self
      have rest := ih (fun child member => children child (List.mem_cons_of_mem _ member))
      exact ⟨by simpa only [Pattern.hasCanonicalBinderMetadataList,first.1,Bool.true_and] using rest.1,
        by simpa only [isObjectPatternList,first.2,Bool.true_and] using rest.2⟩
  exact ⟨typed,metadata.1,metadata.2,typed.isWellScopedAt⟩

private theorem vector_open (language : LanguageDef) (free : FreeTypeContext)
    (type : TypeExpr) (values : List Pattern)
    (children : ∀ child ∈ values, OpenPatternWellSorted language free [] type child) :
    OpenPatternWellSorted language free [] (.collection .vec type) (Join.vector values) := by
  have parts : ElementsHaveType language free [] values type ∧
      Pattern.hasCanonicalBinderMetadataList values = true ∧ isObjectPatternList values = true := by
    induction values with
    | nil => exact ⟨.nil _ _,rfl,rfl⟩
    | cons head tail ih =>
      have first := children head List.mem_cons_self
      have rest := ih (fun child member => children child (List.mem_cons_of_mem _ member))
      exact ⟨.cons first.1 rest.1,
        by simpa only [Pattern.hasCanonicalBinderMetadataList,first.2.1,Bool.true_and] using rest.2.1,
        by simpa only [isObjectPatternList,first.2.2.1,Bool.true_and] using rest.2.2⟩
  have typed := HasType.collection (collectionType := .vec) (rest := none) parts.1
  exact ⟨typed,parts.2.1,parts.2.2,typed.isWellScopedAt⟩

theorem value_encoded_open (language : LanguageDef) (pools : Join.Pools)
    (value : Value) (code : Pattern) (encoded : PhysicalInstances.value? pools value = some code) :
    OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlValue") code := by
  obtain ⟨index,found,rfl⟩ := Option.map_eq_some_iff.mp encoded
  exact ReferenceTyping.value_open language pools index (List.idxOf?_eq_some_iff.mp found).1

private theorem values_encoded_open (language : LanguageDef) (pools : Join.Pools)
    (values : List Value) (codes : List Pattern)
    (encoded : values.mapM (PhysicalInstances.value? pools) = some codes) :
    ∀ code ∈ codes, OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlValue") code := by
  induction values generalizing codes with
  | nil =>
    have same : codes = [] := (Option.some.inj encoded).symm
    simp [same]
  | cons head tail ih =>
    rw [List.mapM_cons] at encoded
    change ((PhysicalInstances.value? pools head).bind fun first =>
      (tail.mapM (PhysicalInstances.value? pools)).bind fun remaining =>
        some (first :: remaining)) = some codes at encoded
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at encoded
    obtain ⟨first,firstRead,remaining,tailRead,rfl⟩ :=
      encoded
    intro code member
    rcases List.mem_cons.mp member with rfl | member
    · exact value_encoded_open language pools head code firstRead
    · exact ih remaining tailRead code member

theorem fact_open (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (source : GroundFact) (code : Pattern)
    (encoded : Executable.fact? pools source = some code) :
    OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlStatement") code := by
  change ((pools.relations.idxOf? source.relation).bind fun relation =>
    (source.values.mapM (PhysicalInstances.value? pools)).bind fun values =>
      some (Pattern.apply "GroundFact" [Executable.relationRef relation,.apply "GroundTuple" [Join.vector values]])) = some code at encoded
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at encoded
  obtain ⟨relation,relationRead,values,valuesRead,rfl⟩ := encoded
  have relationOpen := ReferenceTyping.relation_open language pools relation (List.idxOf?_eq_some_iff.mp relationRead).1
  have vectorOpen := vector_open language _ (.base "DlValue") values (values_encoded_open language pools source.values values valuesRead)
  have tupleTyped := constructor_typed language terms _ ⟨9,by decide +kernel⟩ [Join.vector values]
    (by rintro ⟨_,_,_,impossible⟩; have bad : (0 : Nat) = 1 := congrArg List.length impossible; cases bad)
    (.cons trivial rfl vectorOpen.1 .nil)
  have tupleOpen := node_open tupleTyped (by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨vectorOpen.2.1,vectorOpen.2.2.1⟩)
  have factTyped := constructor_typed language terms _ ⟨28,by decide +kernel⟩
    [Executable.relationRef relation,.apply "GroundTuple" [Join.vector values]]
    (by rintro ⟨_,_,_,impossible⟩; have bad : (2 : Nat) = 1 := congrArg List.length impossible; cases bad)
    (.cons trivial rfl relationOpen.1 (.cons trivial rfl tupleOpen.1 .nil))
  apply node_open factTyped
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨relationOpen.2.1,relationOpen.2.2.1⟩
  · cases List.mem_singleton.mp member
    exact ⟨tupleOpen.2.1,tupleOpen.2.2.1⟩

theorem request_open (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) :
    OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlStatement") (Executable.request pools) := by
  have relationsOpen := vector_open language (FreeTypeContext.ofList (Executable.freeTypes pools)) (.base "DlRelation")
      ((List.range pools.relations.length).map Executable.relationRef) (by
    intro child member
    obtain ⟨index,inside,rfl⟩ := List.mem_map.mp member
    exact ReferenceTyping.relation_open language pools index (List.mem_range.mp inside))
  have literalsOpen := vector_open language (FreeTypeContext.ofList (Executable.freeTypes pools)) (.base "DlValue")
      ((List.range pools.literals.length).map Executable.valueRef) (by
    intro child member
    obtain ⟨index,inside,rfl⟩ := List.mem_map.mp member
    exact ReferenceTyping.value_open language pools index (List.mem_range.mp inside))
  have typed := constructor_typed language terms _ ⟨33,by decide +kernel⟩ _
    (by rintro ⟨_,_,_,impossible⟩; have bad : (2 : Nat) = 1 := congrArg List.length impossible; cases bad)
    (.cons trivial rfl relationsOpen.1 (.cons trivial rfl literalsOpen.1 .nil))
  exact node_open typed (by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨relationsOpen.2.1,relationsOpen.2.2.1⟩
    · cases List.mem_singleton.mp member
      exact ⟨literalsOpen.2.1,literalsOpen.2.2.1⟩)

#print axioms value_encoded_open
#print axioms fact_open
#print axioms request_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PhysicalTyping
