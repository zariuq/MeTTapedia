import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# What a signature map cannot change

A signature map renames constructors.  It sends an application to an
application with the same number of arguments, a collection to a collection of
the same kind and length, a binder to a binder, and a variable to itself.  The
shape of a pattern is what is left when variable identities, constructor
names and binder names are forgotten; a signature map preserves it, and so
does closing a free name into a bound variable.

A translation that changes the shape of even one term is therefore not the
action of any signature map.  This is the precise sense in which an encoding
that sends a constructor to a derived construction is not a map of
signatures.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)

/-- The shape of a pattern: its tree of node kinds. -/
inductive PatternShape where
  | leaf
  | application (arguments : List PatternShape)
  | binder (body : PatternShape)
  | multiBinder (arity : Nat) (body : PatternShape)
  | substitution (body replacement : PatternShape)
  | collection (kind : CollType) (elements : List PatternShape) (isOpen : Bool)

mutual
/-- Forget variable identities, constructor names and binder names. -/
def patternShape : Pattern → PatternShape
  | .bvar _ => .leaf
  | .fvar _ => .leaf
  | .apply _ arguments => .application (patternShapeList arguments)
  | .lambda _ body => .binder (patternShape body)
  | .multiLambda arity _ body => .multiBinder arity (patternShape body)
  | .subst body replacement => .substitution (patternShape body) (patternShape replacement)
  | .collection kind elements rest =>
      .collection kind (patternShapeList elements) rest.isSome

/-- Shapes along a list of patterns. -/
def patternShapeList : List Pattern → List PatternShape
  | [] => []
  | pattern :: patterns => patternShape pattern :: patternShapeList patterns
end

@[simp] theorem patternShapeList_eq_map :
    ∀ patterns : List Pattern, patternShapeList patterns = patterns.map patternShape
  | [] => rfl
  | pattern :: patterns => by
      simp only [patternShapeList, List.map_cons, patternShapeList_eq_map patterns]

mutual
/-- The number of nodes of a shape. -/
def PatternShape.size : PatternShape → Nat
  | .leaf => 1
  | .application arguments => 1 + PatternShape.sizeList arguments
  | .binder body => 1 + body.size
  | .multiBinder _ body => 1 + body.size
  | .substitution body replacement => 1 + body.size + replacement.size
  | .collection _ elements _ => 1 + PatternShape.sizeList elements

/-- The number of nodes of a list of shapes. -/
def PatternShape.sizeList : List PatternShape → Nat
  | [] => 0
  | shape :: shapes => shape.size + PatternShape.sizeList shapes
end

mutual
/-- The number of applications with a given number of arguments. -/
def PatternShape.arityCount (arity : Nat) : PatternShape → Nat
  | .leaf => 0
  | .application arguments =>
      (if arguments.length = arity then 1 else 0) + PatternShape.arityCountList arity arguments
  | .binder body => body.arityCount arity
  | .multiBinder _ body => body.arityCount arity
  | .substitution body replacement => body.arityCount arity + replacement.arityCount arity
  | .collection _ elements _ => PatternShape.arityCountList arity elements

/-- The number of applications with a given number of arguments, along a
list of shapes. -/
def PatternShape.arityCountList (arity : Nat) : List PatternShape → Nat
  | [] => 0
  | shape :: shapes => shape.arityCount arity + PatternShape.arityCountList arity shapes
end

theorem PatternShape.arityCountList_append (arity : Nat) :
    ∀ first second : List PatternShape,
      PatternShape.arityCountList arity (first ++ second) =
        PatternShape.arityCountList arity first + PatternShape.arityCountList arity second
  | [], second => by simp [PatternShape.arityCountList]
  | shape :: first, second => by
      simp only [List.cons_append, PatternShape.arityCountList,
        PatternShape.arityCountList_append arity first second]
      omega

/-- The number of nodes of a pattern. -/
def nodeCount (pattern : Pattern) : Nat := (patternShape pattern).size

/-- **A signature map preserves shape.** -/
theorem patternShape_mapPattern (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    patternShape (mapPattern symbols pattern) = patternShape pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments recurse =>
      simp only [mapPattern, patternShape, mapPatternList_eq_map, patternShapeList_eq_map,
        List.map_map]
      congr 1
      exact List.map_congr_left fun argument membership => recurse argument membership
  | hlambda binder body recurse => simp only [mapPattern, patternShape, recurse]
  | hmultiLambda arity binders body recurse => simp only [mapPattern, patternShape, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      simp only [mapPattern, patternShape, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      simp only [mapPattern, patternShape, mapPatternList_eq_map, patternShapeList_eq_map,
        List.map_map]
      congr 1
      exact List.map_congr_left fun element membership => recurse element membership

/-- **Binding a free name preserves shape.** -/
theorem patternShape_closeFVar (name : String) (pattern : Pattern) :
    ∀ depth : Nat, patternShape (closeFVar depth name pattern) = patternShape pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [closeFVar]
  | hfvar other =>
      intro depth
      rw [closeFVar]
      split <;> rfl
  | happly constructor arguments recurse =>
      intro depth
      rw [closeFVar]
      simp only [patternShape, patternShapeList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun argument membership => recurse argument membership depth
  | hlambda binder body recurse =>
      intro depth
      rw [closeFVar]
      simp only [patternShape, recurse]
  | hmultiLambda arity binders body recurse =>
      intro depth
      rw [closeFVar]
      simp only [patternShape, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro depth
      rw [closeFVar]
      simp only [patternShape, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro depth
      rw [closeFVar]
      simp only [patternShape, patternShapeList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element membership => recurse element membership depth

/-- A signature map preserves the number of nodes. -/
theorem nodeCount_mapPattern (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    nodeCount (mapPattern symbols pattern) = nodeCount pattern := by
  rw [nodeCount, patternShape_mapPattern, nodeCount]

/-- A signature map sends an application to an application with the same
number of arguments. -/
theorem mapPattern_apply_arity (symbols : LanguageDefSymbolMap) (constructor : String)
    (arguments : List Pattern) :
    ∃ mapped : List Pattern,
      mapPattern symbols (.apply constructor arguments) =
        .apply (symbols.constructor constructor) mapped ∧
      mapped.length = arguments.length :=
  ⟨arguments.map (mapPattern symbols), by simp [mapPattern], by simp⟩

/-- A signature map sends a collection to a collection of the same kind and
length, with the same rest variable. -/
theorem mapPattern_collection_length (symbols : LanguageDefSymbolMap) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    ∃ mapped : List Pattern,
      mapPattern symbols (.collection kind elements rest) = .collection kind mapped rest ∧
      mapped.length = elements.length :=
  ⟨elements.map (mapPattern symbols), by simp [mapPattern], by simp⟩

/-- **A translation that changes the shape of a term is not a signature map
there.**  No renaming of constructors sends the first pattern to the second
when their shapes differ. -/
theorem mapPattern_ne_of_shape_ne {source target : Pattern}
    (distinct : patternShape source ≠ patternShape target) (symbols : LanguageDefSymbolMap) :
    mapPattern symbols source ≠ target := by
  intro same
  apply distinct
  rw [← same, patternShape_mapPattern]

/-- No signature map sends an application to a collection. -/
theorem mapPattern_apply_ne_collection (symbols : LanguageDefSymbolMap) (constructor : String)
    (arguments : List Pattern) (kind : CollType) (elements : List Pattern)
    (rest : Option String) :
    mapPattern symbols (.apply constructor arguments) ≠ .collection kind elements rest :=
  mapPattern_ne_of_shape_ne (by simp [patternShape]) symbols

/-- No signature map sends an application to an application with a different
number of arguments. -/
theorem mapPattern_apply_ne_of_length_ne (symbols : LanguageDefSymbolMap)
    (constructor label : String) {arguments images : List Pattern}
    (distinct : arguments.length ≠ images.length) :
    mapPattern symbols (.apply constructor arguments) ≠ .apply label images := by
  intro same
  obtain ⟨mapped, shape, length⟩ := mapPattern_apply_arity symbols constructor arguments
  rw [shape] at same
  injection same with _ lists
  exact distinct (by rw [← length, lists])

/-- A translation that changes the number of nodes of a term is not a
signature map there. -/
theorem mapPattern_ne_of_nodeCount_ne {source target : Pattern}
    (distinct : nodeCount source ≠ nodeCount target) (symbols : LanguageDefSymbolMap) :
    mapPattern symbols source ≠ target := by
  intro same
  apply distinct
  rw [← same, nodeCount_mapPattern]

/-- The action on terms of a structural morphism between validated languages
is a signature map, so it preserves shape. -/
theorem StructuralMorphism.patternShape_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) (pattern : Pattern) :
    patternShape (mapPattern morphism.symbols pattern) = patternShape pattern :=
  patternShape_mapPattern morphism.symbols pattern

end Mettapedia.GSLT.LanguageDef
