import Mettapedia.Languages.MeTTa.HE.HumanEvalSpec

/-!
# Human type-boundary conformance

This downstream module relates the executable-independent human type and
syntax predicates to the corresponding computable HE boundary functions.  The
relations themselves remain free of executable helpers and fuel.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanTypeConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open HumanTypeSpec
open HumanEvalSpec

/-! ## Syntax classifiers -/

theorem metaTypeRel_iff_getMetaType (atom type : Atom) :
    MetaTypeRel atom type ↔ getMetaType atom = type := by
  constructor
  · intro h
    cases h <;> rfl
  · cases atom <;> intro h <;> subst type <;> constructor

theorem isErrorRel_iff_isErrorAtom (atom : Atom) :
    IsErrorRel atom ↔ isErrorAtom atom = true := by
  cases atom with
  | symbol name => simp [IsErrorRel, isErrorAtom]
  | var name => simp [IsErrorRel, isErrorAtom]
  | grounded value => simp [IsErrorRel, isErrorAtom]
  | expression atoms =>
      cases atoms with
      | nil => simp [IsErrorRel, isErrorAtom]
      | cons head tail =>
          cases head with
          | symbol name =>
              by_cases hname : name = "Error"
              · subst name
                simp [IsErrorRel, isErrorAtom]
              · simp [IsErrorRel, isErrorAtom, hname]
          | var name => simp [IsErrorRel, isErrorAtom]
          | grounded value => simp [IsErrorRel, isErrorAtom]
          | expression children => simp [IsErrorRel, isErrorAtom]

private theorem isEmptyAtom_iff (atom : Atom) :
    isEmptyAtom atom = true ↔ atom = Atom.empty := by
  simp [isEmptyAtom]

theorem isEmptyOrErrorRel_iff_isEmptyOrError (atom : Atom) :
    IsEmptyOrErrorRel atom ↔ isEmptyOrError atom = true := by
  rw [show isEmptyOrError atom = (isEmptyAtom atom || isErrorAtom atom) by rfl]
  simp only [Bool.or_eq_true]
  rw [isEmptyAtom_iff, ← isErrorRel_iff_isErrorAtom]
  rfl

/-! ## Ordered type lookup -/

private def directAnnotationType? (target : Atom) : Atom → Option Atom
  | .expression [.symbol ":", annotated, type] =>
      if annotated == target then some type else none
  | _ => none

private theorem getAnnotatedTypes_ofList_eq_filterMap
    (target : Atom) (atoms : List Atom) :
    getAnnotatedTypes (Space.ofList atoms) target =
      atoms.filterMap (directAnnotationType? target) := by
  rfl

private theorem directAnnotationType?_eq_some_iff
    {target head type : Atom} :
    directAnnotationType? target head = some type ↔
      head = .expression [.symbol ":", target, type] := by
  constructor
  · intro h
    simp only [directAnnotationType?] at h
    split at h
    next annotated candidate hshape =>
      split at h
      next heq =>
        cases h
        exact congrArg
          (fun atom : Atom => Atom.expression [Atom.symbol ":", atom, type])
          (beq_iff_eq.mp heq)
      next => contradiction
    next => contradiction
  · rintro rfl
    simp [directAnnotationType?]

theorem annotationTypesRel_getAnnotatedTypes
    (target : Atom) (atoms : List Atom) :
    AnnotationTypesRel target atoms
      (getAnnotatedTypes (Space.ofList atoms) target) := by
  induction atoms with
  | nil => exact AnnotationTypesRel.nil
  | cons head tail ih =>
      rw [getAnnotatedTypes_ofList_eq_filterMap] at ih ⊢
      cases hopt : directAnnotationType? target head with
      | none =>
          rw [List.filterMap_cons, hopt]
          apply AnnotationTypesRel.skip
          · intro type hshape
            subst head
            simp [directAnnotationType?] at hopt
          · exact ih
      | some type =>
          have hshape :
              head = .expression [.symbol ":", target, type] :=
            directAnnotationType?_eq_some_iff.mp hopt
          rw [List.filterMap_cons, hopt]
          exact hshape ▸ AnnotationTypesRel.hit ih

private theorem AnnotationTypesRel.unique
    {target : Atom} {atoms left right : List Atom}
    (hleft : AnnotationTypesRel target atoms left)
    (hright : AnnotationTypesRel target atoms right) : left = right := by
  induction hleft generalizing right with
  | nil =>
      cases hright
      rfl
  | hit htail ih =>
      cases hright with
      | hit hright => exact congrArg (List.cons _) (ih hright)
      | skip hskip _ => exact (hskip _ rfl).elim
  | skip hskip htail ih =>
      cases hright with
      | hit _ => exact (hskip _ rfl).elim
      | skip _ hright => exact ih hright

theorem annotationTypesRel_eq_getAnnotatedTypes
    {target : Atom} {atoms types : List Atom}
    (h : AnnotationTypesRel target atoms types) :
    getAnnotatedTypes (Space.ofList atoms) target = types := by
  exact AnnotationTypesRel.unique
    (annotationTypesRel_getAnnotatedTypes target atoms) h

theorem intrinsicGroundedTypeRel_iff_getGroundedType
    (value : GroundedValue) (type : Atom) :
    IntrinsicGroundedTypeRel value type ↔ getGroundedType value = type := by
  constructor
  · intro h
    cases h <;> rfl
  · cases value <;> intro h <;> subst type <;> constructor

theorem typesOfRel_eq_getAtomTypes
    {space : Space} {atom : Atom} {types : List Atom}
    (h : TypesOfRel space atom types) :
    getAtomTypes space atom = types := by
  cases h with
  | «variable» => rfl
  | groundedKnown htype hne =>
      have hEq := intrinsicGroundedTypeRel_iff_getGroundedType _ _ |>.mp htype
      simp [getAtomTypes, hEq, hne]
  | groundedUndefined htype =>
      have hEq := intrinsicGroundedTypeRel_iff_getGroundedType _ _ |>.mp htype
      simp [getAtomTypes, hEq]
  | @symbolKnown name types htypes hne =>
      have hEq := annotationTypesRel_eq_getAnnotatedTypes htypes
      have hEq' : getAnnotatedTypes space (.symbol name) = types := by
        simpa [Space.ofList] using hEq
      simp [getAtomTypes, hEq', hne]
  | @symbolUndefined name htypes =>
      have hEq := annotationTypesRel_eq_getAnnotatedTypes htypes
      have hEq' : getAnnotatedTypes space (.symbol name) = [] := by
        simpa [Space.ofList] using hEq
      simp [getAtomTypes, hEq']
  | unit => rfl
  | @expressionKnown head tail types htypes hne =>
      have hEq := annotationTypesRel_eq_getAnnotatedTypes htypes
      have hEq' :
          getAnnotatedTypes space (.expression (head :: tail)) = types := by
        simpa [Space.ofList] using hEq
      simp [getAtomTypes, hEq', hne]
  | @expressionUndefined head tail htypes =>
      have hEq := annotationTypesRel_eq_getAnnotatedTypes htypes
      have hEq' :
          getAnnotatedTypes space (.expression (head :: tail)) = [] := by
        simpa [Space.ofList] using hEq
      simp [getAtomTypes, hEq']

theorem typeOfRel_iff_mem_getAtomTypes
    (space : Space) (atom type : Atom) :
    TypeOfRel space atom type ↔ type ∈ getAtomTypes space atom := by
  constructor
  · rintro ⟨types, htypes, hmem⟩
    rw [typesOfRel_eq_getAtomTypes htypes]
    exact hmem
  · intro hmem
    refine ⟨getAtomTypes space atom, ?_, hmem⟩
    cases atom with
    | var name => exact TypesOfRel.variable space name
    | grounded value =>
        cases value with
        | int value =>
            simpa [getAtomTypes, getGroundedType, Atom.undefinedType] using
              TypesOfRel.groundedKnown (space := space)
                (IntrinsicGroundedTypeRel.int value)
                (by simp [Atom.undefinedType])
        | bool value =>
            simpa [getAtomTypes, getGroundedType, Atom.undefinedType] using
              TypesOfRel.groundedKnown (space := space)
                (IntrinsicGroundedTypeRel.bool value)
                (by simp [Atom.undefinedType])
        | string value =>
            simpa [getAtomTypes, getGroundedType, Atom.undefinedType] using
              TypesOfRel.groundedKnown (space := space)
                (IntrinsicGroundedTypeRel.string value)
                (by simp [Atom.undefinedType])
        | custom type payload =>
            by_cases htype : type = "%Undefined%"
            · subst type
              simpa [getAtomTypes, getGroundedType, Atom.undefinedType] using
                TypesOfRel.groundedUndefined (space := space)
                  (IntrinsicGroundedTypeRel.custom "%Undefined%" payload)
            · simpa [getAtomTypes, getGroundedType, Atom.undefinedType, htype] using
                TypesOfRel.groundedKnown (space := space)
                  (IntrinsicGroundedTypeRel.custom type payload)
                  (by simpa [Atom.undefinedType] using htype)
    | symbol name =>
        let types := getAnnotatedTypes space (.symbol name)
        have hrel : AnnotationTypesRel (.symbol name) space.atoms types :=
          annotationTypesRel_getAnnotatedTypes (.symbol name) space.atoms
        by_cases htypes : types = []
        · simpa [getAtomTypes, types, htypes] using
            TypesOfRel.symbolUndefined (space := space) (name := name)
              (htypes ▸ hrel)
        · simpa [getAtomTypes, types, htypes] using
            TypesOfRel.symbolKnown (space := space) (name := name) hrel htypes
    | expression atoms =>
        cases atoms with
        | nil => exact TypesOfRel.unit space
        | cons head tail =>
            let types := getAnnotatedTypes space (.expression (head :: tail))
            have hrel :
                AnnotationTypesRel (.expression (head :: tail)) space.atoms types :=
              annotationTypesRel_getAnnotatedTypes
                (.expression (head :: tail)) space.atoms
            by_cases htypes : types = []
            · simpa [getAtomTypes, types, htypes] using
                TypesOfRel.expressionUndefined
                  (space := space) (head := head) (tail := tail)
                  (htypes ▸ hrel)
            · simpa [getAtomTypes, types, htypes] using
                TypesOfRel.expressionKnown
                  (space := space) (head := head) (tail := tail) hrel htypes

/-! ## Function-type destructors -/

theorem functionTypeRel_getFunctionParts
    {functionType : Atom} {argumentTypes : List Atom} {returnType : Atom}
    (h : FunctionTypeRel functionType argumentTypes returnType) :
    isFunctionType functionType = true ∧
      getFunctionArgTypes functionType = some argumentTypes ∧
      getFunctionRetType functionType = some returnType := by
  change functionType =
    .expression (.symbol "->" :: (argumentTypes ++ [returnType])) at h
  subst functionType
  have hdrop : (argumentTypes ++ [returnType]).dropLast = argumentTypes :=
    List.dropLast_concat
  have hlast : (argumentTypes ++ [returnType]).getLast? = some returnType :=
    List.getLast?_concat
  have hisFunction :
      isFunctionType
        (.expression (.symbol "->" :: (argumentTypes ++ [returnType]))) =
          true := by
    cases argumentTypes <;> rfl
  refine ⟨hisFunction, ?_, ?_⟩
  · simp [getFunctionArgTypes, hdrop]
  · simp [getFunctionRetType, hlast]

end Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
