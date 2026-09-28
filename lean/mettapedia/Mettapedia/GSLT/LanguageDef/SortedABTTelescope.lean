import Mettapedia.GSLT.LanguageDef.SortedABTSubstitution

/-!
# Prefix-scoped telescope fields over the existing sorted ABT

The annotation on a declaration is under the preceding declarations, never
under its own binder or a later one.  The body is under all declarations.
This module constructs exactly those fields and proves that the existing
capture-avoiding renaming and simultaneous substitution commute with the
construction.  It is useful after named annotations have been resolved.

This does not implement native name resolution, freshening, the `(In field k)`
selector, or the C alpha comparator.  Those source/representation bridges are
separate from this theorem about the actual sorted ABT carrier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Telescope

open Term

variable {VarSort Head : Type}

/-- The declared sorts, in source order. -/
def sorts (declarations : List (VarSort × Term VarSort Head)) : List VarSort :=
  declarations.map Prod.fst

/-- Lower the annotation slots and the body to the existing physical fields.
All binder lists are relative to the same enclosing constructor. -/
def compile (outer : List VarSort) :
    List (VarSort × Term VarSort Head) → Term VarSort Head → Fields VarSort Head
  | [], body => .cons outer body .nil
  | (sort, annotation) :: rest, body =>
      .cons outer annotation (compile (outer ++ [sort]) rest body)

/-- Transform annotations using their actual preceding binder prefixes. -/
def mapAnnotations (transform : List VarSort → Term VarSort Head → Term VarSort Head)
    (outer : List VarSort) :
    List (VarSort × Term VarSort Head) → List (VarSort × Term VarSort Head)
  | [] => []
  | (sort, annotation) :: rest =>
      (sort, transform outer annotation) ::
        mapAnnotations transform (outer ++ [sort]) rest

@[simp] theorem sorts_mapAnnotations
    (transform : List VarSort → Term VarSort Head → Term VarSort Head)
    (outer : List VarSort) (declarations : List (VarSort × Term VarSort Head)) :
    sorts (mapAnnotations transform outer declarations) = sorts declarations := by
  induction declarations generalizing outer with
  | nil => rfl
  | cons declaration rest ih =>
    rcases declaration with ⟨sort, annotation⟩
    change sort :: sorts (mapAnnotations transform (outer ++ [sort]) rest) =
      sort :: sorts rest
    rw [ih]

variable [DecidableEq VarSort]

/-- A generic field renaming observes precisely the annotation prefix and
the full telescope at the body.  No extra binder shift is inserted. -/
theorem compile_parallelRename (rho : Renaming VarSort) (outer : List VarSort)
    (declarations : List (VarSort × Term VarSort Head)) (body : Term VarSort Head) :
    Fields.parallelRename rho (compile outer declarations body) =
      compile outer
        (mapAnnotations (fun binders => parallelRename (liftRenaming binders rho))
          outer declarations)
        (parallelRename (liftRenaming (outer ++ sorts declarations) rho) body) := by
  induction declarations generalizing outer with
  | nil => simp [compile, sorts, mapAnnotations, Fields.parallelRename]
  | cons declaration rest ih =>
    rcases declaration with ⟨sort, annotation⟩
    simpa [compile, mapAnnotations, sorts, Fields.parallelRename, List.append_assoc]
      using congrArg (Fields.cons outer (parallelRename (liftRenaming outer rho) annotation))
        (ih (outer ++ [sort]))

/-- The same commuting square for genuine capture-avoiding substitutions;
the imported operation weakens replacements on every bound variable sort. -/
theorem compile_parallelSubstitute (sigma : Substitution VarSort Head)
    (outer : List VarSort) (declarations : List (VarSort × Term VarSort Head))
    (body : Term VarSort Head) :
    Fields.parallelSubstitute sigma (compile outer declarations body) =
      compile outer
        (mapAnnotations
          (fun binders => parallelSubstitute (liftSubstitution binders sigma))
          outer declarations)
        (parallelSubstitute
          (liftSubstitution (outer ++ sorts declarations) sigma) body) := by
  induction declarations generalizing outer with
  | nil => simp [compile, sorts, mapAnnotations, Fields.parallelSubstitute]
  | cons declaration rest ih =>
    rcases declaration with ⟨sort, annotation⟩
    simpa [compile, mapAnnotations, sorts, Fields.parallelSubstitute, List.append_assoc]
      using congrArg
        (Fields.cons outer (parallelSubstitute (liftSubstitution outer sigma) annotation))
        (ih (outer ++ [sort]))

/-- Check annotations left to right, before extending the current prefix. -/
def annotationsSupported (depth : VarSort → Nat) (outer : List VarSort) :
    List (VarSort × Term VarSort Head) → Bool
  | [] => true
  | (sort, annotation) :: rest =>
      supportedAt (enter depth outer) annotation &&
        annotationsSupported depth (outer ++ [sort]) rest

theorem compile_supported_iff (depth : VarSort → Nat) (outer : List VarSort)
    (declarations : List (VarSort × Term VarSort Head)) (body : Term VarSort Head) :
    Fields.supportedAt depth (compile outer declarations body) = true ↔
      annotationsSupported depth outer declarations = true ∧
        supportedAt (enter depth (outer ++ sorts declarations)) body = true := by
  induction declarations generalizing outer with
  | nil => simp [compile, sorts, Fields.supportedAt, annotationsSupported]
  | cons declaration rest ih =>
    rcases declaration with ⟨sort, annotation⟩
    simp [compile, sorts, Fields.supportedAt, annotationsSupported, ih,
      Bool.and_eq_true, List.append_assoc, and_assoc]

/-- The compiled telescope inherits support preservation from the existing
simultaneous-substitution theorem, for arbitrary variable sorts and heads. -/
theorem compile_substitution_preserves_scope
    {source target : VarSort → Nat} {sigma : Substitution VarSort Head}
    (replacements : SubstitutionSupported source target sigma)
    (outer : List VarSort) (declarations : List (VarSort × Term VarSort Head))
    (body : Term VarSort Head)
    (supported : Fields.supportedAt source (compile outer declarations body) = true) :
    Fields.supportedAt target
      (compile outer
        (mapAnnotations
          (fun binders => parallelSubstitute (liftSubstitution binders sigma))
          outer declarations)
        (parallelSubstitute
          (liftSubstitution (outer ++ sorts declarations) sigma) body)) = true := by
  rw [← compile_parallelSubstitute]
  exact Fields.supportedAt_parallelSubstitute replacements _ supported

/-! Controls use a two-declaration dependent telescope. The second annotation
mentions the first declaration; the body sees both. -/

private def typeConstant : Term Unit String := .node "Type" .nil

private def dependentDeclarations : List (Unit × Term Unit String) :=
  [((), typeConstant), ((), .idx () 0)]

example : Fields.supportedAt (fun _ => 0)
    (compile [] dependentDeclarations (.idx () 1)) = true := by decide +kernel

/-- The first annotation cannot refer to its own binder. -/
example : Fields.supportedAt (fun _ => 0)
    (compile [] [((), .idx () 0), ((), typeConstant)] (.idx () 1)) = false := by
  decide +kernel

/-- The second annotation cannot refer to a later declaration. -/
example : Fields.supportedAt (fun _ => 0)
    (compile [] [((), typeConstant), ((), .idx () 1)] (.idx () 1)) = false := by
  decide +kernel

/-- Earlier local indices remain fixed; the free body index is weakened. -/
example : Fields.parallelRename (fun _ index => index + 3)
    (compile [] dependentDeclarations (.idx () 2)) =
      .cons [] typeConstant
        (.cons [()] (.idx () 0)
          (.cons [(), ()] (.idx () 5) .nil)) := by decide +kernel

/-- Shifting the bound occurrence in the second annotation would be wrong. -/
example : Fields.parallelRename (fun _ index => index + 3)
    (compile [] dependentDeclarations (.idx () 2)) ≠
      .cons [] typeConstant
        (.cons [()] (.idx () 3)
          (.cons [(), ()] (.idx () 5) .nil)) := by decide +kernel

/-- Substituting for a free variable preserves both local declarations. -/
example : Fields.parallelSubstitute (fun _ _ => typeConstant)
    (compile [] dependentDeclarations (.idx () 2)) =
      .cons [] typeConstant
        (.cons [()] (.idx () 0)
          (.cons [(), ()] typeConstant .nil)) := by decide +kernel

#print axioms compile_parallelRename
#print axioms compile_parallelSubstitute
#print axioms compile_supported_iff
#print axioms compile_substitution_preserves_scope

end Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Telescope
