import Mettapedia.GSLT.LanguageDef.DialectGluing
import Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory

/-!
# Structural inclusion morphisms for dialect gluing

The list-level gluing of two presentations admits structural inclusion maps
when the required presentations are validated.  The left inclusion keeps
every left declaration.  The right inclusion additionally requires coverage
of right/base key collisions: every filtered-out right declaration must
already occur verbatim in the left presentation.

Structural maps from both extensions to a common target induce a mediator
when their total symbol actions agree.  Both inclusion triangles then
commute.  This is a sufficient special case, not a pushout universal property:
a general cocone need only agree after restriction to the shared base.

The synthetic sort-renaming countermodel below separates those premises.
Its component maps agree on the common sort while renaming private sorts
differently.  A piecewise mediator satisfies both extensional triangles even
though the total symbol actions differ.  The general mediator and uniqueness
for arbitrary compatible spans are not established here.
-/

namespace Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory

/-! ## The left inclusion -/

/-- The left extension includes into any gluing over it, with identity symbol
action: `glue` keeps every left declaration verbatim in append-left position. -/
def leftInclusionMorphism (name : String) (base : LanguageDef)
    {left right : LanguageDef}
    (leftValid : left.validate = [])
    (gluedValid : (glue name base left right).validate = []) :
    StructuralMorphism ⟨left, leftValid⟩ ⟨glue name base left right, gluedValid⟩ where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations equation membership := by
    rw [mapEquation_id]
    exact List.mem_append_left _ membership
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_id]
    exact List.mem_append_left _ membership

/-! ## Right/base collision coverage and the right inclusion -/

/-- Right/base collisions are *covered* when every right declaration whose gluing key
already occurs in the base is itself a declaration of the left extension.
The four keys mirror the four filters of `glue` exactly: type name,
constructor label, equation name, rewrite name.  Collision coverage is what
makes the filter of `glue` harmless: a filtered-out right declaration is not
lost, because the left extension already carries it verbatim.

The `types` field is stated with `List.Mem`, as in `StructuralMorphism`,
because the `Membership String (List TypeDecl)` instance in the syntax module
captures `∈` on type-declaration lists through its out-param. -/
structure RightBaseCollisionsCovered (base left right : LanguageDef) : Prop where
  types : ∀ declaration : TypeDecl, List.Mem declaration right.types →
    declaration.name ∈ base.typeNames → List.Mem declaration left.types
  terms : ∀ rule ∈ right.terms,
    (∃ baseRule ∈ base.terms, baseRule.label = rule.label) → rule ∈ left.terms
  equations : ∀ equation ∈ right.equations,
    (∃ baseEquation ∈ base.equations, baseEquation.name = equation.name) →
      equation ∈ left.equations
  rewrites : ∀ rewrite ∈ right.rewrites,
    (∃ baseRewrite ∈ base.rewrites, baseRewrite.name = rewrite.name) →
      rewrite ∈ left.rewrites

/-- The right extension includes into the gluing when right/base collisions
are covered, with
identity symbol action.  A right declaration either passes the gluing filter
(append-right membership) or collides with the base on its key, in which case
coherence places it verbatim in the left extension (append-left membership). -/
def rightInclusionMorphism (name : String) {base left right : LanguageDef}
    (collisionsCovered : RightBaseCollisionsCovered base left right)
    (rightValid : right.validate = [])
    (gluedValid : (glue name base left right).validate = []) :
    StructuralMorphism ⟨right, rightValid⟩ ⟨glue name base left right, gluedValid⟩ where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    by_cases collision : declaration.name ∈ base.typeNames
    · exact List.mem_append_left _
        (collisionsCovered.types declaration membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    by_cases collision : ∃ baseRule ∈ base.terms, baseRule.label = rule.label
    · exact List.mem_append_left _
        (collisionsCovered.terms rule membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision
  mapsEquations equation membership := by
    rw [mapEquation_id]
    by_cases collision :
        ∃ baseEquation ∈ base.equations, baseEquation.name = equation.name
    · exact List.mem_append_left _
        (collisionsCovered.equations equation membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_id]
    by_cases collision :
        ∃ baseRewrite ∈ base.rewrites, baseRewrite.name = rewrite.name
    · exact List.mem_append_left _
        (collisionsCovered.rewrites rewrite membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision

/-! ## A same-global-action mediator (not a universal property) -/

/-- Structural maps out of the left and right extensions with the same total
symbol action induce a structural map out of the glued presentation: a glued
declaration comes either from the left extension or through the gluing filter
from the right one, and is mapped accordingly.  This special case does not
cover a general cocone, whose maps need only agree after restriction to the
shared base. -/
def sameActionMediator (name : String) {base left right : LanguageDef}
    {target : ValidatedLanguageDef}
    {leftValid : left.validate = []} {rightValid : right.validate = []}
    (gluedValid : (glue name base left right).validate = [])
    (leftMorphism : StructuralMorphism ⟨left, leftValid⟩ target)
    (rightMorphism : StructuralMorphism ⟨right, rightValid⟩ target)
    (sharedSymbols : leftMorphism.symbols = rightMorphism.symbols) :
    StructuralMorphism ⟨glue name base left right, gluedValid⟩ target where
  symbols := leftMorphism.symbols
  mapsTypes declaration membership := by
    have split : List.Mem declaration (left.types ++ right.types.filter
        (fun declaration => !(base.typeNames.contains declaration.name))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsTypes declaration leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsTypes declaration (List.mem_filter.mp rightMember).1
  mapsTerms rule membership := by
    have split : rule ∈ left.terms ++ right.terms.filter
        (fun rule => !(base.terms.any (·.label == rule.label))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsTerms rule leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsTerms rule (List.mem_filter.mp rightMember).1
  mapsEquations equation membership := by
    have split : equation ∈ left.equations ++ right.equations.filter
        (fun equation => !(base.equations.any (·.name == equation.name))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsEquations equation leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsEquations equation
        (List.mem_filter.mp rightMember).1
  mapsRewrites rewrite membership := by
    have split : rewrite ∈ left.rewrites ++ right.rewrites.filter
        (fun rewrite => !(base.rewrites.any (·.name == rewrite.name))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsRewrites rewrite leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsRewrites rewrite (List.mem_filter.mp rightMember).1

/-- The left triangle commutes on the nose. -/
theorem sameActionMediator_comp_left_inclusion (name : String)
    {base left right : LanguageDef} {target : ValidatedLanguageDef}
    {leftValid : left.validate = []} {rightValid : right.validate = []}
    (gluedValid : (glue name base left right).validate = [])
    (leftMorphism : StructuralMorphism ⟨left, leftValid⟩ target)
    (rightMorphism : StructuralMorphism ⟨right, rightValid⟩ target)
    (sharedSymbols : leftMorphism.symbols = rightMorphism.symbols) :
    StructuralMorphism.comp (leftInclusionMorphism name base leftValid gluedValid)
        (sameActionMediator name gluedValid leftMorphism rightMorphism
          sharedSymbols) =
      leftMorphism :=
  StructuralMorphism.ext rfl

/-- The right triangle commutes on the nose, given the shared symbol action;
the coherence witness is needed only to state the right inclusion. -/
theorem sameActionMediator_comp_right_inclusion (name : String)
    {base left right : LanguageDef} {target : ValidatedLanguageDef}
    (collisionsCovered : RightBaseCollisionsCovered base left right)
    {leftValid : left.validate = []} {rightValid : right.validate = []}
    (gluedValid : (glue name base left right).validate = [])
    (leftMorphism : StructuralMorphism ⟨left, leftValid⟩ target)
    (rightMorphism : StructuralMorphism ⟨right, rightValid⟩ target)
    (sharedSymbols : leftMorphism.symbols = rightMorphism.symbols) :
    StructuralMorphism.comp
        (rightInclusionMorphism name collisionsCovered rightValid gluedValid)
        (sameActionMediator name gluedValid leftMorphism rightMorphism
          sharedSymbols) =
      rightMorphism :=
  StructuralMorphism.ext (by rw [← sharedSymbols]; rfl)

/-! ## Why base agreement is strictly weaker than one global action

The following all-sort presentations isolate the categorical gap without any
operational or validator noise.  Both component maps fix the shared sort `B`.
The left map independently renames `L`, while the right map independently
renames `R`.  Hence the two composites out of the base are extensionally
equal, although the total symbol actions are unequal.  A piecewise mediator
exists and satisfies both triangles in the quotient category.
-/

private def agreementBase : LanguageDef :=
  { name := "gluing-base-agreement-base"
    types := [TypeDecl.plain "B"]
    terms := []
    equations := []
    rewrites := [] }

private def agreementLeft : LanguageDef :=
  { name := "gluing-base-agreement-left"
    types := [TypeDecl.plain "B", TypeDecl.plain "L"]
    terms := []
    equations := []
    rewrites := [] }

private def agreementRight : LanguageDef :=
  { name := "gluing-base-agreement-right"
    types := [TypeDecl.plain "B", TypeDecl.plain "R"]
    terms := []
    equations := []
    rewrites := [] }

private def agreementTarget : LanguageDef :=
  { name := "gluing-base-agreement-target"
    types := [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
    terms := []
    equations := []
    rewrites := [] }

private theorem agreementBase_validate : agreementBase.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementBase, LanguageDef.typeNames, TypeDecl.plain]

private theorem agreementLeft_validate : agreementLeft.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementLeft, LanguageDef.typeNames, TypeDecl.plain]

private theorem agreementRight_validate : agreementRight.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementRight, LanguageDef.typeNames, TypeDecl.plain]

private theorem agreementTarget_validate : agreementTarget.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementTarget, LanguageDef.typeNames, TypeDecl.plain]

private def agreementGlued : LanguageDef :=
  glue "gluing-base-agreement" agreementBase agreementLeft agreementRight

private theorem agreementGlued_validate : agreementGlued.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementGlued, glue, agreementBase, agreementLeft, agreementRight,
      LanguageDef.typeNames, TypeDecl.plain]

private def renameSort (source target : String) (name : String) : String :=
  if name = source then target else name

private def agreementLeftSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with sort := renameSort "L" "TL" }

private def agreementRightSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with sort := renameSort "R" "TR" }

private def agreementMediatorSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
    sort := fun name =>
      if name = "L" then "TL" else if name = "R" then "TR" else name }

private theorem agreementTarget_has_B :
    List.Mem (TypeDecl.plain "B") agreementTarget.types := by
  change List.Mem (TypeDecl.plain "B")
    [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
  exact List.Mem.head _

private theorem agreementTarget_has_TL :
    List.Mem (TypeDecl.plain "TL") agreementTarget.types := by
  change List.Mem (TypeDecl.plain "TL")
    [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
  exact List.Mem.tail _ (List.Mem.head _)

private theorem agreementTarget_has_TR :
    List.Mem (TypeDecl.plain "TR") agreementTarget.types := by
  change List.Mem (TypeDecl.plain "TR")
    [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private def agreementLeftMap :
    StructuralMorphism ⟨agreementLeft, agreementLeft_validate⟩
      ⟨agreementTarget, agreementTarget_validate⟩ where
  symbols := agreementLeftSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "L"]
      at membership
    rcases List.mem_cons.mp membership with head | tail
    · subst declaration
      simpa [agreementLeftSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_B
    · have head := List.mem_singleton.mp tail
      subst declaration
      simpa [agreementLeftSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_TL
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementRightMap :
    StructuralMorphism ⟨agreementRight, agreementRight_validate⟩
      ⟨agreementTarget, agreementTarget_validate⟩ where
  symbols := agreementRightSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "R"]
      at membership
    rcases List.mem_cons.mp membership with head | tail
    · subst declaration
      simpa [agreementRightSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_B
    · have head := List.mem_singleton.mp tail
      subst declaration
      simpa [agreementRightSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_TR
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private theorem agreementRightBaseCollisionsCovered :
    RightBaseCollisionsCovered agreementBase agreementLeft agreementRight where
  types declaration rightMember collision := by
    change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "R"]
      at rightMember
    rcases List.mem_cons.mp rightMember with head | tail
    · subst declaration
      change List.Mem (TypeDecl.plain "B")
        [TypeDecl.plain "B", TypeDecl.plain "L"]
      exact List.Mem.head _
    · have head := List.mem_singleton.mp tail
      subst declaration
      simp [agreementBase, LanguageDef.typeNames, TypeDecl.plain] at collision
  terms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  equations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  rewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementLeftInclusion :
    StructuralMorphism ⟨agreementLeft, agreementLeft_validate⟩
      ⟨agreementGlued, agreementGlued_validate⟩ :=
  leftInclusionMorphism "gluing-base-agreement" agreementBase
    agreementLeft_validate agreementGlued_validate

private def agreementRightInclusion :
    StructuralMorphism ⟨agreementRight, agreementRight_validate⟩
      ⟨agreementGlued, agreementGlued_validate⟩ :=
  rightInclusionMorphism "gluing-base-agreement"
    agreementRightBaseCollisionsCovered
    agreementRight_validate agreementGlued_validate

private def agreementBaseIntoLeft :
    StructuralMorphism ⟨agreementBase, agreementBase_validate⟩
      ⟨agreementLeft, agreementLeft_validate⟩ where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration [TypeDecl.plain "B"] at membership
    have head := List.mem_singleton.mp membership
    subst declaration
    change List.Mem (TypeDecl.plain "B")
      [TypeDecl.plain "B", TypeDecl.plain "L"]
    exact List.Mem.head _
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementBaseIntoRight :
    StructuralMorphism ⟨agreementBase, agreementBase_validate⟩
      ⟨agreementRight, agreementRight_validate⟩ where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration [TypeDecl.plain "B"] at membership
    have head := List.mem_singleton.mp membership
    subst declaration
    change List.Mem (TypeDecl.plain "B")
      [TypeDecl.plain "B", TypeDecl.plain "R"]
    exact List.Mem.head _
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementMediator :
    StructuralMorphism ⟨agreementGlued, agreementGlued_validate⟩
      ⟨agreementTarget, agreementTarget_validate⟩ where
  symbols := agreementMediatorSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration
      [TypeDecl.plain "B", TypeDecl.plain "L", TypeDecl.plain "R"]
      at membership
    rcases List.mem_cons.mp membership with head | tail
    · subst declaration
      simpa [agreementMediatorSymbols, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_B
    · rcases List.mem_cons.mp tail with head | tail
      · subst declaration
        simpa [agreementMediatorSymbols, mapTypeDecl, TypeDecl.plain] using
          agreementTarget_has_TL
      · have head := List.mem_singleton.mp tail
        subst declaration
        simpa [agreementMediatorSymbols, mapTypeDecl, TypeDecl.plain] using
          agreementTarget_has_TR
  mapsTerms rule membership := by
    change List.Mem rule ([] ++ []) at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation ([] ++ []) at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite ([] ++ []) at membership
    cases membership

/-
The definitions above intentionally spell out the two base inclusions and the
piecewise mediator.  Keeping them independent of the special-case helper is
what makes the canary capable of detecting that helper's stronger premise.
-/

/-- The two component maps form a genuine cocone over the shared base. -/
theorem agreement_maps_agree_on_base :
    Equivalent
      (StructuralMorphism.comp agreementBaseIntoLeft agreementLeftMap)
      (StructuralMorphism.comp agreementBaseIntoRight agreementRightMap) where
  types declaration membership := by
    change List.Mem declaration [TypeDecl.plain "B"] at membership
    have head := List.mem_singleton.mp membership
    subst declaration
    simp [StructuralMorphism.comp, LanguageDefSymbolMap.comp,
      agreementBaseIntoLeft, agreementBaseIntoRight, agreementLeftMap,
      agreementRightMap, agreementLeftSymbols, agreementRightSymbols,
      renameSort, mapTypeDecl, LanguageDefSymbolMap.id, TypeDecl.plain]
  terms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  equations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  rewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

/-- The same cocone's total symbol actions differ away from the shared base.
Consequently, base agreement cannot justify the `sharedSymbols` premise of
`sameActionMediator`. -/
theorem baseAgreement_does_not_imply_same_global_action :
    agreementLeftMap.symbols ≠ agreementRightMap.symbols := by
  intro equal
  have atLeft := congrArg (fun symbols => symbols.sort "L") equal
  simp [agreementLeftMap, agreementRightMap, agreementLeftSymbols,
    agreementRightSymbols, renameSort] at atLeft

/-- A mediator nevertheless exists for this cocone in the extensional
category; the missing general construction must synthesize such a piecewise
symbol action rather than require the two component actions to be equal. -/
theorem agreement_mediator_triangles :
    Equivalent
        (StructuralMorphism.comp agreementLeftInclusion agreementMediator)
        agreementLeftMap ∧
      Equivalent
        (StructuralMorphism.comp agreementRightInclusion agreementMediator)
        agreementRightMap := by
  constructor
  · constructor <;> intro declaration membership
    · change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "L"]
        at membership
      rcases List.mem_cons.mp membership with head | tail
      · subst declaration
        simp [StructuralMorphism.comp, LanguageDefSymbolMap.comp,
          agreementLeftInclusion, agreementMediator, agreementLeftMap,
          agreementMediatorSymbols, agreementLeftSymbols, renameSort,
          mapTypeDecl, leftInclusionMorphism, LanguageDefSymbolMap.id,
          TypeDecl.plain]
      · have head := List.mem_singleton.mp tail
        subst declaration
        simp [StructuralMorphism.comp, LanguageDefSymbolMap.comp,
          agreementLeftInclusion, agreementMediator, agreementLeftMap,
          agreementMediatorSymbols, agreementLeftSymbols, renameSort,
          mapTypeDecl, leftInclusionMorphism, LanguageDefSymbolMap.id,
          TypeDecl.plain]
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership

  · constructor <;> intro declaration membership
    · change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "R"]
        at membership
      rcases List.mem_cons.mp membership with head | tail
      · subst declaration
        simp [StructuralMorphism.comp, LanguageDefSymbolMap.comp,
          agreementRightInclusion, agreementMediator, agreementRightMap,
          agreementMediatorSymbols, agreementRightSymbols, renameSort,
          mapTypeDecl, rightInclusionMorphism, LanguageDefSymbolMap.id,
          TypeDecl.plain]
      · have head := List.mem_singleton.mp tail
        subst declaration
        simp [StructuralMorphism.comp, LanguageDefSymbolMap.comp,
          agreementRightInclusion, agreementMediator, agreementRightMap,
          agreementMediatorSymbols, agreementRightSymbols, renameSort,
          mapTypeDecl, rightInclusionMorphism, LanguageDefSymbolMap.id,
          TypeDecl.plain]
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership

/-- There is a validated gluing cocone whose component maps agree on the
shared base but have different total symbol actions, while a piecewise
mediator still satisfies both triangles.  This exposes the exact scope gap in
`sameActionMediator` without exporting the private canary presentations.

The result is deliberately existential: it proves that a general gluing
construction must synthesize declaration-supported piecewise actions.  It
does not claim that the current `glue` operation already has a pushout
universal property for every compatible span. -/
theorem exists_base_agreeing_cocone_with_piecewise_mediator :
    ∃ (base left right glued target : ValidatedLanguageDef)
      (baseIntoLeft : StructuralMorphism base left)
      (baseIntoRight : StructuralMorphism base right)
      (leftInclusion : StructuralMorphism left glued)
      (rightInclusion : StructuralMorphism right glued)
      (leftMap : StructuralMorphism left target)
      (rightMap : StructuralMorphism right target)
      (mediator : StructuralMorphism glued target),
      glued.language =
          glue "gluing-base-agreement" base.language left.language
            right.language ∧
        Equivalent
            (StructuralMorphism.comp baseIntoLeft leftMap)
            (StructuralMorphism.comp baseIntoRight rightMap) ∧
        leftMap.symbols ≠ rightMap.symbols ∧
        Equivalent
            (StructuralMorphism.comp leftInclusion mediator) leftMap ∧
        Equivalent
            (StructuralMorphism.comp rightInclusion mediator) rightMap := by
  refine ⟨⟨agreementBase, agreementBase_validate⟩,
    ⟨agreementLeft, agreementLeft_validate⟩,
    ⟨agreementRight, agreementRight_validate⟩,
    ⟨agreementGlued, agreementGlued_validate⟩,
    ⟨agreementTarget, agreementTarget_validate⟩,
    agreementBaseIntoLeft, agreementBaseIntoRight,
    agreementLeftInclusion, agreementRightInclusion,
    agreementLeftMap, agreementRightMap, agreementMediator, ?_⟩
  exact ⟨rfl, agreement_maps_agree_on_base,
    baseAgreement_does_not_imply_same_global_action,
    agreement_mediator_triangles.1, agreement_mediator_triangles.2⟩

/-! ## Axiom audit -/

#print axioms leftInclusionMorphism
#print axioms rightInclusionMorphism
#print axioms sameActionMediator
#print axioms sameActionMediator_comp_left_inclusion
#print axioms sameActionMediator_comp_right_inclusion
#print axioms agreement_maps_agree_on_base
#print axioms baseAgreement_does_not_imply_same_global_action
#print axioms agreement_mediator_triangles
#print axioms exists_base_agreeing_cocone_with_piecewise_mediator

end Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms
