import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Well-sorted carriers with an explicit reflection profile

The five-field carrier checks ordinary typing, representation, and locally
nameless scope.  This module attaches the additional quote-sealing obligation
selected by a reflection profile.  Erasing the profile leaves the core
carrier literally unchanged.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Every quotation constructor selected by a reflection profile seals the
ambient binder context at the stated depth. -/
def ReflectiveScopeSafeAt (profile : ReflectionProfile) (depth : Nat)
    (pattern : Pattern) : Prop :=
  ∀ presentation ∈ profile.presentations,
    binderSafeAt presentation.quoteConstructor depth pattern = true

@[simp]
theorem reflectiveScopeSafeAt_empty (depth : Nat) (pattern : Pattern) :
    ReflectiveScopeSafeAt .empty depth pattern := by
  simp [ReflectiveScopeSafeAt]

/-- The core open carrier together with the independently authored reflection
obligation. -/
def OpenPatternWellSorted (profile : ReflectionProfile)
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) : Prop :=
  WellSorted.OpenPatternWellSorted language free bound type pattern ∧
    ReflectiveScopeSafeAt profile bound.length pattern

abbrev OpenPattern (profile : ReflectionProfile) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr) :=
  { pattern : Pattern //
      OpenPatternWellSorted profile language free bound type pattern }

/-- The reflective open carrier at one authored base sort. -/
def OpenTermWellSorted (profile : ReflectionProfile)
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (sort : LangSort language)
    (pattern : Pattern) : Prop :=
  OpenPatternWellSorted profile language free bound (.base sort.1) pattern

abbrev OpenTerm (profile : ReflectionProfile) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort language) :=
  { pattern : Pattern //
      OpenTermWellSorted profile language free bound sort pattern }

/-- Transport a reflective open term between propositionally equal typing
fibres.  The object pattern and its quote-sealing evidence are unchanged. -/
def OpenTerm.reindex {profile : ReflectionProfile}
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm profile language sourceFree sourceBound sourceSort) :
    OpenTerm profile language targetFree targetBound targetSort := by
  cases freeEquality
  cases boundEquality
  cases sortEquality
  exact term

@[simp]
theorem OpenTerm.reindex_pattern {profile : ReflectionProfile}
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm profile language sourceFree sourceBound sourceSort) :
    (term.reindex freeEquality boundEquality sortEquality).1 = term.1 := by
  cases freeEquality
  cases boundEquality
  cases sortEquality
  rfl

/-- The core closed carrier together with top-level quote sealing. -/
def ClosedTermWellSorted (profile : ReflectionProfile)
    (language : LanguageDef) (sort : LangSort language)
    (pattern : Pattern) : Prop :=
  WellSorted.ClosedTermWellSorted language sort pattern ∧
    ReflectiveScopeSafeAt profile 0 pattern

abbrev ClosedTerm (profile : ReflectionProfile) (language : LanguageDef)
    (sort : LangSort language) :=
  { pattern : Pattern // ClosedTermWellSorted profile language sort pattern }

/-- Forgetting reflection evidence returns exactly the five-field open
carrier. -/
def OpenPattern.toCore {profile : ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern profile language free bound type) :
    WellSorted.OpenPattern language free bound type :=
  ⟨pattern.1, pattern.2.1⟩

/-- Forgetting reflection evidence returns exactly the five-field open term
carrier at the same sort. -/
def OpenTerm.toCore {profile : ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm profile language free bound sort) :
    WellSorted.OpenTerm language free bound sort :=
  ⟨term.1, term.2.1⟩

@[simp]
theorem OpenTerm.toCore_pattern {profile : ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm profile language free bound sort) :
    term.toCore.1 = term.1 :=
  rfl

@[simp]
theorem OpenTerm.toCore_coe {profile : ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm profile language free bound sort) :
    (term.toCore : Pattern) = (term : Pattern) :=
  rfl

/-- Restrict the ambient free context to the names used by a reflective open
term.  The five-field typing derivation is recontextualized by the core
operation, while the reflection certificate is unchanged because the raw
pattern and binder depth do not change. -/
def OpenTerm.restrictFreeContext {profile : ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm profile language free bound sort) :
    OpenTerm profile language
      (free.restrictTo term.1.freeFvarNames) bound sort :=
  ⟨term.toCore.restrictFreeContext.1,
    term.toCore.restrictFreeContext.2, term.2.2⟩

@[simp]
theorem OpenTerm.restrictFreeContext_pattern {profile : ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm profile language free bound sort) :
    term.restrictFreeContext.1 = term.1 :=
  rfl

/-- Forgetting reflection evidence returns exactly the five-field closed
carrier. -/
def ClosedTerm.toCore {profile : ReflectionProfile}
    {language : LanguageDef} {sort : LangSort language}
    (term : ClosedTerm profile language sort) :
    WellSorted.ClosedTerm language sort :=
  ⟨term.1, term.2.1⟩

private def quoteCanaryPresentation : ReflectivePresentationDecl :=
  { name := "quoted"
    processSort := "P"
    nameSort := "N"
    quoteConstructor := "Q"
    dropConstructor := "D"
    parallelCollection := .hashBag
    parallelUnitConstructor := "Z"
    quoteDropEquation := "QD" }

private def quoteCanaryProfile : ReflectionProfile :=
  { presentations := [quoteCanaryPresentation] }

/-- Negative canary: ordinary local scope does not imply sealing at a quote
boundary. -/
example :
    ScopeSafeAt 1 (.apply "Q" [.bvar 0]) ∧
      ¬ ReflectiveScopeSafeAt quoteCanaryProfile
        1 (.apply "Q" [.bvar 0]) := by
  constructor
  · simp [ScopeSafeAt, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · simp [ReflectiveScopeSafeAt, quoteCanaryProfile,
      quoteCanaryPresentation, binderSafeAt, binderSafeListAt]

end Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
