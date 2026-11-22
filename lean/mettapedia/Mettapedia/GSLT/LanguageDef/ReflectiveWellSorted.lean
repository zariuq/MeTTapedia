import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.QuoteScopeSafety

/-!
# Well-sorted carriers with an explicit reflection profile

The five-field carrier checks ordinary typing, representation, and locally
nameless scope.  This module attaches the scope obligation selected by a
reflection profile: each presentation asks what its declared quote scope needs
(`scopeSafeAt`), quotation sealing for a closed scope and ordinary scope for a
reaching one.  Erasing the profile leaves the core carrier literally unchanged.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Every presentation selected by a reflection profile asks of the pattern, at
the stated binder depth, the scope safety its declared quote scope needs:
a closed scope seals the ambient binder context at its quotations, a reaching
scope asks ordinary scope. -/
def ReflectiveScopeSafeAt (profile : ReflectionProfile) (depth : Nat)
    (pattern : Pattern) : Prop :=
  ∀ presentation ∈ profile.presentations,
    scopeSafeAt presentation.quoteScope presentation.quoteConstructor depth pattern = true

@[simp]
theorem reflectiveScopeSafeAt_empty (depth : Nat) (pattern : Pattern) :
    ReflectiveScopeSafeAt .empty depth pattern := by
  simp [ReflectiveScopeSafeAt]

/-- A profile all of whose presentations keep quoted code closed. -/
def ClosedProfile (profile : ReflectionProfile) : Prop :=
  ∀ presentation ∈ profile.presentations, presentation.quoteScope = .closed

instance (profile : ReflectionProfile) : Decidable (ClosedProfile profile) :=
  inferInstanceAs (Decidable (∀ presentation ∈ profile.presentations,
    presentation.quoteScope = .closed))

@[simp]
theorem closedProfile_empty : ClosedProfile .empty := by
  simp [ClosedProfile]

/-- Rho keeps quoted code closed. -/
theorem rhoReflectionProfile_closed :
    ClosedProfile ReflectionExtension.rhoReflectionProfile := by
  decide

/-- Over a closed profile the obligation is quotation sealing. -/
theorem reflectiveScopeSafeAt_iff_of_closed {profile : ReflectionProfile}
    (closed : ClosedProfile profile) {depth : Nat} {pattern : Pattern} :
    ReflectiveScopeSafeAt profile depth pattern ↔
      ∀ presentation ∈ profile.presentations,
        binderSafeAt presentation.quoteConstructor depth pattern = true := by
  refine forall₂_congr fun presentation member => ?_
  rw [scopeSafeAt_of_closed (closed presentation member)]

/-- A pattern sealed at every selected quotation is safe under every declared
scope. -/
theorem ReflectiveScopeSafeAt.of_binderSafeAt {profile : ReflectionProfile}
    {depth : Nat} {pattern : Pattern}
    (sealed : ∀ presentation ∈ profile.presentations,
      binderSafeAt presentation.quoteConstructor depth pattern = true) :
    ReflectiveScopeSafeAt profile depth pattern :=
  fun presentation member =>
    scopeSafeAt_of_binderSafeAt presentation.quoteScope (sealed presentation member)

/-- An operation that keeps quotation sealing for every quotation constructor
and keeps ordinary scope keeps the obligation of every profile. -/
theorem ReflectiveScopeSafeAt.map {profile : ReflectionProfile}
    {depth depth' : Nat} {pattern pattern' : Pattern}
    (sealing : ∀ quoteConstructor, binderSafeAt quoteConstructor depth pattern = true →
      binderSafeAt quoteConstructor depth' pattern' = true)
    (scoping : pattern.isWellScopedAt depth = true → pattern'.isWellScopedAt depth' = true)
    (safe : ReflectiveScopeSafeAt profile depth pattern) :
    ReflectiveScopeSafeAt profile depth' pattern' :=
  fun presentation member =>
    scopeSafeAt_map (sealing presentation.quoteConstructor) scoping (safe presentation member)

/-- An operation that keeps sealing and ordinary scope in both directions keeps
the obligation in both directions. -/
theorem ReflectiveScopeSafeAt.congr {profile : ReflectionProfile}
    {depth depth' : Nat} {pattern pattern' : Pattern}
    (sealing : ∀ quoteConstructor, binderSafeAt quoteConstructor depth pattern =
      binderSafeAt quoteConstructor depth' pattern')
    (scoping : pattern.isWellScopedAt depth = pattern'.isWellScopedAt depth') :
    ReflectiveScopeSafeAt profile depth pattern ↔ ReflectiveScopeSafeAt profile depth' pattern' :=
  forall₂_congr fun presentation _ => by
    rw [scopeSafeAt_congr (sealing presentation.quoteConstructor) scoping]

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
fibres.  The object pattern and its scope evidence are unchanged. -/
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
    quoteDropEquation := "QD"
    -- Closed: the canary's quotation seals its body against outer binders.
    quoteScope := .closed }

private def quoteCanaryProfile : ReflectionProfile :=
  { presentations := [quoteCanaryPresentation] }

/-- Negative canary: ordinary local scope does not imply sealing at a closed
quote boundary. -/
example :
    ScopeSafeAt 1 (.apply "Q" [.bvar 0]) ∧
      ¬ ReflectiveScopeSafeAt quoteCanaryProfile
        1 (.apply "Q" [.bvar 0]) := by
  constructor
  · simp [ScopeSafeAt, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · simp [ReflectiveScopeSafeAt, quoteCanaryProfile,
      quoteCanaryPresentation, binderSafeAt]

private def reachingCanaryProfile : ReflectionProfile :=
  { presentations := [{ quoteCanaryPresentation with quoteScope := .reaching .apply }] }

/-- Positive canary: a presentation whose binders reach into quotations asks
only ordinary scope, so its quotation may mention the binder around it. -/
example : ReflectiveScopeSafeAt reachingCanaryProfile 1 (.apply "Q" [.bvar 0]) := by
  simp [ReflectiveScopeSafeAt, reachingCanaryProfile, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

/-- Negative canary: a reaching presentation still asks ordinary scope. -/
example : ¬ ReflectiveScopeSafeAt reachingCanaryProfile 0 (.apply "Q" [.bvar 0]) := by
  simp [ReflectiveScopeSafeAt, reachingCanaryProfile, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

end Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
