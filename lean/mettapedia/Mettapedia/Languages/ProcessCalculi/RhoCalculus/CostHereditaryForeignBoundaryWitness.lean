import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

/-!
# The foreign name-typed boundary witness, and why it does not exist

The shared rho name sort makes an opposite-colour quote *correctly sorted* at a
name-typed position, so the role side condition of a foreign boundary plan is
satisfiable there.  That is what made the witness

    PDrop_c ( NQuote_dc ( PDrop_dc ( bvar 0 ) ) )      vs      PDrop_c ( bvar 0 )

look realizable, and with it a certified boundary whose content canonicalizes
to a bare bound variable.

It is not realizable, and the obstruction is neither the role nor the sort.  It
is the *reflective* half of well-sortedness.  `ReflectiveScopeSafeAt` demands
`binderSafeAt presentation.quoteConstructor` for every presentation of the
profile, and `binderSafeAt` **resets the admissible binder depth to zero under a
quotation**.  A quotation body therefore admits no ambient bound variable at
all — at either colour, at every sort, and at every depth.

Boundary certification runs exactly that check, so the `(certified boundary,
bound-variable)` configuration is empty for the quote/drop shape.  The
companion shape, a parallel singleton, is already excluded at the process type
by the disjointness of the two process fibres.

Everything below is stated for an arbitrary reflective declaration drawn from
the profile, so it covers the selected and the opposite colour uniformly.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## The witness content, and its kernel-checked rejection -/

/-- The shared rho name type.  Both static colours send `Name` here. -/
def rhoNameType : TypeExpr := .base (costBaseSortName "Name")

/-- One ambient name binder. -/
def rhoNameSupport : List TypeExpr := [rhoNameType]

/-- The proposed foreign boundary content: an opposite-colour quote/drop over
the ambient name binder, sitting at the shared name sort. -/
def foreignQuoteDropContent : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]

/-- Its selected-colour spelling. -/
def selectedQuoteDropContent : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [.bvar 0]]

/-- **The witness content is not admissible.**  The opposite-colour quote/drop
over an ambient binder fails reflective well-sortedness, so no boundary
certificate for it exists. -/
theorem foreignQuoteDropContent_not_wellSorted :
    ReflectiveWellSorted.checkOpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty rhoNameSupport rhoNameType
        foreignQuoteDropContent = false := by
  decide

/-- The same failure at the selected colour: the obstruction is not the
colour. -/
theorem selectedQuoteDropContent_not_wellSorted :
    ReflectiveWellSorted.checkOpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty rhoNameSupport rhoNameType
        selectedQuoteDropContent = false := by
  decide

/-- The *ordinary* half of well-sortedness accepts the witness content; only
the reflective half rejects it.  This pins the obstruction precisely: it is
not typing, not scoping at the core level, and not the sort. -/
theorem foreignQuoteDropContent_core_wellSorted :
    WellSorted.checkOpenPatternWellSorted rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty rhoNameSupport rhoNameType
        foreignQuoteDropContent = true := by
  decide

/-! ## The full witness pair, and its verdict

The proposed pair was

    left  = PDrop_base ( NQuote_wrapped ( PDrop_wrapped ( bvar 0 ) ) )
    right = PDrop_base ( bvar 0 )

at one ambient name binder and the base process type.  The right endpoint is a
genuine term.  The left endpoint is not a term at all, so no plan, no node, no
tree and no static root view exist over it, and the pair never enters any
obligation's telescope. -/

/-- The base process type. -/
def rhoBaseProcType : TypeExpr := .base (costBaseSortName "Proc")

/-- The proposed left endpoint. -/
def witnessLeft : Pattern :=
  .apply (costBaseConstructorName "PDrop") [foreignQuoteDropContent]

/-- The proposed right endpoint. -/
def witnessRight : Pattern :=
  .apply (costBaseConstructorName "PDrop") [.bvar 0]

/-- The same left shape with a *closed* quotation body. -/
def witnessLeftClosedQuote : Pattern :=
  .apply (costBaseConstructorName "PDrop")
    [.apply (costWrappedConstructorName "NQuote")
      [.apply (costWrappedConstructorName "PZero") []]]

/-- **The left endpoint is not a well-sorted term.** -/
theorem witnessLeft_not_wellSorted :
    ReflectiveWellSorted.checkOpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty rhoNameSupport rhoBaseProcType
        witnessLeft = false := by
  decide

/-- The right endpoint is a well-sorted term. -/
theorem witnessRight_wellSorted :
    ReflectiveWellSorted.checkOpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty rhoNameSupport rhoBaseProcType
        witnessRight = true := by
  decide

/-- Closing the quotation body restores admissibility.  So the obstruction is
exactly the ambient bound variable underneath the quotation — not the mixed
colouring, which survives here untouched. -/
theorem witnessLeftClosedQuote_wellSorted :
    ReflectiveWellSorted.checkOpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty rhoNameSupport rhoBaseProcType
        witnessLeftClosedQuote = true := by
  decide

/-! ## The general guard: a quotation seals the ambient binder context -/

/-- The quote/drop-over-a-bound-variable content, at either declaration
colour.  This is one of the only two shapes whose canonical form is a bare
bound variable. -/
def quoteDropBVar (color : CostStaticColor) (index : Nat) : Pattern :=
  .apply
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor
    [.apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor
      [.bvar index]]

theorem foreignQuoteDropContent_eq :
    foreignQuoteDropContent = quoteDropBVar .wrapped 0 := rfl

theorem selectedQuoteDropContent_eq :
    selectedQuoteDropContent = quoteDropBVar .base 0 := rfl

/-- Reflective admission of a quotation-rooted pattern seals its body: the
admissible binder depth inside a quotation is zero. -/
theorem binderSafeAt_body_of_reflectiveScopeSafeAt
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ profile.presentations)
    {depth : Nat} {body : Pattern}
    (safe : ReflectiveWellSorted.ReflectiveScopeSafeAt profile depth
      (.apply declaration.quoteConstructor [body])) :
    binderSafeAt declaration.quoteConstructor 0 body = true := by
  have applied := safe declaration membership
  simpa [binderSafeAt] using applied

/-- Every coloured rho reflective declaration is a presentation of the whole
Cost reflection profile. -/
theorem rhoDecl_mem_profile (color : CostStaticColor) :
    costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
  apply costStaticReflectivePresentationDecl_mem
  decide

/-- The two rho declaration colours each keep drop and quote distinct. -/
theorem rhoDecl_drop_ne_quote (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).dropConstructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor := by
  cases color <;> decide

/-- **The boundary-content emptiness lemma for the quote/drop shape.**

No admissible pattern, at any support, free context or type, is a quotation
whose body is a drop of an ambient bound variable — at either colour.  The
obstruction is `binderSafeAt`, which resets the admissible binder depth to
zero under a quotation. -/
theorem not_reflectivelyWellSorted_quoteDropBVar
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {targetSupport : List TypeExpr} {targetType : TypeExpr} {index : Nat} :
    ¬ ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree targetSupport targetType (quoteDropBVar color index) := by
  intro admitted
  have sealed := binderSafeAt_body_of_reflectiveScopeSafeAt
    (rhoDecl_mem_profile color) admitted.2
  simp [binderSafeAt, binderSafeListAt] at sealed

/-- **Certification never accepts quote/drop over a bound variable**, at either
colour, and independently of the boundary's own colour, support, type and free
context. -/
theorem certifyCostRegionBoundary?_quoteDropBVar_eq_none
    (color declarationColor : CostStaticColor) (targetFree : FreeTypeContext)
    (targetSupport : List TypeExpr) (targetType : TypeExpr) (index : Nat) :
    certifyCostRegionBoundary? rhoCIGSLT color targetFree targetSupport
        targetType (quoteDropBVar declarationColor index) = none := by
  have rejected :
      ReflectiveWellSorted.checkOpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree targetSupport targetType
          (quoteDropBVar declarationColor index) ≠ true := by
    intro checked
    exact not_reflectivelyWellSorted_quoteDropBVar declarationColor
      ((ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree targetSupport targetType
        (quoteDropBVar declarationColor index)).mp checked)
  unfold certifyCostRegionBoundary?
  cases decodeCostStaticTypeExpr rhoCIGSLT color targetType with
  | none => rfl
  | some sourceType => exact dif_neg rejected

/-- Certification of the concrete witness content therefore fails outright. -/
theorem foreignQuoteDropContent_not_certified :
    certifyCostRegionBoundary? rhoCIGSLT .base FreeTypeContext.empty
        rhoNameSupport rhoNameType foreignQuoteDropContent = none := by
  rw [foreignQuoteDropContent_eq]
  exact certifyCostRegionBoundary?_quoteDropBVar_eq_none _ _ _ _ _ _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness
