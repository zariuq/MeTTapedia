import Mettapedia.GSLT.LanguageDef.ProofGSLTConversionElimination
import Mettapedia.GSLT.LanguageDef.ProofGSLTArticleIdentity

/-!
# Conversion tiers: scoping the sub-categories of hostable proof systems

Congruence is to contextual closure what conversion is to definitional
equality: a silent structural permission that a naive framework grants
globally, and that must instead be declared, scoped, and gated.  The
congruence side of that discipline is built (`Premise.congruence`,
`DirectTraceLanguage`, `languageDirectTraceAdequate`, and the falsifier
`congruence_is_not_free`).  This module opens the conversion side.

The proof calculus's `conversion` field carries the declaration — optional,
versioned, naming a binary judgment whose ordinary inference proofs are the
conversion edges.  What was missing is the classification it induces on
presentations, and an honest account of what the present checker does with
it.

## The tiers

```
  tier          judgment equality is        who lives here
  ----          --------------------        --------------
  syntactic     literal identity            Metamath, MM0, Hilbert systems,
                                            generated trace presentations
  certified     a declared judgment whose   CIC/Lean-family theories after
                proofs transport terms      conversion elimination
```

A third tier is *deliberately absent*: theories whose conversion is
decidable and which expect the checker to **recompute** it (the αβη
conversion of HOL-family kernels) cannot be expressed, because the checker
has no primitive that computes a conversion rather than replaying a proof of
one.  Adding it means adding to the trusted generic vocabulary, which is a
decision with its own semantics, wire encoding, and native-refinement
obligation — not a definition that can be slipped in here.

## What the present checker actually does

`checkRaw_independent_of_conversion` proves the uncomfortable half: the
current checker never consults the conversion declaration.  Acceptance
depends on the rule table alone (`checkRaw_congr`).  So today *every*
presentation is checked with syntactic-tier semantics, and a certified-tier
presentation is checked correctly only because its transport is authored as
an ordinary rule.  The declaration is validated and inert.

That is not a defect to hide; it is the precise statement of what the
conversion lane still owes, and it is why the syntactic tier — Metamath —
is the vertical that can be built with no new trusted machinery at all.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Acceptance depends on the rule table alone -/

mutual

/-- Two presentations with the same rule lookup accept the same proofs.
Nothing else about a presentation — its syntax declarations, judgment
signature, or conversion interface — reaches the checker. -/
theorem checkRaw_congr {source target : ValidatedPresentation}
    (agree : ∀ id, source.1.lookupRule? id = target.1.lookupRule? id)
    (goal : Pattern) (proof : RawProof) :
    checkRaw source goal proof = checkRaw target goal proof := by
  cases proof with
  | node ruleInstance children =>
      rw [checkRaw, checkRaw, instantiateRule?_congr (agree ruleInstance.ruleId)]
      cases instantiated : instantiateRule? target ruleInstance with
      | none => rfl
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [checkRawChildren_congr agree premises children]
  termination_by sizeOf proof

theorem checkRawChildren_congr {source target : ValidatedPresentation}
    (agree : ∀ id, source.1.lookupRule? id = target.1.lookupRule? id)
    (goals : List Pattern) (proofs : List RawProof) :
    checkRawChildren source goals proofs =
      checkRawChildren target goals proofs := by
  cases goals with
  | nil =>
      cases proofs with
      | nil => simp [checkRawChildren]
      | cons proof proofs => simp [checkRawChildren]
  | cons goal goals =>
      cases proofs with
      | nil => simp [checkRawChildren]
      | cons proof proofs =>
          rw [checkRawChildren, checkRawChildren,
            checkRaw_congr agree goal proof,
            checkRawChildren_congr agree goals proofs]
  termination_by sizeOf proofs

end

/-! ## Tiers -/

/-- How a presentation treats judgment equality. -/
inductive ConversionTier where
  /-- No conversion interface: equal judgments are literally identical. -/
  | syntactic
  /-- Conversion is a declared binary judgment; its ordinary proofs are the
  transport evidence, and transport is an authored rule. -/
  | certified
deriving DecidableEq, Repr

/-- A presentation's tier is read off its conversion declaration. -/
def conversionTierOf (presentation : Presentation) : ConversionTier :=
  match presentation.conversion with
  | none => ConversionTier.syntactic
  | some _ => ConversionTier.certified

theorem conversionTierOf_none {presentation : Presentation}
    (noConversion : presentation.conversion = none) :
    conversionTierOf presentation = ConversionTier.syntactic := by
  simp [conversionTierOf, noConversion]

theorem conversionTierOf_some {presentation : Presentation}
    {declaration : ConversionDecl}
    (declared : presentation.conversion = some declaration) :
    conversionTierOf presentation = ConversionTier.certified := by
  simp [conversionTierOf, declared]

/-- **The conversion declaration is inert in the present checker.**  Two
presentations differing only in their conversion interface accept exactly
the same proofs, so acceptance is currently syntactic-tier for every
presentation.  A certified-tier presentation is checked correctly only
because its transport is authored as an ordinary rule; the declaration
itself contributes nothing yet. -/
theorem checkRaw_independent_of_conversion
    {source target : ValidatedPresentation}
    (sameRules : source.1.rules = target.1.rules)
    (goal : Pattern) (proof : RawProof) :
    checkRaw source goal proof = checkRaw target goal proof := by
  refine checkRaw_congr (fun id => ?_) goal proof
  unfold Presentation.lookupRule?
  rw [sameRules]

/-- **The tiers are not yet distinguished by the checker.**  A syntactic-tier
presentation and a certified-tier presentation over the same rule table are
indistinguishable to `checkRaw`.

The tier hypotheses are stated and then *not used*: that is precisely the
content.  A reader should take the unused binders as the claim.  Two
consequences follow, and they pull in opposite directions.  For the
syntactic tier nothing is lost, since there is no conversion to honour —
which is why a syntactic-tier vertical needs no new trusted machinery.  For
the certified tier the declaration currently earns nothing, so such a
presentation is checked correctly only if its transport is authored as an
ordinary rule; making the declaration load-bearing is an obligation this
module opens and does not discharge. -/
theorem tier_not_consulted_by_checker
    {source target : ValidatedPresentation}
    (_sourceSyntactic : conversionTierOf source.1 = ConversionTier.syntactic)
    (_targetCertified : conversionTierOf target.1 = ConversionTier.certified)
    (sameRules : source.1.rules = target.1.rules) :
    ∀ (goal : Pattern) (proof : RawProof),
      checkRaw source goal proof = checkRaw target goal proof :=
  fun goal proof => checkRaw_independent_of_conversion sameRules goal proof

/-- The syntactic tier is exactly the presentations that declare no
conversion interface, so membership is decidable by inspection. -/
theorem conversionTierOf_syntactic_iff {presentation : Presentation} :
    conversionTierOf presentation = ConversionTier.syntactic ↔
      presentation.conversion = none := by
  unfold conversionTierOf
  cases presentation.conversion with
  | none => simp
  | some declaration => simp

end Mettapedia.GSLT.LanguageDef.ProofGSLT
