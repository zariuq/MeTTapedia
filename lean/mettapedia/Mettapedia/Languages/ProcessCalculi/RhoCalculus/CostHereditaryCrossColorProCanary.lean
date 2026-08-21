/-
# The depth-three cross-colour canary (external-review fixture)

The pair

    proLeft  = Q_b(D_b(Q_w(0_w)))
    proRight = Q_w(D_w(Q_b(0_b)))

is the minimal closed cross-colour witness from the external mathematical
review (2026-08-18).  Each endpoint collapses at its own colour and stays
rigid at the other; at no single colour are the two canonicalizations equal.
Under colour erasure both canonical forms are the authored normal `Q(0)`.

What this fixture establishes, kernel-checked:

* the two closure computations at each endpoint's own colour;
* inequality of the base/wrapped canonicalizations at **both** colours;
* concordance after colour erasure (the authored normal `Q(0)`);
* hence the pair satisfies the premise of an authored-equality theorem while
  never satisfying the premise of any single-colour canonical-equality
  theorem at either colour: such a pair lies strictly *outside* the present
  single-colour premise of the cross-colour obligation.  It refutes the
  raw `RestoresTogether`-style raw-equality reading of that obligation,
  forcing the heterogeneous authored-apex reform.

What it does not attempt: instantiating the present cospan record.  That is
the follow-up repair step (authored apex with two reification legs), which
builds on `costErase` and this fixture's facts rather than the legacy
same-colour provider.
-/

import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- **Colour erasure at the constructor string level.**  Cost-tagged
constructors are tag-prefixed authored labels; erasure strips the tag.
(Fixture-local; the authored-apex step generalizes this to a first-class
erasure with typing preservation.) -/
def proEraseConstructor (constructor : String) : String :=
  if constructor = costBaseConstructorName "NQuote" then "NQuote"
  else if constructor = costWrappedConstructorName "NQuote" then "NQuote"
  else if constructor = costBaseConstructorName "PDrop" then "PDrop"
  else if constructor = costWrappedConstructorName "PDrop" then "PDrop"
  else if constructor = costBaseConstructorName "PZero" then "PZero"
  else if constructor = costWrappedConstructorName "PZero" then "PZero"
  else constructor

/-- Pointwise lifting of constructor erasure over a pattern. -/
def proErase : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply (proEraseConstructor constructor) (arguments.map proErase)
  | .lambda binder body => .lambda binder (proErase body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders (proErase body)
  | .subst body replacement => .subst (proErase body) (proErase replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (elements.map proErase) rest

/-- The left endpoint: `Q_b(D_b(Q_w(0_w)))`. -/
def proLeft : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop")
      [.apply (costWrappedConstructorName "NQuote")
        [.apply (costWrappedConstructorName "PZero") []]]]

/-- The right endpoint: `Q_w(D_w(Q_b(0_b)))`. -/
def proRight : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop")
      [.apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "PZero") []]]]

/-- **The left endpoint collapses at its own colour** (base), onto the
wrapped-authored parallel unit's quote. -/
theorem proLeft_canonical_base :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft =
      .apply (costWrappedConstructorName "NQuote")
        [.apply (costWrappedConstructorName "PZero") []] := by decide

/-- **The right endpoint collapses at its own colour** (wrapped), onto the
base-authored quote-unit. -/
theorem proRight_canonical_wrapped :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight =
      .apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "PZero") []] := by decide

/-- Erasure removes the base quote tag. -/
theorem proErase_constructor_baseQuote :
    proEraseConstructor (costBaseConstructorName "NQuote") = "NQuote" := by
  decide

/-- Erasure removes the wrapped quote tag. -/
theorem proErase_constructor_wrappedQuote :
    proEraseConstructor (costWrappedConstructorName "NQuote") = "NQuote" := by
  decide

/-- Erasure removes the base zero tag. -/
theorem proErase_constructor_baseZero :
    proEraseConstructor (costBaseConstructorName "PZero") = "PZero" := by
  decide

/-- Erasure removes the wrapped zero tag. -/
theorem proErase_constructor_wrappedZero :
    proEraseConstructor (costWrappedConstructorName "PZero") = "PZero" := by
  decide


/-- **The erasure values coincide on the authored normal `Q(0)`.**  This is
the equality the external review's refutation witnesses: a relation premised
on erased, authored syntax WOULD hold for this pair ... -/
theorem proLeftRight_erase_agree :
    proErase (canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT
        .base rhoReflectivePresentation.toReflectivePresentationDecl)
        proLeft) =
      proErase (canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT
        .wrapped rhoReflectivePresentation.toReflectivePresentationDecl)
        proRight) := by
  rw [proLeft_canonical_base, proRight_canonical_wrapped]
  simp only [proErase, List.map_cons, List.map_nil,
    proErase_constructor_baseQuote, proErase_constructor_baseZero,
    proErase_constructor_wrappedQuote, proErase_constructor_wrappedZero]


/-- ... while at the base colour the canonicalizations differ. -/
theorem proPair_not_canonical_base :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight := by
  decide

/-- ... and likewise at the wrapped colour. -/
theorem proPair_not_canonical_wrapped :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight := by
  decide

/-- **The pair is outside the single-colour premise at every colour.**
Any theorem whose cross-colour arm is premised on single-colour canonical
equality never sees this witness at all — while an authored/erased-equality
premise admits it.  This is the regression fixture: the raw-equality cross
-colour formulation cannot quietly return. -/
theorem proPair_outside_singleColour_premise (color : CostStaticColor) :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight := by
  cases color
  · exact proPair_not_canonical_base
  · exact proPair_not_canonical_wrapped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
