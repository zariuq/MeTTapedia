import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed
import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Two quotation boundaries, and why they must not be conflated

A multi-presentation reflection profile carries **two distinct notions of
"this constructor is a quotation boundary"**, and they are not the same
predicate:

* **Restoration boundary** — `ReflectiveContextSupport.isQuoteConstructor`
  asks whether the constructor is the quote of *some* presentation in the
  profile.  Binder support resets there, whichever presentation owns the
  quote, because restoration reads the profile as a whole.
* **Canonicalization boundary** — `canonicalizeByDepths` resets its
  available depth exactly at `declaration.quoteConstructor`, the quote of
  *the one declaration it is canonicalizing under*.  A quote belonging to
  a different presentation is, to this declaration, an ordinary rigid
  application.

Both readings are correct for their own job.  The theorems below prove
they **diverge**, and locate the divergence precisely: at any quote owned
by a presentation other than the one being canonicalized under.

This is not a defect to be repaired by making one predicate match the
other.  It is a genuine two-relation structure — a term can sit inside a
quotation boundary for restoration purposes while sitting in plain rigid
context for canonicalization purposes.

**What this does and does not imply.**  It does *not* imply that a relation
carrying a single depth index is unsatisfiable at a foreign quote.  Such a
relation is unproblematic wherever its index is only the index of the
relation and does not appear in its endpoints — for example
`CommonRestorationApex` is inhabited at every depth by `refl`, and its
foreign-quote application case is proved outright by
`CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead`.

The divergence forces two indices exactly where one index would have to be
*both* the relation's index *and* the depth at which an endpoint is
canonicalized.  In `CommonRestorationApex` that happens only at the bare
`parallel` constructor.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- **The divergence.**  In a profile carrying two presentations with
distinct quote constructors, the quote of one presentation is a
restoration boundary for the profile while *not* being a canonicalization
boundary for the other presentation's declaration. -/
theorem quoteBoundary_diverges
    (profile : ReflectionProfile)
    (owner other : ReflectivePresentationDecl)
    (ownerMem : owner ∈ profile.presentations)
    (distinct : owner.quoteConstructor ≠ other.quoteConstructor) :
    ReflectiveContextSupport.isQuoteConstructor profile
        owner.quoteConstructor = true ∧
      (owner.quoteConstructor == other.quoteConstructor) = false := by
  constructor
  · unfold ReflectiveContextSupport.isQuoteConstructor
    exact List.any_eq_true.mpr ⟨owner, ownerMem, beq_self_eq_true _⟩
  · exact beq_eq_false_iff_ne.mpr distinct

/-- **The consequence for keyed canonicalization.**  At a foreign quote
the canonicalizer does not reset its available depth: the arguments are
keyed at the ambient depth, exactly as under any rigid constructor.  This
is the half of the divergence that the restoration side does not see. -/
theorem canonicalizeByDepths_foreignQuote_preserves_depth
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (foreignQuote : String)
    (foreign : foreignQuote ≠ declaration.quoteConstructor)
    (availableDepth scopeDepth : Nat) (arguments : List Pattern) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
        (.apply foreignQuote arguments) =
      finishNormalizeReflectiveApply declaration foreignQuote
        (canonicalizeListByDepths key declaration availableDepth scopeDepth
          arguments) := by
  simp only [canonicalizeByDepths, beq_eq_false_iff_ne.mpr foreign,
    Bool.false_eq_true, if_false]

/-- **The contrasting half.**  At the declaration's own quote the
canonicalizer resets the available depth to zero, so its arguments are
keyed relative to that boundary rather than to the ambient depth. -/
theorem canonicalizeByDepths_ownQuote_resets_depth
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (arguments : List Pattern) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
        (.apply declaration.quoteConstructor arguments) =
      finishNormalizeReflectiveApply declaration declaration.quoteConstructor
        (canonicalizeListByDepths key declaration 0 scopeDepth arguments) := by
  simp only [canonicalizeByDepths, beq_self_eq_true, if_true]


/-! ## Where one index cannot serve both disciplines

The two boundary notions each induce a depth discipline, and at a foreign
quote reached at non-zero ambient depth they give different numbers.

A single index is therefore untenable exactly where it is required to follow
both at once — that is, where it is simultaneously the index of a relation
*and* the depth at which that relation's endpoints are canonicalized.  In the
common-restoration apex this happens at the bare `parallel` constructor and
nowhere else; at every other constructor the index is the relation's alone and
one number suffices. -/

/-- **The two disciplines give different depths at a foreign quote.**  At a
foreign quote reached at non-zero ambient depth, resetting at *any*
presentation's quote and resetting at *this declaration's* quote yield
different numbers.

This is a statement about the two depth *computations*, not about the
inhabitation of any relation: a carrier whose single index is only the index
of the relation is unaffected.  The consequence bites only where one index
would have to be both the relation's index and the depth at which an endpoint
is canonicalized. -/
theorem restorationDepth_ne_keyDepth_at_foreignQuote
    (profile : ReflectionProfile)
    (owner declaration : ReflectivePresentationDecl)
    (ownerMem : owner ∈ profile.presentations)
    (foreign : owner.quoteConstructor ≠ declaration.quoteConstructor)
    (depth : Nat) (positive : depth ≠ 0) :
    (if ReflectiveContextSupport.isQuoteConstructor profile
        owner.quoteConstructor then 0 else depth) ≠
      (if owner.quoteConstructor == declaration.quoteConstructor
        then 0 else depth) := by
  have restoration :
      ReflectiveContextSupport.isQuoteConstructor profile
        owner.quoteConstructor = true := by
    unfold ReflectiveContextSupport.isQuoteConstructor
    exact List.any_eq_true.mpr ⟨owner, ownerMem, beq_self_eq_true _⟩
  have keying :
      (owner.quoteConstructor == declaration.quoteConstructor) = false :=
    beq_eq_false_iff_ne.mpr foreign
  rw [restoration, keying]
  simp only [if_true, if_false, Bool.false_eq_true]
  exact fun contra => positive contra.symm

/-- Restated as the design consequence: the two disciplines agree exactly
when the constructor's status is the same under both readings — which,
for a genuinely foreign quote, it is not. -/
theorem depthDisciplines_agree_iff_same_quote_status
    (profile : ReflectionProfile) (declaration : ReflectivePresentationDecl)
    (constructor : String) (depth : Nat) (positive : depth ≠ 0) :
    ((if ReflectiveContextSupport.isQuoteConstructor profile constructor
        then 0 else depth) =
      (if constructor == declaration.quoteConstructor then 0 else depth)) ↔
      (ReflectiveContextSupport.isQuoteConstructor profile constructor =
        (constructor == declaration.quoteConstructor)) := by
  cases restorationStatus :
      ReflectiveContextSupport.isQuoteConstructor profile constructor <;>
    cases keyingStatus : (constructor == declaration.quoteConstructor) <;>
      simp [positive, Ne.symm positive]

end Mettapedia.GSLT.LanguageDef
