import Mettapedia.GSLT.LanguageDef.GSLTILContextualProfileComparison
import Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability

/-!
# Displayed typing over a unityped contextual substrate

A unityped contextual structure is useful for Prime only if it remains the
raw substitution layer rather than becoming a universal dynamic type inside
the object language. Rich typing is therefore displayed over raw terms.

For each context, a displayed typing supplies type codes, evidence that a raw
term has a code, and transport of both along raw substitution. Its total typed
terms project to raw terms. The projection commutes exactly with substitution,
but is intentionally neither assumed injective nor assumed surjective:

* several type/evidence fibres may lie over one raw term;
* a raw term may have no exact typing evidence and still remain available to
  the ordinary gradual execution path.

This is the structural erasure boundary. It does not add an internal
`Type : Type`, a cast operation, a checker, or a second evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTyping

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State

universe uCtx uSub uRaw uTy uEvidence uRaw' uExact'

/-! ## Exact totals and their raw projection -/

/-- The Grothendieck total of one exact-evidence family. -/
abbrev ExactTotal (fibre : Fibre.{uRaw, uEvidence}) :=
  Sigma fibre.Exact

/-- Forget exact evidence while retaining the unchanged raw point. -/
def eraseExact {fibre : Fibre.{uRaw, uEvidence}} :
    ExactTotal fibre → fibre.Raw :=
  Sigma.fst

/-- Erasure is injective exactly when every evidence fibre is a subsingleton.
Thus injectivity is an earned proof-irrelevance property, not part of gradual
typing itself. -/
theorem eraseExact_injective_iff_subsingleton_fibres
    (fibre : Fibre.{uRaw, uEvidence}) :
    Function.Injective (@eraseExact fibre) ↔
      ∀ raw, Subsingleton (fibre.Exact raw) := by
  constructor
  · intro injective raw
    constructor
    intro first second
    have totalEquality :
        (⟨raw, first⟩ : ExactTotal fibre) = ⟨raw, second⟩ :=
      injective rfl
    cases totalEquality
    rfl
  · intro fibresSubsingleton
    rintro ⟨firstRaw, firstEvidence⟩ ⟨secondRaw, secondEvidence⟩ rawEquality
    change firstRaw = secondRaw at rawEquality
    subst secondRaw
    have evidenceEquality :=
      (fibresSubsingleton firstRaw).allEq firstEvidence secondEvidence
    cases evidenceEquality
    rfl

/-- Erasure is surjective exactly when every raw point has some exact
evidence. Prime does not impose this condition: untyped fallback is the
expected negative case. -/
theorem eraseExact_surjective_iff_inhabited_fibres
    (fibre : Fibre.{uRaw, uEvidence}) :
    Function.Surjective (@eraseExact fibre) ↔
      ∀ raw, Nonempty (fibre.Exact raw) := by
  constructor
  · intro surjective raw
    rcases surjective raw with ⟨⟨sourceRaw, evidence⟩, rawEquality⟩
    change sourceRaw = raw at rawEquality
    subst sourceRaw
    exact ⟨evidence⟩
  · intro inhabited raw
    rcases inhabited raw with ⟨evidence⟩
    exact ⟨⟨raw, evidence⟩, rfl⟩

/-- Exact maps act on total typed values. -/
def mapExactTotal
    {source : Fibre.{uRaw, uEvidence}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    ExactTotal source → ExactTotal target
  | ⟨raw, evidence⟩ => ⟨map.mapRaw raw, map.mapExact evidence⟩

/-- Mapping exact evidence and then erasing is exactly the raw map. -/
@[simp]
theorem eraseExact_mapExactTotal
    {source : Fibre.{uRaw, uEvidence}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (typed : ExactTotal source) :
    eraseExact (mapExactTotal map typed) = map.mapRaw (eraseExact typed) := by
  rcases typed with ⟨raw, evidence⟩
  rfl

/-! ## A typing display over a raw unityped CwF -/

/-- Type codes and exact typing evidence displayed over the terms of a raw
unityped contextual structure. Only the substitution-stable boundary is
asserted here; formation, conversion, and computation remain properties of a
particular hosted type theory. -/
structure DisplayedTyping
    (raw : Ucwf.{uCtx, uSub, uRaw}) :
    Type (max (uCtx + 1) (uSub + 1) (uRaw + 1) (uTy + 1)
      (uEvidence + 1)) where
  Ty : raw.Ctx → Type uTy
  tySub : {source target : raw.Ctx} →
    Ty target → raw.Sub source target → Ty source
  HasType : (context : raw.Ctx) →
    raw.Tm context → Ty context → Type uEvidence
  hasTypeSub : {source target : raw.Ctx} →
    {term : raw.Tm target} → {type : Ty target} →
    HasType target term type → (substitution : raw.Sub source target) →
      HasType source (raw.tmSub term substitution)
        (tySub type substitution)

namespace DisplayedTyping

variable {raw : Ucwf.{uCtx, uSub, uRaw}}

/-- At one context, exact evidence consists of a type code and a derivation
that the retained raw term has that code. -/
def fibre (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    (context : raw.Ctx) : Fibre.{uRaw, max uTy uEvidence} where
  Raw := raw.Tm context
  Exact := fun term => Sigma fun type => display.HasType context term type

/-- Raw substitution together with evidence transport is an exact map between
the corresponding displayed fibres. -/
def substitutionMap
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    {source target : raw.Ctx} (substitution : raw.Sub source target) :
    ExactMap (display.fibre target) (display.fibre source) where
  mapRaw := fun term => raw.tmSub term substitution
  mapExact := fun evidence =>
    ⟨display.tySub evidence.1 substitution,
      display.hasTypeSub evidence.2 substitution⟩

/-- A typed term is the total object of the display over one context. -/
abbrev TypedTerm
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    (context : raw.Ctx) :=
  ExactTotal (display.fibre context)

/-- Forget the type code and its evidence. -/
def erase
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    {context : raw.Ctx} :
    display.TypedTerm context → raw.Tm context :=
  eraseExact

/-- Reindex a typed term by transporting its raw term, type code, and exact
evidence together. -/
def reindex
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    {source target : raw.Ctx} (substitution : raw.Sub source target) :
    display.TypedTerm target → display.TypedTerm source :=
  mapExactTotal (display.substitutionMap substitution)

/-- Typed substitution erases to the original unityped substitution on the
nose. -/
@[simp]
theorem erase_reindex
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    {source target : raw.Ctx} (substitution : raw.Sub source target)
    (typed : display.TypedTerm target) :
    display.erase (display.reindex substitution typed) =
      raw.tmSub (display.erase typed) substitution :=
  eraseExact_mapExactTotal (display.substitutionMap substitution) typed

/-- Every raw term has a canonical suspended gradual state even when its exact
typing fibre is empty. -/
def suspended
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    {context : raw.Ctx} (term : raw.Tm context) :
    State (display.fibre context) term :=
  .suspended

end DisplayedTyping

/-! ## Positive and negative controls -/

namespace Canary

/-- A substitution-stable typing discipline on Boolean-valued unityped terms:
the sole type is inhabited exactly by functions that return `true`
everywhere. -/
def truthDisplay :
    DisplayedTyping (unitypedFamilies Bool) where
  Ty := fun _ => Unit
  tySub := fun _ _ => Unit.unit
  HasType := fun context term _ =>
    PLift (∀ point : context, term point = true)
  hasTypeSub := fun evidence substitution =>
    ⟨fun point => evidence.down (substitution point)⟩

/-- The constantly true raw term carries exact evidence. -/
def typedTrue : truthDisplay.TypedTerm Unit :=
  ⟨fun _ => true, Unit.unit, ⟨fun _ => rfl⟩⟩

@[simp]
theorem typedTrue_erases :
    truthDisplay.erase typedTrue = (fun _ : Unit => true) :=
  rfl

/-- The constantly false term remains a raw term but has no exact evidence in
the truth display. -/
theorem false_has_no_exact_typing :
    ¬ Nonempty ((truthDisplay.fibre Unit).Exact
      (fun _ : Unit => false)) := by
  rintro ⟨⟨type, evidence⟩⟩
  have impossible := evidence.down Unit.unit
  exact Bool.false_ne_true impossible

/-- Hence exact erasure is not surjective even though the false term remains
available as a suspended raw point. -/
theorem truthDisplay_erasure_not_surjective :
    ¬ Function.Surjective
      (@eraseExact (truthDisplay.fibre Unit)) := by
  intro surjective
  have allInhabited :=
    (eraseExact_surjective_iff_inhabited_fibres
      (truthDisplay.fibre Unit)).mp surjective
  exact false_has_no_exact_typing
    (allInhabited (fun _ : Unit => false))

/-- A deliberately ambiguous display: every raw term has two distinct type
codes. This witnesses why erasure must not be assumed faithful. -/
def ambiguousDisplay :
    DisplayedTyping (unitypedFamilies Bool) where
  Ty := fun _ => Bool
  tySub := fun type _ => type
  HasType := fun _ _ _ => Unit
  hasTypeSub := fun _ _ => Unit.unit

def typedAsFalse : ambiguousDisplay.TypedTerm Unit :=
  ⟨fun _ => true, false, Unit.unit⟩

def typedAsTrue : ambiguousDisplay.TypedTerm Unit :=
  ⟨fun _ => true, true, Unit.unit⟩

theorem ambiguous_typed_terms_differ : typedAsFalse ≠ typedAsTrue := by
  intro equality
  have typeEquality := congrArg (fun typed => typed.2.1) equality
  exact Bool.false_ne_true typeEquality

theorem ambiguous_typed_terms_erase_equal :
    ambiguousDisplay.erase typedAsFalse =
      ambiguousDisplay.erase typedAsTrue :=
  rfl

/-- Erasure is genuinely non-injective when the hosted type theory admits
more than one exact typing over a raw term. -/
theorem ambiguousDisplay_erasure_not_injective :
    ¬ Function.Injective
      (@eraseExact (ambiguousDisplay.fibre Unit)) := by
  intro injective
  exact ambiguous_typed_terms_differ
    (injective ambiguous_typed_terms_erase_equal)

/-- The untypable raw point still inhabits the gradual substrate in suspended
form; no fabricated type or error term is needed. -/
def suspendedFalse :
    State (truthDisplay.fibre Unit) (fun _ : Unit => false) :=
  truthDisplay.suspended (fun _ => false)

end Canary

#print axioms eraseExact_injective_iff_subsingleton_fibres
#print axioms eraseExact_surjective_iff_inhabited_fibres
#print axioms eraseExact_mapExactTotal
#print axioms DisplayedTyping.substitutionMap
#print axioms DisplayedTyping.erase_reindex
#print axioms Canary.false_has_no_exact_typing
#print axioms Canary.truthDisplay_erasure_not_surjective
#print axioms Canary.ambiguousDisplay_erasure_not_injective

end Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTyping
