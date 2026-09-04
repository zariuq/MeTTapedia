import Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTyping

/-!
# Coherence and symmetric translation for displayed typing

`DisplayedTyping` deliberately states only that types and typing evidence can
be transported along raw substitutions.  That weak boundary is useful for
partial and gradual profiles, but it does not by itself say that transport is
functorial: a malicious display could change its evidence even along the
identity substitution.

This module isolates the stronger, split case.  `StrictCoherence` requires
identity and composition for both type codes and proof-relevant evidence.
`Translation` requires a map between two displays to commute with the same
action.  The resulting reindexing laws are the comparison gate needed before
any particular HOL, dependent, or gradual display is selected.

The adjective `strict` is load-bearing.  A profile whose transports compose
only up to a specified isomorphism needs a separately named pseudo-coherence
interface; it must not be silently accepted by this one.  Conversely, strict
coherence does not imply proof irrelevance, faithful erasure, equivalence of
two profiles, or a choice of Prime's native type discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTypingCoherence

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTyping

universe uCtx uSub uRaw uTy uEvidence uTy' uEvidence'

variable {raw : Ucwf.{uCtx, uSub, uRaw}}

/-! ## Strictly functorial displays -/

/-- Identity and composition coherence for a typing display.  Heterogeneous
equality is used for evidence because its type records the transported raw
term and type code.  It does not erase proof relevance: it compares the two
canonical transport paths themselves. -/
structure StrictCoherence
    (display : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw) :
    Prop where
  tySub_id :
    ∀ {context : raw.Ctx} (type : display.Ty context),
      display.tySub type (raw.idS context) = type
  tySub_comp :
    ∀ {source middle target : raw.Ctx}
      (type : display.Ty target)
      (later : raw.Sub middle target)
      (earlier : raw.Sub source middle),
      display.tySub type (raw.compS later earlier) =
        display.tySub (display.tySub type later) earlier
  hasTypeSub_id :
    ∀ {context : raw.Ctx} {term : raw.Tm context}
      {type : display.Ty context}
      (evidence : display.HasType context term type),
      HEq (display.hasTypeSub evidence (raw.idS context)) evidence
  hasTypeSub_comp :
    ∀ {source middle target : raw.Ctx}
      {term : raw.Tm target} {type : display.Ty target}
      (evidence : display.HasType target term type)
      (later : raw.Sub middle target)
      (earlier : raw.Sub source middle),
      HEq
        (display.hasTypeSub evidence (raw.compS later earlier))
        (display.hasTypeSub
          (display.hasTypeSub evidence later) earlier)

namespace StrictCoherence

variable {display :
  DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw}

/-- With coherence supplied, displayed reindexing respects identity on the
whole proof-relevant total, not merely after raw erasure. -/
theorem reindex_id (coherence : StrictCoherence display)
    {context : raw.Ctx} (typed : display.TypedTerm context) :
    display.reindex (raw.idS context) typed = typed := by
  rcases typed with ⟨term, type, evidence⟩
  have termLaw := raw.tmSub_id term
  have typeLaw := coherence.tySub_id type
  have evidenceLaw := coherence.hasTypeSub_id evidence
  cases termLaw.symm
  cases typeLaw.symm
  have evidenceEquality :
      display.hasTypeSub evidence (raw.idS context) = evidence :=
    eq_of_heq evidenceLaw
  cases evidenceEquality
  rfl

/-- With coherence supplied, reindexing by a composite equals successive
reindexing, including the retained evidence. -/
theorem reindex_comp (coherence : StrictCoherence display)
    {source middle target : raw.Ctx}
    (typed : display.TypedTerm target)
    (later : raw.Sub middle target)
    (earlier : raw.Sub source middle) :
    display.reindex (raw.compS later earlier) typed =
      display.reindex earlier (display.reindex later typed) := by
  rcases typed with ⟨term, type, evidence⟩
  have termLaw := raw.tmSub_comp term later earlier
  have typeLaw := coherence.tySub_comp type later earlier
  have evidenceLaw := coherence.hasTypeSub_comp evidence later earlier
  cases termLaw.symm
  cases typeLaw.symm
  have evidenceEquality :
      display.hasTypeSub evidence (raw.compS later earlier) =
        display.hasTypeSub (display.hasTypeSub evidence later) earlier :=
    eq_of_heq evidenceLaw
  cases evidenceEquality
  rfl

end StrictCoherence

/-! ## Natural translations between two displays -/

/-- A translation of type codes and exact evidence over one unchanged raw
unityped substrate.  Both components must commute with substitution. -/
structure Translation
    (source : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    (target : DisplayedTyping.{uCtx, uSub, uRaw, uTy', uEvidence'} raw) where
  mapType : ∀ {context : raw.Ctx}, source.Ty context → target.Ty context
  mapType_sub :
    ∀ {sourceContext targetContext : raw.Ctx}
      (type : source.Ty targetContext)
      (substitution : raw.Sub sourceContext targetContext),
      mapType (source.tySub type substitution) =
        target.tySub (mapType type) substitution
  mapEvidence :
    ∀ {context : raw.Ctx} {term : raw.Tm context}
      {type : source.Ty context},
      source.HasType context term type →
        target.HasType context term (mapType type)
  mapEvidence_sub :
    ∀ {sourceContext targetContext : raw.Ctx}
      {term : raw.Tm targetContext} {type : source.Ty targetContext}
      (evidence : source.HasType targetContext term type)
      (substitution : raw.Sub sourceContext targetContext),
      HEq
        (mapEvidence (source.hasTypeSub evidence substitution))
        (target.hasTypeSub (mapEvidence evidence) substitution)

namespace Translation

variable
  {source : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw}
  {target : DisplayedTyping.{uCtx, uSub, uRaw, uTy', uEvidence'} raw}

/-- Every display has an identity translation. -/
def identity (display :
    DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw) :
    Translation display display where
  mapType := fun type => type
  mapType_sub := by intros; rfl
  mapEvidence := fun evidence => evidence
  mapEvidence_sub := by intros; rfl

/-- A natural translation maps a typed total without changing its raw term. -/
def mapTypedTerm (translation : Translation source target)
    {context : raw.Ctx} :
    source.TypedTerm context → target.TypedTerm context
  | ⟨term, type, evidence⟩ =>
      ⟨term, translation.mapType type,
        translation.mapEvidence evidence⟩

/-- Translation is over the identity raw map. -/
@[simp] theorem erase_mapTypedTerm (translation : Translation source target)
    {context : raw.Ctx} (typed : source.TypedTerm context) :
    target.erase (translation.mapTypedTerm typed) = source.erase typed := by
  rcases typed with ⟨term, type, evidence⟩
  rfl

/-- Translation commutes with displayed reindexing, including evidence. -/
theorem mapTypedTerm_reindex (translation : Translation source target)
    {sourceContext targetContext : raw.Ctx}
    (substitution : raw.Sub sourceContext targetContext)
    (typed : source.TypedTerm targetContext) :
    translation.mapTypedTerm (source.reindex substitution typed) =
      target.reindex substitution (translation.mapTypedTerm typed) := by
  rcases typed with ⟨term, type, evidence⟩
  have typeLaw := translation.mapType_sub type substitution
  have evidenceLaw := translation.mapEvidence_sub evidence substitution
  cases typeLaw.symm
  have evidenceEquality :
      translation.mapEvidence
          (source.hasTypeSub evidence substitution) =
        target.hasTypeSub (translation.mapEvidence evidence) substitution :=
    eq_of_heq evidenceLaw
  cases evidenceEquality
  rfl

end Translation

/-- A symmetric comparison harness asks both candidates to satisfy the same
coherence gate and supplies translations in both directions.  It deliberately
does not assert that the translations are inverse; conservativity or
equivalence must be established separately on a stated fragment. -/
structure BidirectionalHarness
    (left : DisplayedTyping.{uCtx, uSub, uRaw, uTy, uEvidence} raw)
    (right : DisplayedTyping.{uCtx, uSub, uRaw, uTy', uEvidence'} raw) where
  leftCoherence : StrictCoherence left
  rightCoherence : StrictCoherence right
  forward : Translation left right
  backward : Translation right left

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTyping.Canary

/-- The truth display's evidence transport is strictly coherent. -/
def truthStrictCoherence : StrictCoherence truthDisplay where
  tySub_id := by intros; rfl
  tySub_comp := by intros; rfl
  hasTypeSub_id := by intros; rfl
  hasTypeSub_comp := by intros; rfl

/-- The ambiguous display is coherent too: coherence does not collapse
distinct type codes or make erasure faithful. -/
def ambiguousStrictCoherence : StrictCoherence ambiguousDisplay where
  tySub_id := by intros; rfl
  tySub_comp := by intros; rfl
  hasTypeSub_id := by intros; rfl
  hasTypeSub_comp := by intros; rfl

/-- Strict coherence is compatible with genuinely non-injective erasure. -/
theorem coherence_does_not_imply_faithful_erasure :
    Nonempty (StrictCoherence ambiguousDisplay) ∧
      ¬ Function.Injective
        (@eraseExact (ambiguousDisplay.fibre Unit)) :=
  ⟨⟨ambiguousStrictCoherence⟩,
    ambiguousDisplay_erasure_not_injective⟩

/-- A deliberately unlawful display flips its evidence on every transport,
including identity.  It satisfies the original transport signature but not
the coherence certificate. -/
def togglingDisplay :
    DisplayedTyping (unitypedFamilies Bool) where
  Ty := fun _ => Unit
  tySub := fun _ _ => Unit.unit
  HasType := fun _ _ _ => Bool
  hasTypeSub := fun evidence _ => !evidence

/-- Negative control: the weak `DisplayedTyping` fields alone do not force
the identity law. -/
theorem togglingDisplay_has_no_strictCoherence :
    ¬ Nonempty (StrictCoherence togglingDisplay) := by
  rintro ⟨coherence⟩
  have impossible := coherence.hasTypeSub_id
    (context := Unit) (term := fun _ : Unit => false)
    (type := Unit.unit) false
  change HEq true false at impossible
  exact Bool.false_ne_true (eq_of_heq impossible).symm

/-- The positive display inhabits the symmetric gate without privileging a
direction.  This is only a harness canary, not a claim that two different
foundational profiles are equivalent. -/
def truthSelfHarness : BidirectionalHarness truthDisplay truthDisplay where
  leftCoherence := truthStrictCoherence
  rightCoherence := truthStrictCoherence
  forward := Translation.identity truthDisplay
  backward := Translation.identity truthDisplay

end Canary

#print axioms StrictCoherence.reindex_id
#print axioms StrictCoherence.reindex_comp
#print axioms Translation.erase_mapTypedTerm
#print axioms Translation.mapTypedTerm_reindex
#print axioms Canary.coherence_does_not_imply_faithful_erasure
#print axioms Canary.togglingDisplay_has_no_strictCoherence

end Mettapedia.Languages.MeTTa.Prime.UnitypedDisplayedTypingCoherence
