import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.GSLT.LanguageDef.QuoteBoundaryDivergence

/-!
# The apex with its two depths separated

Two quotation disciplines coexist in a multi-presentation profile:

* **restoration support** resets at **any** presentation's quote — this is
  the discipline bridged to operational substitution depth by
  `restorationDepthThroughContext_eq_substituteContextAt_snd`;
* **canonicalization keying** resets only at **this declaration's** quote,
  because `canonicalizeByAt` tests `declaration.quoteConstructor`.

They differ at a *foreign* quote — one colour's quote seen from the other's
declaration.

**Where this actually forces a second index.**  In `CommonRestorationApex`
the single index is, at most constructors, only the index of the *relation*;
the endpoints do not mention it, so the two disciplines never meet there.  In
particular the one-index carrier is perfectly satisfiable at a foreign quote:
`CommonRestorationApex.refl` inhabits it at every depth, and
`CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead`
(`CostRestorationRelationQuoteArm`) closes the foreign-quote *application*
case outright, with three independently chosen depths and no side condition.

The one place the index escapes into the endpoints is `parallel`, where it is
passed to `canonicalizeListByAt` and so *is* the keying depth.  There, and
only there, a single index cannot also be the restoration depth.

`TwoDepthApex` separates them.  It is indexed by a restoration depth *and* a
key depth, each advancing by its own rule.  It replaces nothing: the one-index
carrier remains correct and is the right tool everywhere except bare parallel.

**Scope warning for `toTwoDepth`.**  The embedding below exhibits the
one-index apex as this one's diagonal under `QuoteStatusAgrees`.  That
hypothesis is *false* over every Cost-generated language
(`not_quoteStatusAgrees_costStatic`), so the embedding is vacuous there and
must not be used to migrate evidence.  It is stated for single-colour
profiles, where it is meaningful.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace CostStaticAtomKeyCospan

mutual

/-- Recursive equality evidence at a common semantic restoration apex,
with the restoration depth and the canonicalization key depth carried
separately.  Ordinary binders advance both; a quote of *any* presentation
resets the restoration depth; a quote of *this declaration* resets the key
depth. -/
inductive TwoDepthApex
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Nat → Pattern → Pattern → Prop where
  /-- Leaves that already restore together at every depth. -/
  | leafAligned {restorationDepth keyDepth : Nat} {left right : Pattern}
      (aligned : PatternLeafAligned
        (ReflectiveContextSupport.RestoresTogether
          source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment) left right) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        left right
  /-- Rigid application congruence.  **The two depths reset on different
  predicates**, which is the entire content of this carrier. -/
  | apply {restorationDepth keyDepth : Nat} (constructor : String)
      {leftArguments rightArguments : List Pattern}
      (arguments : TwoDepthApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor
          then 0 else restorationDepth)
        (if constructor == declaration.quoteConstructor
          then 0 else keyDepth)
        leftArguments rightArguments) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        (.apply constructor leftArguments) (.apply constructor rightArguments)
  | lambda {restorationDepth keyDepth : Nat} (binder : Option String)
      {leftBody rightBody : Pattern}
      (body : TwoDepthApex source cospan declaration (restorationDepth + 1)
        (keyDepth + 1) leftBody rightBody) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        (.lambda binder leftBody) (.lambda binder rightBody)
  | multiLambda {restorationDepth keyDepth arity : Nat}
      (binders : List String) {leftBody rightBody : Pattern}
      (body : TwoDepthApex source cospan declaration
        (restorationDepth + arity) (keyDepth + arity) leftBody rightBody) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        (.multiLambda arity binders leftBody)
        (.multiLambda arity binders rightBody)
  | subst {restorationDepth keyDepth : Nat}
      {leftBody rightBody leftReplacement rightReplacement : Pattern}
      (body : TwoDepthApex source cospan declaration (restorationDepth + 1)
        (keyDepth + 1) leftBody rightBody)
      (replacement : TwoDepthApex source cospan declaration restorationDepth
        keyDepth leftReplacement rightReplacement) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        (.subst leftBody leftReplacement) (.subst rightBody rightReplacement)
  | collection {restorationDepth keyDepth : Nat} (collectionType : CollType)
      (rest : Option String) {leftElements rightElements : List Pattern}
      (elements : TwoDepthApexList source cospan declaration restorationDepth
        keyDepth leftElements rightElements) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        (.collection collectionType leftElements rest)
        (.collection collectionType rightElements rest)

  /-- **Bare parallel.**  Canonicalization keys with `keyDepth` — the
  declaration-relative depth — while the recursive evidence continues to
  carry both indices.  This is the constructor the separation exists for:
  under one index the keying depth and the restoration depth were forced
  to coincide, which fails at any foreign quote. -/
  | parallel {restorationDepth keyDepth : Nat}
      {leftElements rightElements middle : List Pattern}
      (aligned : TwoDepthApexList source cospan declaration restorationDepth
        keyDepth
        (parallelContents declaration
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt source) declaration keyDepth
            leftElements))
        middle)
      (permutation : List.Perm middle
        (parallelContents declaration
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt source) declaration keyDepth
            rightElements))) :
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth
          (.collection declaration.parallelCollection leftElements none))
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth
          (.collection declaration.parallelCollection rightElements none))

/-- Pointwise companion. -/
inductive TwoDepthApexList
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Nat → List Pattern → List Pattern → Prop where
  | nil (restorationDepth keyDepth : Nat) :
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        [] []
  | cons {restorationDepth keyDepth : Nat} {leftHead rightHead : Pattern}
      {leftTail rightTail : List Pattern}
      (head : TwoDepthApex source cospan declaration restorationDepth
        keyDepth leftHead rightHead)
      (tail : TwoDepthApexList source cospan declaration restorationDepth
        keyDepth leftTail rightTail) :
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        (leftHead :: leftTail) (rightHead :: rightTail)

end

/-! ## The two depths agree exactly where the old index was sound -/

/-- The agreement condition: every application head has the same
quote status under both readings.  This is precisely the side condition
the one-index theory carries, and it fails at foreign quotes. -/
def QuoteStatusAgrees (source : CIGSLT)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ constructor : String,
    ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile constructor =
    (constructor == declaration.quoteConstructor)

/-- Under agreement the two indices advance identically at applications,
so the diagonal is preserved: this is the sense in which `TwoDepthApex`
generalizes the one-index carrier rather than competing with it. -/
theorem apply_depths_coincide_of_agrees {source : CIGSLT}
    {declaration : ReflectivePresentationDecl}
    (agrees : QuoteStatusAgrees source declaration)
    (constructor : String) (depth : Nat) :
    (if ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile constructor then 0 else depth) =
      (if constructor == declaration.quoteConstructor then 0 else depth) := by
  rw [agrees constructor]

/-- **Agreement fails exactly at foreign quotes.**  If the profile owns a
quote other than this declaration's, the two readings disagree, so no
single-index apex is available there — which is why the separated carrier
is necessary rather than merely convenient. -/
theorem not_quoteStatusAgrees_of_foreignQuote {source : CIGSLT}
    {declaration owner : ReflectivePresentationDecl}
    (ownerMem : owner ∈ source.costWholeReflectionProfile.presentations)
    (foreign : owner.quoteConstructor ≠ declaration.quoteConstructor) :
    ¬ QuoteStatusAgrees source declaration := by
  intro agrees
  have restoration :
      ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile owner.quoteConstructor = true := by
    unfold ReflectiveContextSupport.isQuoteConstructor
    exact List.any_eq_true.mpr ⟨owner, ownerMem, beq_self_eq_true _⟩
  have keying :
      (owner.quoteConstructor == declaration.quoteConstructor) = false :=
    beq_eq_false_iff_ne.mpr foreign
  have status := agrees owner.quoteConstructor
  rw [restoration, keying] at status
  exact Bool.noConfusion status


/-! ## The one-index apex embeds as the diagonal -/

mutual

/-- **The generalization theorem.**  Where the two quote readings agree,
every `CommonRestorationApex` is a `TwoDepthApex` with both indices equal, so
the separated carrier loses nothing.

**Vacuous over Cost.**  `QuoteStatusAgrees` is refuted for every
Cost-generated language (`not_quoteStatusAgrees_costStatic`), so this
embedding has no instances there and cannot be used to migrate evidence.  It
is meaningful for single-colour profiles. -/
theorem CommonRestorationApex.toTwoDepth {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    (agrees : QuoteStatusAgrees source declaration) :
    ∀ {depth : Nat} {left right : Pattern},
      CommonRestorationApex source cospan declaration depth left right →
      TwoDepthApex source cospan declaration depth depth left right
  | _, _, _, .leafAligned aligned => .leafAligned aligned
  | _, _, _, .apply constructor arguments => by
      refine .apply constructor ?_
      have coincide := apply_depths_coincide_of_agrees agrees constructor
      rw [← coincide]
      exact CommonRestorationApexList.toTwoDepth agrees arguments
  | _, _, _, .lambda binder body =>
      .lambda binder (CommonRestorationApex.toTwoDepth agrees body)
  | _, _, _, .multiLambda binders body =>
      .multiLambda binders (CommonRestorationApex.toTwoDepth agrees body)
  | _, _, _, .subst body replacement =>
      .subst (CommonRestorationApex.toTwoDepth agrees body)
        (CommonRestorationApex.toTwoDepth agrees replacement)
  | _, _, _, .collection collectionType rest elements =>
      .collection collectionType rest
        (CommonRestorationApexList.toTwoDepth agrees elements)
  | _, _, _, .parallel aligned permutation =>
      .parallel (CommonRestorationApexList.toTwoDepth agrees aligned)
        permutation

/-- Listwise companion of the generalization theorem. -/
theorem CommonRestorationApexList.toTwoDepth {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    (agrees : QuoteStatusAgrees source declaration) :
    ∀ {depth : Nat} {left right : List Pattern},
      CommonRestorationApexList source cospan declaration depth left right →
      TwoDepthApexList source cospan declaration depth depth left right
  | _, _, _, .nil _ => .nil _ _
  | _, _, _, .cons head tail =>
      .cons (CommonRestorationApex.toTwoDepth agrees head)
        (CommonRestorationApexList.toTwoDepth agrees tail)

end


/-! ## The carrier handles the configuration that broke its predecessor -/

/-- **The foreign-quote descent, now expressible.**  At a quote owned by
another presentation, the restoration index resets to zero while the key
index is preserved — the divergent configuration in which no one-index
apex exists (`restorationDepth_ne_keyDepth_at_foreignQuote`).  The
separated carrier states it directly. -/
theorem twoDepthApex_foreignQuote_descends {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {constructor : String}
    (foreign : constructor ≠ declaration.quoteConstructor)
    (isQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile constructor = true)
    {restorationDepth keyDepth : Nat}
    {leftArguments rightArguments : List Pattern}
    (arguments : TwoDepthApexList source cospan declaration 0 keyDepth
      leftArguments rightArguments) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      (.apply constructor leftArguments)
      (.apply constructor rightArguments) := by
  refine .apply constructor ?_
  rw [isQuote, beq_eq_false_iff_ne.mpr foreign]
  simpa using arguments

/-- **The declaration's own quote**, for contrast: both indices reset, so
the two carriers agree here.  Together with the previous theorem this
exhibits the exact boundary — same behaviour at the selected quote,
divergent behaviour at a foreign one. -/
theorem twoDepthApex_ownQuote_descends {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    (isQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile declaration.quoteConstructor = true)
    {restorationDepth keyDepth : Nat}
    {leftArguments rightArguments : List Pattern}
    (arguments : TwoDepthApexList source cospan declaration 0 0
      leftArguments rightArguments) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      (.apply declaration.quoteConstructor leftArguments)
      (.apply declaration.quoteConstructor rightArguments) := by
  refine .apply declaration.quoteConstructor ?_
  rw [isQuote, beq_self_eq_true]
  simpa using arguments



/-! ## A *global* strengthening of the apex lemma's side condition

`CommonRestorationApex.of_canonicalRootAligned` carries a hypothesis of the
shape

```lean
constructor ≠ declaration.quoteConstructor →
  ReflectiveContextSupport.isQuoteConstructor
    source.costWholeReflectionProfile constructor = false
```

**but quantified only over heads matching its two endpoints** — it is an
*endpoint-indexed* condition, discharged locally by whatever the endpoints
actually are.

`OrdinaryHeadCondition` below is the corresponding condition quantified over
**all strings**.  The two are not the same: the global one can fail while the
endpoint-indexed one holds — vacuously at any non-application pair, and
locally at an application whose own head is not a profile quote.

So the theorems in this section say something narrower than they may appear
to.  They characterize when the *global* condition holds, and they show it
fails wherever a foreign quote exists.  They do **not** show that consumers of
`of_canonicalRootAligned` carried an undischargeable obligation; those
consumers only ever needed the endpoint-indexed version, and the
foreign-quote application case has its own proved arm
(`of_canonicalRootAligned_languageQuoteHead`). -/

/-- The apex lemma's side condition, strengthened to quantify over **all**
constructors rather than only the heads of its endpoints. -/
def OrdinaryHeadCondition (source : CIGSLT)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ constructor : String, constructor ≠ declaration.quoteConstructor →
    ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile constructor = false

/-- Agreement implies the side condition. -/
theorem ordinaryHeadCondition_of_agrees {source : CIGSLT}
    {declaration : ReflectivePresentationDecl}
    (agrees : QuoteStatusAgrees source declaration) :
    OrdinaryHeadCondition source declaration := by
  intro constructor foreign
  rw [agrees constructor]
  exact beq_eq_false_iff_ne.mpr foreign

/-- Conversely, the side condition plus the (always available) fact that a
declaration's own quote is a quote of the profile gives full agreement.
So the two are the same assumption. -/
theorem agrees_of_ordinaryHeadCondition {source : CIGSLT}
    {declaration : ReflectivePresentationDecl}
    (ordinaryHead : OrdinaryHeadCondition source declaration)
    (ownQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile declaration.quoteConstructor = true) :
    QuoteStatusAgrees source declaration := by
  intro constructor
  by_cases isOwn : constructor = declaration.quoteConstructor
  · subst isOwn
    rw [ownQuote, beq_self_eq_true]
  · rw [ordinaryHead constructor isOwn, beq_eq_false_iff_ne.mpr isOwn]

/-- Where a foreign quote exists, the **globally quantified** condition is
unsatisfiable.

This says nothing about consumers of `of_canonicalRootAligned`, which need
only the endpoint-indexed condition and can discharge it locally. -/
theorem not_ordinaryHeadCondition_of_foreignQuote {source : CIGSLT}
    {declaration owner : ReflectivePresentationDecl}
    (ownerMem : owner ∈ source.costWholeReflectionProfile.presentations)
    (foreign : owner.quoteConstructor ≠ declaration.quoteConstructor) :
    ¬ OrdinaryHeadCondition source declaration := by
  intro ordinaryHead
  have restoration :
      ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile owner.quoteConstructor = true := by
    unfold ReflectiveContextSupport.isQuoteConstructor
    exact List.any_eq_true.mpr ⟨owner, ownerMem, beq_self_eq_true _⟩
  have refuted := ordinaryHead owner.quoteConstructor foreign
  rw [restoration] at refuted
  exact Bool.noConfusion refuted


/-! ## Basic constructors mirroring the one-index carrier -/

namespace TwoDepthApex

/-- Reflexive apex evidence at any pair of depths. -/
theorem refl {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat) (pattern : Pattern) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      pattern pattern :=
  .leafAligned (PatternLeafAligned.refl
    (fun name => ReflectiveContextSupport.RestoresTogether.refl
      source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment
      (.fvar name)) pattern)

/-- Exact equality embeds without inventing a semantic leaf. -/
theorem of_eq {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat)
    {left right : Pattern} (equal : left = right) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      left right := by
  subst equal
  exact refl cospan declaration restorationDepth keyDepth left

/-- **Leaf alignment is depth-independent, hence free for the separated
carrier.**

A pair related by `PatternLeafAligned` over the restoration relation inhabits
`TwoDepthApex` at *every* pair of depths simultaneously — neither index
appears in the premise.

This is the structural reason the certified-boundary shapes of the foreign
residual require no two-depth mathematics: their terminals already conclude in
`PatternLeafAligned`, so they lift at whatever `(restorationDepth, keyDepth)`
a consumer demands.  The genuine two-depth difficulty is confined to the
shapes where a depth actually occurs in the constructor — that is, to bare
parallel, whose canonicalization is keyed at `keyDepth`. -/
theorem forall_depths_of_leafAligned {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (aligned : PatternLeafAligned
      (ReflectiveContextSupport.RestoresTogether
        source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment) left right) :
    ∀ restorationDepth keyDepth : Nat,
      TwoDepthApex source cospan declaration restorationDepth keyDepth
        left right :=
  fun _ _ => .leafAligned aligned

/-- Transport an apex across syntactic equalities of its endpoints.
Needed by every leaf terminal, and identical in shape to the one-index
`CommonRestorationApex.reindex`. -/
theorem reindex {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {restorationDepth keyDepth : Nat} {left right left' right' : Pattern}
    (leftEq : left = left') (rightEq : right = right')
    (apex : TwoDepthApex source cospan declaration restorationDepth keyDepth
      left right) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      left' right' := by
  cases leftEq
  cases rightEq
  exact apex

/-- Pointwise reflexivity, needed by every context frame. -/
theorem reflList {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat) :
    ∀ patterns : List Pattern,
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        patterns patterns
  | [] => .nil _ _
  | pattern :: patterns =>
      .cons (refl cospan declaration restorationDepth keyDepth pattern)
        (reflList cospan declaration restorationDepth keyDepth patterns)

/-- Concatenate two pointwise apex lists without changing occurrence order. -/
theorem appendList {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    {restorationDepth keyDepth : Nat} :
    ∀ {leftFirst rightFirst leftSecond rightSecond : List Pattern},
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        leftFirst rightFirst →
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        leftSecond rightSecond →
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        (leftFirst ++ leftSecond) (rightFirst ++ rightSecond)
  | _, _, _, _, .nil _ _, second => second
  | _, _, _, _, .cons head tail, second =>
      .cons head (appendList cospan declaration tail second)

/-! ### Positive parallel constructors at *independent* depths

The bare-parallel constructor is the only one whose endpoints mention a depth:
canonicalization is keyed at `keyDepth`.  Everything else in the carrier is
either depth-free (`leafAligned`) or advances both indices in lockstep.  So the
question that decides whether the separation is usable is precisely whether
parallel evidence exists when the two indices **differ** — the configuration a
foreign quote produces.

The two canaries below answer yes.  They are the one-index parallel canaries
restated with `restorationDepth` and `keyDepth` universally and independently
quantified; no relation between them is assumed or used. -/

/-- **Positive: swapped parallel leaves, at independent depths.**  Two rigid
bound leaves in opposite parallel orders meet at a separated apex for *every*
pair `(restorationDepth, keyDepth)`.  The apex records the swap as a
permutation rather than pretending it is positional alignment. -/
theorem parallel_swap_bvars (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth first second : Nat) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth
        (.collection declaration.parallelCollection
          [.bvar first, .bvar second] none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth
        (.collection declaration.parallelCollection
          [.bvar second, .bvar first] none)) := by
  apply TwoDepthApex.parallel
  · exact reflList cospan declaration restorationDepth keyDepth _
  · simpa [canonicalizeListByAt, canonicalizeByAt, parallelContents,
      parallelSplice] using
      (List.Perm.swap (Pattern.bvar second) (Pattern.bvar first) [])

end TwoDepthApex

/-! ## The keying depth through a one-hole context

`restorationDepthThroughContext` computes the depth visible at a hole under
the *restoration* discipline: it resets at any presentation's quote, and is
bridged to operational substitution by
`restorationDepthThroughContext_eq_substituteContextAt_snd`.

Keyed canonicalization uses a different rule.  `canonicalizeByAt` resets its
available depth at `declaration.quoteConstructor` and at nothing else, so the
depth a *key* sees at the hole is computed by the function below.  The two
agree frame-by-frame except at applications, which is exactly where the
single-index carrier was over-determined. -/

/-- Binder depth visible at the hole of a one-hole context under the
**keying** discipline, mirroring `canonicalizeByAt`'s own recursion:
binders extend the depth, ordinary applications and collections preserve
it, and only *this declaration's* quote resets it. -/
def keyDepthThroughContext (declaration : ReflectivePresentationDecl) :
    Nat → OneHoleContext → Nat
  | depth, .hole => depth
  | depth, .apply constructor _ inner _ =>
      keyDepthThroughContext declaration
        (if constructor == declaration.quoteConstructor then 0 else depth)
        inner
  | depth, .lambda _ inner =>
      keyDepthThroughContext declaration (depth + 1) inner
  | depth, .multiLambda arity _ inner =>
      keyDepthThroughContext declaration (depth + arity) inner
  | depth, .substBody inner _ =>
      keyDepthThroughContext declaration (depth + 1) inner
  | depth, .substReplacement _ inner =>
      keyDepthThroughContext declaration depth inner
  | depth, .collection _ _ inner _ _ =>
      keyDepthThroughContext declaration depth inner

/-- Under agreement the two context disciplines are the same function, which
is the context-level form of `apply_depths_coincide_of_agrees`. -/
theorem keyDepthThroughContext_eq_restorationDepthThroughContext
    {source : CIGSLT} {declaration : ReflectivePresentationDecl}
    (agrees : QuoteStatusAgrees source declaration) :
    ∀ (depth : Nat) (context : OneHoleContext),
      keyDepthThroughContext declaration depth context =
        restorationDepthThroughContext source depth context
  | depth, .hole => rfl
  | depth, .apply constructor _ inner _ => by
      simp only [keyDepthThroughContext, restorationDepthThroughContext,
        ← apply_depths_coincide_of_agrees agrees constructor depth]
      exact keyDepthThroughContext_eq_restorationDepthThroughContext agrees _ inner
  | depth, .lambda _ inner =>
      keyDepthThroughContext_eq_restorationDepthThroughContext agrees _ inner
  | depth, .multiLambda _ _ inner =>
      keyDepthThroughContext_eq_restorationDepthThroughContext agrees _ inner
  | depth, .substBody inner _ =>
      keyDepthThroughContext_eq_restorationDepthThroughContext agrees _ inner
  | depth, .substReplacement _ inner =>
      keyDepthThroughContext_eq_restorationDepthThroughContext agrees _ inner
  | depth, .collection _ _ inner _ _ =>
      keyDepthThroughContext_eq_restorationDepthThroughContext agrees _ inner

/-- **Negative canary.**  A single foreign-quote frame already separates the
two context disciplines at any non-zero depth: the restoration reading resets
while the keying reading passes through.  This is why the paired context below
carries four indices rather than two. -/
theorem keyDepthThroughContext_ne_restorationDepthThroughContext_at_foreignQuote
    {source : CIGSLT} {declaration : ReflectivePresentationDecl}
    {constructor : String} (foreign : constructor ≠ declaration.quoteConstructor)
    (isQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile constructor = true)
    {depth : Nat} (positive : depth ≠ 0)
    (before after : List Pattern) :
    keyDepthThroughContext declaration depth
        (.apply constructor before .hole after) ≠
      restorationDepthThroughContext source depth
        (.apply constructor before .hole after) := by
  simp only [keyDepthThroughContext, restorationDepthThroughContext,
    beq_eq_false_iff_ne.mpr foreign, isQuote, if_true]
  exact positive

/-! ## Paired one-hole contexts carrying both disciplines -/

/-- A pair of one-hole contexts whose fixed siblings meet at a common
semantic restoration apex, with the restoration depth and the keying depth
transported independently.

Four indices: the restoration and keying depths visible at the roots, and
the restoration and keying depths visible at the holes.  The `apply` frame
is the only one where the two advance by different rules. -/
inductive TwoDepthApexContext
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Nat → Nat → Nat → OneHoleContext → OneHoleContext → Prop where
  | hole (restorationDepth keyDepth : Nat) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        restorationDepth keyDepth .hole .hole
  /-- **The frame where the disciplines part.**  The restoration depth resets
  at any presentation's quote; the keying depth resets only at this
  declaration's. -/
  | apply {restorationDepth keyDepth holeRestorationDepth holeKeyDepth : Nat}
      (constructor : String)
      {leftBefore rightBefore leftAfter rightAfter : List Pattern}
      {leftInner rightInner : OneHoleContext}
      (before : TwoDepthApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor
          then 0 else restorationDepth)
        (if constructor == declaration.quoteConstructor then 0 else keyDepth)
        leftBefore rightBefore)
      (inner : TwoDepthApexContext source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor
          then 0 else restorationDepth)
        (if constructor == declaration.quoteConstructor then 0 else keyDepth)
        holeRestorationDepth holeKeyDepth leftInner rightInner)
      (after : TwoDepthApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor
          then 0 else restorationDepth)
        (if constructor == declaration.quoteConstructor then 0 else keyDepth)
        leftAfter rightAfter) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        holeRestorationDepth holeKeyDepth
        (.apply constructor leftBefore leftInner leftAfter)
        (.apply constructor rightBefore rightInner rightAfter)
  | lambda {restorationDepth keyDepth holeRestorationDepth holeKeyDepth : Nat}
      (binder : Option String) {leftInner rightInner : OneHoleContext}
      (inner : TwoDepthApexContext source cospan declaration
        (restorationDepth + 1) (keyDepth + 1)
        holeRestorationDepth holeKeyDepth leftInner rightInner) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        holeRestorationDepth holeKeyDepth
        (.lambda binder leftInner) (.lambda binder rightInner)
  | multiLambda {restorationDepth keyDepth holeRestorationDepth holeKeyDepth
        arity : Nat} (binders : List String)
      {leftInner rightInner : OneHoleContext}
      (inner : TwoDepthApexContext source cospan declaration
        (restorationDepth + arity) (keyDepth + arity)
        holeRestorationDepth holeKeyDepth leftInner rightInner) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        holeRestorationDepth holeKeyDepth
        (.multiLambda arity binders leftInner)
        (.multiLambda arity binders rightInner)
  | substBody {restorationDepth keyDepth holeRestorationDepth holeKeyDepth : Nat}
      {leftInner rightInner : OneHoleContext}
      {leftReplacement rightReplacement : Pattern}
      (inner : TwoDepthApexContext source cospan declaration
        (restorationDepth + 1) (keyDepth + 1)
        holeRestorationDepth holeKeyDepth leftInner rightInner)
      (replacement : TwoDepthApex source cospan declaration restorationDepth
        keyDepth leftReplacement rightReplacement) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        holeRestorationDepth holeKeyDepth
        (.substBody leftInner leftReplacement)
        (.substBody rightInner rightReplacement)
  | substReplacement {restorationDepth keyDepth holeRestorationDepth
        holeKeyDepth : Nat} {leftBody rightBody : Pattern}
      {leftInner rightInner : OneHoleContext}
      (body : TwoDepthApex source cospan declaration (restorationDepth + 1)
        (keyDepth + 1) leftBody rightBody)
      (inner : TwoDepthApexContext source cospan declaration restorationDepth
        keyDepth holeRestorationDepth holeKeyDepth leftInner rightInner) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        holeRestorationDepth holeKeyDepth
        (.substReplacement leftBody leftInner)
        (.substReplacement rightBody rightInner)
  | collection {restorationDepth keyDepth holeRestorationDepth holeKeyDepth :
        Nat} (collectionType : CollType) (rest : Option String)
      {leftBefore rightBefore leftAfter rightAfter : List Pattern}
      {leftInner rightInner : OneHoleContext}
      (before : TwoDepthApexList source cospan declaration restorationDepth
        keyDepth leftBefore rightBefore)
      (inner : TwoDepthApexContext source cospan declaration restorationDepth
        keyDepth holeRestorationDepth holeKeyDepth leftInner rightInner)
      (after : TwoDepthApexList source cospan declaration restorationDepth
        keyDepth leftAfter rightAfter) :
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        holeRestorationDepth holeKeyDepth
        (.collection collectionType leftBefore leftInner leftAfter rest)
        (.collection collectionType rightBefore rightInner rightAfter rest)

namespace TwoDepthApexContext

/-- **The compatibility law.**  Every context is aligned with itself at
exactly the pair of hole depths computed by the two disciplines — the
restoration depth by `restorationDepthThroughContext`, the keying depth by
`keyDepthThroughContext`.

This is the statement that the two rulers can be carried through one and the
same context simultaneously.  It has content precisely at `apply` frames,
where the conclusion's two indices are produced by different tests of the
same head constructor; the single-index carrier could only state it by
assuming those tests agree. -/
theorem refl {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    ∀ (restorationDepth keyDepth : Nat) (context : OneHoleContext),
      TwoDepthApexContext source cospan declaration restorationDepth keyDepth
        (restorationDepthThroughContext source restorationDepth context)
        (keyDepthThroughContext declaration keyDepth context) context context
  | restorationDepth, keyDepth, .hole => .hole restorationDepth keyDepth
  | _, _, .apply constructor before inner after =>
      .apply constructor
        (TwoDepthApex.reflList cospan declaration _ _ before)
        (refl cospan declaration _ _ inner)
        (TwoDepthApex.reflList cospan declaration _ _ after)
  | _, _, .lambda binder inner =>
      .lambda binder (refl cospan declaration _ _ inner)
  | _, _, .multiLambda _ binders inner =>
      .multiLambda binders (refl cospan declaration _ _ inner)
  | restorationDepth, keyDepth, .substBody inner replacement =>
      .substBody (refl cospan declaration _ _ inner)
        (TwoDepthApex.refl cospan declaration restorationDepth keyDepth
          replacement)
  | restorationDepth, keyDepth, .substReplacement body inner =>
      .substReplacement
        (TwoDepthApex.refl cospan declaration (restorationDepth + 1)
          (keyDepth + 1) body)
        (refl cospan declaration _ _ inner)
  | _, _, .collection collectionType before inner after rest =>
      .collection collectionType rest
        (TwoDepthApex.reflList cospan declaration _ _ before)
        (refl cospan declaration _ _ inner)
        (TwoDepthApex.reflList cospan declaration _ _ after)

/-- Transport a paired context across syntactic equalities of its endpoints. -/
theorem reindex {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {restorationDepth keyDepth holeRestorationDepth holeKeyDepth : Nat}
    {left right left' right' : OneHoleContext}
    (leftEq : left = left') (rightEq : right = right')
    (context : TwoDepthApexContext source cospan declaration restorationDepth
      keyDepth holeRestorationDepth holeKeyDepth left right) :
    TwoDepthApexContext source cospan declaration restorationDepth keyDepth
      holeRestorationDepth holeKeyDepth left' right' := by
  cases leftEq
  cases rightEq
  exact context

end TwoDepthApexContext

/-! ## The typed client obligation for bare parallel

The syntax layer already delivers, unconditionally and at independently
selected depths, a permutation of the keyed flattened frontiers
(`canonicalize_parallelContents_keyed_perm_of_equal`,
`canonicalize_keyed_eq_of_canonicalize_eq`).  What it explicitly does *not*
deliver is exact apex evidence for the matched classes — that is left to the
typed client.

`TwoDepthPermutation` is the carrier for discharging it.  Occurrence order and
semantic alignment are kept separate on purpose: the alignment relates the left
frontier to an intermediate list *pointwise*, and only then is a permutation
composed on the right.  Pairing frontier entries by value instead would be
unsound exactly here, because parallel composition is what creates repeated
elements. -/

/-- An occurrence-preserving aligned permutation at separated depths: a
pointwise apex alignment onto an intermediate list, followed by a permutation
onto the right list.  The intermediate list is what keeps duplicate
occurrences distinct. -/
structure TwoDepthPermutation
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat)
    (left right : List Pattern) : Type where
  middle : List Pattern
  aligned : TwoDepthApexList source cospan declaration restorationDepth
    keyDepth left middle
  permutation : List.Perm middle right

/-- Pointwise view of a two-depth apex list. -/
private theorem twoDepthApexList_toForall₂ {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {restorationDepth keyDepth : Nat} :
    ∀ {left right : List Pattern},
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        left right →
      List.Forall₂
        (TwoDepthApex source cospan declaration restorationDepth keyDepth)
        left right
  | _, _, .nil _ _ => .nil
  | _, _, .cons head tail => .cons head (twoDepthApexList_toForall₂ tail)

/-- Inverse of the pointwise view. -/
private theorem twoDepthApexList_ofForall₂ {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {restorationDepth keyDepth : Nat} :
    ∀ {left right : List Pattern},
      List.Forall₂
        (TwoDepthApex source cospan declaration restorationDepth keyDepth)
        left right →
      TwoDepthApexList source cospan declaration restorationDepth keyDepth
        left right
  | _, _, .nil => .nil _ _
  | _, _, .cons head tail => .cons head (twoDepthApexList_ofForall₂ tail)

/-- **Reindex both endpoints of an aligned permutation, at separated depths.**

Occurrence order and semantic alignment stay separate: the left permutation is
transported *through* the pointwise relation, and the right permutation is
composed only after that alignment has been retained.

This is the bridge the bare-parallel terminal actually needs.  The mismatch
between a permutation over `canonicalizeListByAt … elements` and one over
`parallelContents (canonicalizeListByAt … elements)` is closed by reindexing
both endpoints with typed frontier permutations — not by any absorption or
idempotence law, which is refuted in general. -/
noncomputable def TwoDepthPermutation.of_endpoint_perms {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {restorationDepth keyDepth : Nat}
    {left left' right right' : List Pattern}
    (alignment : TwoDepthPermutation (source := source) cospan declaration
      restorationDepth keyDepth left right)
    (leftPermutation : List.Perm left' left)
    (rightPermutation : List.Perm right' right) :
    TwoDepthPermutation (source := source) cospan declaration restorationDepth
      keyDepth left' right' := by
  let evidence := List.perm_comp_forall₂ leftPermutation
    (twoDepthApexList_toForall₂ alignment.aligned)
  let middle' := Classical.choose evidence
  have middleSpec := Classical.choose_spec evidence
  exact
    { middle := middle'
      aligned := twoDepthApexList_ofForall₂ middleSpec.1
      permutation := middleSpec.2.trans
        (alignment.permutation.trans rightPermutation.symm) }

/-- **Discharging the typed obligation, at separated depths.**

Lift a permutation of ordinary canonical classes through a local apex
constructor.  The callback receives membership in *both* original endpoint
lists, so typing, support, size descent, provenance, and occurrence evidence
can all be recovered before recursive closure; multiplicities and discarded
positional identities are retained by the intermediate list rather than being
reconstructed from values.

The permutation premise is the one the syntax layer already supplies
unconditionally at independently selected depths, so this is the exact seam at
which the two-depth carrier meets the existing order-agnostic machinery. -/
noncomputable def TwoDepthPermutation.of_canonical_map_perm
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat)
    {left right : List Pattern}
    (permutation : List.Perm
      (left.map (canonicalize declaration))
      (right.map (canonicalize declaration)))
    (close : ∀ {leftPattern rightPattern},
      leftPattern ∈ left → rightPattern ∈ right →
      canonicalize declaration leftPattern =
          canonicalize declaration rightPattern →
        TwoDepthApex source cospan declaration restorationDepth keyDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration keyDepth leftPattern)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration keyDepth rightPattern)) :
    TwoDepthPermutation (source := source) cospan declaration restorationDepth
      keyDepth
      (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth left)
      (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth right) := by
  let evidence :=
    CommonRestorationApex.exists_forall₂_canonical_eq_of_map_perm declaration
      permutation
  let middle := Classical.choose evidence
  have middleSpec := Classical.choose_spec evidence
  have aligned := middleSpec.1
  have reordered := middleSpec.2
  let normalize := canonicalizeByAt
    (cospan.commonSemanticPatternKeyAt source) declaration keyDepth
  have liftAligned : ∀ {leftPatterns rightPatterns : List Pattern},
      List.Forall₂
          (fun leftPattern rightPattern =>
            canonicalize declaration leftPattern =
              canonicalize declaration rightPattern)
          leftPatterns rightPatterns →
        (∀ pattern ∈ leftPatterns, pattern ∈ left) →
        (∀ pattern ∈ rightPatterns, pattern ∈ right) →
        TwoDepthApexList source cospan declaration restorationDepth keyDepth
          (leftPatterns.map normalize) (rightPatterns.map normalize) := by
    intro leftPatterns rightPatterns relation leftMembership rightMembership
    induction relation with
    | nil => exact .nil restorationDepth keyDepth
    | cons related _ inductionHypothesis =>
        exact .cons
          (close (leftMembership _ (by simp))
            (rightMembership _ (by simp)) related)
          (inductionHypothesis
            (fun pattern membership =>
              leftMembership pattern (by simp [membership]))
            (fun pattern membership =>
              rightMembership pattern (by simp [membership])))
  have normalizedAligned : TwoDepthApexList source cospan declaration
      restorationDepth keyDepth (left.map normalize) (middle.map normalize) :=
    liftAligned aligned (fun _ membership => membership)
      (fun pattern membership => reordered.mem_iff.mp membership)
  refine
    { middle := middle.map normalize
      aligned := ?_
      permutation := ?_ }
  · simpa [normalize, canonicalizeListByAt_eq_map] using normalizedAligned
  · simpa [normalize, canonicalizeListByAt_eq_map] using reordered.map normalize

/-- **Bare parallel from an aligned permutation, at separated depths.**  This
is the two-depth form of the parallel terminal: given occurrence-preserving
alignment of the post-canonicalization, post-splice frontiers — keyed at
`keyDepth` — the parallel apex follows at that `keyDepth` and at *any*
restoration depth. -/
theorem TwoDepthApex.parallel_of_permutation
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat)
    {leftElements rightElements : List Pattern}
    (alignment : TwoDepthPermutation (source := source) cospan declaration
      restorationDepth keyDepth
      (parallelContents declaration
        (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth leftElements))
      (parallelContents declaration
        (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth rightElements))) :
    TwoDepthApex source cospan declaration restorationDepth keyDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth
        (.collection declaration.parallelCollection leftElements none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth
        (.collection declaration.parallelCollection rightElements none)) :=
  .parallel alignment.aligned alignment.permutation

/-- **Lifting through a context, with both rulers.**  Apex evidence supplied
at the hole — stated at the two depths the two disciplines compute there —
lifts to apex evidence at the roots.

This is the second half of the context interface, and the place where the
separation earns its keep: the one-index lift required the hole evidence at a
single depth, which at a foreign quote is the wrong depth for one of the two
consumers.  Here each ruler is transported by its own rule and neither is
coerced into the other. -/
theorem TwoDepthApex.throughContext {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    ∀ (context : OneHoleContext) (restorationDepth keyDepth : Nat)
      {left right : Pattern},
      TwoDepthApex source cospan declaration
          (restorationDepthThroughContext source restorationDepth context)
          (keyDepthThroughContext declaration keyDepth context) left right →
        TwoDepthApex source cospan declaration restorationDepth keyDepth
          (context.fill left) (context.fill right)
  | .hole, _, _, _, _, apex => apex
  | .apply constructor before inner after, _, _, _, _, apex =>
      .apply constructor
        (TwoDepthApex.appendList cospan declaration
          (TwoDepthApex.reflList cospan declaration _ _ before)
          (.cons (TwoDepthApex.throughContext cospan declaration inner _ _ apex)
            (TwoDepthApex.reflList cospan declaration _ _ after)))
  | .lambda binder inner, _, _, _, _, apex =>
      .lambda binder
        (TwoDepthApex.throughContext cospan declaration inner _ _ apex)
  | .multiLambda _ binders inner, _, _, _, _, apex =>
      .multiLambda binders
        (TwoDepthApex.throughContext cospan declaration inner _ _ apex)
  | .substBody inner replacement, restorationDepth, keyDepth, _, _, apex =>
      .subst (TwoDepthApex.throughContext cospan declaration inner _ _ apex)
        (TwoDepthApex.refl cospan declaration restorationDepth keyDepth
          replacement)
  | .substReplacement body inner, restorationDepth, keyDepth, _, _, apex =>
      .subst
        (TwoDepthApex.refl cospan declaration (restorationDepth + 1)
          (keyDepth + 1) body)
        (TwoDepthApex.throughContext cospan declaration inner _ _ apex)
  | .collection collectionType before inner after rest, _, _, _, _, apex =>
      .collection collectionType rest
        (TwoDepthApex.appendList cospan declaration
          (TwoDepthApex.reflList cospan declaration _ _ before)
          (.cons (TwoDepthApex.throughContext cospan declaration inner _ _ apex)
            (TwoDepthApex.reflList cospan declaration _ _ after)))

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
