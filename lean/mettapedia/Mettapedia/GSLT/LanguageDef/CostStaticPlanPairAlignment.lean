import Mettapedia.GSLT.LanguageDef.CostStaticPlanContextView
import Mettapedia.GSLT.LanguageDef.CostElaborationDecoration
import Mettapedia.GSLT.LanguageDef.CostElaborationTransport
import Mettapedia.GSLT.LanguageDef.CostGeneratedOccurrence

/-!
# Paired nonlinear context views of static-region plans

One authored generator edge relates two endpoint static plans.  Each endpoint
independently admits a total one-sided context inventory view; the edge
independently carries the nonlinear contravariant boundary pullback.  This
module joins them.

The join is deliberately not a positional zipper.  Endpoint occurrence
identity is a replayable finite position derived from the Type-valued
keep/skip embedding; cross-endpoint transport is the edge's own
`CostBoundaryFiberMap`, which may duplicate (non-injective pullback) or
discard (non-surjective pullback).  The paired carrier therefore composes an
exact endpoint position with the edge pullback and never assumes equal
lengths, injectivity, surjectivity, boundary-value uniqueness, or a single
changed child.

`CostStaticPlanEntryEmbedding.position` settles the carrier-sufficiency
question positively: the keep/skip path determines a strictly monotone
position function whose values recover the retained entries, so repeated
equal typed boundary entries keep distinct replayable positions and no
dependent cast can conflate them after the fact.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open WellSorted

/-- The authored source declaration selected by a generator witness, with
the equation/reflection/derived-law distinction preserved. -/
inductive SourceGeneratorDeclaration : Type where
  | equation (declaration : Equation)
  | reflective (declaration : ReflectivePresentationDecl)
  | derived (declaration : GrammarRule)

namespace ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness

/-- Extract the exact authored declaration used by a proof-relevant
generator witness. -/
def sourceDeclaration
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
        profile base language left right → SourceGeneratorDeclaration
  | .core (.equation _ instanceWitness) =>
      match instanceWitness with
      | .forward _ used _ _ _ _ _ => .equation used.1
      | .reverse _ used _ _ _ _ _ => .equation used.1
  | .core (.derived _ lawWitness) => .derived lawWitness.rule
  | .reflective _ used _ => .reflective used.1

end ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness

namespace CostStaticPlanEntryEmbedding

/-- The exact finite position selected by a keep/skip path.  The path is
data, so the position function is defined by recursion on it rather than by
searching the table for an equal value. -/
def position {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    {small large : List (TypedCostRegionBoundary source color targetFree)} →
      CostStaticPlanEntryEmbedding source color targetFree small large →
        Fin small.length → Fin large.length
  | _, _, .nil _, index => absurd index.isLt (by simp)
  | _ :: _, _ :: _, .keep tail, index =>
      Fin.cases ⟨0, Nat.succ_pos _⟩
        (fun previous => (tail.position previous).succ) index
  | _, _ :: _, .skip _ tail, index => (tail.position index).succ

/-- The entry at the selected position is exactly the retained entry: the
position function is a value-preserving replay of the keep/skip path. -/
theorem position_get {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ {small large : List (TypedCostRegionBoundary source color targetFree)}
      (embedding : CostStaticPlanEntryEmbedding source color targetFree small
        large) (index : Fin small.length),
      large.get (embedding.position index) = small.get index
  | _, _, .nil _, index => absurd index.isLt (by simp)
  | _ :: _, _ :: _, .keep tail, index => by
      induction index using Fin.cases with
      | zero => rfl
      | succ previous => exact position_get tail previous
  | _, _ :: _, .skip _ tail, index => position_get tail index

/-- Positional replay respects composition of keep/skip embeddings.  This is
the finite-index law that lets nested context views select the same original
occurrence as one composed view, including when several retained entries have
equal boundary values. -/
theorem position_comp {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {small middle large :
      List (TypedCostRegionBoundary source color targetFree)}
    (smallToMiddle : CostStaticPlanEntryEmbedding source color targetFree
      small middle)
    (middleToLarge : CostStaticPlanEntryEmbedding source color targetFree
      middle large)
    (index : Fin small.length) :
    (smallToMiddle.comp middleToLarge).position index =
      middleToLarge.position (smallToMiddle.position index) := by
  induction middleToLarge generalizing small with
  | nil largeEntries => exact Fin.elim0 (smallToMiddle.position index)
  | @keep entry middleEntries largeEntries tail inductionHypothesis =>
      cases smallToMiddle with
      | nil => exact Fin.elim0 index
      | keep smallTailToMiddle =>
          induction index using Fin.cases with
          | zero => rfl
          | succ previous =>
              exact congrArg Fin.succ
                (inductionHypothesis smallTailToMiddle previous)
      | skip skipped smallToMiddleTail =>
          exact congrArg Fin.succ
            (inductionHypothesis smallToMiddleTail index)
  | @skip entry middleEntries largeEntries tail inductionHypothesis =>
      cases smallToMiddle with
      | nil => exact Fin.elim0 index
      | keep smallTailToMiddle =>
          exact congrArg Fin.succ
            (inductionHypothesis (.keep smallTailToMiddle) index)
      | skip skipped smallToMiddleTail =>
          exact congrArg Fin.succ
            (inductionHypothesis (.skip skipped smallToMiddleTail) index)

/-- Strict monotonicity: distinct retained positions stay distinct in the
large table even when the retained entry values are equal.  This is the
machine-checked sufficiency answer for repeated equal typed boundary
entries. -/
theorem position_strictMono {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ {small large : List (TypedCostRegionBoundary source color targetFree)}
      (embedding : CostStaticPlanEntryEmbedding source color targetFree small
        large) {first second : Fin small.length},
      first < second →
      embedding.position first < embedding.position second
  | _, _, .nil _, first, _, _ => absurd first.isLt (by simp)
  | _ :: _, _ :: _, .keep tail, first, second, less => by
      induction second using Fin.cases with
      | zero => exact absurd less (by simp)
      | succ secondPrevious =>
          induction first using Fin.cases with
          | zero => exact Fin.succ_pos _
          | succ firstPrevious =>
              exact Fin.succ_lt_succ_iff.mpr
                (position_strictMono tail (Fin.succ_lt_succ_iff.mp less))
  | _, _ :: _, .skip _ tail, first, second, less =>
      Fin.succ_lt_succ_iff.mpr (position_strictMono tail less)

/-- Positions are injective independently of entry values. -/
theorem position_injective {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {small large : List (TypedCostRegionBoundary source color targetFree)}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree small
      large) :
    Function.Injective embedding.position := by
  intro first second equal
  rcases lt_trichotomy first second with less | exact | greater
  · exact absurd equal (position_strictMono embedding less).ne
  · exact exact
  · exact absurd equal.symm (position_strictMono embedding greater).ne

end CostStaticPlanEntryEmbedding

/-- Two spellings of one boundary list have exactly transferable lengths. -/
private theorem map_eq_map_length {α β γ : Type _} {f : α → γ} {g : β → γ}
    {left : List α} {right : List β}
    (spelling : left.map f = right.map g) : left.length = right.length := by
  simpa using congrArg List.length spelling

/-- Two spellings of one boundary list transfer entry values position by
position. -/
private theorem map_eq_map_get {α β γ : Type _} {f : α → γ} {g : β → γ}
    {left : List α} {right : List β}
    (spelling : left.map f = right.map g) (index : Fin left.length) :
    f (left.get index) =
      g (right.get (Fin.cast (map_eq_map_length spelling) index)) := by
  have congruence : ∀ {δ : Type _} (firstList secondList : List δ)
      (listsEq : firstList = secondList) (position : Nat)
      (inBounds : position < firstList.length),
      firstList[position]'inBounds =
        secondList[position]'(listsEq ▸ inBounds) := by
    intro _ firstList secondList listsEq position inBounds
    cases listsEq
    rfl
  have step := congruence (left.map f) (right.map g) spelling index.1
    (by simp)
  simpa using step

/-- One occurrence cell of a paired nonlinear context view: the two
endpoint context inventory views for one selected occurrence pair, joined to
the exact authored generator edge by replayable endpoint positions into the
edge's own boundary inventories.

The four reached/stopped combinations are exactly the four constructor
combinations of the two retained views; different endpoint plan shapes need
no additional tag.  A wrapped-colour view whose traversal stops at a
base-content boundary represents static colour re-entry through the
certified boundary itself; the enclosing edge stays in one static fibre, as
`edge.sameFiber` demands.

Nonlinear transport is not a field: it is derived below by composing the
right endpoint position with the edge's contravariant pullback, so
duplication and discard are inherited from the edge rather than restated. -/
structure CostStaticPlanContextPair (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries)
    (leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern)
    (leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)) : Type where
  left : CostStaticPlanContextInventoryView source color targetFree
    leftPayload leftRootAbstract leftEntries
  right : CostStaticPlanContextInventoryView source color targetFree
    rightPayload rightRootAbstract rightEntries
  leftRoot_eq : first.abstractPattern = leftRootAbstract
  rightRoot_eq : second.abstractPattern = rightRootAbstract
  leftTable_eq : leftEntries.map (fun entry => entry.boundary) =
    sourceBoundaries.map (fun boundary => boundary.1)
  rightTable_eq : rightEntries.map (fun entry => entry.boundary) =
    targetBoundaries.map (fun boundary => boundary.1)

namespace CostStaticPlanContextPair

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : FreeTypeContext}
  {first second : CostStaticPlanDecoration source}
  {sourceBoundaries targetBoundaries :
    List (CostRegionBoundary × CostTreeDecoration source)}
  {edge : CostStaticPlanEdge source first second sourceBoundaries
    targetBoundaries}
  {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
  {leftEntries rightEntries :
    List (TypedCostRegionBoundary source color targetFree)}

/-- Transport the edge's exact authored generator witness to the two concrete
plan-root abstracts.  This is the semantic tie supplied by an endpoint pair;
it still does not relate the edge to an enclosing generated-Cost occurrence. -/
def rootGeneratorWitness
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.reflection.1 defaultBasePremises
      source.theory.presentation.presentation.language leftRootAbstract
        rightRootAbstract := by
  rw [← pair.leftRoot_eq, ← pair.rightRoot_eq]
  exact edge.generatorWitness

/-- The exact left endpoint position is derived from the keep/skip path and
the edge-inventory spelling.  It is not an inhabitant-supplied choice, so two
equal boundary values cannot redirect a retained occurrence to a different
duplicate. -/
def leftPosition
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    Fin alignment.left.view.retainedEntries.length →
      Fin sourceBoundaries.length :=
  fun index =>
    Fin.cast (map_eq_map_length alignment.leftTable_eq)
      (alignment.left.entryEmbedding.position index)

/-- The derived left position recovers the retained boundary value. -/
theorem leftPosition_eq
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (index : Fin alignment.left.view.retainedEntries.length) :
    (sourceBoundaries.get (alignment.leftPosition index)).1 =
      (alignment.left.view.retainedEntries.get index).boundary := by
  have transfer := map_eq_map_get alignment.leftTable_eq
    (alignment.left.entryEmbedding.position index)
  rw [CostStaticPlanEntryEmbedding.position_get] at transfer
  exact transfer.symm

/-- Derived left positions remain injective even when boundary values repeat. -/
theorem leftPosition_injective
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    Function.Injective alignment.leftPosition := by
  intro firstIndex secondIndex positionsEq
  apply alignment.left.entryEmbedding.position_injective
  exact (Fin.cast_injective _ positionsEq)

/-- The exact right endpoint position, derived rather than supplied. -/
def rightPosition
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    Fin alignment.right.view.retainedEntries.length →
      Fin targetBoundaries.length :=
  fun index =>
    Fin.cast (map_eq_map_length alignment.rightTable_eq)
      (alignment.right.entryEmbedding.position index)

/-- The derived right position recovers the retained boundary value. -/
theorem rightPosition_eq
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (index : Fin alignment.right.view.retainedEntries.length) :
    (targetBoundaries.get (alignment.rightPosition index)).1 =
      (alignment.right.view.retainedEntries.get index).boundary := by
  have transfer := map_eq_map_get alignment.rightTable_eq
    (alignment.right.entryEmbedding.position index)
  rw [CostStaticPlanEntryEmbedding.position_get] at transfer
  exact transfer.symm

/-- Derived right positions remain injective even when boundary values repeat. -/
theorem rightPosition_injective
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    Function.Injective alignment.rightPosition := by
  intro firstIndex secondIndex positionsEq
  apply alignment.right.entryEmbedding.position_injective
  exact (Fin.cast_injective _ positionsEq)

/-- The nonlinear pullback restricted to the entries selected by the right
context view: compose the exact endpoint position with the edge's
contravariant occurrence map.  Non-injectivity of the edge pullback realizes
duplication; source occurrences outside the image realize discard.  No
injectivity, surjectivity, or length assumption is available or needed. -/
def selectedPullback
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    Fin alignment.right.view.retainedEntries.length →
      Fin sourceBoundaries.length :=
  fun index => edge.boundaryOrigins.pullback (alignment.rightPosition index)

/-- Every selected right occurrence pulls back to a source occurrence in the
same exact type/support fibre.  This is the typed-level restatement of the
edge's no-manufactured-boundary law and is what a later restoration closure
compares at a common typed apex. -/
theorem selectedPullback_sameFiber
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (index : Fin alignment.right.view.retainedEntries.length) :
    CostRegionBoundary.SameFiber
      (sourceBoundaries.get (alignment.selectedPullback index)).1
      (alignment.right.view.retainedEntries.get index).boundary := by
  have fiber := edge.boundaryOrigins.preservesFiber
    (alignment.rightPosition index)
  rw [alignment.rightPosition_eq index] at fiber
  exact fiber

/-- Recover the typed left-table entry at an arbitrary position of the
edge's source inventory.  This is intentionally defined on the full source
inventory, not only on entries retained by the left context view: a lawful
target pullback may select a source occurrence outside that smaller view. -/
def leftEntryIndexAtSource
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (position : Fin sourceBoundaries.length) : Fin leftEntries.length :=
  Fin.cast (map_eq_map_length alignment.leftTable_eq).symm position

/-- The recovered typed entry spells exactly the source boundary at the
requested edge position. -/
theorem leftEntryIndexAtSource_boundary
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (position : Fin sourceBoundaries.length) :
    (leftEntries.get (alignment.leftEntryIndexAtSource position)).boundary =
      (sourceBoundaries.get position).1 := by
  have transfer := map_eq_map_get alignment.leftTable_eq
    (alignment.leftEntryIndexAtSource position)
  simpa [leftEntryIndexAtSource] using transfer

/-- The exact typed source entry selected by one retained target occurrence's
nonlinear pullback. -/
def selectedSourceEntry
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (index : Fin alignment.right.view.retainedEntries.length) :
    TypedCostRegionBoundary source color targetFree :=
  leftEntries.get
    (alignment.leftEntryIndexAtSource (alignment.selectedPullback index))

/-- Pullback transport preserves the complete fibre of the actual typed
entries, without assuming that the selected source entry lies in the left
context view's retained subinventory. -/
theorem selectedSourceEntry_sameFiber
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (index : Fin alignment.right.view.retainedEntries.length) :
    CostRegionBoundary.SameFiber
      (alignment.selectedSourceEntry index).boundary
      (alignment.right.view.retainedEntries.get index).boundary := by
  have fiber := alignment.selectedPullback_sameFiber index
  rw [← alignment.leftEntryIndexAtSource_boundary
    (alignment.selectedPullback index)] at fiber
  exact fiber

/-- The retained right entries can never outrun the edge's own target
inventory: a stopped boundary occupies an exact position of the edge's
finite table.  With an empty target inventory no selected entry exists. -/
theorem noSelectedEntry_of_targetEmpty
    (alignment : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (empty : targetBoundaries = []) :
    alignment.right.view.retainedEntries.length = 0 := by
  by_contra nonempty
  have index : Fin alignment.right.view.retainedEntries.length :=
    ⟨0, Nat.pos_of_ne_zero nonempty⟩
  have position := alignment.rightPosition index
  rw [empty] at position
  exact absurd position.isLt (by simp)

end CostStaticPlanContextPair

/-- One candidate occurrence cell of a generator edge: the payload pair
selected by one context pair.  Root abstracts and
root tables are shared across the cells of one edge. -/
structure CostStaticPlanContextPairCell (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries)
    (leftRootAbstract rightRootAbstract : Pattern)
    (leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)) : Type where
  leftPayload : Pattern
  rightPayload : Pattern
  pair : CostStaticPlanContextPair source color targetFree edge
    leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
    rightEntries

/-- A finite family of candidate occurrence cells over one authored generator
edge.  It can store several cells sharing the edge, root abstracts, and root
tables, but does not yet prove that they cover the generator occurrence. -/
structure CostStaticPlanContextPairFamily (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries)
    (leftRootAbstract rightRootAbstract : Pattern)
    (leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)) : Type where
  cells : List (CostStaticPlanContextPairCell source color targetFree
    edge leftRootAbstract rightRootAbstract leftEntries rightEntries)

/-- One candidate changed static sibling of an authored generator occurrence,
with its own colour, cell-level edge, and endpoint pair.  The two
endpoint decorations, inventories, and colour are per-cell because one
generator occurrence can change siblings living in different static colours
and different maximal regions. -/
structure CostStaticPlanSiblingPairCell (source : CIGSLT)
    (targetFree : FreeTypeContext) : Type where
  color : CostStaticColor
  first : CostStaticPlanDecoration source
  second : CostStaticPlanDecoration source
  sourceBoundaries : List (CostRegionBoundary × CostTreeDecoration source)
  targetBoundaries : List (CostRegionBoundary × CostTreeDecoration source)
  edge : CostStaticPlanEdge source first second sourceBoundaries
    targetBoundaries
  /-- Cached authored declaration of `edge`.  The equality keeps the cache
  honest while preventing clients from normalizing every dependent plan
  index merely to inspect the declaration. -/
  sourceDeclaration : SourceGeneratorDeclaration
  sourceDeclaration_eq : edge.generatorWitness.sourceDeclaration =
    sourceDeclaration
  leftPayload : Pattern
  rightPayload : Pattern
  leftRootAbstract : Pattern
  rightRootAbstract : Pattern
  leftEntries : List (TypedCostRegionBoundary source color targetFree)
  rightEntries : List (TypedCostRegionBoundary source color targetFree)
  pair : CostStaticPlanContextPair source color targetFree edge
    leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
    rightEntries

/-- Raw changed-sibling candidates attached to one exact authored generator
occurrence of the generated Cost language.  The list can express several
cells, but this carrier deliberately supplies neither coverage nor a proof
that a cell-level edge erases to the enclosing occurrence. -/
structure CostStaticPlanGeneratorPairCandidates (source : CIGSLT)
    (targetFree : FreeTypeContext) {left right : Pattern}
    (occurrence : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right) : Type where
  cells : List (CostStaticPlanSiblingPairCell source targetFree)

namespace CostStaticPlanGeneratorPairCandidates

/-- The raw candidate carrier deliberately permits no cells.  Consequently it
is not yet a generator alignment or a coverage certificate; the next layer
must tie cells to the enclosing occurrence and prove coverage. -/
def empty (source : CIGSLT) (targetFree : FreeTypeContext)
    {left right : Pattern}
    (occurrence : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right) :
    CostStaticPlanGeneratorPairCandidates source targetFree occurrence where
  cells := []

end CostStaticPlanGeneratorPairCandidates

/-- Totality: an authored edge whose endpoint decorations spell the two plan
tables, together with any two occurrence contexts selecting payloads in the
endpoint patterns, always yields an endpoint pair.  The endpoint views come
from the one-sided total decomposition; the endpoint positions are the
replayable keep/skip positions transferred along the edge's own inventory
spelling equations.  No case is deferred to a hypothesis shaped like the
conclusion. -/
theorem CostStaticPlanEdge.nonempty_contextPair
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries)
    {leftSourceBound leftTargetBound : List TypeExpr}
    {leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound}
    {leftAvailable : List TypeExpr} {leftOuter : OneHoleContext}
    {leftPattern : Pattern} {leftSourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType)
    {rightSourceBound rightTargetBound : List TypeExpr}
    {rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound}
    {rightAvailable : List TypeExpr} {rightOuter : OneHoleContext}
    {rightPattern : Pattern} {rightSourceType : TypeExpr}
    (rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType)
    (leftDecoration_eq : first = leftPlan.decoration)
    (rightDecoration_eq : second = rightPlan.decoration)
    (leftContext rightContext : OneHoleContext)
    {leftPayload rightPayload : Pattern}
    (leftFill : leftPattern = leftContext.fill leftPayload)
    (rightFill : rightPattern = rightContext.fill rightPayload) :
    Nonempty (CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftPlan.abstractPattern
      rightPlan.abstractPattern leftPlan.boundaryTable.entries
      rightPlan.boundaryTable.entries) := by
  obtain ⟨leftView⟩ :=
    leftPlan.nonempty_contextInventoryView leftContext leftFill
  obtain ⟨rightView⟩ :=
    rightPlan.nonempty_contextInventoryView rightContext rightFill
  have leftRoot_eq : first.abstractPattern = leftPlan.abstractPattern := by
    rw [leftDecoration_eq]
    exact leftPlan.decoration_abstractPattern
  have rightRoot_eq : second.abstractPattern = rightPlan.abstractPattern := by
    rw [rightDecoration_eq]
    exact rightPlan.decoration_abstractPattern
  have leftBoundaries_eq : first.boundaries =
      leftPlan.boundaryTable.entries.map (fun entry => entry.boundary) := by
    rw [leftDecoration_eq]
    exact leftPlan.decoration_boundaries
  have rightBoundaries_eq : second.boundaries =
      rightPlan.boundaryTable.entries.map (fun entry => entry.boundary) := by
    rw [rightDecoration_eq]
    exact rightPlan.decoration_boundaries
  have leftSpelling :
      leftPlan.boundaryTable.entries.map (fun entry => entry.boundary) =
        sourceBoundaries.map (fun boundary => boundary.1) :=
    leftBoundaries_eq.symm.trans edge.sourceBoundaryInventory
  have rightSpelling :
      rightPlan.boundaryTable.entries.map (fun entry => entry.boundary) =
        targetBoundaries.map (fun boundary => boundary.1) :=
    rightBoundaries_eq.symm.trans edge.targetBoundaryInventory
  refine ⟨{ left := leftView
            right := rightView
            leftRoot_eq := leftRoot_eq
            rightRoot_eq := rightRoot_eq
            leftTable_eq := leftSpelling
            rightTable_eq := rightSpelling }⟩

end Mettapedia.GSLT.LanguageDef
