import Mettapedia.GSLT.Dynamics.RevisionViewRealizationProduct

/-!
# Equation-projection revision authority

A space may contain both executable equation occurrences and unrelated data.
An equation-selection view is derived only from the ordered equation
projection.  Consequently, a data-only transition may reuse that view, while
an equation append, removal, or reordering must change its authority key.

The factorization is observer-relative.  A global equation key is exact for
broad authored-order observation, but can still be finer than one particular
head observer.  Per-head physical sharing is therefore a separate realization
choice, not part of the semantic key law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.EquationProjectionRevisionAuthority

open RevisionBoundProgramView
open ReusableRevisionViewAuthority

universe uData uId uHead uRow uViewId uViewRow uCode

abbrev EquationOccurrence
    (Id : Type uId) (Head : Type uHead) (Row : Type uRow) :=
  RevisionViewRealizationProduct.Occurrence Id Head Row

/-- Complete physical space state, separated into non-equation data and the
ordered family of authored equation occurrences. -/
structure SpaceState
    (Data : Type uData) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) where
  data : List Data
  equations : List (EquationOccurrence Id Head Row)
deriving DecidableEq, Repr

/-- The semantic coordinate observed by equation selection. -/
def equationProjection
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (state : SpaceState Data Id Head Row) :
    List (EquationOccurrence Id Head Row) :=
  state.equations

/-- Two complete states are equivalent for every equation observer exactly
when their ordered equation projections agree. -/
def SameEquationProjection
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (left right : SpaceState Data Id Head Row) : Prop :=
  equationProjection left = equationProjection right

/-- Concrete-head observation factors through the equation projection and
retains wildcard occurrences, authored order, identity, and multiplicity. -/
def observeHead
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    [DecidableEq Head]
    (head : Head) (state : SpaceState Data Id Head Row) :
    List (EquationOccurrence Id Head Row) :=
  RevisionViewRealizationProduct.observe head (equationProjection state)

/-- Every head observation is invariant under a data-only state change. -/
theorem observeHead_eq_of_sameEquationProjection
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    [DecidableEq Head]
    (head : Head) (left right : SpaceState Data Id Head Row)
    (same : SameEquationProjection left right) :
    observeHead head left = observeHead head right := by
  unfold SameEquationProjection at same
  simp only [observeHead]
  rw [same]

/-- Broad authored-order observation is the complete equation projection. -/
def observeBroad
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (state : SpaceState Data Id Head Row) :
    List (EquationOccurrence Id Head Row) :=
  equationProjection state

/-- The reusable authority key forgets unrelated data while retaining the
complete ordered equation projection. -/
def authorityKey
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (state : SpaceState Data Id Head Row) :
    RevisionKey Unit (List (EquationOccurrence Id Head Row)) where
  store := ()
  revision := equationProjection state

/-- Data-only equivalent states receive the identical reusable-authority key. -/
theorem authorityKey_eq_of_sameEquationProjection
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (left right : SpaceState Data Id Head Row)
    (same : SameEquationProjection left right) :
    authorityKey left = authorityKey right := by
  unfold SameEquationProjection at same
  simp only [authorityKey]
  rw [same]

/-- The global equation key is neither weaker nor stronger than broad
authored-order observation: each determines the other exactly. -/
theorem broad_eq_iff_authorityKey_eq
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (left right : SpaceState Data Id Head Row) :
    observeBroad left = observeBroad right ↔
      authorityKey left = authorityKey right := by
  constructor
  · intro same
    exact authorityKey_eq_of_sameEquationProjection left right same
  · intro same
    exact congrArg RevisionKey.revision same

/-- Once one state has installed a view, a data-only equivalent state reuses
that exact cached value with zero semantic rebuild work. -/
theorem acquire_after_sameEquationProjection_reuses
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    {ViewId : Type uViewId} {ViewRow : Type uViewRow}
    {Code : Type uCode}
    [DecidableEq Id] [DecidableEq Head] [DecidableEq Row]
    (family : SnapshotFamily Unit
      (List (EquationOccurrence Id Head Row)) ViewId ViewRow)
    (compile : ViewRow → Option Code)
    (authority : Authority Unit
      (List (EquationOccurrence Id Head Row)) ViewId ViewRow Code)
    (left right : SpaceState Data Id Head Row)
    (same : SameEquationProjection left right) :
    let first := acquire family compile authority (authorityKey left)
    let second := acquire family compile first.authority (authorityKey right)
    second.kind = .reused ∧
      second.buildCount = 0 ∧ second.lease = first.lease := by
  have keys := authorityKey_eq_of_sameEquationProjection left right same
  simpa [keys] using
    acquire_twice_reuses family compile authority (authorityKey left)

/-- Appending one equation always changes the complete equation key.  This is
the negative boundary which prevents data-only reuse from hiding a newly
authored occurrence. -/
theorem authorityKey_append_equation_ne
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (state : SpaceState Data Id Head Row)
    (occurrence : EquationOccurrence Id Head Row) :
    authorityKey
        ({ state with equations := state.equations ++ [occurrence] }) ≠
      authorityKey state := by
  intro equalKeys
  have equalLengths := congrArg
    (fun key : RevisionKey Unit
        (List (EquationOccurrence Id Head Row)) => key.revision.length)
    equalKeys
  simp [authorityKey, equationProjection] at equalLengths

/-! ## Classified physical publication -/

/-- The physical state carries both the complete revision and the strictly
smaller equation-projection revision. -/
structure RevisionState
    (Data : Type uData) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) where
  logical : SpaceState Data Id Head Row
  fullRevision : Nat
  equationRevision : Nat

/-- A mutation either proves that the equation projection is unchanged,
identifies an equation-relevant transition, or declines to classify an opaque
backend transition.  The latter two constructors intentionally carry no
semantic inequality proof: conservative invalidation is not evidence that two
concrete projections differ. -/
inductive ProjectionClassification
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (before after : SpaceState Data Id Head Row) : Type _ where
  | dataOnly (same : SameEquationProjection before after)
  | equationRelevant
  | opaque

/-- The single publication authority always advances the complete revision.
It advances the equation coordinate for an equation-relevant or opaque
transition, thereby making both conservative classifications explicit. -/
def publish
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row)
    (classification : ProjectionClassification before.logical after) :
    RevisionState Data Id Head Row :=
  { logical := after
    fullRevision := before.fullRevision + 1
    equationRevision :=
      match classification with
      | .dataOnly _ => before.equationRevision
      | .equationRelevant => before.equationRevision + 1
      | .opaque => before.equationRevision + 1 }

structure FullToken where
  lifetime : Nat
  revision : Nat
deriving DecidableEq, Repr

structure EquationToken where
  lifetime : Nat
  revision : Nat
deriving DecidableEq, Repr

def issueFullToken
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row) : FullToken :=
  { lifetime, revision := state.fullRevision }

def issueEquationToken
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row) : EquationToken :=
  { lifetime, revision := state.equationRevision }

def FullToken.Current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : FullToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row) : Prop :=
  token = issueFullToken lifetime state

def EquationToken.Current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : EquationToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row) : Prop :=
  token = issueEquationToken lifetime state

theorem publish_fullRevision_succ
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row)
    (classification : ProjectionClassification before.logical after) :
    (publish before after classification).fullRevision =
      before.fullRevision + 1 := by
  rfl

/-- A data-only publication invalidates a complete-state token while retaining
the exact equation token.  This is the build-broadly/reuse-narrowly law used by
the runtime authority. -/
theorem dataOnly_full_stale_equation_current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row)
    (same : SameEquationProjection before.logical after) :
    ¬ (issueFullToken lifetime before).Current lifetime
        (publish before after (.dataOnly same)) ∧
      (issueEquationToken lifetime before).Current lifetime
        (publish before after (.dataOnly same)) := by
  simp [FullToken.Current, EquationToken.Current, issueFullToken,
    issueEquationToken, publish]

theorem equationRelevant_old_token_not_current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row) :
    ¬ (issueEquationToken lifetime before).Current lifetime
        (publish before after .equationRelevant) := by
  simp [EquationToken.Current, issueEquationToken, publish]

theorem opaque_old_token_not_current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row) :
    ¬ (issueEquationToken lifetime before).Current lifetime
        (publish before after .opaque) := by
  simp [EquationToken.Current, issueEquationToken, publish]

theorem equationToken_rejects_distinct_lifetime
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (before : RevisionState Data Id Head Row)
    {oldLifetime newLifetime : Nat}
    (different : oldLifetime ≠ newLifetime) :
    ¬ (issueEquationToken oldLifetime before).Current newLifetime before := by
  intro current
  apply different
  exact congrArg EquationToken.lifetime current

/-! ## Projection dependencies -/

/-- A physical equation token may additionally depend on the state stamp of
the actual base-prefix chain it observes.  Ordinary spaces use `none`; an
overlay uses `some epoch`.  Unrelated spaces are absent from this coordinate,
so their publications cannot invalidate the token. -/
structure PhysicalEquationToken where
  core : EquationToken
  dependencyEpoch : Option Nat
deriving DecidableEq, Repr

def issuePhysicalEquationToken
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat) : PhysicalEquationToken :=
  { core := issueEquationToken lifetime state, dependencyEpoch }

def PhysicalEquationToken.Current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : PhysicalEquationToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat) : Prop :=
  token = issuePhysicalEquationToken lifetime state dependencyEpoch

/-- Forgetting the base-prefix dependency projects physical currentness to the
local equation token law. -/
theorem physicalEquationToken_current_core
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : PhysicalEquationToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat)
    (current : token.Current lifetime state dependencyEpoch) :
    token.core.Current lifetime state := by
  subst current
  rfl

/-- A data-only local publication preserves a dependent token when its actual
base-prefix authority is unchanged. -/
theorem dataOnly_physical_token_current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row)
    (same : SameEquationProjection before.logical after)
    (dependencyEpoch : Option Nat) :
    (issuePhysicalEquationToken lifetime before dependencyEpoch).Current
      lifetime (publish before after (.dataOnly same)) dependencyEpoch := by
  simp [PhysicalEquationToken.Current, issuePhysicalEquationToken,
    issueEquationToken, publish]

/-- Rewriting an observed base prefix advances its dependency coordinate and
invalidates a dependent token even when the local equation coordinate remains
unchanged. -/
theorem base_prefix_epoch_succ_rejects_physical_token
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime dependencyEpoch : Nat)
    (state : RevisionState Data Id Head Row) :
    ¬ (issuePhysicalEquationToken lifetime state (some dependencyEpoch)).Current
        lifetime state (some (dependencyEpoch + 1)) := by
  simp [PhysicalEquationToken.Current, issuePhysicalEquationToken]

/-- An independent token carries no base-prefix coordinate. -/
theorem independent_physical_token_has_no_dependency
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row) :
    (issuePhysicalEquationToken lifetime state none).Current
      lifetime state none := by
  rfl

/-- The physical world separates the base-prefix chain actually observed by
the token from publications in unrelated spaces. -/
structure DependencyWorld where
  relevantPrefixEpoch : Option Nat
  unrelatedPublicationEpoch : Nat
deriving DecidableEq, Repr

/-- Projection currency deliberately forgets unrelated publications. -/
def dependencyKey (world : DependencyWorld) : Option Nat :=
  world.relevantPrefixEpoch

def issuePhysicalEquationTokenInWorld
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row)
    (world : DependencyWorld) : PhysicalEquationToken :=
  issuePhysicalEquationToken lifetime state (dependencyKey world)

def PhysicalEquationToken.CurrentInWorld
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : PhysicalEquationToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row)
    (world : DependencyWorld) : Prop :=
  token = issuePhysicalEquationTokenInWorld lifetime state world

/-- Changing only an unrelated space leaves projection currency current. -/
theorem unrelated_publication_preserves_physical_token
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row)
    (world : DependencyWorld) (newUnrelatedEpoch : Nat) :
    (issuePhysicalEquationTokenInWorld lifetime state world).CurrentInWorld
      lifetime state
        { world with unrelatedPublicationEpoch := newUnrelatedEpoch } := by
  rfl

/-- Changing the selected base-prefix coordinate is observable at the token
boundary; unrelated coordinates cannot mask it. -/
theorem relevant_prefix_succ_rejects_physical_token
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime prefixEpoch unrelatedEpoch : Nat)
    (state : RevisionState Data Id Head Row) :
    let before : DependencyWorld :=
      { relevantPrefixEpoch := some prefixEpoch
        unrelatedPublicationEpoch := unrelatedEpoch }
    let after : DependencyWorld :=
      { relevantPrefixEpoch := some (prefixEpoch + 1)
        unrelatedPublicationEpoch := unrelatedEpoch }
    ¬ (issuePhysicalEquationTokenInWorld lifetime state before).CurrentInWorld
        lifetime state after := by
  simp [PhysicalEquationToken.CurrentInWorld,
    issuePhysicalEquationTokenInWorld, dependencyKey,
    issuePhysicalEquationToken]

/-! ## Selection and occurrence currency -/

/-- Selection of a callable equation family and the positional evidence used
to name its occurrences have different physical dependencies.  The equation
coordinate preserves selected rows; the prefix coordinate preserves their
authored positions. -/
structure SelectionOccurrenceToken where
  equations : PhysicalEquationToken
  prefixEpoch : Nat
deriving DecidableEq, Repr

def issueSelectionOccurrenceToken
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat) (prefixEpoch : Nat) :
    SelectionOccurrenceToken :=
  { equations := issuePhysicalEquationToken lifetime state dependencyEpoch
    prefixEpoch }

def SelectionOccurrenceToken.Current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : SelectionOccurrenceToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat) (prefixEpoch : Nat) : Prop :=
  token = issueSelectionOccurrenceToken lifetime state dependencyEpoch
    prefixEpoch

/-- A data-only append preserves both the equation family and every existing
occurrence position, so a selection/occurrence token remains current even
though the complete Space revision advances. -/
theorem dataOnly_append_selection_occurrence_token_current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row)
    (same : SameEquationProjection before.logical after)
    (dependencyEpoch : Option Nat) (prefixEpoch : Nat) :
    (issueSelectionOccurrenceToken lifetime before dependencyEpoch
      prefixEpoch).Current lifetime
        (publish before after (.dataOnly same)) dependencyEpoch prefixEpoch := by
  simp [SelectionOccurrenceToken.Current, issueSelectionOccurrenceToken,
    issuePhysicalEquationToken, issueEquationToken, publish]

/-- Rewriting the prefix rejects old positional evidence even when the
equation projection itself remains current. -/
theorem rewritten_prefix_rejects_selection_occurrence_token
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime prefixEpoch : Nat)
    (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat) :
    ¬ (issueSelectionOccurrenceToken lifetime state dependencyEpoch
          prefixEpoch).Current lifetime state dependencyEpoch
          (prefixEpoch + 1) := by
  simp [SelectionOccurrenceToken.Current,
    issueSelectionOccurrenceToken]

/-- An equation-relevant publication rejects the old candidate selection even
when its positional prefix happens not to move. -/
theorem equation_relevant_rejects_selection_occurrence_token
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (lifetime : Nat) (before : RevisionState Data Id Head Row)
    (after : SpaceState Data Id Head Row)
    (dependencyEpoch : Option Nat) (prefixEpoch : Nat) :
    ¬ (issueSelectionOccurrenceToken lifetime before dependencyEpoch
          prefixEpoch).Current lifetime
          (publish before after .equationRelevant) dependencyEpoch
          prefixEpoch := by
  simp [SelectionOccurrenceToken.Current,
    issueSelectionOccurrenceToken, issuePhysicalEquationToken,
    issueEquationToken, publish]

/-- Current selection/occurrence evidence contains a current equation token;
the positional refinement never weakens selection authority. -/
theorem selection_occurrence_current_equation_current
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    (token : SelectionOccurrenceToken) (lifetime : Nat)
    (state : RevisionState Data Id Head Row)
    (dependencyEpoch : Option Nat) (prefixEpoch : Nat)
    (current : token.Current lifetime state dependencyEpoch prefixEpoch) :
    token.equations.Current lifetime state dependencyEpoch := by
  change token = issueSelectionOccurrenceToken lifetime state
    dependencyEpoch prefixEpoch at current
  subst token
  rfl

/-- Counter deltas are the observable receipt of the same classified
publication algebra. -/
structure PublicationDelta where
  full : Nat
  dataOnly : Nat
  equation : Nat
  opaqueMutation : Nat
  equationRevision : Nat
deriving DecidableEq, Repr

def publicationDelta
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    {before after : SpaceState Data Id Head Row}
    (classification : ProjectionClassification before after) :
    PublicationDelta :=
  match classification with
  | .dataOnly _ =>
      { full := 1, dataOnly := 1, equation := 0, opaqueMutation := 0,
        equationRevision := 0 }
  | .equationRelevant =>
      { full := 1, dataOnly := 0, equation := 1, opaqueMutation := 0,
        equationRevision := 1 }
  | .opaque =>
      { full := 1, dataOnly := 0, equation := 0, opaqueMutation := 1,
        equationRevision := 1 }

theorem publicationDelta_full_exact
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    {before after : SpaceState Data Id Head Row}
    (classification : ProjectionClassification before after) :
    (publicationDelta classification).full =
      (publicationDelta classification).dataOnly +
      (publicationDelta classification).equation +
      (publicationDelta classification).opaqueMutation := by
  cases classification <;> rfl

theorem publicationDelta_equation_exact
    {Data : Type uData} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    {before after : SpaceState Data Id Head Row}
    (classification : ProjectionClassification before after) :
    (publicationDelta classification).equationRevision =
      (publicationDelta classification).equation +
      (publicationDelta classification).opaqueMutation := by
  cases classification <;> rfl

namespace Canaries

def exactA : EquationOccurrence Nat Bool Nat :=
  { id := 10, head := some false, payload := 100 }

def wildcard : EquationOccurrence Nat Bool Nat :=
  { id := 11, head := none, payload := 200 }

def exactB : EquationOccurrence Nat Bool Nat :=
  { id := 12, head := some true, payload := 300 }

def before : SpaceState Nat Nat Bool Nat :=
  { data := [1, 2], equations := [exactA, wildcard] }

def afterDataOnly : SpaceState Nat Nat Bool Nat :=
  { data := [9, 8, 7], equations := [exactA, wildcard] }

def afterOtherHead : SpaceState Nat Nat Bool Nat :=
  { data := [1, 2], equations := [exactA, wildcard, exactB] }

def reordered : SpaceState Nat Nat Bool Nat :=
  { data := [1, 2], equations := [wildcard, exactA] }

def revisionBefore : RevisionState Nat Nat Bool Nat :=
  { logical := before, fullRevision := 7, equationRevision := 3 }

/-- Positive: unrelated data can change while the equation authority and every
head observation remain identical. -/
example :
    SameEquationProjection before afterDataOnly ∧
      authorityKey before = authorityKey afterDataOnly ∧
      observeHead false before = observeHead false afterDataOnly := by
  simp [SameEquationProjection, equationProjection, authorityKey,
    observeHead, before, afterDataOnly,
    RevisionViewRealizationProduct.observe]

/-- Positive: exact and wildcard occurrences retain authored order. -/
example : observeHead false before = [exactA, wildcard] := by
  simp [observeHead, equationProjection, before, exactA, wildcard,
    RevisionViewRealizationProduct.observe]

/-- Negative global boundary: appending a different-head equation leaves this
particular head observation unchanged but changes the broad authority key. -/
example :
    observeHead false before = observeHead false afterOtherHead ∧
      authorityKey before ≠ authorityKey afterOtherHead := by
  simp [observeHead, equationProjection, authorityKey, before,
    afterOtherHead, exactA, wildcard, exactB,
    RevisionViewRealizationProduct.observe]

/-- Negative order boundary: equal occurrence support in another order cannot
reuse the global authored-order authority. -/
example : authorityKey before ≠ authorityKey reordered := by
  simp [authorityKey, equationProjection, before, reordered,
    exactA, wildcard]

/-- Negative whole-state boundary: keying by the complete physical state would
reject the lawful data-only reuse proved above. -/
example : before ≠ afterDataOnly ∧
    authorityKey before = authorityKey afterDataOnly := by
  simp [authorityKey, equationProjection, before, afterDataOnly]

/-- Positive physical canary: a data-only publication advances the complete
coordinate but leaves the equation token current. -/
example :
    ¬ (issueFullToken 41 revisionBefore).Current 41
        (publish revisionBefore afterDataOnly
          (.dataOnly (by
            simp [SameEquationProjection, equationProjection,
              revisionBefore, before, afterDataOnly]))) ∧
      (issueEquationToken 41 revisionBefore).Current 41
        (publish revisionBefore afterDataOnly
          (.dataOnly (by
            simp [SameEquationProjection, equationProjection,
              revisionBefore, before, afterDataOnly]))) := by
  apply dataOnly_full_stale_equation_current

/-- Negative physical canary: an equation append rejects the old token. -/
example :
    ¬ (issueEquationToken 41 revisionBefore).Current 41
        (publish revisionBefore afterOtherHead
          .equationRelevant) := by
  apply equationRelevant_old_token_not_current

/-- Positive positional canary: a data-only append retains the narrower
selection/occurrence currency. -/
example :
    (issueSelectionOccurrenceToken 41 revisionBefore none 9).Current 41
      (publish revisionBefore afterDataOnly
        (.dataOnly (by
          simp [SameEquationProjection, equationProjection,
            revisionBefore, before, afterDataOnly]))) none 9 := by
  apply dataOnly_append_selection_occurrence_token_current

/-- Negative positional canary: a rewritten occurrence prefix cannot retain
the old selection/occurrence evidence. -/
example :
    ¬ (issueSelectionOccurrenceToken 41 revisionBefore none 9).Current 41
        revisionBefore none 10 := by
  apply rewritten_prefix_rejects_selection_occurrence_token

/-- Negative conservative boundary: an opaque publisher invalidates even when
the concrete transition happens to preserve the equation projection. -/
example :
    SameEquationProjection revisionBefore.logical afterDataOnly ∧
      ¬ (issueEquationToken 41 revisionBefore).Current 41
          (publish revisionBefore afterDataOnly .opaque) := by
  constructor
  · simp [SameEquationProjection, equationProjection,
      revisionBefore, before, afterDataOnly]
  · exact opaque_old_token_not_current 41 revisionBefore afterDataOnly

end Canaries

#print axioms observeHead_eq_of_sameEquationProjection
#print axioms authorityKey_eq_of_sameEquationProjection
#print axioms broad_eq_iff_authorityKey_eq
#print axioms acquire_after_sameEquationProjection_reuses
#print axioms authorityKey_append_equation_ne
#print axioms dataOnly_full_stale_equation_current
#print axioms equationRelevant_old_token_not_current
#print axioms opaque_old_token_not_current
#print axioms equationToken_rejects_distinct_lifetime
#print axioms physicalEquationToken_current_core
#print axioms dataOnly_physical_token_current
#print axioms base_prefix_epoch_succ_rejects_physical_token
#print axioms independent_physical_token_has_no_dependency
#print axioms unrelated_publication_preserves_physical_token
#print axioms relevant_prefix_succ_rejects_physical_token
#print axioms dataOnly_append_selection_occurrence_token_current
#print axioms rewritten_prefix_rejects_selection_occurrence_token
#print axioms equation_relevant_rejects_selection_occurrence_token
#print axioms selection_occurrence_current_equation_current
#print axioms publicationDelta_full_exact
#print axioms publicationDelta_equation_exact

end Mettapedia.GSLT.Dynamics.EquationProjectionRevisionAuthority
