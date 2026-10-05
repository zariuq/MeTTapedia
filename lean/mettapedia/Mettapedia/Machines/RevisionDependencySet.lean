import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.BindingPublication
import Mathlib.Data.Finset.Image
import Mettapedia.Machines.LinkedScopeStack
import Mettapedia.Machines.Cursor.OwnedLifecycle

/-!
# Finite dependencies on revision-scoped store occurrences

A derived result may depend on exact logical occurrences from several stores.
The occurrence identity retains store, revision, and logical position; a finite
dependency set records which of those identities must remain current.

Validity is local.  Environments that agree on the stores named by a
dependency set give the same validity judgment.  Updating an unrelated store
therefore preserves validity, while changing the revision of any named store
invalidates every dependency on the old revision.

This is a source-validity contract, not a cache implementation.  Cache
invalidation may use the contract, but deleting or retaining physical entries
is a separate operational decision.
-/

set_option autoImplicit false

namespace Mettapedia.Machines

/-- The current revision selected for every logical store. -/
structure RevisionEnvironment (StoreId Revision : Type) where
  current : StoreId → Revision

namespace RevisionEnvironment

variable {StoreId Revision : Type}

/-- Change the current revision of exactly one store. -/
def update [DecidableEq StoreId]
    (environment : RevisionEnvironment StoreId Revision)
    (store : StoreId) (revision : Revision) :
    RevisionEnvironment StoreId Revision where
  current := Function.update environment.current store revision

/-- Two revision environments agree on a selected finite store support. -/
def AgreesOn [DecidableEq StoreId] (support : Finset StoreId)
    (left right : RevisionEnvironment StoreId Revision) : Prop :=
  ∀ store ∈ support, left.current store = right.current store

theorem agreesOn_refl [DecidableEq StoreId] (support : Finset StoreId)
    (environment : RevisionEnvironment StoreId Revision) :
    AgreesOn support environment environment := by
  intro store _
  rfl

theorem agreesOn_symm [DecidableEq StoreId] {support : Finset StoreId}
    {left right : RevisionEnvironment StoreId Revision}
    (agrees : AgreesOn support left right) :
    AgreesOn support right left := by
  intro store member
  exact (agrees store member).symm

theorem agreesOn_trans [DecidableEq StoreId] {support : Finset StoreId}
    {first second third : RevisionEnvironment StoreId Revision}
    (firstSecond : AgreesOn support first second)
    (secondThird : AgreesOn support second third) :
    AgreesOn support first third := by
  intro store member
  exact (firstSecond store member).trans (secondThird store member)

/-- Complete query results can be revision values in the same captured-read
interface. Filtering retains row order and multiplicity; `Row` may carry a
physical occurrence identity as well as a payload. -/
def matchingRows {Query Row : Type} (accepts : Query → Row → Bool)
    (rows : List Row) : RevisionEnvironment Query (List Row) where
  current query := rows.filter (accepts query)

theorem matchingRows_append {Query Row : Type}
    (accepts : Query → Row → Bool) (rows added : List Row) (query : Query) :
    (matchingRows accepts (rows ++ added)).current query =
      (matchingRows accepts rows).current query ++
        (matchingRows accepts added).current query :=
  List.filter_append rows added

/-- Inserting rows outside every consulted query leaves their complete
readouts unchanged. No global store-revision equality is needed. -/
theorem matchingRows_agrees_of_nonmatching_append {Query Row : Type}
    [DecidableEq Query] (accepts : Query → Row → Bool)
    (rows added : List Row) (support : Finset Query)
    (outside : ∀ query ∈ support, ∀ row ∈ added, accepts query row = false) :
    AgreesOn support (matchingRows accepts rows)
      (matchingRows accepts (rows ++ added)) := by
  intro query consulted
  have empty : added.filter (accepts query) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    simp [outside query consulted row member]
  simp only [matchingRows, List.filter_append, empty, List.append_nil]

/-- A newly matching occurrence changes the complete query result even if
all previously selected row identities and payloads remain present. -/
theorem matchingRows_ne_after_matching_append {Query Row : Type}
    (accepts : Query → Row → Bool) (rows : List Row) (query : Query)
    (row : Row) (matching : accepts query row = true) :
    (matchingRows accepts (rows ++ [row])).current query ≠
      (matchingRows accepts rows).current query := by
  intro equal
  have sameLength := congrArg List.length equal
  simp [matchingRows, List.filter_append, matching] at sameLength

/-- Ordered, short-circuit checks against the captured revisions. The observer
returns both its answer and its actual next state; that state is retained even
when a comparison fails. No observer-purity law is built into this algorithm. -/
def checkObserved {State : Type} [DecidableEq Revision]
    (expected : RevisionEnvironment StoreId Revision)
    (observe : StoreId → State → Revision × State) :
    List StoreId → State → Bool × State
  | [], state => (true, state)
  | store :: rest, state =>
      let sampled := observe store state
      if sampled.1 = expected.current store then
        checkObserved expected observe rest sampled.2
      else (false, sampled.2)

/-- Truthful observations which preserve the complete consulted support make
sequential validation exact. State outside that support may change, including
observer bookkeeping. Protecting only the currently sampled key is weaker. -/
theorem checkObserved_spec {State : Type} [DecidableEq StoreId] [DecidableEq Revision]
    (projection : State → RevisionEnvironment StoreId Revision)
    (observe : StoreId → State → Revision × State)
    (expected : RevisionEnvironment StoreId Revision) (support : Finset StoreId)
    (truthful : ∀ store ∈ support, ∀ state,
      (observe store state).1 = (projection state).current store)
    (stable : ∀ store ∈ support, ∀ state,
      AgreesOn support (projection (observe store state).2) (projection state))
    (stores : List StoreId) (covered : ∀ store ∈ stores, store ∈ support) (state : State) :
    AgreesOn support (projection (checkObserved expected observe stores state).2)
        (projection state) ∧
      ((checkObserved expected observe stores state).1 = true ↔
        AgreesOn stores.toFinset (projection state) expected) := by
  induction stores generalizing state with
  | nil =>
      refine ⟨agreesOn_refl support (projection state), ?_⟩
      simp [checkObserved, AgreesOn]
  | cons store rest ih =>
      have member := covered store List.mem_cons_self
      have read := truthful store member state
      have preserved := stable store member state
      have coveredRest : ∀ other ∈ rest, other ∈ support :=
        fun other present => covered other (List.mem_cons_of_mem store present)
      by_cases compared : (observe store state).1 = expected.current store
      · simp only [checkObserved, compared, ↓reduceIte]
        obtain ⟨after, agreement⟩ := ih coveredRest (observe store state).2
        refine ⟨agreesOn_trans after preserved, ?_⟩
        rw [agreement]
        have firstMatches := read.symm.trans compared
        constructor
        · intro remaining other present
          rcases List.mem_cons.mp (List.mem_toFinset.mp present) with same | later
          · subst other
            exact firstMatches
          · exact (preserved other (coveredRest other later)).symm.trans
              (remaining other (List.mem_toFinset.mpr later))
        · intro all other present
          have later := List.mem_toFinset.mp present
          exact (preserved other (coveredRest other later)).trans
            (all other (List.mem_toFinset.mpr (List.mem_cons_of_mem store later)))
      · simp only [checkObserved, compared, ↓reduceIte]
        refine ⟨preserved, ?_⟩
        constructor
        · intro impossible
          cases impossible
        · intro all
          exact False.elim (compared (read.trans
            (all store (List.mem_toFinset.mpr List.mem_cons_self))))

/-- The same checked run is exact at publication, after all observer effects.
Stability covers earlier reads as well as the last read. -/
theorem checkObserved_accepts_final {State : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (projection : State → RevisionEnvironment StoreId Revision)
    (observe : StoreId → State → Revision × State)
    (expected : RevisionEnvironment StoreId Revision) (stores : List StoreId)
    (truthful : ∀ store ∈ stores.toFinset, ∀ state,
      (observe store state).1 = (projection state).current store)
    (stable : ∀ store ∈ stores.toFinset, ∀ state,
      AgreesOn stores.toFinset (projection (observe store state).2) (projection state))
    (state : State) :
    (checkObserved expected observe stores state).1 = true ↔
      AgreesOn stores.toFinset
        (projection (checkObserved expected observe stores state).2) expected := by
  obtain ⟨after, agreement⟩ := checkObserved_spec projection observe expected stores.toFinset
    truthful stable stores (fun _ member => List.mem_toFinset.mpr member) state
  rw [agreement]
  constructor
  · intro before
    exact agreesOn_trans after before
  · intro final
    exact agreesOn_trans (agreesOn_symm after) final

end RevisionEnvironment

/-- A finite set of exact occurrence identities consulted by a result. -/
abbrev RevisionDependencySet (StoreId Revision : Type) :=
  Finset (StoreOccurrenceId StoreId Revision)

namespace RevisionDependencySet

variable {StoreId Revision : Type}
variable [DecidableEq StoreId] [DecidableEq Revision]

/-- The finite set of stores on which the exact occurrences depend. -/
def storeSupport (dependencies : RevisionDependencySet StoreId Revision) :
    Finset StoreId :=
  dependencies.image fun occurrence => occurrence.read.storeId

/-- Every named occurrence belongs to the revision currently selected for its
store. -/
def ValidAt (environment : RevisionEnvironment StoreId Revision)
    (dependencies : RevisionDependencySet StoreId Revision) : Prop :=
  ∀ occurrence ∈ dependencies,
    environment.current occurrence.read.storeId = occurrence.read.revision

omit [DecidableEq StoreId] [DecidableEq Revision] in
@[simp] theorem validAt_empty
    (environment : RevisionEnvironment StoreId Revision) :
    ValidAt environment ∅ := by
  simp [ValidAt]

omit [DecidableEq StoreId] [DecidableEq Revision] in
@[simp] theorem validAt_singleton_iff
    (environment : RevisionEnvironment StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision) :
    ValidAt environment {occurrence} ↔
      environment.current occurrence.read.storeId =
        occurrence.read.revision := by
  simp [ValidAt]

@[simp] theorem validAt_union_iff
    (environment : RevisionEnvironment StoreId Revision)
    (left right : RevisionDependencySet StoreId Revision) :
    ValidAt environment (left ∪ right) ↔
      ValidAt environment left ∧ ValidAt environment right := by
  constructor
  · intro valid
    constructor
    · intro occurrence member
      exact valid occurrence (Finset.mem_union_left right member)
    · intro occurrence member
      exact valid occurrence (Finset.mem_union_right left member)
  · rintro ⟨leftValid, rightValid⟩ occurrence member
    rcases Finset.mem_union.mp member with leftMember | rightMember
    · exact leftValid occurrence leftMember
    · exact rightValid occurrence rightMember

omit [DecidableEq Revision] in
/-- Revision validity depends only on the current revisions of stores in the
finite support. -/
theorem validAt_iff_of_agreesOn_storeSupport
    {left right : RevisionEnvironment StoreId Revision}
    (dependencies : RevisionDependencySet StoreId Revision)
    (agrees : RevisionEnvironment.AgreesOn
      dependencies.storeSupport left right) :
    ValidAt left dependencies ↔ ValidAt right dependencies := by
  constructor
  · intro valid occurrence member
    have storeMember : occurrence.read.storeId ∈ dependencies.storeSupport :=
      Finset.mem_image.mpr ⟨occurrence, member, rfl⟩
    calc
      right.current occurrence.read.storeId =
          left.current occurrence.read.storeId :=
        (agrees occurrence.read.storeId storeMember).symm
      _ = occurrence.read.revision := valid occurrence member
  · intro valid occurrence member
    have storeMember : occurrence.read.storeId ∈ dependencies.storeSupport :=
      Finset.mem_image.mpr ⟨occurrence, member, rfl⟩
    calc
      left.current occurrence.read.storeId =
          right.current occurrence.read.storeId :=
        agrees occurrence.read.storeId storeMember
      _ = occurrence.read.revision := valid occurrence member

omit [DecidableEq Revision] in
/-- Advancing a store outside the finite support cannot stale the dependency
set. -/
theorem validAt_update_iff_of_not_mem_storeSupport
    (environment : RevisionEnvironment StoreId Revision)
    (dependencies : RevisionDependencySet StoreId Revision)
    (store : StoreId) (revision : Revision)
    (outside : store ∉ dependencies.storeSupport) :
    ValidAt (environment.update store revision) dependencies ↔
      ValidAt environment dependencies := by
  apply validAt_iff_of_agreesOn_storeSupport
  intro observed observedMember
  have different : observed ≠ store := by
    intro equalStore
    subst equalStore
    exact outside observedMember
  simp [RevisionEnvironment.update, different]

omit [DecidableEq Revision] in
/-- Advancing the store of a consulted occurrence to a genuinely different
revision makes the old finite dependency set invalid. -/
theorem not_validAt_update_of_mem
    (environment : RevisionEnvironment StoreId Revision)
    (dependencies : RevisionDependencySet StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision)
    (member : occurrence ∈ dependencies)
    (nextRevision : Revision)
    (changed : nextRevision ≠ occurrence.read.revision) :
    ¬ ValidAt
      (environment.update occurrence.read.storeId nextRevision)
      dependencies := by
  intro valid
  have current := valid occurrence member
  simp [RevisionEnvironment.update] at current
  exact changed current

end RevisionDependencySet

/-! ## Captured read views and sticky invalidation -/

/-- A lookup that disagreed with the value captured at admission. `Revision`
may be an optional binding, so absence is retained as an ordinary value. -/
structure CapturedReadMismatch (StoreId Revision : Type) where
  store : StoreId
  expected : Revision
  actual : Revision
deriving DecidableEq

/-- A complete admitted environment and the names actually consulted in it.
The first observed mismatch is retained even if the live environment is later
restored. Values referred to by a binding keep their own occurrence contracts. -/
structure CapturedReadView (StoreId Revision : Type) where
  captured : RevisionEnvironment StoreId Revision
  consulted : List StoreId
  firstMismatch : Option (CapturedReadMismatch StoreId Revision)
  captureComplete : Bool

namespace CapturedReadView

variable {StoreId Revision : Type}
variable [DecidableEq StoreId] [DecidableEq Revision]

/-- Admit a new view without claiming that it has consulted any store yet. -/
def admit (environment : RevisionEnvironment StoreId Revision) :
    CapturedReadView StoreId Revision :=
  ⟨environment, [], none, true⟩

/-- The ordinary revision-scoped identity of a captured binding. Position zero
names the binding itself; the binding's referenced store has separate positions. -/
def bindingOccurrence (view : CapturedReadView StoreId Revision)
    (store : StoreId) : StoreOccurrenceId StoreId Revision :=
  ⟨⟨store, view.captured.current store⟩, 0⟩

/-- Consultation uses the existing finite dependency contract. Repeated reads
of one binding impose one validity obligation. -/
def dependencies (view : CapturedReadView StoreId Revision) :
    RevisionDependencySet StoreId Revision :=
  view.consulted.toFinset.image view.bindingOccurrence

theorem valid_dependencies_iff (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) :
    RevisionDependencySet.ValidAt live view.dependencies ↔
      RevisionEnvironment.AgreesOn view.consulted.toFinset live view.captured := by
  constructor
  · intro valid store member
    exact valid (view.bindingOccurrence store)
      (Finset.mem_image.mpr ⟨store, member, rfl⟩)
  · intro agrees occurrence member
    obtain ⟨store, storeMember, rfl⟩ := Finset.mem_image.mp member
    exact agrees store storeMember

/-- Only names actually consulted occur in the validity support. -/
theorem dependencies_storeSupport (view : CapturedReadView StoreId Revision) :
    view.dependencies.storeSupport = view.consulted.toFinset := by
  ext store
  simp only [RevisionDependencySet.storeSupport, dependencies, Finset.mem_image]
  constructor
  · rintro ⟨occurrence, ⟨observed, observedMember, rfl⟩, rfl⟩
    exact observedMember
  · intro member
    exact ⟨view.bindingOccurrence store, ⟨store, member, rfl⟩, rfl⟩

/-- Detect a changed binding without replacing its captured value. -/
def mismatchAt (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    Option (CapturedReadMismatch StoreId Revision) :=
  if live.current store = view.captured.current store then none
  else some ⟨store, view.captured.current store, live.current store⟩

omit [DecidableEq StoreId] in
@[simp] theorem mismatchAt_eq_none_iff
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    view.mismatchAt live store = none ↔
      live.current store = view.captured.current store := by
  simp [mismatchAt]

/-- The first mismatch in consultation order. -/
def firstCurrentMismatch (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) :
    List StoreId → Option (CapturedReadMismatch StoreId Revision)
  | [] => none
  | store :: rest => (view.mismatchAt live store).or
      (view.firstCurrentMismatch live rest)

omit [DecidableEq StoreId] in
theorem firstCurrentMismatch_eq_none_iff
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (stores : List StoreId) :
    view.firstCurrentMismatch live stores = none ↔
      ∀ store ∈ stores, live.current store = view.captured.current store := by
  induction stores with
  | nil => simp [firstCurrentMismatch]
  | cons store rest inductionHypothesis =>
    simp [firstCurrentMismatch, inductionHypothesis]

/-- Record a read and retain an already observed mismatch. Returning the
captured value is separate from permission to publish the resulting work. -/
def consult (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    CapturedReadView StoreId Revision where
  captured := view.captured
  consulted := if store ∈ view.consulted then view.consulted
    else view.consulted ++ [store]
  firstMismatch := view.firstMismatch.or (view.mismatchAt live store)
  captureComplete := view.captureComplete

@[simp] theorem consult_preserves_captured
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    (view.consult live store).captured = view.captured := rfl

theorem mem_consulted_consult_iff (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (read observed : StoreId) :
    observed ∈ (view.consult live read).consulted ↔
      observed ∈ view.consulted ∨ observed = read := by
  by_cases member : read ∈ view.consulted
  · simp [consult, member]
    exact fun equality => equality ▸ member
  · simp [consult, member]

/-- A lookup returns the admitted value, including an admitted absence. -/
def read (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    Revision × CapturedReadView StoreId Revision :=
  (view.captured.current store, view.consult live store)

@[simp] theorem read_returns_captured (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    (view.read live store).1 = view.captured.current store := rfl

/-- Resume validation inspects every consulted binding, without rebasing any. -/
def validate (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) :
    CapturedReadView StoreId Revision :=
  { view with firstMismatch :=
      Option.or view.firstMismatch (view.firstCurrentMismatch live view.consulted) }

/-- Publication requires both absence of an earlier observed mismatch and
current validity of the actual finite dependency set. -/
def CanPublish (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) : Prop :=
  view.captureComplete = true ∧ view.firstMismatch = none ∧
    RevisionDependencySet.ValidAt live view.dependencies

/-- Both capture completeness and validation are checked before publication. -/
def accepted (view : CapturedReadView StoreId Revision) : Bool :=
  view.captureComplete && view.firstMismatch.isNone

theorem validate_accepted_iff_canPublish
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) :
    (view.validate live).accepted = true ↔ view.CanPublish live := by
  simp only [accepted, Bool.and_eq_true, Option.isNone_iff_eq_none,
    validate, Option.or_eq_none_iff, CanPublish,
    firstCurrentMismatch_eq_none_iff, valid_dependencies_iff,
    RevisionEnvironment.AgreesOn, List.mem_toFinset]

/-- Ordered native observations discharge the existing publication contract
when they report current revisions and preserve every consulted dependency.
The final state includes their effects; it is not replaced by the entry state. -/
theorem checkObserved_canPublish {State : Type}
    (view : CapturedReadView StoreId Revision)
    (projection : State → RevisionEnvironment StoreId Revision)
    (observe : StoreId → State → Revision × State)
    (complete : view.captureComplete = true) (unpoisoned : view.firstMismatch = none)
    (truthful : ∀ store ∈ view.consulted.toFinset, ∀ state,
      (observe store state).1 = (projection state).current store)
    (stable : ∀ store ∈ view.consulted.toFinset, ∀ state,
      RevisionEnvironment.AgreesOn view.consulted.toFinset
        (projection (observe store state).2) (projection state)) (state : State) :
    (RevisionEnvironment.checkObserved view.captured observe view.consulted state).1 = true ↔
      view.CanPublish (projection
        (RevisionEnvironment.checkObserved view.captured observe view.consulted state).2) := by
  simpa only [CanPublish, complete, unpoisoned, true_and, valid_dependencies_iff] using
    RevisionEnvironment.checkObserved_accepts_final projection observe view.captured
      view.consulted truthful stable state

/-- A recorded mismatch cannot be erased by consultation or later restoration. -/
theorem consult_preserves_mismatch
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId)
    (mismatch : CapturedReadMismatch StoreId Revision)
    (recorded : view.firstMismatch = some mismatch) :
    (view.consult live store).firstMismatch = some mismatch := by
  simp [consult, recorded]

omit [DecidableEq StoreId] in
theorem validate_preserves_mismatch
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision)
    (mismatch : CapturedReadMismatch StoreId Revision)
    (recorded : view.firstMismatch = some mismatch) :
    (view.validate live).firstMismatch = some mismatch := by
  simp [validate, recorded]

/-- Changing an unconsulted binding preserves publication eligibility. -/
theorem canPublish_update_iff_of_not_consulted
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId)
    (revision : Revision) (unconsulted : store ∉ view.consulted) :
    view.CanPublish (live.update store revision) ↔ view.CanPublish live := by
  unfold CanPublish
  rw [RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport]
  simpa [dependencies_storeSupport] using unconsulted

/-- A complete finite binding delta outside the consulted keys preserves
publication eligibility. The delta uses the independently specified binding
publication map; choice metadata and other world components are not erased. -/
theorem canPublish_applyWrites_iff {Value : Type} [DecidableEq Value]
    (view : CapturedReadView StoreId (Option Value))
    (live : RevisionEnvironment StoreId (Option Value)) (writes : List (StoreId × Value))
    (outside : List.Disjoint view.consulted (writes.map Prod.fst)) :
    view.CanPublish ⟨BindingPublication.applyWrites live.current writes⟩ ↔
      view.CanPublish live := by
  unfold CanPublish
  rw [RevisionDependencySet.validAt_iff_of_agreesOn_storeSupport
    (dependencies := view.dependencies)]
  rw [dependencies_storeSupport]
  intro key member
  exact BindingPublication.applyWrites_lookup_of_not_mem live.current writes key
    (List.disjoint_left.mp outside (by simpa using member))

/-- Complete-match and absence reads use the ordinary finite dependency
contract. Rows appended outside every consulted predicate cannot invalidate
the publication of this view. -/
theorem canPublish_nonmatching_append_iff {Row : Type} [DecidableEq Row]
    (accepts : StoreId → Row → Bool) (rows added : List Row)
    (view : CapturedReadView StoreId (List Row))
    (outside : ∀ query ∈ view.consulted.toFinset,
      ∀ row ∈ added, accepts query row = false) :
    view.CanPublish (RevisionEnvironment.matchingRows accepts (rows ++ added)) ↔
      view.CanPublish (RevisionEnvironment.matchingRows accepts rows) := by
  unfold CanPublish
  rw [RevisionDependencySet.validAt_iff_of_agreesOn_storeSupport
    (dependencies := view.dependencies)]
  rw [dependencies_storeSupport]
  exact RevisionEnvironment.agreesOn_symm
    (RevisionEnvironment.matchingRows_agrees_of_nonmatching_append
      accepts rows added view.consulted.toFinset outside)

/-- A phantom matching row invalidates a captured complete read. This
includes a captured absence, whose result list was empty. Merely retaining
the previously selected rows does not justify publication. -/
theorem matching_append_invalidates_complete_read {Row : Type}
    [DecidableEq Row] (accepts : StoreId → Row → Bool) (rows : List Row)
    (query : StoreId) (row : Row) (matching : accepts query row = true) :
    ¬ ((admit (RevisionEnvironment.matchingRows accepts rows)).consult
        (RevisionEnvironment.matchingRows accepts rows) query).CanPublish
      (RevisionEnvironment.matchingRows accepts (rows ++ [row])) := by
  intro allowed
  have agrees := (valid_dependencies_iff _ _).mp allowed.2.2
  have same := agrees query (by simp [consult, admit])
  exact RevisionEnvironment.matchingRows_ne_after_matching_append
    accepts rows query row matching (by simpa [consult, admit] using same)

/-- Nested admission inherits the complete captured environment. It does not
replace an absent binding by a newer live one. Parent publication obligations
remain with the parent. -/
def nested (view : CapturedReadView StoreId Revision) :
    CapturedReadView StoreId Revision :=
  { admit view.captured with captureComplete := view.captureComplete }

@[simp] theorem nested_returns_parent_value
    (view : CapturedReadView StoreId Revision)
    (live : RevisionEnvironment StoreId Revision) (store : StoreId) :
    (view.nested.read live store).1 = view.captured.current store := rfl

end CapturedReadView

/-- A read frame retains its source authority, admitted view and whole
captured computation payload. Lookup may add dependencies but cannot replace
the payload with the ambient caller's bindings or continuation. -/
structure CapturedReadFrame (SourceId StoreId Revision Capture : Type) where
  source : SourceId
  view : CapturedReadView StoreId Revision
  capture : Capture

namespace CapturedReadFrame

variable {FrameId SourceId StoreId Revision Capture : Type}
variable [DecidableEq FrameId] [DecidableEq SourceId]
variable [DecidableEq StoreId] [DecidableEq Revision]

abbrev Table := FrameId → CapturedReadFrame SourceId StoreId Revision Capture
abbrev Observation := Option Revision × Table (FrameId := FrameId)
  (SourceId := SourceId) (StoreId := StoreId) (Revision := Revision) (Capture := Capture)

/-- All matching observers see the live lookup. Only the first matching
observer chooses the value returned to the computation. `some none` can
therefore select an admitted absence when revisions themselves are optional. -/
def observeOne (source : SourceId) (live : RevisionEnvironment StoreId Revision)
    (key : StoreId) (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture))
    (owner : FrameId) : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture) :=
  let frame := state.2 owner
  if frame.source = source then
    (state.1.or (some (frame.view.captured.current key)),
      fun other => if other = owner then
        { frame with view := frame.view.consult live key } else state.2 other)
  else state

/-- The reference interpretation visits the independently specified active
list in order. The table retains inactive frames for subsequent resumption. -/
def observeList (source : SourceId) (live : RevisionEnvironment StoreId Revision)
    (key : StoreId) (active : List FrameId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) :
    Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture) :=
  active.foldl (observeOne source live key) state

/-- The implementation model follows the object's actual predecessor link.
Exhausting this observation budget leaves qualification unfinished. -/
def observeLinks (parent : FrameId → Option FrameId) (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId) :
    Nat → Option FrameId → Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture) →
      Option (Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture))
  | _, none, state => some state
  | 0, some _, _ => none
  | fuel + 1, some owner, state =>
      observeLinks parent source live key fuel (parent owner)
        (observeOne source live key state owner)

theorem observeLinks_of_matches (parent : FrameId → Option FrameId)
    (source : SourceId) (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    {active : List FrameId} (linked : LinkedScopeStack.MatchesLinks parent active)
    (extra : Nat) (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) :
    observeLinks parent source live key (active.length + extra) active.head? state =
      some (observeList source live key active state) := by
  induction active generalizing state with
  | nil => cases extra <;> rfl
  | cons owner rest ih =>
      have fuel : (owner :: rest).length + extra = (rest.length + extra) + 1 := by
        simp only [List.length_cons]
        omega
      rw [fuel]
      simp only [List.head?_cons, observeLinks]
      rw [linked.1, ih linked.2]
      rfl

theorem observeLinks_eq_reference (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    {stack : LinkedScopeStack FrameId} {active : List FrameId}
    (represented : stack.Represents active) (extra : Nat)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) :
    observeLinks stack.parent source live key (active.length + extra) stack.top state =
      some (observeList source live key active state) := by
  rw [represented.top]
  exact observeLinks_of_matches _ _ _ _ represented.links extra state

theorem observeOne_preserves_capture (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner other : FrameId) :
    ((observeOne source live key state owner).2 other).capture = (state.2 other).capture ∧
      ((observeOne source live key state owner).2 other).source = (state.2 other).source ∧
      ((observeOne source live key state owner).2 other).view.captured =
        (state.2 other).view.captured := by
  simp only [observeOne]
  split
  · by_cases equal : other = owner <;> simp [equal, CapturedReadView.consult]
  · exact ⟨rfl, rfl, rfl⟩

theorem observeList_preserves_capture (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId) (active : List FrameId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner : FrameId) :
    ((observeList source live key active state).2 owner).capture = (state.2 owner).capture ∧
      ((observeList source live key active state).2 owner).source = (state.2 owner).source ∧
      ((observeList source live key active state).2 owner).view.captured =
        (state.2 owner).view.captured := by
  induction active generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons first rest ih =>
      have firstLaw := observeOne_preserves_capture source live key state first owner
      have tailLaw := ih (observeOne source live key state first)
      exact ⟨tailLaw.1.trans firstLaw.1, tailLaw.2.1.trans firstLaw.2.1,
        tailLaw.2.2.trans firstLaw.2.2⟩

theorem observeOne_retains_selected (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    (table : Table (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (selected : Revision) :
    (observeOne source live key (some selected, table) owner).1 = some selected := by
  simp only [observeOne]
  split <;> rfl

theorem observeList_retains_selected (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId) (active : List FrameId)
    (table : Table (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (selected : Revision) :
    (observeList source live key active (some selected, table)).1 = some selected := by
  induction active generalizing table with
  | nil => rfl
  | cons owner rest ih =>
      change (observeList source live key rest
        (observeOne source live key (some selected, table) owner)).1 = _
      have chosen := observeOne_retains_selected source live key table owner selected
      rw [← Prod.eta (observeOne source live key (some selected, table) owner)]
      rw [chosen]
      exact ih _

theorem observeOne_preserves_consulted (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key prior : StoreId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner other : FrameId)
    (consulted : prior ∈ (state.2 other).view.consulted) :
    prior ∈ ((observeOne source live key state owner).2 other).view.consulted := by
  simp only [observeOne]
  split
  · by_cases equal : other = owner
    · subst other
      simpa only [↓reduceIte] using
        (CapturedReadView.mem_consulted_consult_iff _ _ _ _).mpr (Or.inl consulted)
    · simpa only [if_neg equal] using consulted
  · exact consulted

theorem observeList_preserves_consulted (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key prior : StoreId) (active : List FrameId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (consulted : prior ∈ (state.2 owner).view.consulted) :
    prior ∈ ((observeList source live key active state).2 owner).view.consulted := by
  induction active generalizing state with
  | nil => exact consulted
  | cons first rest ih =>
      exact ih _ (observeOne_preserves_consulted source live key prior state first owner consulted)

theorem observeOne_marks (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (same : (state.2 owner).source = source) :
    key ∈ ((observeOne source live key state owner).2 owner).view.consulted := by
  simp only [observeOne, same, ↓reduceIte]
  exact (CapturedReadView.mem_consulted_consult_iff _ _ _ _).mpr (Or.inr rfl)

theorem observeList_marks_all_matching (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId) (active : List FrameId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId)
      (StoreId := StoreId) (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (member : owner ∈ active) (same : (state.2 owner).source = source) :
    key ∈ ((observeList source live key active state).2 owner).view.consulted := by
  induction active generalizing state with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst first
        exact observeList_preserves_consulted source live key key rest _ owner
          (observeOne_marks source live key state owner same)
      · have sourceKept := (observeOne_preserves_capture source live key state first owner).2.1
        exact ih _ later (sourceKept.trans same)

theorem observeList_head_value (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    (owner : FrameId) (rest : List FrameId)
    (table : Table (FrameId := FrameId) (SourceId := SourceId) (StoreId := StoreId)
      (Revision := Revision) (Capture := Capture))
    (same : (table owner).source = source) :
    (observeList source live key (owner :: rest) (none, table)).1 =
      some ((table owner).view.captured.current key) := by
  change (observeList source live key rest
    (observeOne source live key (none, table) owner)).1 = _
  simp only [observeOne, same, ↓reduceIte, Option.none_or]
  exact observeList_retains_selected source live key rest _ _

theorem observeOne_other (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId) (StoreId := StoreId)
      (Revision := Revision) (Capture := Capture)) (owner other : FrameId)
    (different : other ≠ owner) :
    (observeOne source live key state owner).2 other = state.2 other := by
  simp only [observeOne]
  split <;> simp [different]

theorem observeList_inactive_unchanged (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId) (active : List FrameId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId) (StoreId := StoreId)
      (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (inactive : owner ∉ active) :
    (observeList source live key active state).2 owner = state.2 owner := by
  induction active generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have different : owner ≠ first := fun same => inactive (List.mem_cons.mpr (Or.inl same))
      have later : owner ∉ rest := fun member => inactive (List.mem_cons_of_mem _ member)
      exact (ih _ later).trans (observeOne_other source live key state first owner different)

section OwnedCapture

open ResourceOwnership Cursor.OwnedLifecycle

variable {Owner Address Value World : Type} [DecidableEq Owner] [DecidableEq Address]

/-- Dependency recording leaves the captured paths unchanged. Publishing
their starting roots before retiring a scope preserves every complete read.
The path projection must cover the runtime's actual strong references. -/
theorem observeList_owned_paths (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId) (active : List FrameId)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId) (StoreId := StoreId)
      (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (paths : Capture → List (Address × List Address))
    (memory : Session Owner Address Value World) (dead : Finset Owner) (output : Owner)
    (outside : output ∉ dead)
    (allocated : ∀ query ∈ paths (state.2 owner).capture, query.1 ∈ memory.heap.allocated) :
    RequestBorrow.observe
      (commit memory dead output ((paths (state.2 owner).capture).map Prod.fst)).heap
      (paths ((observeList source live key active state).2 owner).capture) =
      RequestBorrow.observe memory.heap (paths (state.2 owner).capture) := by
  rw [(observeList_preserves_capture source live key active state owner).1]
  exact commit_preserves_paths memory dead output _ outside allocated

variable {DestinationAddress DestinationValue : Type} [DecidableEq DestinationAddress]

/-- Actual link traversal and independent publication/copying compose. The
destination owns the capture after source-scope retirement; the active read
frames acquire their dependencies without replacing that captured payload. -/
theorem observeLinks_copied_paths (source : SourceId)
    (live : RevisionEnvironment StoreId Revision) (key : StoreId)
    {stack : LinkedScopeStack FrameId} {active : List FrameId}
    (represented : stack.Represents active) (extra : Nat)
    (state : Observation (FrameId := FrameId) (SourceId := SourceId) (StoreId := StoreId)
      (Revision := Revision) (Capture := Capture)) (owner : FrameId)
    (paths : Capture → List (Address × List Address))
    (memory : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation memory.heap destination)
    (dead : Finset Owner) (output : Owner) (outside : output ∉ dead)
    (allocated : ∀ query ∈ paths (state.2 owner).capture, query.1 ∈ memory.heap.allocated) :
    ∃ result,
      observeLinks stack.parent source live key (active.length + extra) stack.top state =
        some result ∧
      (result.2 owner).capture = (state.2 owner).capture ∧
      RequestBorrow.observe
        (commit (relocateSession memory destination copy) dead output
          ((RequestBorrow.relocatePaths copy.address (paths (state.2 owner).capture)).map
            Prod.fst)).heap
        (RequestBorrow.relocatePaths copy.address (paths (result.2 owner).capture)) =
        (RequestBorrow.observe memory.heap (paths (state.2 owner).capture)).map
          (Option.map fun pair =>
            (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := by
  refine ⟨observeList source live key active state,
    observeLinks_eq_reference source live key represented extra state,
    (observeList_preserves_capture source live key active state owner).1, ?_⟩
  rw [(observeList_preserves_capture source live key active state owner).1]
  exact relocate_commit_paths memory destination copy dead output _ outside allocated

end OwnedCapture

namespace Controls

def captured : RevisionEnvironment Nat (Option Nat) :=
  ⟨fun key => if key = 3 then none else some 7⟩

def replaced : RevisionEnvironment Nat (Option Nat) :=
  ⟨fun key => if key = 3 then some 9 else some 7⟩

def frames (owner : Nat) : CapturedReadFrame Nat Nat (Option Nat) (Nat × List Nat) :=
  if owner = 2 then
    ⟨1, CapturedReadView.admit ⟨fun _ => some 99⟩, (22, [4, 4])⟩
  else ⟨0, CapturedReadView.admit captured, (owner, [0, 1])⟩

def observed := observeList 0 replaced 3 [1, 2, 0] (none, frames)

theorem absence_is_selected : observed.1 = some none := by rfl

theorem every_matching_scope_records_absence :
    (observed.2 1).view.consulted = [3] ∧ (observed.2 0).view.consulted = [3] := by
  exact ⟨rfl, rfl⟩

theorem foreign_scope_unchanged : observed.2 2 = frames 2 := by rfl

theorem outer_and_inner_detect_replacement :
    (observed.2 1).view.firstMismatch = some ⟨3, none, some 9⟩ ∧
      (observed.2 0).view.firstMismatch = some ⟨3, none, some 9⟩ := by
  exact ⟨rfl, rfl⟩

theorem observing_only_inner_loses_outer_dependency :
    ((observeOne 0 replaced 3 (none, frames) 1).2 0).view.consulted = [] ∧
      (observed.2 0).view.consulted ≠ [] := by
  exact ⟨rfl, by decide⟩

theorem ambient_replacement_is_not_the_selected_value :
    observed.1 ≠ some (replaced.current 3) := by decide

theorem full_payload_survives (owner : Nat) :
    (observed.2 owner).capture = (frames owner).capture :=
  (observeList_preserves_capture 0 replaced 3 [1, 2, 0] (none, frames) owner).1

open ResourceOwnership Cursor.OwnedLifecycle

def ownedFrames (owner : Nat) :
    CapturedReadFrame Nat Nat (Option Nat) (List (Fin 3 × List (Fin 3))) where
  source := (frames owner).source
  view := (frames owner).view
  capture := if owner = 0 then Cursor.OwnedLifecycle.Examples.capturedPaths else [(1, [2, 1])]

def activeStack : LinkedScopeStack Nat :=
  ((LinkedScopeStack.Controls.empty.enter 0).enter 2).enter 1

theorem activeStack_represents : activeStack.Represents [1, 2, 0] := by
  exact LinkedScopeStack.enter_represents
    (LinkedScopeStack.enter_represents
      (LinkedScopeStack.enter_represents LinkedScopeStack.Controls.empty_represents
        (by simp)) (by simp)) (by simp)

/-- The native-shaped linked traversal selects a captured absence while
both read observers retain their cyclic payload. A copied capture remains
readable after the old owner is cancelled. -/
theorem linked_read_and_retired_capture :
    ∃ result,
      observeLinks activeStack.parent 0 replaced 3 3 activeStack.top
        (none, ownedFrames) = some result ∧
      result.1 = some none ∧
      RequestBorrow.observe
        (commit Cursor.OwnedLifecycle.Examples.copiedCursorSession {0} 7 [1, 1, 1]).heap
        (RequestBorrow.relocatePaths ResourceOwnership.Examples.relocationAddress
          (result.2 0).capture) =
        [some (3, ResourceOwnership.Examples.copiedCell 3),
          some (3, ResourceOwnership.Examples.copiedCell 3), none] := by
  obtain ⟨result, traversed, kept, copied⟩ :=
    observeLinks_copied_paths 0 replaced 3 activeStack_represents 0 (none, ownedFrames) 0
      id Cursor.OwnedLifecycle.Examples.cursorSession ResourceOwnership.Examples.copiedHeap
      ResourceOwnership.Examples.shiftedCopy {0} 7 (by decide)
        (by intro query _; exact Finset.mem_univ query.1)
  refine ⟨result, traversed, ?_, copied⟩
  have reference := observeLinks_eq_reference 0 replaced 3 activeStack_represents 0
    (none, ownedFrames)
  have same := Option.some.inj (traversed.symm.trans reference)
  rw [same]
  rfl

end Controls
end CapturedReadFrame

/-! ## Positive and negative controls -/

namespace RevisionDependencySetCanary

inductive Store where
  | evidence
  | model
  | unrelated
deriving DecidableEq

def environment : RevisionEnvironment Store Nat where
  current
    | .evidence => 7
    | .model => 3
    | .unrelated => 99

def evidenceOccurrence : StoreOccurrenceId Store Nat :=
  ⟨⟨.evidence, 7⟩, 0⟩

def modelOccurrence : StoreOccurrenceId Store Nat :=
  ⟨⟨.model, 3⟩, 4⟩

def dependencies : RevisionDependencySet Store Nat :=
  {evidenceOccurrence, modelOccurrence}

example : RevisionDependencySet.ValidAt environment dependencies := by
  simp [RevisionDependencySet.ValidAt, dependencies, evidenceOccurrence,
    modelOccurrence, environment]

/-- An unrelated store revision leaves the dependency set live. -/
example : RevisionDependencySet.ValidAt
    (environment.update .unrelated 100) dependencies := by
  rw [RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport]
  · simp [RevisionDependencySet.ValidAt, dependencies, evidenceOccurrence,
      modelOccurrence, environment]
  · simp [RevisionDependencySet.storeSupport, dependencies,
      evidenceOccurrence, modelOccurrence]

/-- Advancing a consulted store rejects its old occurrence identity. -/
example : ¬ RevisionDependencySet.ValidAt
    (environment.update .evidence 8) dependencies := by
  apply RevisionDependencySet.not_validAt_update_of_mem
    environment dependencies evidenceOccurrence
  · simp [dependencies]
  · decide

end RevisionDependencySetCanary

namespace AuthorityObservationControls

open RevisionDependencySetCanary (Store environment)

/-- Operational bookkeeping is separate from the three semantic stores. -/
structure State where
  evidence : Nat
  model : Nat
  unrelated : Nat
  cacheTicks : Nat
  deriving DecidableEq

def projection (state : State) : RevisionEnvironment Store Nat where
  current
    | .evidence => state.evidence
    | .model => state.model
    | .unrelated => state.unrelated

def initial : State := ⟨7, 3, 99, 0⟩

def capture : CapturedReadView Store Nat :=
  ((CapturedReadView.admit environment).consult environment .evidence).consult environment .model

/-- The observer does real bookkeeping while keeping the selected meanings. -/
def stableObserve (store : Store) (state : State) : Nat × State :=
  ((projection state).current store, { state with cacheTicks := state.cacheTicks + 1 })

/-- Sampling the second store changes the first store after its successful
comparison. Each returned revision is nevertheless truthful at its own read. -/
def lateObserve (store : Store) (state : State) : Nat × State :=
  ((projection state).current store,
    if store = .model then
      { state with evidence := state.evidence + 1, cacheTicks := state.cacheTicks + 1 }
    else { state with cacheTicks := state.cacheTicks + 1 })

theorem stable_observer_truthful (store : Store) (state : State) :
    (stableObserve store state).1 = (projection state).current store := rfl

theorem stable_observer_preserves_support (sampled : Store) (state : State)
    (support : Finset Store) :
    RevisionEnvironment.AgreesOn support (projection (stableObserve sampled state).2)
      (projection state) := by
  intro store _
  cases store <;> rfl

theorem stable_checks_accept_with_bookkeeping :
    RevisionEnvironment.checkObserved environment stableObserve [.evidence, .model] initial =
      (true, { initial with cacheTicks := 2 }) := rfl

theorem stable_checks_publish :
    capture.CanPublish (projection
      (RevisionEnvironment.checkObserved capture.captured stableObserve capture.consulted initial).2) := by
  apply (CapturedReadView.checkObserved_canPublish capture projection stableObserve rfl rfl
    (fun store _ state => stable_observer_truthful store state)
    (fun store _ state => stable_observer_preserves_support store state _) initial).mp
  rfl

theorem late_observer_truthful (store : Store) (state : State) :
    (lateObserve store state).1 = (projection state).current store := rfl

/-- The late observer even preserves the key it is presently sampling. -/
theorem late_observer_preserves_own_key (store : Store) (state : State) :
    (projection (lateObserve store state).2).current store =
      (projection state).current store := by
  cases store <;> rfl

theorem late_checks_accept_changed_prior_revision :
    RevisionEnvironment.checkObserved environment lateObserve [.evidence, .model] initial =
      (true, { initial with evidence := 8, cacheTicks := 2 }) := rfl

/-- Two successful comparisons do not grant current publication authority
when the second observer invalidates an earlier consulted store. -/
theorem late_checks_cannot_publish :
    ¬ capture.CanPublish (projection
      (RevisionEnvironment.checkObserved capture.captured lateObserve capture.consulted initial).2) := by
  intro allowed
  have current := (CapturedReadView.valid_dependencies_iff _ _).mp allowed.2.2
  have first := current .evidence (by decide)
  change (8 : Nat) = 7 at first
  contradiction

theorem late_observer_violates_consulted_support :
    ¬ RevisionEnvironment.AgreesOn capture.consulted.toFinset
      (projection (lateObserve .model initial).2) (projection initial) := by
  intro stable
  have first := stable .evidence (by decide)
  change (8 : Nat) = 7 at first
  contradiction

end AuthorityObservationControls

namespace CapturedReadViewCanary

open RevisionDependencySetCanary (Store)

def bindings : RevisionEnvironment Store (Option Nat) where
  current
    | .evidence => some 7
    | .model => none
    | .unrelated => some 99

def admitted : CapturedReadView Store (Option Nat) := CapturedReadView.admit bindings

def observed : CapturedReadView Store (Option Nat) :=
  (admitted.consult bindings .evidence).consult bindings .model

/-- A captured absence remains absent during evaluation, despite insertion. -/
theorem insertion_does_not_rebind :
    (admitted.read (bindings.update .model (some 3)) .model).1 = none := rfl

/-- A captured value remains available during evaluation, despite removal. -/
theorem removal_does_not_rebind :
    (admitted.read (bindings.update .evidence none) .evidence).1 = some 7 := rfl

theorem unchanged_reads_can_publish : observed.CanPublish bindings := by
  apply (CapturedReadView.validate_accepted_iff_canPublish observed bindings).mp
  rfl

theorem unrelated_change_can_publish :
    observed.CanPublish (bindings.update .unrelated (some 100)) := by
  rw [CapturedReadView.canPublish_update_iff_of_not_consulted]
  · exact unchanged_reads_can_publish
  · decide

/-- Repeated independent writes preserve both the captured present binding
and the captured absence. -/
theorem independent_delta_can_publish :
    observed.CanPublish ⟨BindingPublication.applyWrites bindings.current
      [(Store.unrelated, 100), (Store.unrelated, 101)]⟩ := by
  apply (CapturedReadView.canPublish_applyWrites_iff observed bindings _ ?_).mpr
    unchanged_reads_can_publish
  simp [observed, admitted, CapturedReadView.consult, CapturedReadView.admit]

theorem insertion_invalidates_consulted_absence :
    ¬ observed.CanPublish (bindings.update .model (some 3)) := by
  intro permitted
  have accepted := (CapturedReadView.validate_accepted_iff_canPublish observed
    (bindings.update .model (some 3))).mpr permitted
  change false = true at accepted
  contradiction

/-- Disjoint child write sets can still conflict with a captured read. The
second delta replaces an absence consulted by the first child. -/
theorem disjoint_write_sets_do_not_preserve_consulted_absence :
    List.Disjoint
        ([(Store.unrelated, (100 : Nat))].map Prod.fst)
        ([(Store.model, (3 : Nat))].map Prod.fst) ∧
      ¬ observed.CanPublish ⟨BindingPublication.applyWrites bindings.current
        [(Store.model, 3)]⟩ := by
  refine ⟨by simp, ?_⟩
  exact insertion_invalidates_consulted_absence

theorem removal_invalidates_consulted_binding :
    ¬ observed.CanPublish (bindings.update .evidence none) := by
  intro permitted
  have accepted := (CapturedReadView.validate_accepted_iff_canPublish observed
    (bindings.update .evidence none)).mpr permitted
  change false = true at accepted
  contradiction

def sawReplacement : CapturedReadView Store (Option Nat) :=
  admitted.consult (bindings.update .evidence (some 8)) .evidence

/-- Restoration does not erase the fact that a read already saw a mismatch. -/
theorem restored_binding_does_not_clear_mismatch :
    (sawReplacement.validate bindings).firstMismatch =
      some ⟨Store.evidence, some 7, some 8⟩ := rfl

theorem restored_binding_cannot_publish : ¬ sawReplacement.CanPublish bindings := by
  intro permitted
  have mismatch := permitted.2.1
  change some (⟨Store.evidence, some 7, some 8⟩ :
    CapturedReadMismatch Store (Option Nat)) = none at mismatch
  contradiction

/-- A nested admission inherits absence from the parent's complete world. -/
theorem nested_absence_is_inherited :
    (admitted.nested.read (bindings.update .model (some 3)) .model).1 = none := rfl

/-- A dropped capture obligation cannot acquire publication permission merely
because the bindings which were recorded happen to match. -/
theorem incomplete_capture_cannot_publish :
    ¬ ({ observed with captureComplete := false }).CanPublish bindings := by
  intro permitted
  exact Bool.false_ne_true permitted.1

theorem nested_incomplete_capture_stays_incomplete :
    ({ observed with captureComplete := false }).nested.captureComplete = false := rfl

/-- Rows carry an occurrence number separately from their value. -/
def queryRows : List (Nat × Nat) := [(0, 7), (1, 8)]

def acceptsValue (query : Nat) (row : Nat × Nat) : Bool := row.2 == query

def observedQuery (query : Nat) : CapturedReadView Nat (List (Nat × Nat)) :=
  let environment := RevisionEnvironment.matchingRows acceptsValue queryRows
  (CapturedReadView.admit environment).consult environment query

theorem unchanged_query_can_publish (query : Nat) :
    (observedQuery query).CanPublish
      (RevisionEnvironment.matchingRows acceptsValue queryRows) := by
  apply (CapturedReadView.validate_accepted_iff_canPublish _ _).mp
  simp [observedQuery, CapturedReadView.validate, CapturedReadView.accepted,
    CapturedReadView.consult, CapturedReadView.admit,
    CapturedReadView.mismatchAt, CapturedReadView.firstCurrentMismatch]

/-- A write outside the consulted predicate need not serialize this reader. -/
theorem nonmatching_insertion_can_publish :
    (observedQuery 7).CanPublish
      (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(2, 8)])) := by
  apply (CapturedReadView.canPublish_nonmatching_append_iff
    acceptsValue queryRows [(2, 8)] (observedQuery 7) ?_).mpr
      (unchanged_query_can_publish 7)
  simp [observedQuery, CapturedReadView.consult, CapturedReadView.admit,
    acceptsValue]

/-- An equal payload is still a new matching physical occurrence. -/
theorem duplicate_payload_invalidates_complete_query :
    ¬ (observedQuery 7).CanPublish
      (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(2, 7)])) := by
  exact CapturedReadView.matching_append_invalidates_complete_read
    acceptsValue queryRows 7 (2, 7) (by decide)

/-- The same read contract detects insertion into a previously empty result. -/
theorem matching_insertion_invalidates_absence :
    ¬ (observedQuery 9).CanPublish
      (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(3, 9)])) := by
  exact CapturedReadView.matching_append_invalidates_complete_read
    acceptsValue queryRows 9 (3, 9) (by decide)

example : (RevisionEnvironment.matchingRows acceptsValue queryRows).current 9 = [] := rfl

example : (RevisionEnvironment.matchingRows acceptsValue
    (queryRows ++ [(2, 7)])).current 7 = [(0, 7), (2, 7)] := rfl

end CapturedReadViewCanary

#print axioms RevisionDependencySet.validAt_iff_of_agreesOn_storeSupport
#print axioms RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport
#print axioms RevisionDependencySet.not_validAt_update_of_mem

end Mettapedia.Machines
