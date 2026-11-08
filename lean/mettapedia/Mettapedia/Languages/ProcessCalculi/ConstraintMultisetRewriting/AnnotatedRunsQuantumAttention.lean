import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantum
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeGather
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeControls

/-!
# Attention with phase: routes that cancel, and a commit guard that never reports dark falsely

## Routes as causal histories

Attention spreads to an atom along routes; each route is a causal history of the unfolding whose
firings carry amplitudes. The attention an atom receives is the record-respecting readout of the
routes that reach it (`branchReadout`).

* **Two unrecorded routes out of phase cancel** (`QuietPair.routes_cancel`): the route `first`
  takes the token and makes the answer `20`; the route `quiet` does the same and also checks a
  trivially true equation. They are two causal histories that reach one configuration class, so
  nothing records which route was taken. With amplitudes `1` and `-1` the readout is `0`, against
  an incoherent `2`.
* **Recorded routes do not** (`Recorded.recorded_branch_counted_as_interfering`): R27's superposed
  alternatives make the answers `20` and `21`, so their ends differ and each made row is a record.
  `AnnotatedRunsAmplitudeControls` certifies a cancellation there, because `Z_Q` adds the two
  amplitudes; the record-respecting readout is `2`.

## The attention verdict

`attentionVerdict` is `dark` only when the frontier is closed, the routes reach one end
(`OneEnd`) and their amplitudes cancel; it is `undecided` at an open frontier, and otherwise it
reports the record-respecting weight.

* **Sound** (`dark_sound`): a dark verdict means a closed frontier, a readout of `0` over every
  terminal causal history, and routes that carry weight.
* **Never dark from an incomplete gather** (`never_dark_of_open`), **never dark for recorded
  routes that carry weight** (`recorded_never_dark`).
* Controls: the quiet pair is dark (`QuietPair.quiet_dark`); the superposed alternatives are not
  (`Recorded.superposed_not_dark`); the staged superposition, whose partial paths cancel at depth
  budget `1`, is undecided there (`Staged.partial_undecided`).

## The commit guard

* `attentionCollection` is complete only at a closed frontier whose routes reach one end. Its
  status row travels with its gathered rows (R33's `statusGatherFiring`), and the commit is R33's
  certified cancellation guard reading that row.
* **Never dark from an incomplete or recorded gather** (`commit_refused_of_incomplete`): after a
  status gather of an attention collection that is not complete, the commit is refused at every
  cut.
* **Sound when complete** (`commit_iff_dark`, `commit_sound`): after a status gather of a complete
  attention collection into an empty region, the commit fires exactly when the attention verdict
  is dark, and then the record-respecting readout is `0`.
* **A client inserting a path refuses the commit** (`commit_refuses_insertion`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

namespace Attention

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open MeTTaCalculus.OccurrenceCommits (regionOf)
open AnnotatedRunUnfolding (CausalClass)
open AnnotatedRunBranchCollection (terminalBranches Closed Collection)
open WorldModelRuns (GuardBits)

universe uT uS uO

/-! ## The attention verdict -/

section Verdict

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)
variable (catalogue : List (Firing T S O)) (budget : ℕ) (root : Configuration T O)
  (Q : ConfigurationClass A O → Prop)

/-- **No record separates the routes**: every causal history that ends in `Q` reaches one
configuration class. -/
def OneEnd : Prop :=
  ∃ e : ConfigurationClass A O, ∀ trace ∈ regionBranches A label catalogue budget root Q,
    classEnd A label root trace = e

/-- The verdict of an attention guard. -/
inductive Verdict where
  | dark
  | lit (weight : ℚ)
  | undecided

open Classical in
/-- **The attention verdict**: `dark` only at a closed frontier whose routes reach one end and
cancel; `undecided` at an open frontier; otherwise the record-respecting weight. -/
noncomputable def attentionVerdict : Verdict :=
  if Closed A label catalogue budget root then
    if OneEnd A label catalogue budget root Q ∧
        Destructive (branchAmplitudes A label amp catalogue budget root Q) then .dark
    else .lit (branchReadout A label amp catalogue budget root Q)
  else .undecided

open Classical in
/-- **The attention collection**: complete only at a closed frontier whose routes reach one
end. -/
noncomputable def attentionCollection : Collection Amplitude :=
  if Closed A label catalogue budget root ∧ OneEnd A label catalogue budget root Q then
    .complete (branchAmplitudes A label amp catalogue budget root Q)
  else .incomplete (branchAmplitudes A label amp catalogue budget root Q)

variable {catalogue budget root Q}

theorem attentionVerdict_dark_iff :
    attentionVerdict A label amp catalogue budget root Q = .dark ↔
      Closed A label catalogue budget root ∧ OneEnd A label catalogue budget root Q ∧
        Destructive (branchAmplitudes A label amp catalogue budget root Q) := by
  classical
  unfold attentionVerdict
  by_cases closed : Closed A label catalogue budget root
  · by_cases certified : OneEnd A label catalogue budget root Q ∧
        Destructive (branchAmplitudes A label amp catalogue budget root Q)
    · rw [if_pos closed, if_pos certified]
      exact ⟨fun _ => ⟨closed, certified⟩, fun _ => rfl⟩
    · simp only [if_pos closed, if_neg certified, reduceCtorEq, false_iff]
      exact fun both => certified both.2
  · simp only [if_neg closed, reduceCtorEq, false_iff]
    exact fun both => closed both.1

/-- **Never dark from an incomplete collection**: at an open frontier the verdict is
undecided, whatever the partial paths. -/
theorem never_dark_of_open (open_ : ¬ Closed A label catalogue budget root) :
    attentionVerdict A label amp catalogue budget root Q = .undecided := by
  classical
  unfold attentionVerdict
  rw [if_neg open_]

/-- **A dark verdict is sound**: the frontier is closed, the record-respecting readout of the
routes is `0` over every terminal causal history, and the routes carry weight. -/
theorem dark_sound (dark : attentionVerdict A label amp catalogue budget root Q = .dark) :
    Closed A label catalogue budget root ∧
      branchReadout A label amp catalogue budget root Q = 0 ∧
      0 < incoherent (branchAmplitudes A label amp catalogue budget root Q) := by
  obtain ⟨closed, ⟨e, shared⟩, cancels⟩ := (attentionVerdict_dark_iff A label amp).mp dark
  have nonempty : (regionBranches A label catalogue budget root Q).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro empty
    have positive := cancels.2
    unfold branchAmplitudes at positive
    rw [empty] at positive
    simp at positive
  refine ⟨closed, ?_, cancels.2⟩
  rw [branchReadout_of_one_end A label amp nonempty shared, regionalAmplitude_eq_coherent,
    cancels.1, born_zero]

/-- **Recorded routes that carry weight are never dark.** -/
theorem recorded_never_dark
    (recorded : Set.InjOn (classEnd A label root)
      (regionBranches A label catalogue budget root Q))
    (weighted : 0 < incoherent (branchAmplitudes A label amp catalogue budget root Q)) :
    attentionVerdict A label amp catalogue budget root Q ≠ .dark := fun dark => by
  have zero := (dark_sound A label amp dark).2.1
  rw [branchReadout_of_recorded A label amp recorded] at zero
  rw [zero] at weighted
  exact lt_irrefl _ weighted

theorem attentionCollection_eq_complete_iff (bag : Multiset Amplitude) :
    attentionCollection A label amp catalogue budget root Q = .complete bag ↔
      Closed A label catalogue budget root ∧ OneEnd A label catalogue budget root Q ∧
        bag = branchAmplitudes A label amp catalogue budget root Q := by
  classical
  unfold attentionCollection
  by_cases certified : Closed A label catalogue budget root ∧
      OneEnd A label catalogue budget root Q
  · rw [if_pos certified]
    constructor
    · intro same
      cases same
      exact ⟨certified.1, certified.2, rfl⟩
    · rintro ⟨-, -, rfl⟩
      rfl
  · rw [if_neg certified]
    constructor
    · intro same
      cases same
    · rintro ⟨closed, oneEnd, -⟩
      exact absurd ⟨closed, oneEnd⟩ certified

end Verdict

/-! ## The commit guard -/

section Commit

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)
variable {status bits : GuardBits A} {pathRow : Amplitude → T} {paths : List Amplitude}
  {rows : List O} {s : O} {row : Amplitude → T} {region : T → Bool}
variable {T' : Type uT} {S' : Type uS} {O' : Type uO} [DecidableEq O']
variable {A' : SubstitutionAction T' S'} {label' : O' → T'} {amp : Firing T' S' O' → Amplitude}
  {catalogue : List (Firing T' S' O')} {budget : ℕ} {root : Configuration T' O'}
  {Q : ConfigurationClass A' O' → Prop}

/-- **Never dark from an incomplete or recorded gather**: after a status gather of an attention
collection that is not complete, the commit is refused at every cut, whatever the gathered paths. -/
theorem commit_refused_of_incomplete {found : Multiset Amplitude}
    (incomplete : attentionCollection A' label' amp catalogue budget root Q = .incomplete found)
    {C : Configuration T O}
    (valid : (statusGatherFiring A status (attentionCollection A' label' amp catalogue budget root Q)
      pathRow paths rows s).Valid A label C)
    {seen : Finset O} {r : O} {D : Configuration T O} :
    ¬ (certifiedCancellationFiring A label wave status bits row region seen s r).Valid A label D := by
  rw [incomplete] at valid
  exact statusGather_incomplete_refused A label wave valid

/-- **Sound when complete**: after a status gather of a complete attention collection into an
empty region, the commit fires exactly when the attention verdict is dark. -/
theorem commit_iff_dark {bag : Multiset Amplitude}
    (complete : attentionCollection A' label' amp catalogue budget root Q = .complete bag)
    (listed : (paths : Multiset Amplitude) = bag) {C : Configuration T O}
    (valid : (statusGatherFiring A status (.complete bag) pathRow paths rows s).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths)
    (outside : region status.yes = false) {r : O}
    (fresh : r ∉ ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
      label C).present)
    (rowEq : label r = row 0)
    (consistent : A.Consistent (((statusGatherFiring A status (.complete bag) pathRow paths rows
      s).result label C).equations ++ [(status.yes, label s)])) :
    (certifiedCancellationFiring A label wave status bits row region
        (regionOf label ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
          label C).present region) s r).Valid A label
        ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result label C) ↔
      attentionVerdict A' label' amp catalogue budget root Q = .dark := by
  obtain ⟨closed, oneEnd, same⟩ :=
    (attentionCollection_eq_complete_iff A' label' amp bag).mp complete
  have amplitudeComplete :
      amplitudeCollection A' label' amp catalogue budget root Q = .complete bag :=
    (amplitudeCollection_eq_complete_iff A' label' amp catalogue budget root Q bag).mpr
      ⟨closed, same⟩
  rw [statusGather_complete_iff A label wave amplitudeComplete listed valid empty encodes outside
    fresh rowEq consistent, certifiesCancellation_iff, attentionVerdict_dark_iff]
  exact ⟨fun ⟨closed', cancels⟩ => ⟨closed', oneEnd, cancels⟩,
    fun ⟨closed', _, cancels⟩ => ⟨closed', cancels⟩⟩

/-- **A commit that fires certifies darkness**: the record-respecting readout of the routes is `0`
over every terminal causal history, and the routes carry weight. -/
theorem commit_sound {bag : Multiset Amplitude}
    (complete : attentionCollection A' label' amp catalogue budget root Q = .complete bag)
    (listed : (paths : Multiset Amplitude) = bag) {C : Configuration T O}
    (valid : (statusGatherFiring A status (.complete bag) pathRow paths rows s).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths)
    (outside : region status.yes = false) {r : O}
    (fresh : r ∉ ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
      label C).present)
    (rowEq : label r = row 0)
    (consistent : A.Consistent (((statusGatherFiring A status (.complete bag) pathRow paths rows
      s).result label C).equations ++ [(status.yes, label s)]))
    (commits : (certifiedCancellationFiring A label wave status bits row region
        (regionOf label ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
          label C).present region) s r).Valid A label
        ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result label C)) :
    branchReadout A' label' amp catalogue budget root Q = 0 ∧
      0 < incoherent (branchAmplitudes A' label' amp catalogue budget root Q) := by
  have dark := (commit_iff_dark A label wave complete listed valid empty encodes outside fresh
    rowEq consistent).mp commits
  exact (dark_sound A' label' amp dark).2

/-- **A client inserting a path into the region refuses the commit**: the commit saw the region
whole, so a path arriving there is seen again at the new cut. -/
theorem commit_refuses_insertion {seen : Finset O} {r : O} {C : Configuration T O}
    (commits : (certifiedCancellationFiring A label wave status bits row region seen s r).Valid
      A label C) {o : O} (absent : o ∉ C.present) (inRegion : region (label o) = true) :
    ¬ (certifiedCancellationFiring A label wave status bits row region seen s r).Valid A label
      ⟨C.equations, C.present ∪ {o}⟩ :=
  query_refuses_arrival A label commits (query := ⟨region, seen⟩) (List.mem_singleton_self _)
    absent inRegion

end Commit

/-! ## Two unrecorded routes out of phase -/

namespace QuietPair

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run zeros)
open AnnotatedRunBranchCollection.Controls.Superpose (root first first_valid)
open AmplitudeControls (everything regionBranches_everything single_class_injective
  refused_of_absent)
open AnnotatedRunUnfolding (mem_frontier)
open AnnotatedRunBranchCollection (mem_terminalBranches)

/-- **A second route to the same state**: like `first`, it takes the token and makes the answer
`20`; it also checks an equation that always holds. -/
def quiet : Run :=
  ⟨⟨[.const 9], [], [], [.equal (.const 2) (.const 2)], [.const 2]⟩, [], ⟨[9], [], [20]⟩⟩

/-- The two routes. -/
def routes : List Run := [first, quiet]

theorem quiet_valid : quiet.Valid A label root := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, ?_⟩, by simp [quiet]⟩
  · intro equation member
    have same : equation = (.const 9, label 9) := by
      simpa [Selection.problem, Selection.equations, root, quiet] using member
    subst same
    rfl
  · intro check member σ _
    have same : check = .equal (.const 2) (.const 2) := by simpa [quiet] using member
    subst same
    rfl

/-- **Both routes leave the same configuration.** -/
theorem quiet_result : quiet.result label root = first.result label root := rfl

theorem routes_gone : ∀ f ∈ routes, ¬ f.Valid A label (first.result label root) := by
  intro f member
  simp only [routes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact refused_of_absent (o := 9) (by simp [first]) (by decide)
  · exact refused_of_absent (o := 9) (by simp [quiet]) (by decide)

theorem one_route {g : Run} (covered : ∀ f ∈ [g], f ∈ routes) : g = first ∨ g = quiet := by
  simpa [routes] using covered g (List.mem_singleton_self g)

theorem routes_closed : Closed A label routes 1 root := by
  intro word member
  obtain ⟨length, _, covered⟩ := (mem_frontier A label routes 1 root word).mp member
  rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
  · simp at length
  · rcases one_route covered with rfl | rfl
    · exact routes_gone
    · exact routes_gone
  · simp only [List.length_cons] at length
    omega

open Classical in
theorem routes_branches :
    terminalBranches A label routes 1 root = {Quot.mk _ [first], Quot.mk _ [quiet]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, _, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
    · exact absurd first_valid (terminal first (by simp [routes]))
    · rcases one_route covered with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simp only [List.length_cons] at length
      omega
  · rintro (rfl | rfl)
    · exact ⟨[first], by simp, ⟨first_valid, first_valid.firing.consistent⟩, by simp [routes],
        routes_gone, rfl⟩
    · exact ⟨[quiet], by simp, ⟨quiet_valid, quiet_valid.firing.consistent⟩, by simp [routes],
        routes_gone, rfl⟩

theorem first_ne_quiet : first ≠ quiet := fun same => by
  have checks := congrArg (fun f : Run => f.rule.checks) same
  simp [first, quiet] at checks

/-- **The routes are two causal histories.** -/
theorem routes_distinct :
    (Quot.mk _ [first] : CausalClass A label root) ≠ Quot.mk _ [quiet] := fun same =>
  first_ne_quiet (single_class_injective same)

/-- **No record separates them**: both reach one configuration class. -/
theorem routes_same_end :
    classEnd A label root (Quot.mk _ [first]) = classEnd A label root (Quot.mk _ [quiet]) := rfl

/-- The route `first` carries `1`, the route `quiet` carries `e^{iπ} = -1`. -/
def phase (f : Run) : Amplitude := if f.rule.checks.isEmpty then 1 else -1

theorem phase_first : phase first = 1 := by simp [phase, first]

theorem phase_quiet : phase quiet = -1 := by simp [phase, quiet]

open Classical in
theorem routes_paths (amp : Run → Amplitude) :
    branchAmplitudes A label amp routes 1 root everything = {amp first, amp quiet} := by
  unfold branchAmplitudes
  rw [regionBranches_everything, routes_branches,
    Finset.insert_val_of_notMem (by simpa using routes_distinct), Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude]

open Classical in
theorem routes_one_end : OneEnd A label routes 1 root everything := by
  refine ⟨classEnd A label root (Quot.mk _ [first]), fun trace member => ?_⟩
  rw [regionBranches_everything, routes_branches, Finset.mem_insert, Finset.mem_singleton]
    at member
  rcases member with rfl | rfl
  · rfl
  · exact routes_same_end.symm

/-- **Two unrecorded routes out of phase cancel.** The record-respecting readout is `0`, the Born
weight of `Z_Q = 0`, against an incoherent `2`; it is the incoherent weight plus the cross term
`interference 1 (-1) = -2`. -/
theorem routes_cancel :
    branchAmplitudes A label phase routes 1 root everything = {1, -1} ∧
      regionalAmplitude A label phase routes 1 root everything = 0 ∧
      branchReadout A label phase routes 1 root everything = 0 ∧
      incoherent (branchAmplitudes A label phase routes 1 root everything) = 2 ∧
      branchReadout A label phase routes 1 root everything =
        incoherent (branchAmplitudes A label phase routes 1 root everything) +
          interference (classAmplitude A label phase root (Quot.mk _ [first]))
            (classAmplitude A label phase root (Quot.mk _ [quiet])) := by
  classical
  have bag : branchAmplitudes A label phase routes 1 root everything = {1, -1} := by
    rw [routes_paths, phase_first, phase_quiet]
  have regional : regionalAmplitude A label phase routes 1 root everything = 0 := by
    rw [regionalAmplitude_eq_coherent, bag]
    exact opposite_phase_control.2.2.1
  have inFirst : (Quot.mk _ [first] : CausalClass A label root) ∈
      regionBranches A label routes 1 root everything := by
    rw [regionBranches_everything, routes_branches]
    exact Finset.mem_insert_self _ _
  have inQuiet : (Quot.mk _ [quiet] : CausalClass A label root) ∈
      regionBranches A label routes 1 root everything := by
    rw [regionBranches_everything, routes_branches]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have readout : branchReadout A label phase routes 1 root everything = 0 := by
    obtain ⟨e, shared⟩ := routes_one_end
    rw [branchReadout_of_one_end A label phase ⟨_, inFirst⟩ shared, regional, born_zero]
  refine ⟨bag, regional, readout, by rw [bag]; exact opposite_phase_control.2.1, ?_⟩
  refine branchReadout_unrecorded_pair A label phase inFirst inQuiet routes_distinct
    routes_same_end ?_
  rw [regionBranches_everything, routes_branches, Finset.erase_insert_of_ne routes_distinct,
    Finset.erase_singleton]
  intro x inX y inY _
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.notMem_empty, or_false] at inX inY
  rw [inX, inY]

/-- **The attention verdict of the quiet pair is dark.** -/
theorem quiet_dark : attentionVerdict A label phase routes 1 root everything = .dark := by
  refine (attentionVerdict_dark_iff A label phase).mpr ⟨routes_closed, routes_one_end, ?_⟩
  rw [routes_cancel.1]
  exact opposite_phase_control.2.2

end QuietPair

/-! ## Recorded routes: a recorded branch counted as interfering -/

namespace Recorded

open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)
open AnnotatedRunBranchCollection.Controls.Superpose (root first second alternatives branches)
open AmplitudeControls (everything regionBranches_everything)
open AmplitudeControls.Superposed (shifted superposed_cancel)

/-- **The superposed alternatives end in different configuration classes**: their made rows,
`20` and `21`, are records. -/
theorem superposed_ends_differ :
    classEnd A label root (Quot.mk _ [first]) ≠ classEnd A label root (Quot.mk _ [second]) := by
  intro same
  have present := (Quotient.exact same).2
  have firstPresent : (first.result label root).present = {20} := by decide
  have secondPresent : (second.result label root).present = {21} := by decide
  change (first.result label root).present = (second.result label root).present at present
  rw [firstPresent, secondPresent] at present
  exact absurd present (by decide)

theorem superposed_recorded :
    Set.InjOn (classEnd A label root) (regionBranches A label alternatives 1 root everything) := by
  rw [regionBranches_everything, branches]
  intro x inX y inY same
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at inX inY
  rcases inX with rfl | rfl <;> rcases inY with rfl | rfl
  · rfl
  · exact absurd same superposed_ends_differ
  · exact absurd same.symm superposed_ends_differ
  · rfl

/-- **A recorded branch counted as interfering.** The complete collection of the superposed
alternatives certifies a cancellation, because `Z_Q` adds the amplitudes `1` and `-1` of branches
with different ends; the record-respecting readout is their incoherent weight `2`. -/
theorem recorded_branch_counted_as_interfering :
    CertifiesCancellation (amplitudeCollection A label shifted alternatives 1 root everything) ∧
      born (regionalAmplitude A label shifted alternatives 1 root everything) = 0 ∧
      branchReadout A label shifted alternatives 1 root everything = 2 := by
  refine ⟨superposed_cancel.2.2.2.2.1, ?_, ?_⟩
  · rw [superposed_cancel.2.1, born_zero]
  · rw [branchReadout_of_recorded A label shifted superposed_recorded]
    exact superposed_cancel.2.2.1

/-- **The attention verdict of the superposed alternatives is not dark.** -/
theorem superposed_not_dark :
    attentionVerdict A label shifted alternatives 1 root everything ≠ .dark :=
  recorded_never_dark A label shifted superposed_recorded
    (by rw [superposed_cancel.2.2.1]; norm_num)

end Recorded

/-! ## An incomplete collection whose partial paths cancel -/

namespace Staged

open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)
open AnnotatedRunBranchCollection.Controls.Superpose (root)
open AmplitudeControls (everything)
open AmplitudeControls.Superposed (shifted)
open AmplitudeControls.Staged (staged partial_cancellation_not_certified)

/-- **The staged superposition is undecided at depth budget `1`**, though its partial paths cancel;
at budget `2` the frontier is closed and the certified amplitude is `1`. -/
theorem partial_undecided :
    attentionVerdict A label shifted staged 1 root everything = .undecided ∧
      Destructive {1, -1} ∧
      certifiedAmplitude (amplitudeCollection A label shifted staged 2 root everything) = some 1 :=
  ⟨never_dark_of_open A label shifted partial_cancellation_not_certified.1,
    partial_cancellation_not_certified.2.2.1, partial_cancellation_not_certified.2.2.2.2.2.2⟩

end Staged

end Attention

end AmplitudeRuns

open AmplitudeRuns.Attention

#print axioms attentionVerdict_dark_iff
#print axioms never_dark_of_open
#print axioms dark_sound
#print axioms recorded_never_dark
#print axioms attentionCollection_eq_complete_iff
#print axioms commit_refused_of_incomplete
#print axioms commit_iff_dark
#print axioms commit_sound
#print axioms commit_refuses_insertion
#print axioms QuietPair.quiet_valid
#print axioms QuietPair.routes_closed
#print axioms QuietPair.routes_branches
#print axioms QuietPair.routes_distinct
#print axioms QuietPair.routes_same_end
#print axioms QuietPair.routes_paths
#print axioms QuietPair.routes_one_end
#print axioms QuietPair.routes_cancel
#print axioms QuietPair.quiet_dark
#print axioms Recorded.superposed_ends_differ
#print axioms Recorded.superposed_recorded
#print axioms Recorded.recorded_branch_counted_as_interfering
#print axioms Recorded.superposed_not_dark
#print axioms Staged.partial_undecided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
