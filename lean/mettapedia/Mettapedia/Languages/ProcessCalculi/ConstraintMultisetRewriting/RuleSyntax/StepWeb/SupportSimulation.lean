import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes

/-!
# From a bag store to its set support: a stuttering simulation for propagation rules

Two step constructions over first-order terms at one frame, each named by its five choices.

* **The one-match step of a program** (`RuleSyntax.step`). Store: a bag of labelled occurrences, so
  one row may be present several times, with the knowledge kept beside it; made rows are opened
  terms, which the knowledge relates to the rows the firing read. Commit: one match. Guards: asked at
  every solution of the firing's information, its own tells included. Rules: a fixed set beside the
  store. Knowledge: one equation store, keeping every equation a firing adds.
* **The one-match set step** (`SetStoreSyntax.DisciplinedStep .one timing`). Store: a finite set of
  rows, with the knowledge solved into them: after each step the principal answer is applied to the
  rows and the equations are erased. Commit: one match (a bag of matches with one member). Guards:
  after the tells or before them (`timing`). Rules: a fixed set beside the store. Knowledge: one
  store.

For rules that `Propagates` (no takes, no tells, equation guards only, made and checked unknowns
bound by reads) the two guard timings agree, so the constructions differ in the store alone. On
ground rows the one-match set step is the step of the set store's propagation closure
(`SetStoreClosure.Step`) of the program's ground instances (`one_step_iff_closure`). The results
below are stated for the closure step at every universe, and for the one-match set step at the
universe where the set-store disciplines are defined (terms in `Type`).

## The support map

`support s` reads the present rows of a bag state through the principal answer of its knowledge:
the set store's own readout `SetStore.support`, at the answer the solver returns. It forgets how many
occurrences carry a row and which identities they have. A state is **settled** (`Settled`) when its
knowledge is consistent and grounds every present row; ground seeds are settled
(`settled_of_ground`). On a settled state every solution of the knowledge reads the rows as the
support (`support_eq_of_models`, `readings_eq`), so the support does not depend on the solver.

## What is shown, for programs whose rules all `Propagates`

* **The ground instance of a firing** (`firingMatch`): an admitted bag firing at a settled state,
  read through any solution of its information, is a ground instance enabled at the support, and the
  support after the firing is the support with its made rows (`firing_support`).
* **Forward stuttering simulation** (`forward_step_closure`, `forward_step`): every bag step from a
  settled state reaches a settled state; its support is unchanged or it is a set step from the old
  support. The support is unchanged exactly when every row the firing makes is already in it
  (`stutter_iff`).
* **Backward lifting** (`lift_match`, `backward_step_closure`, `backward_step`): given a numbering of
  the unknowns (`slots`), every set step from the support of a settled state is a ground instance
  whose firing, with any fresh made identities and an opening in a name space of unknowns the state
  does not use, is a bag step reaching that set. Two read patterns may select one occurrence (the
  step asks distinct occurrences only of the taken and the made ones), so one occurrence of a row
  serves every read of it: reads do not separate the bag store from the set store; takes and counts
  do.
* **Runs** (`forward_run_closure`, `forward_run`, `backward_run_closure`, `backward_run`): bag runs
  map to set runs with the stutters absorbed; given `slots` and infinitely many occurrence
  identities, set runs lift to bag runs. A joint set step, of any bag of matches and so of any
  declared discipline, is a closure run, its members fired one after another
  (`closure_run_of_joint`), so joint set runs lift as well (`backward_run_joint`): from a settled
  state the bag store and the set store reach the same rows (`reachable_iff`).
* **Outcomes.** A bag state is **completed** (`Completed`) when no bag step changes its support. A
  settled state with a closed support is completed (`completed_of_closed`). Given `slots` and
  infinitely many occurrence identities: a settled state is completed exactly when its support is
  closed (`completed_iff_closed`), and exactly when its support is terminal for the one-match set
  step (`completed_iff_terminal`); every bag step keeps it completed (`completed_of_step`); the
  support of a completed bag outcome is the least closure of the seed's support
  (`completed_support_eq_closure`), and it agrees with the terminal outcome of every declared
  set-store discipline, through `completed_outcomes_agree` (`completed_outcome_eq`, which also asks
  that discipline's own hypotheses: a finite list covering the program, determinacy for `unique`).
  Completed bag outcomes exist under a finite closed carrier (`exists_completed`).
* **Terminal bag states and divergence**, given `slots` and infinitely many identities. A settled bag
  state has no step at all exactly when no ground instance is enabled at its support (`stuck_iff`).
  Wherever one is enabled the bag store has an infinite run (`diverges`), while under a finite closed
  carrier the set store has none (`SetStoreClosure.no_infinite_run`). So the outcomes of the bag store
  are its completed states, and the simulation is blind to divergence.

## What is not shown

* Rules that take: the support map is then no simulation (`SupportControls`).
* Counts: the support forgets multiplicities, and count and none guards are outside `Propagates`
  (`SupportControls` shows a count guard separating the two stores).
* States that are not settled; any correspondence that preserves divergence; a joint set step as
  one bag step (one bag step makes the rows of one match).

The two supplies are needed: with one occurrence identity, or with one unknown, a state can be
completed while its support is not closed (`SupportControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Support

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings
open SetStoreSyntax
open LogicOverTheStep.StepSpan (Succ)

universe uOcc

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {O : Type uOcc} [DecidableEq O] {P : Program (Terms (Term signature))}

/-! ## The support of a bag state -/

/-- **The support of a bag state**: its present rows read through the principal answer of its
knowledge, by the set store's readout `SetStore.support`. Inconsistent knowledge reads no rows. -/
noncomputable def support (s : State (Terms (Term signature)) O) : Finset (Term signature) :=
  match unifyTotal s.knowledge with
  | some answer => SetStore.support X (a := PUnit.unit) s answer
  | none => ∅

/-- **A settled bag state**: its knowledge is consistent and its principal answer grounds every
present row. -/
def Settled (s : State (Terms (Term signature)) O) : Prop :=
  ∃ answer : Subst signature, unifyTotal s.knowledge = some answer ∧
    ∀ o ∈ s.present, (answer.applyTerm (s.label o)).isGround

/-- A term that the principal answer grounds is read the same way by every solution. -/
theorem fixed_of_principal {store : EquationStore (Term signature)} {answer σ : Subst signature}
    (accepted : unifyTotal store = some answer)
    (solves : (FirstOrder.action signature).Models σ store) {t : Term signature}
    (ground : (answer.applyTerm t).isGround) : σ.applyTerm t = answer.applyTerm t := by
  obtain ⟨residual, factors⟩ :=
    (FirstOrder.accepted_principal store answer accepted).factors σ solves
  have factor : σ.applyTerm t = (residual.comp answer).applyTerm t := factors t
  rw [factor, Subst.applyTerm_comp, FirstOrder.ground_fixed residual _ ground]

omit [DecidableEq O] in
theorem support_eq {s : State (Terms (Term signature)) O} {answer : Subst signature}
    (accepted : unifyTotal s.knowledge = some answer) :
    support s = s.present.image fun o => answer.applyTerm (s.label o) := by
  simp only [support, accepted]
  rfl

omit [DecidableEq O] in
/-- **The support of a settled state, read through any solution of its knowledge.** -/
theorem support_eq_of_models {s : State (Terms (Term signature)) O} (settled : Settled s)
    {σ : Subst signature} (solves : (FirstOrder.action signature).Models σ s.knowledge) :
    support s = s.present.image fun o => σ.applyTerm (s.label o) := by
  obtain ⟨answer, accepted, ground⟩ := settled
  rw [support_eq accepted]
  exact Finset.image_congr fun o inside =>
    (fixed_of_principal accepted solves (ground o inside)).symm

omit [DecidableEq O] in
theorem support_ground {s : State (Terms (Term signature)) O} (settled : Settled s) :
    GroundRows (support s) := by
  obtain ⟨answer, accepted, ground⟩ := settled
  intro value inside
  rw [support_eq accepted] at inside
  obtain ⟨o, present, rfl⟩ := Finset.mem_image.mp inside
  exact ground o present

omit [DecidableEq O] in
/-- **Ground seeds are settled.** -/
theorem settled_of_ground {s : State (Terms (Term signature)) O}
    (consistent : (FirstOrder.action signature).Consistent s.knowledge)
    (ground : ∀ o ∈ s.present, (s.label o).isGround) : Settled s := by
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent s.knowledge).mpr consistent
  refine ⟨answer, accepted, fun o inside => ?_⟩
  rw [FirstOrder.ground_fixed answer _ (ground o inside)]
  exact ground o inside

omit [DecidableEq O] in
/-- **The support of a ground seed is the set of its labels.** -/
theorem support_of_ground {s : State (Terms (Term signature)) O}
    (consistent : (FirstOrder.action signature).Consistent s.knowledge)
    (ground : ∀ o ∈ s.present, (s.label o).isGround) : support s = s.present.image s.label := by
  obtain ⟨σ, solves⟩ := consistent
  rw [support_eq_of_models (settled_of_ground ⟨σ, solves⟩ ground) solves]
  exact Finset.image_congr fun o inside => FirstOrder.ground_fixed σ _ (ground o inside)

omit [DecidableEq O] in
/-- **The support is the one reading of a settled state's rows**: every solution of its knowledge
reads its labelled rows as its support. -/
theorem readings_eq {s : State (Terms (Term signature)) O} (settled : Settled s) :
    SetStore.readings s.knowledge (s.present.image s.label) = {support s} := by
  ext values
  constructor
  · rintro ⟨σ, solves, rfl⟩
    rw [Set.mem_singleton_iff, support_eq_of_models settled solves, Finset.image_image]
    rfl
  · rintro rfl
    obtain ⟨answer, accepted, -⟩ := id settled
    refine ⟨answer, unifyTotal_sound _ _ accepted, ?_⟩
    rw [support_eq accepted, Finset.image_image]
    rfl

/-! ## The ground instance a bag firing performs -/

section Firing

variable {s : State (Terms (Term signature)) O} (f : Firing O (E (signature := signature)) P s.frame)

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] [DecidableEq O] in
theorem row_eq (o : O) : f.row X s o = s.label o := Subst.applyTerm_id _

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] [DecidableEq O] in
theorem knowledge_part :
    X.applyStore ((E (signature := signature)).weaken f.ext) s.knowledge = s.knowledge :=
  Interface.Frames.applyStore_id (X := X) s.knowledge

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] [DecidableEq O] in
/-- A solution of a firing's information solves the knowledge of its state. -/
theorem models_knowledge {τ : Subst signature}
    (solved : X.Models (b := PUnit.unit) τ (f.information X s)) :
    (FirstOrder.action signature).Models τ s.knowledge := by
  intro e inside
  have whole : e ∈ f.information X s := by
    unfold Firing.information
    rw [knowledge_part f]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ inside))
  exact solved e whole

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] [DecidableEq O] in
theorem opened_read_pair {term : Term signature} {o : O}
    (pair : (term, o) ∈ f.rule.body.read.zip f.selection.read) :
    (f.opening.applyTerm term, o) ∈ (f.opened X).read.zip f.selection.read := by
  change (f.opening.applyTerm term, o) ∈
    (f.rule.body.read.map f.opening.applyTerm).zip f.selection.read
  rw [List.zip_map_left]
  exact List.mem_map.mpr ⟨(term, o), pair, rfl⟩

omit [DecidableEq O] in
/-- **A read through a solution**: the opened read pattern takes the reading of its selected row. -/
theorem read_value {answer τ : Subst signature} (accepted : unifyTotal s.knowledge = some answer)
    (solved : X.Models (b := PUnit.unit) τ (f.information X s)) {term : Term signature} {o : O}
    (pair : (term, o) ∈ f.rule.body.read.zip f.selection.read)
    (ground : (answer.applyTerm (s.label o)).isGround) :
    (τ.comp f.opening).applyTerm term = answer.applyTerm (s.label o) := by
  have equal : τ.applyTerm (f.opening.applyTerm term) = τ.applyTerm (f.row X s o) :=
    f.read_solved (X := X) solved (opened_read_pair f pair)
  rw [row_eq] at equal
  rw [Subst.applyTerm_comp, equal]
  exact fixed_of_principal accepted (models_knowledge f solved) ground

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] [DecidableEq O] in
/-- Without takes and tells, the information is solved by the knowledge and the read equations. -/
theorem models_of_reads (noTake : f.rule.body.take = []) (noTell : f.rule.body.tell = [])
    {τ : Subst signature} (known : (FirstOrder.action signature).Models τ s.knowledge)
    (reads : ∀ x ∈ f.rule.body.read.zip f.selection.read,
      τ.applyTerm (f.opening.applyTerm x.1) = τ.applyTerm (s.label x.2)) :
    X.Models (b := PUnit.unit) τ (f.information X s) := by
  have takes : (f.opened X).take = [] := by
    change f.rule.body.take.map _ = []
    rw [noTake, List.map_nil]
  have tells : (f.opened X).tell = [] := by
    change f.rule.body.tell.map _ = []
    rw [noTell, List.map_nil]
  intro e inside
  unfold Firing.information at inside
  rw [knowledge_part f, takes, tells] at inside
  rcases List.mem_append.mp inside with inside | inTell
  · rcases List.mem_append.mp inside with inside | inRead
    · rcases List.mem_append.mp inside with inKnown | inTake
      · exact known e inKnown
      · simp [Firing.matching] at inTake
    · unfold Firing.matching at inRead
      rw [← List.map_uncurry_zip_eq_zipWith] at inRead
      obtain ⟨⟨opened, o⟩, pair, rfl⟩ := List.mem_map.mp inRead
      change (opened, o) ∈ (f.rule.body.read.map f.opening.applyTerm).zip f.selection.read at pair
      rw [List.zip_map_left] at pair
      obtain ⟨⟨term, o'⟩, pair', same⟩ := List.mem_map.mp pair
      simp only [Prod.map, id, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have value := reads _ pair'
      change τ.applyTerm _ = τ.applyTerm (f.row X s _)
      rw [row_eq]
      exact value
  · cases inTell

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
theorem present_of_read (admitted : f.Admits X s) {term : Term signature} {o : O}
    (pair : (term, o) ∈ f.rule.body.read.zip f.selection.read) : o ∈ s.present :=
  admitted.2.1.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip pair).2)

/-- **The ground instance a bag firing performs**: its rule, with its unknowns read through a
solution of the firing's information. -/
def firingMatch (pure : ∀ rule ∈ P, Propagates rule) (settled : Settled s)
    (admitted : f.Admits X s) (τ : Subst signature)
    (solved : X.Models (b := PUnit.unit) τ (f.information X s)) : GroundMatch P where
  rule := f.rule
  member := f.member
  propagates := pure f.rule f.member
  assignment := τ.comp f.opening
  groundReads term inside := by
    obtain ⟨answer, accepted, ground⟩ := settled
    obtain ⟨o, pair⟩ := SetStore.zip_left admitted.1.2.2.2.2.1 inside
    rw [read_value f accepted solved pair (ground o (present_of_read f admitted pair))]
    exact ground o (present_of_read f admitted pair)
  checked left right inside := by
    have holds := (admitted.2.2.2 PUnit.unit τ solved).1
      (Check.equal (f.opening.applyTerm left) (f.opening.applyTerm right))
      (List.mem_map.mpr ⟨Check.equal left right, inside, rfl⟩)
    change τ.applyTerm (f.opening.applyTerm left) = τ.applyTerm (f.opening.applyTerm right) at holds
    simpa only [Subst.applyTerm_comp] using holds

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem taken_nil (pure : ∀ rule ∈ P, Propagates rule) (admitted : f.Admits X s) :
    f.selection.taken = [] := by
  have lengths := admitted.1.2.2.2.1
  rw [(pure f.rule f.member).noTake, List.length_nil] at lengths
  exact List.eq_nil_of_length_eq_zero lengths.symm

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
/-- **A firing keeps every present occurrence and adds its made identities.** -/
theorem result_present (pure : ∀ rule ∈ P, Propagates rule) (admitted : f.Admits X s) :
    (f.result X s).present = s.present ∪ f.selection.made.toFinset := by
  change (s.present \ f.selection.taken.toFinset) ∪ f.selection.made.toFinset = _
  rw [taken_nil f pure admitted, List.toFinset_nil, Finset.sdiff_empty]

/-- The readout of a firing's result at any instantiation, by the tree's `SetStore.support_result`. -/
theorem support_result_at (pure : ∀ rule ∈ P, Propagates rule) (admitted : f.Admits X s)
    (τ : Subst signature) :
    SetStore.support X (a := PUnit.unit) (f.result X s) τ =
      (s.present.image fun o => τ.applyTerm (s.label o)) ∪
        (f.rule.body.produce.map (τ.comp f.opening).applyTerm).toFinset := by
  have raw := SetStore.support_result X (a := PUnit.unit) s (Bag.single f)
    ((Bag.single_admits_iff X s f).mpr admitted) τ
  rw [Bag.single_result] at raw
  simp only [Bag.single] at raw
  rw [Bag.selection_single, Bag.produce_single] at raw
  have restated : SetStore.support X (a := PUnit.unit) (f.result X s) τ =
      (s.present \ f.selection.taken.toFinset).image
          (fun o => τ.applyTerm ((Subst.id signature).applyTerm (s.label o))) ∪
        (f.rule.body.produce.map f.opening.applyTerm).toFinset.image τ.applyTerm := raw
  rw [restated, taken_nil f pure admitted, List.toFinset_nil, Finset.sdiff_empty]
  simp only [Subst.applyTerm_id]
  congr 1
  ext value
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Subst.applyTerm_comp]
  constructor
  · rintro ⟨_, ⟨t, inside, rfl⟩, rfl⟩
    exact ⟨t, inside, rfl⟩
  · rintro ⟨t, inside, rfl⟩
    exact ⟨_, ⟨t, inside, rfl⟩, rfl⟩

/-- **A bag step from a settled state reaches a settled state.** -/
theorem result_settled (pure : ∀ rule ∈ P, Propagates rule) (settled : Settled s)
    (admitted : f.Admits X s) : Settled (f.result X s) := by
  obtain ⟨_, τ, solved⟩ := admitted.2.2.1
  obtain ⟨answer', accepted'⟩ :=
    (FirstOrder.accepted_iff_consistent (f.information X s)).mpr ⟨τ, solved⟩
  have solvedAnswer : X.Models (b := PUnit.unit) answer' (f.information X s) :=
    unifyTotal_sound _ _ accepted'
  refine ⟨answer', accepted', fun o inside => ?_⟩
  have member : answer'.applyTerm ((f.result X s).label o) ∈
      SetStore.support X (a := PUnit.unit) (f.result X s) answer' :=
    Finset.mem_image_of_mem (fun o => answer'.applyTerm ((f.result X s).label o)) inside
  rw [support_result_at f pure admitted answer'] at member
  rcases Finset.mem_union.mp member with old | made
  · obtain ⟨p, present, equal⟩ := Finset.mem_image.mp old
    obtain ⟨answer, accepted, ground⟩ := settled
    rw [← equal, fixed_of_principal accepted (models_knowledge f solvedAnswer) (ground p present)]
    exact ground p present
  · exact instance_ground (firingMatch f pure settled admitted answer' solvedAnswer) _ made

/-- **The support after a firing** is the support before, with the rows the firing makes. -/
theorem firing_support (pure : ∀ rule ∈ P, Propagates rule) (settled : Settled s)
    (admitted : f.Admits X s) {τ : Subst signature}
    (solved : X.Models (b := PUnit.unit) τ (f.information X s)) :
    support (f.result X s) =
      support s ∪ (consequence (firingMatch f pure settled admitted τ solved)).made := by
  rw [support_eq_of_models (result_settled f pure settled admitted) solved,
    support_eq_of_models settled (models_knowledge f solved)]
  exact support_result_at f pure admitted τ

/-- **A stutter is a firing whose made rows are already in the support.** -/
theorem stutter_iff (pure : ∀ rule ∈ P, Propagates rule) (settled : Settled s)
    (admitted : f.Admits X s) {τ : Subst signature}
    (solved : X.Models (b := PUnit.unit) τ (f.information X s)) :
    support (f.result X s) = support s ↔
      (consequence (firingMatch f pure settled admitted τ solved)).made ⊆ support s := by
  rw [firing_support f pure settled admitted solved]
  exact Finset.union_eq_left

/-- **The ground instance of a firing is enabled at the support.** -/
theorem firingMatch_enabled (pure : ∀ rule ∈ P, Propagates rule) (settled : Settled s)
    (admitted : f.Admits X s) {τ : Subst signature}
    (solved : X.Models (b := PUnit.unit) τ (f.information X s)) :
    (consequence (firingMatch f pure settled admitted τ solved)).read ⊆ support s := by
  obtain ⟨answer, accepted, ground⟩ := id settled
  intro value inside
  obtain ⟨term, read, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inside)
  obtain ⟨o, pair⟩ := SetStore.zip_left admitted.1.2.2.2.2.1 read
  have present := present_of_read f admitted pair
  rw [support_eq accepted]
  exact Finset.mem_image.mpr
    ⟨o, present, (read_value f accepted solved pair (ground o present)).symm⟩

end Firing

/-! ## The one-match set step is the closure step -/

/-- A ground instance enabled at ground rows, adding a row, is a one-match set step. -/
theorem one_step_of_match (timing : SetStore.AskTiming) {rows : Finset (Term signature)}
    (ground : GroundRows rows) (m : GroundMatch P) (enabled : (consequence m).read ⊆ rows)
    (outside : ¬ (consequence m).made ⊆ rows) :
    DisciplinedStep .one timing P rows (rows ∪ (consequence m).made) := by
  obtain ⟨answer, accepted, nonempty, admitted, changed⟩ :=
    single_progress_witness timing rows ground m enabled outside
  have info : (Bag.single m.firing).information X (SetStore.represent rows) = problem m := by
    simp only [Bag.single]
    rw [Bag.information_single]
    exact firing_information m rows
  have solved : (FirstOrder.action signature).Models answer (problem m) := by
    rw [← info]
    exact unifyTotal_sound _ _ accepted
  have result := lifted_result m rows ground answer solved
  refine ⟨Bag.single m.firing, nonempty, admitted, rfl, answer, accepted, result.symm, ?_⟩
  rwa [result] at changed

/-- A one-match set step from ground rows is an enabled ground instance adding a row. -/
theorem match_of_one_step (pure : ∀ rule ∈ P, Propagates rule) {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} (ground : GroundRows rows)
    (moved : DisciplinedStep .one timing P rows after) :
    ∃ m : GroundMatch P, (consequence m).read ⊆ rows ∧ ¬ (consequence m).made ⊆ rows ∧
      after = rows ∪ (consequence m).made := by
  obtain ⟨⟨⟨⟩, members⟩, -, admitted, one, answer, accepted, rfl, changed⟩ := moved
  have single : members.length = 1 := one
  obtain ⟨member, rfl⟩ := List.length_eq_one_iff.mp single
  have yes := SetStore.admitted_after admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      ((⟨PUnit.unit, [member]⟩ : SetStore.Candidate P).information X (SetStore.represent rows)) :=
    unifyTotal_sound _ _ accepted
  have produce : Bag.produce SetStore.X (⟨PUnit.unit, [member]⟩ : SetStore.Candidate P) =
      (member.firing.opened X).produce :=
    Bag.produce_single SetStore.X member
  have result : SetStore.setResult rows ⟨PUnit.unit, [member]⟩ answer =
      rows ∪ (consequence (settledMember rows ground pure _ yes answer solved member
        (List.mem_singleton_self member))).made := by
    have takes := propagation_no_takes rows pure _ yes
    have fixed : rows.image answer.applyTerm = rows := by
      calc rows.image answer.applyTerm = rows.image id :=
            Finset.image_congr fun term inside =>
              FirstOrder.ground_fixed answer term (ground term inside)
        _ = rows := Finset.image_id
    unfold SetStore.setResult SetStore.update
    rw [takes, List.toFinset_nil, Finset.image_empty, Finset.sdiff_empty, fixed, produce]
    congr 1
    ext value
    change value ∈ (member.rule.body.produce.map member.opening.applyTerm).toFinset.image
        answer.applyTerm ↔
      value ∈ (member.rule.body.produce.map (answer.comp member.opening).applyTerm).toFinset
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Subst.applyTerm_comp]
    constructor
    · rintro ⟨_, ⟨t, inside, rfl⟩, rfl⟩
      exact ⟨t, inside, rfl⟩
    · rintro ⟨t, inside, rfl⟩
      exact ⟨_, ⟨t, inside, rfl⟩, rfl⟩
  refine ⟨_, settledMember_enabled rows ground pure _ yes answer solved member
    (List.mem_singleton_self member), fun inside => changed ?_, result⟩
  rw [result, Finset.union_eq_left.mpr inside]
  exact SetStore.sameRows_refl rows

/-- **The one-match set step of the propagation fragment**: from ground rows, exactly an enabled
ground instance that adds a row. -/
theorem one_step_iff (pure : ∀ rule ∈ P, Propagates rule) {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} (ground : GroundRows rows) :
    DisciplinedStep .one timing P rows after ↔
      ∃ m : GroundMatch P, (consequence m).read ⊆ rows ∧ ¬ (consequence m).made ⊆ rows ∧
        after = rows ∪ (consequence m).made := by
  constructor
  · exact match_of_one_step pure ground
  · rintro ⟨m, enabled, outside, rfl⟩
    exact one_step_of_match timing ground m enabled outside

/-- The closure step of the ground instances adds the made rows of one enabled instance. -/
theorem closure_step_iff {rows after : Finset (Term signature)} :
    SetStoreClosure.Step (consequence (P := P)) rows after ↔
      ∃ m : GroundMatch P, (consequence m).read ⊆ rows ∧ ¬ (consequence m).made ⊆ rows ∧
        after = rows ∪ (consequence m).made := by
  constructor
  · rintro ⟨m, enabled, result, changed⟩
    have union : after = rows ∪ (consequence m).made := by simpa [SetStore.update] using result
    refine ⟨m, enabled, fun inside => changed ?_, union⟩
    rw [union, Finset.union_eq_left.mpr inside]
  · rintro ⟨m, enabled, outside, rfl⟩
    exact ⟨m, enabled, by simp [SetStore.update],
      fun same => outside (Finset.union_eq_left.mp same)⟩

/-- **The one-match set step is the closure step** of the ground propagation instances. -/
theorem one_step_iff_closure (pure : ∀ rule ∈ P, Propagates rule) {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} (ground : GroundRows rows) :
    DisciplinedStep .one timing P rows after ↔
      SetStoreClosure.Step (consequence (P := P)) rows after :=
  (one_step_iff pure ground).trans closure_step_iff.symm

/-- From ground rows, one-match set runs are closure runs. -/
theorem one_run_iff_closure_run (pure : ∀ rule ∈ P, Propagates rule)
    {timing : SetStore.AskTiming} {seed after : Finset (Term signature)} (ground : GroundRows seed) :
    Relation.ReflTransGen (DisciplinedStep .one timing P) seed after ↔
      Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) seed after := by
  constructor
  · intro run
    induction run with
    | refl => exact .refl
    | tail path next ih =>
      exact ih.tail ((one_step_iff_closure pure
        (actual_reachable_ground timing pure ground (disciplined_run_is_run path))).mp next)
  · intro run
    induction run with
    | refl => exact .refl
    | tail path next ih =>
      exact ih.tail ((one_step_iff_closure pure (reachable_ground ground path)).mpr next)

/-- Ground rows are terminal for the one-match set step exactly when they are closed. -/
theorem terminal_one_iff_closed (pure : ∀ rule ∈ P, Propagates rule)
    {timing : SetStore.AskTiming} {rows : Finset (Term signature)} (ground : GroundRows rows) :
    TerminalWith .one timing P rows ↔ SetStoreClosure.Closed (consequence (P := P)) rows := by
  constructor
  · intro terminal m enabled
    by_contra outside
    exact terminal _ (one_step_of_match timing ground m enabled outside)
  · intro closed after moved
    obtain ⟨m, enabled, outside, -⟩ := match_of_one_step pure ground moved
    exact outside (closed m enabled)

/-! ## Forward stuttering simulation -/

/-- **Forward stuttering simulation, one step, closure form.** A bag step from a settled state
reaches a settled state, and its support is unchanged or is a closure step from the old support. -/
theorem forward_step_closure (pure : ∀ rule ∈ P, Propagates rule)
    {s s' : State (Terms (Term signature)) O} (settled : Settled s)
    (moved : Succ (step X O E P).toStep s s') :
    Settled s' ∧ (support s' = support s ∨
      SetStoreClosure.Step (consequence (P := P)) (support s) (support s')) := by
  obtain ⟨f, admitted, rfl⟩ := moved
  replace admitted : f.Admits X s := admitted
  obtain ⟨⟨⟩, τ, solved⟩ := admitted.2.2.1
  refine ⟨result_settled f pure settled admitted, ?_⟩
  change support (f.result X s) = support s ∨
    SetStoreClosure.Step (consequence (P := P)) (support s) (support (f.result X s))
  rw [firing_support f pure settled admitted solved]
  by_cases inside : (consequence (firingMatch f pure settled admitted τ solved)).made ⊆ support s
  · exact Or.inl (Finset.union_eq_left.mpr inside)
  · exact Or.inr (closure_step_iff.mpr ⟨_, firingMatch_enabled f pure settled admitted solved,
      inside, rfl⟩)

/-- **Forward stuttering simulation, one step.** A bag step from a settled state reaches a settled
state, and its support is unchanged or is a one-match set step from the old support. -/
theorem forward_step (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    {s s' : State (Terms (Term signature)) O} (settled : Settled s)
    (moved : Succ (step X O E P).toStep s s') :
    Settled s' ∧ (support s' = support s ∨ DisciplinedStep .one timing P (support s) (support s')) := by
  obtain ⟨settled', same | next⟩ := forward_step_closure pure settled moved
  · exact ⟨settled', Or.inl same⟩
  · exact ⟨settled', Or.inr ((one_step_iff_closure pure (support_ground settled)).mpr next)⟩

/-! ## Backward lifting -/

omit [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] [DecidableEq O] in
/-- Each enabled read finds a present occurrence whose reading is its row. -/
theorem exists_reads {s : State (Terms (Term signature)) O} {answer : Subst signature}
    (assignment : Subst signature) :
    ∀ patterns : List (Term signature),
      (∀ p ∈ patterns, ∃ o ∈ s.present, answer.applyTerm (s.label o) = assignment.applyTerm p) →
      ∃ reads : List O, reads.length = patterns.length ∧ ∀ x ∈ patterns.zip reads,
        x.2 ∈ s.present ∧ answer.applyTerm (s.label x.2) = assignment.applyTerm x.1
  | [], _ => ⟨[], rfl, fun x inside => by simp at inside⟩
  | p :: rest, found => by
      obtain ⟨o, present, value⟩ := found p List.mem_cons_self
      obtain ⟨reads, length, each⟩ :=
        exists_reads assignment rest fun q inside => found q (List.mem_cons_of_mem _ inside)
      refine ⟨o :: reads, by rw [List.length_cons, length, List.length_cons], fun x inside => ?_⟩
      rw [List.zip_cons_cons] at inside
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨present, value⟩
      · exact each x later

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] [DecidableEq O] in
/-- **A name space of unknowns that a state does not use.** -/
theorem exists_unused (slots : signature.vars ≃ ℕ) (s : State (Terms (Term signature)) O) :
    ∃ index : ℕ, ∀ t, s.Mentions t → ∀ v ∈ t.freeVars, (Nat.unpair (slots v)).1 ≠ index := by
  obtain ⟨index, outside⟩ := Infinite.exists_notMem_finset
    (((varsIn (s.knowledge.map Prod.fst) ∪ varsIn (s.knowledge.map Prod.snd)) ∪
      s.present.biUnion fun o => (s.label o).freeVars).image fun v => (Nat.unpair (slots v)).1)
  refine ⟨index, fun t mentioned v inside same => outside (Finset.mem_image.mpr ⟨v, ?_, same⟩)⟩
  rcases mentioned with known | known | ⟨o, present, rfl⟩
  · exact Finset.mem_union_left _
      (Finset.mem_union_left _ ((mem_variables _ v).mpr ⟨t, known, inside⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ ((mem_variables _ v).mpr ⟨t, known, inside⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨o, present, inside⟩)

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] [DecidableEq O] in
/-- **An opening into an unused name space is fresh**, by the tree's name-space combination. -/
theorem namespace_fresh (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O}
    {index : ℕ} (unused : ∀ t, s.Mentions t → ∀ v ∈ t.freeVars, (Nat.unpair (slots v)).1 ≠ index)
    (f : Firing O (E (signature := signature)) P s.frame)
    (opened : f.opening = FirstOrderFreshFamily.opening slots index) : f.Fresh X s := by
  intro b g h
  cases b
  refine ⟨FirstOrderFreshFamily.combine slots fun space slot =>
      if space = index then h slot else g (namespaceMap slots space slot),
    fun t mentioned => ?_, fun t _ => ?_⟩
  · change (FirstOrderFreshFamily.combine slots fun space slot =>
        if space = index then h slot else g (namespaceMap slots space slot)).applyTerm
          ((Subst.id signature).applyTerm t) = g.applyTerm t
    rw [Subst.applyTerm_id]
    apply apply_eq_of_agree
    intro v inside
    show (if (Nat.unpair (slots v)).1 = index then h (slots.symm (Nat.unpair (slots v)).2)
      else g (namespaceMap slots (Nat.unpair (slots v)).1 (slots.symm (Nat.unpair (slots v)).2))) =
        g v
    rw [if_neg (unused t mentioned v inside)]
    simp [namespaceMap]
  · change (FirstOrderFreshFamily.combine slots fun space slot =>
        if space = index then h slot else g (namespaceMap slots space slot)).applyTerm
          (f.opening.applyTerm t) = h.applyTerm t
    rw [opened]
    refine (FirstOrderFreshFamily.combine_opening slots _ index t).trans ?_
    have same : (fun slot => if index = index then h slot else g (namespaceMap slots index slot)) = h :=
      funext fun _ => if_pos rfl
    exact congrArg (fun σ : Subst signature => σ.applyTerm t) same

/-- **Backward lifting of a ground instance.** An instance enabled at the support of a settled state
fires there, opened in an unused name space and with any fresh made identities, and the support after
it is the support with its made rows. -/
theorem lift_match (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) (m : GroundMatch P)
    (enabled : (consequence m).read ⊆ support s) (made : List O) (nodup : made.Nodup)
    (fresh : Disjoint made.toFinset s.present) (length : m.rule.body.produce.length = made.length) :
    ∃ f : Firing O (E (signature := signature)) P s.frame, f.rule = m.rule ∧
      f.selection.made = made ∧ f.Admits X s ∧ Settled (f.result X s) ∧
      support (f.result X s) = support s ∪ (consequence m).made := by
  obtain ⟨answer, accepted, ground⟩ := id settled
  have found : ∀ p ∈ m.rule.body.read, ∃ o ∈ s.present,
      answer.applyTerm (s.label o) = m.assignment.applyTerm p := by
    intro p inside
    have member := enabled (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, inside, rfl⟩))
    rw [support_eq accepted] at member
    exact Finset.mem_image.mp member
  obtain ⟨reads, readLength, each⟩ := exists_reads m.assignment m.rule.body.read found
  obtain ⟨index, unused⟩ := exists_unused slots s
  let f : Firing O (E (signature := signature)) P s.frame :=
    ⟨m.rule, m.member, PUnit.unit, FirstOrderFreshFamily.opening slots index, ⟨[], reads, made⟩, []⟩
  have isFresh : f.Fresh X s := namespace_fresh slots unused f rfl
  obtain ⟨u, onState, onRule⟩ := isFresh PUnit.unit answer m.assignment
  have uState : ∀ t, s.Mentions t → u.applyTerm t = answer.applyTerm t := by
    intro t mentioned
    have value := onState t mentioned
    change u.applyTerm ((Subst.id signature).applyTerm t) = answer.applyTerm t at value
    rwa [Subst.applyTerm_id] at value
  have uRule : ∀ t ∈ m.rule.terms, u.applyTerm (f.opening.applyTerm t) = m.assignment.applyTerm t :=
    fun t inside => onRule t inside
  have readTerm : ∀ p ∈ m.rule.body.read, p ∈ m.rule.terms := by
    intro p inside
    simp [Rule.terms, inside]
  have produceTerm : ∀ p ∈ m.rule.body.produce, p ∈ m.rule.terms := by
    intro p inside
    simp [Rule.terms, inside]
  have solvedU : X.Models (b := PUnit.unit) u (f.information X s) := by
    apply models_of_reads f m.propagates.noTake m.propagates.noTell
    · intro e inside
      change u.applyTerm e.1 = u.applyTerm e.2
      rw [uState e.1 (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩)),
        uState e.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩)))]
      exact unifyTotal_sound _ _ accepted e inside
    · intro x pair
      rw [uRule x.1 (readTerm x.1 (List.of_mem_zip pair).1),
        uState (s.label x.2) (Or.inr (Or.inr ⟨x.2, (each x pair).1, rfl⟩)), (each x pair).2]
  have shapes : f.Shapes X s := by
    refine ⟨isFresh, List.nodup_nil, nodup, ?_, readLength.symm, length, ?_⟩
    · change m.rule.body.take.length = ([] : List O).length
      rw [m.propagates.noTake]
      rfl
    · change m.rule.collect.length = ([] : List (Finset O)).length
      rw [m.propagates.positive.2]
      rfl
  have enabledF : MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) s.present
      (f.selection.commit (T := Unit)) := by
    refine ⟨fun o inside => ?_, fun o inside => ?_, ?_, fresh, fun q inside => ?_⟩
    · change o ∈ ([] : List O).toFinset at inside
      simp at inside
    · obtain ⟨p, pair⟩ := SetStore.zip_right readLength.symm (List.mem_toFinset.mp inside)
      exact (each (p, o) pair).1
    · change Disjoint ([] : List O).toFinset reads.toFinset
      simp
    · cases inside
  have admitted : f.Admits X s := by
    refine ⟨shapes, enabledF, ⟨PUnit.unit, u, solvedU⟩, fun b τ solved => ?_⟩
    cases b
    have matched : ∀ term ∈ m.rule.body.read,
        (τ.comp f.opening).applyTerm term = m.assignment.applyTerm term := by
      intro term inside
      obtain ⟨o, pair⟩ := SetStore.zip_left readLength.symm inside
      rw [read_value f accepted solved pair (ground o (each (term, o) pair).1),
        (each (term, o) pair).2]
    refine ⟨fun c inside => ?_, fun q inside => ?_⟩
    · obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      obtain ⟨left, right, rfl⟩ := m.propagates.positive.1 original member
      have equal := checks_of_matches m (τ.comp f.opening) matched left right member
      change τ.applyTerm (f.opening.applyTerm left) = τ.applyTerm (f.opening.applyTerm right)
      simpa only [Subst.applyTerm_comp] using equal
    · change q ∈ (f.collectOpened X).zip ([] : List (Finset O)) at inside
      simp at inside
  refine ⟨f, rfl, rfl, admitted, result_settled f pure settled admitted, ?_⟩
  rw [firing_support f pure settled admitted solvedU]
  congr 1
  change (m.rule.body.produce.map (u.comp f.opening).applyTerm).toFinset =
    (m.rule.body.produce.map m.assignment.applyTerm).toFinset
  congr 1
  apply List.map_congr_left
  intro t inside
  rw [Subst.applyTerm_comp]
  exact uRule t (produceTerm t inside)

/-- **The bag step of a ground instance**: with any fresh made identities, it reaches a settled state
whose support is the support with the instance's made rows. -/
theorem lift_instance (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) (m : GroundMatch P)
    (enabled : (consequence m).read ⊆ support s) (made : List O) (nodup : made.Nodup)
    (fresh : Disjoint made.toFinset s.present) (length : m.rule.body.produce.length = made.length) :
    ∃ s', Succ (step X O E P).toStep s s' ∧ s'.present = s.present ∪ made.toFinset ∧
      Settled s' ∧ support s' = support s ∪ (consequence m).made := by
  obtain ⟨f, -, madeEq, admitted, settled', supportEq⟩ :=
    lift_match pure slots settled m enabled made nodup fresh length
  refine ⟨f.result X s, ⟨f, admitted, rfl⟩, ?_, settled', supportEq⟩
  rw [result_present f pure admitted, madeEq]

/-- **Backward lifting, one step, closure form.** A closure step from the support of a settled state
is an enabled ground instance adding a row, and for every list of fresh made identities a bag step
with those identities reaches a settled state whose support is the step's result. -/
theorem backward_step_closure (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) {after : Finset (Term signature)}
    (moved : SetStoreClosure.Step (consequence (P := P)) (support s) after) :
    ∃ m : GroundMatch P, (consequence m).read ⊆ support s ∧ ¬ (consequence m).made ⊆ support s ∧
      after = support s ∪ (consequence m).made ∧
      ∀ made : List O, made.Nodup → Disjoint made.toFinset s.present →
        m.rule.body.produce.length = made.length →
        ∃ s', Succ (step X O E P).toStep s s' ∧ s'.present = s.present ∪ made.toFinset ∧
          Settled s' ∧ support s' = after := by
  obtain ⟨m, enabled, outside, rfl⟩ := closure_step_iff.mp moved
  exact ⟨m, enabled, outside, rfl, fun made nodup fresh length =>
    lift_instance pure slots settled m enabled made nodup fresh length⟩

/-- **Backward lifting, one step.** A one-match set step from the support of a settled state is an
enabled ground instance adding a row, and for every list of fresh made identities a bag step with
those identities reaches a settled state whose support is the step's result. -/
theorem backward_step (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O} (settled : Settled s)
    {after : Finset (Term signature)} (moved : DisciplinedStep .one timing P (support s) after) :
    ∃ m : GroundMatch P, (consequence m).read ⊆ support s ∧ ¬ (consequence m).made ⊆ support s ∧
      after = support s ∪ (consequence m).made ∧
      ∀ made : List O, made.Nodup → Disjoint made.toFinset s.present →
        m.rule.body.produce.length = made.length →
        ∃ s', Succ (step X O E P).toStep s s' ∧ s'.present = s.present ∪ made.toFinset ∧
          Settled s' ∧ support s' = after :=
  backward_step_closure pure slots settled
    ((one_step_iff_closure pure (support_ground settled)).mp moved)

/-! ## Runs -/

/-- Fresh distinct identities of every number, when there are infinitely many. -/
theorem exists_fresh_identities [Infinite O] (used : Finset O) (n : ℕ) :
    ∃ made : List O, made.Nodup ∧ made.length = n ∧ Disjoint made.toFinset used := by
  obtain ⟨chosen, inside, card⟩ := used.finite_toSet.infinite_compl.exists_subset_card_eq n
  refine ⟨chosen.toList, chosen.nodup_toList, by rw [Finset.length_toList, card], ?_⟩
  rw [Finset.toList_toFinset]
  exact Finset.disjoint_left.mpr fun _ member present => inside member present

/-- **Forward stuttering simulation of runs, closure form**: a bag run from a settled state maps
under the support to a closure run, its stutters absorbed. -/
theorem forward_run_closure (pure : ∀ rule ∈ P, Propagates rule)
    {s t : State (Terms (Term signature)) O} (settled : Settled s)
    (run : Relation.ReflTransGen (Succ (step X O E P).toStep) s t) :
    Settled t ∧
      Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) (support s) (support t) := by
  induction run with
  | refl => exact ⟨settled, .refl⟩
  | tail _ moved ih =>
    obtain ⟨middle, path⟩ := ih
    obtain ⟨last, same | next⟩ := forward_step_closure pure middle moved
    · refine ⟨last, ?_⟩
      rw [same]
      exact path
    · exact ⟨last, path.tail next⟩

/-- **Forward stuttering simulation of runs**: a bag run from a settled state maps under the support
to a one-match set run, its stutters absorbed. -/
theorem forward_run (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    {s t : State (Terms (Term signature)) O} (settled : Settled s)
    (run : Relation.ReflTransGen (Succ (step X O E P).toStep) s t) :
    Settled t ∧ Relation.ReflTransGen (DisciplinedStep .one timing P) (support s) (support t) := by
  obtain ⟨settledT, path⟩ := forward_run_closure pure settled run
  exact ⟨settledT, (one_run_iff_closure_run pure (support_ground settled)).mpr path⟩

/-- **Backward lifting of runs, closure form**: a closure run from the support of a settled state is
the support of a bag run, when there are infinitely many occurrence identities. -/
theorem backward_run_closure [Infinite O] (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O} (settled : Settled s)
    {after : Finset (Term signature)}
    (run : Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) (support s) after) :
    ∃ t, Relation.ReflTransGen (Succ (step X O E P).toStep) s t ∧ Settled t ∧ support t = after := by
  induction run with
  | refl => exact ⟨s, .refl, settled, rfl⟩
  | tail _ next ih =>
    obtain ⟨t, path, settledT, rfl⟩ := ih
    obtain ⟨m, -, -, -, lift⟩ := backward_step_closure pure slots settledT next
    obtain ⟨made, nodup, length, fresh⟩ :=
      exists_fresh_identities t.present m.rule.body.produce.length
    obtain ⟨t', moved, -, settled', supportEq⟩ := lift made nodup fresh length.symm
    exact ⟨t', path.tail moved, settled', supportEq⟩

/-- **Backward lifting of runs**: a one-match set run from the support of a settled state is the
support of a bag run, when there are infinitely many occurrence identities. -/
theorem backward_run [Infinite O] (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O} (settled : Settled s)
    {after : Finset (Term signature)}
    (run : Relation.ReflTransGen (DisciplinedStep .one timing P) (support s) after) :
    ∃ t, Relation.ReflTransGen (Succ (step X O E P).toStep) s t ∧ Settled t ∧ support t = after :=
  backward_run_closure pure slots settled
    ((one_run_iff_closure_run pure (support_ground settled)).mp run)

/-! ## Joint set steps lift to bag runs -/

/-- The made rows of a list of ground instances, together. -/
def madeRows (ms : List (GroundMatch P)) : Finset (Term signature) :=
  ms.foldr (fun m rows => (consequence m).made ∪ rows) ∅

theorem mem_madeRows {ms : List (GroundMatch P)} {v : Term signature} :
    v ∈ madeRows ms ↔ ∃ m ∈ ms, v ∈ (consequence m).made := by
  induction ms with
  | nil => simp [madeRows]
  | cons m rest ih =>
    change v ∈ (consequence m).made ∪ madeRows rest ↔ _
    rw [Finset.mem_union, ih]
    constructor
    · rintro (made | ⟨other, inside, made⟩)
      · exact ⟨m, List.mem_cons_self, made⟩
      · exact ⟨other, List.mem_cons_of_mem _ inside, made⟩
    · rintro ⟨other, inside, made⟩
      rcases List.mem_cons.mp inside with rfl | inside
      · exact Or.inl made
      · exact Or.inr ⟨other, inside, made⟩

/-- **Instances enabled together fire one after another**: a list of ground instances enabled at
the rows is a closure run to the rows with all their made rows. -/
theorem closure_run_of_instances {rows : Finset (Term signature)} :
    ∀ ms : List (GroundMatch P), (∀ m ∈ ms, (consequence m).read ⊆ rows) →
      Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) rows (rows ∪ madeRows ms)
  | [], _ => by
      rw [show madeRows ([] : List (GroundMatch P)) = ∅ from rfl, Finset.union_empty]
  | m :: rest, enabled => by
      have path := closure_run_of_instances rest fun other inside =>
        enabled other (List.mem_cons_of_mem _ inside)
      have target : rows ∪ madeRows (m :: rest) = (rows ∪ madeRows rest) ∪ (consequence m).made := by
        change rows ∪ ((consequence m).made ∪ madeRows rest) = _
        rw [Finset.union_comm (consequence m).made, Finset.union_assoc]
      rw [target]
      by_cases inside : (consequence m).made ⊆ rows ∪ madeRows rest
      · rw [Finset.union_eq_left.mpr inside]
        exact path
      · exact path.tail (closure_step_iff.mpr ⟨m,
          (enabled m List.mem_cons_self).trans Finset.subset_union_left, inside, rfl⟩)

/-- **A joint set step is a closure run**: the members of an admitted bag of matches from ground rows
are ground instances enabled there, fired one after another. -/
theorem closure_run_of_joint (pure : ∀ rule ∈ P, Propagates rule) {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} (ground : GroundRows rows)
    (moved : SetStore.Step timing P rows after) :
    Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) rows after := by
  obtain ⟨bag, -, admitted, answer, accepted, rfl, -⟩ := moved
  have yes := SetStore.admitted_after admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (bag.information X (SetStore.represent rows)) := unifyTotal_sound _ _ accepted
  let ms : List (GroundMatch P) := bag.members.attach.map fun member =>
    settledMember rows ground pure bag yes answer solved member.1 member.2
  have enabled : ∀ m ∈ ms, (consequence m).read ⊆ rows := by
    intro m inside
    obtain ⟨⟨member, inMembers⟩, -, rfl⟩ := List.mem_map.mp inside
    exact settledMember_enabled rows ground pure bag yes answer solved member inMembers
  have takes := propagation_no_takes rows pure bag yes
  have result : SetStore.setResult rows bag answer = rows ∪ madeRows ms := by
    ext v
    rw [Finset.mem_union, mem_madeRows]
    unfold SetStore.setResult
    rw [SetStore.mem_update, takes]
    constructor
    · rintro (⟨old, inRows, -, rfl⟩ | made)
      · left
        rw [FirstOrder.ground_fixed answer old (ground old inRows)]
        exact inRows
      · right
        obtain ⟨t, inProduce, rfl⟩ := Finset.mem_image.mp made
        obtain ⟨member, inMembers, opened⟩ :=
          List.mem_flatMap.mp (List.mem_toFinset.mp inProduce)
        obtain ⟨source, inSource, rfl⟩ := List.mem_map.mp opened
        exact ⟨settledMember rows ground pure bag yes answer solved member inMembers,
          List.mem_map.mpr ⟨⟨member, inMembers⟩, List.mem_attach _ _, rfl⟩,
          List.mem_toFinset.mpr (List.mem_map.mpr ⟨source, inSource, Subst.applyTerm_comp _ _ _⟩)⟩
    · rintro (inRows | ⟨m, inside, made⟩)
      · exact Or.inl ⟨v, inRows, by simp, FirstOrder.ground_fixed answer v (ground v inRows)⟩
      · right
        obtain ⟨⟨member, inMembers⟩, -, rfl⟩ := List.mem_map.mp inside
        obtain ⟨source, inSource, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
        exact Finset.mem_image.mpr ⟨member.opening.applyTerm source,
          List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨member, inMembers,
            List.mem_map.mpr ⟨source, inSource, rfl⟩⟩),
          (Subst.applyTerm_comp _ _ _).symm⟩
  rw [result]
  exact closure_run_of_instances ms enabled

/-- **Joint set runs are closure runs**, from ground rows. -/
theorem closure_run_of_joint_run (pure : ∀ rule ∈ P, Propagates rule) {timing : SetStore.AskTiming}
    {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (SetStore.Step timing P) seed after) :
    Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) seed after := by
  induction run with
  | refl => exact .refl
  | tail path moved ih =>
    exact ih.trans (closure_run_of_joint pure (actual_reachable_ground timing pure ground path) moved)

/-- **Backward lifting of joint set runs**: a run of joint set steps (any bag of matches, so any
declared discipline) from the support of a settled state is the support of a bag run. -/
theorem backward_run_joint [Infinite O] (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) {after : Finset (Term signature)}
    (run : Relation.ReflTransGen (SetStore.Step timing P) (support s) after) :
    ∃ t, Relation.ReflTransGen (Succ (step X O E P).toStep) s t ∧ Settled t ∧ support t = after :=
  backward_run_closure pure slots settled (closure_run_of_joint_run pure (support_ground settled) run)

/-- **The bag store and the set store reach the same rows**: from a settled state, the supports of
the states that bag runs reach are the sets that joint set runs reach from its support. -/
theorem reachable_iff [Infinite O] (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O} (settled : Settled s)
    (rows : Finset (Term signature)) :
    (∃ t, Relation.ReflTransGen (Succ (step X O E P).toStep) s t ∧ support t = rows) ↔
      Relation.ReflTransGen (SetStore.Step timing P) (support s) rows := by
  constructor
  · rintro ⟨t, run, rfl⟩
    exact lift_run timing (support_ground settled) (forward_run_closure pure settled run).2
  · intro run
    obtain ⟨t, path, -, reached⟩ := backward_run_joint timing pure slots settled run
    exact ⟨t, path, reached⟩

/-! ## Outcomes -/

/-- **A completed bag state**: no bag step changes its support. -/
def Completed (P : Program (Terms (Term signature))) (s : State (Terms (Term signature)) O) : Prop :=
  ∀ s', Succ (step X O E P).toStep s s' → support s' = support s

theorem completed_of_closed (pure : ∀ rule ∈ P, Propagates rule)
    {s : State (Terms (Term signature)) O} (settled : Settled s)
    (closed : SetStoreClosure.Closed (consequence (P := P)) (support s)) : Completed P s := by
  intro s' moved
  obtain ⟨f, admitted, rfl⟩ := moved
  replace admitted : f.Admits X s := admitted
  obtain ⟨⟨⟩, τ, solved⟩ := admitted.2.2.1
  change support (f.result X s) = support s
  rw [firing_support f pure settled admitted solved]
  exact Finset.union_eq_left.mpr (closed _ (firingMatch_enabled f pure settled admitted solved))

theorem closed_of_completed [Infinite O] (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O} (settled : Settled s)
    (completed : Completed P s) : SetStoreClosure.Closed (consequence (P := P)) (support s) := by
  intro m enabled
  by_contra outside
  obtain ⟨made, nodup, length, fresh⟩ := exists_fresh_identities s.present m.rule.body.produce.length
  obtain ⟨s', moved, -, -, supportEq⟩ :=
    lift_instance pure slots settled m enabled made nodup fresh length.symm
  have same := completed s' moved
  rw [supportEq] at same
  exact outside (Finset.union_eq_left.mp same)

/-- **A settled bag state is completed exactly when its support is closed.** -/
theorem completed_iff_closed [Infinite O] (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s : State (Terms (Term signature)) O} (settled : Settled s) :
    Completed P s ↔ SetStoreClosure.Closed (consequence (P := P)) (support s) :=
  ⟨closed_of_completed pure slots settled, completed_of_closed pure settled⟩

/-- **Completion is kept by every bag step**: the outcome, once reached, stays. -/
theorem completed_of_step [Infinite O] (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s s' : State (Terms (Term signature)) O} (settled : Settled s)
    (completed : Completed P s) (moved : Succ (step X O E P).toStep s s') : Completed P s' := by
  apply completed_of_closed pure (forward_step_closure pure settled moved).1
  rw [completed s' moved]
  exact closed_of_completed pure slots settled completed

/-- **A settled bag state is completed exactly when its support is terminal for the one-match set
step.** -/
theorem completed_iff_terminal [Infinite O] (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) :
    Completed P s ↔ TerminalWith .one timing P (support s) :=
  (completed_iff_closed pure slots settled).trans
    (terminal_one_iff_closed pure (support_ground settled)).symm

/-- **The support of a completed bag outcome is the least closure** of the seed's support. -/
theorem completed_support_eq_closure [Infinite O] (pure : ∀ rule ∈ P, Propagates rule)
    (slots : signature.vars ≃ ℕ) {s t : State (Terms (Term signature)) O} (settled : Settled s)
    (run : Relation.ReflTransGen (Succ (step X O E P).toStep) s t) (completed : Completed P t) :
    (support t : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) (support s) := by
  obtain ⟨settledT, path⟩ := forward_run_closure pure settled run
  exact SetStoreClosure.terminal_eq_closure _ _ path
    ((SetStoreClosure.terminal_iff_closed _ _).mpr (closed_of_completed pure slots settledT completed))

/-- **Completed bag outcomes are the completed set outcomes.** A bag run from a settled state to a
completed state and a set run of any declared discipline from its support to a terminal set reach
the same rows: the bag run is a one-match set run under the support, and the two set outcomes agree
by `completed_outcomes_agree`. -/
theorem completed_outcome_eq [Infinite O] (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    {s t : State (Terms (Term signature)) O} {after : Finset (Term signature)} (settled : Settled s)
    (bagRun : Relation.ReflTransGen (Succ (step X O E P).toStep) s t) (completed : Completed P t)
    (setRun : Relation.ReflTransGen (DisciplinedStep discipline timing P) (support s) after)
    (setEnd : TerminalWith discipline timing P after)
    (uniquePolicy : discipline = .unique → Determinate (P := P) after) :
    support t = after := by
  obtain ⟨settledT, oneRun⟩ := forward_run .afterTells pure settled bagRun
  exact completed_outcomes_agree slots .one discipline .afterTells timing pure rules covers
    (support_ground settled) oneRun setRun
    ((completed_iff_terminal .afterTells pure slots settledT).mp completed) setEnd
    (fun same => nomatch same) uniquePolicy

/-- **Completed bag outcomes exist** under a finite closed carrier, and their support is the least
closure of the seed's support. -/
theorem exists_completed [Infinite O] (slots : signature.vars ≃ ℕ)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    {s : State (Terms (Term signature)) O} (settled : Settled s) (inside : support s ⊆ carrier) :
    ∃ t, Relation.ReflTransGen (Succ (step X O E P).toStep) s t ∧ Completed P t ∧
      (support t : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) (support s) := by
  obtain ⟨after, run, terminal⟩ :=
    SetStoreClosure.exists_terminal (consequence (P := P)) carrier closed (support s) inside
  obtain ⟨t, bagRun, settledT, rfl⟩ := backward_run_closure pure slots settled run
  refine ⟨t, bagRun, completed_of_closed pure settledT
    ((SetStoreClosure.terminal_iff_closed _ _).mp terminal), ?_⟩
  exact SetStoreClosure.terminal_eq_closure _ _ run terminal

/-! ## Terminal bag states and divergence -/

/-- **A settled bag state has no step exactly when no ground instance is enabled at its support.** -/
theorem stuck_iff [Infinite O] (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) :
    (∀ s', ¬ Succ (step X O E P).toStep s s') ↔
      ∀ m : GroundMatch P, ¬ (consequence m).read ⊆ support s := by
  constructor
  · intro stuck m enabled
    obtain ⟨made, nodup, length, fresh⟩ :=
      exists_fresh_identities s.present m.rule.body.produce.length
    obtain ⟨s', moved, -⟩ := lift_instance pure slots settled m enabled made nodup fresh length.symm
    exact stuck s' moved
  · intro none s' moved
    obtain ⟨f, admitted, rfl⟩ := moved
    replace admitted : f.Admits X s := admitted
    obtain ⟨⟨⟩, τ, solved⟩ := admitted.2.2.1
    exact none _ (firingMatch_enabled f pure settled admitted solved)

/-- **The bag store diverges wherever a ground instance is enabled**: a propagation firing stays
enabled after it fires, so there is an infinite bag run. -/
theorem diverges [Infinite O] (pure : ∀ rule ∈ P, Propagates rule) (slots : signature.vars ≃ ℕ)
    {s : State (Terms (Term signature)) O} (settled : Settled s) (m : GroundMatch P)
    (enabled : (consequence m).read ⊆ support s) :
    ∃ run : ℕ → State (Terms (Term signature)) O, run 0 = s ∧
      ∀ n, Succ (step X O E P).toStep (run n) (run (n + 1)) := by
  have next : ∀ t : State (Terms (Term signature)) O,
      Settled t ∧ (consequence m).read ⊆ support t →
        ∃ t', Succ (step X O E P).toStep t t' ∧ (Settled t' ∧ (consequence m).read ⊆ support t') := by
    rintro t ⟨settledT, enabledT⟩
    obtain ⟨made, nodup, length, fresh⟩ :=
      exists_fresh_identities t.present m.rule.body.produce.length
    obtain ⟨t', moved, -, settled', supportEq⟩ :=
      lift_instance pure slots settledT m enabledT made nodup fresh length.symm
    refine ⟨t', moved, settled', ?_⟩
    rw [supportEq]
    exact enabledT.trans Finset.subset_union_left
  choose later moves keeps using next
  let walk : ℕ → {t : State (Terms (Term signature)) O //
      Settled t ∧ (consequence m).read ⊆ support t} := fun n =>
    Nat.rec (motive := fun _ => {t : State (Terms (Term signature)) O //
        Settled t ∧ (consequence m).read ⊆ support t})
      ⟨s, settled, enabled⟩ (fun _ previous => ⟨later previous.1 previous.2,
        keeps previous.1 previous.2⟩) n
  exact ⟨fun n => (walk n).1, rfl, fun n => moves (walk n).1 (walk n).2⟩

#print axioms support_eq_of_models
#print axioms readings_eq
#print axioms firing_support
#print axioms stutter_iff
#print axioms one_step_iff_closure
#print axioms one_run_iff_closure_run
#print axioms forward_step_closure
#print axioms forward_step
#print axioms lift_match
#print axioms lift_instance
#print axioms backward_step_closure
#print axioms backward_step
#print axioms forward_run_closure
#print axioms forward_run
#print axioms backward_run_closure
#print axioms backward_run
#print axioms closure_run_of_joint
#print axioms backward_run_joint
#print axioms reachable_iff
#print axioms completed_iff_closed
#print axioms completed_of_step
#print axioms completed_iff_terminal
#print axioms completed_support_eq_closure
#print axioms completed_outcome_eq
#print axioms exists_completed
#print axioms stuck_iff
#print axioms diverges

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Support
