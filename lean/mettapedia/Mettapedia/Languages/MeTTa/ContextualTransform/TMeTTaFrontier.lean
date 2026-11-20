import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaCollection
import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport

/-!
# Owned collector frontiers

Each open collector owns its ready work, suspended work, journal and return
continuation. The public world and its revisions are shared. A fresh owner
also reserves the opaque name of its eventual result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Frontier

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.AnswerCollection Collection
open Mettapedia.Machines (RevisionDependencySet)
open Mettapedia.Machines.Cursor.StampedSnapshots (Store)

abbrev Work (D : Discipline RuntimeSig [] ()) := Branch keys [] () D.Ty
variable {D : Discipline RuntimeSig [] ()}

def problem (store : List (Constraint keys [] ())) :=
  ContextualResidual.observeProblem store

structure Job (D : Discipline RuntimeSig [] ()) where
  branch : Work D
  checked : Option (ContextualFrameWorklist.Result (problem branch.store))

def Job.fresh (branch : Work D) : Job D :=
  ⟨branch, none⟩

def Job.withFocus (job : Job D) (focus : Focus keys [] () D.Ty) : Job D :=
  ⟨{job.branch with focus}, job.checked⟩

def Job.attempt (job : Job D) (fuel : Nat) :
    ContextualFrameWorklist.Result (problem job.branch.store) :=
  job.checked.getD (Query.NativeSolver.attempt fuel (problem job.branch.store))

theorem Job.attempt_models (job : Job D) (fuel : Nat) {V : Type} {declaration : V → MetaArity RuntimeSig}
    (point : Assignment (fam keys) declaration) :
    Query.NativeSolver.modelsThrough (job.attempt fuel) point ↔ Models point job.branch.store :=
  (Query.NativeSolver.modelsThrough_exact _ _).trans (ContextualResidual.models_observeProblem _ _)

private def resumeStore {before after : List (Constraint keys [] ())}
    (prior : ContextualFrameWorklist.Result (problem before)) (fuel : Nat)
    (extra : List (Constraint keys [] ())) (extended : after = before ++ extra) :
    ContextualFrameWorklist.Result (problem after) :=
  (Query.NativeSolver.resume prior fuel (problem extra)).cast
    ((show problem (before ++ extra) = problem before ++ problem extra from List.map_append).symm.trans
      (congrArg problem extended.symm))

/-- Moves preserving the knowledge retain its solver result. Moves extending
it continue with the new equations in that result's declaration family. -/
noncomputable def Job.follow (job : Job D) (fuel : Nat) (branch : Work D) : Job D := by
  classical
  exact if same : job.branch.store = branch.store then
    ⟨branch, some ((job.attempt fuel).cast (congrArg problem same))⟩
  else
    let extra := branch.store.drop job.branch.store.length
    if extended : branch.store = job.branch.store ++ extra then
      ⟨branch, some (resumeStore (job.attempt fuel) fuel extra extended)⟩
    else .fresh branch

@[simp] theorem Job.follow_branch (job : Job D) (fuel : Nat) (branch : Work D) :
    (job.follow fuel branch).branch = branch := by
  unfold Job.follow
  split
  · rfl
  · dsimp only
    split <;> rfl

inductive Wait (D : Discipline RuntimeSig [] ()) where
  | input (job : Job D) (name : Datum)
  | equations (branch : Work D) (saved : ContextualFrameWorklist.Result (problem branch.store))

def Wait.job : Wait D → Job D
  | .input job _ => job
  | .equations branch result => ⟨branch, some result⟩

def Wait.branch (waiting : Wait D) : Work D := waiting.job.branch

structure Input where
  name : Name keys
  value : Term RuntimeSig (fam keys name).1 (fam keys name).2

/-- Contextual inputs bind an intrinsic closure over the declared parameters.
Nullary inputs add the ordinary input equation. -/
private def abstract {V : Type} {declaration : V → MetaArity RuntimeSig} :
    {Γ : List Unit} → Term (signature RuntimeSig declaration) Γ () →
      Term (signature RuntimeSig declaration) [] ()
  | [], term => term
  | () :: _, term => abstract (.op (.inl (.inl .lam)) (.cons term .nil))

private def closeTerm {V : Type} {declaration : V → MetaArity RuntimeSig}
    {Γ : List Unit} {sort : Unit} (term : Term (signature RuntimeSig declaration) Γ sort) :
    Term (signature RuntimeSig declaration) [] () := by
  cases sort
  exact abstract term

def Input.equation (input : Input) : Constraint keys [] () :=
  (closeTerm (generator (fam keys) input.name),
    closeTerm (Rigid.includeTerm (fam keys) input.value))

def Input.refine (input : Input) (branch : Work D) : Work D :=
  {branch with store := branch.store ++ [input.equation]}

private theorem abstract_injective {V : Type} {declaration : V → MetaArity RuntimeSig} :
    ∀ {Γ : List Unit}, Function.Injective (@abstract V declaration Γ)
  | [] => fun _ _ h => h
  | () :: Γ => by
    intro left right same
    have body := abstract_injective (Γ := Γ) same
    exact (Args.cons.inj (eq_of_heq (Term.op.inj body).2)).1

private theorem instantiate_abstract {V W : Type} {d : V → MetaArity RuntimeSig}
    {e : W → MetaArity RuntimeSig} (image : Assignment d e) :
    ∀ {Γ : List Unit} (term : Term (signature RuntimeSig d) Γ ()),
      instantiate image (abstract term) = abstract (instantiate image term)
  | [], _ => rfl
  | () :: Γ, term => by
    exact instantiate_abstract image (Γ := Γ) (.op (.inl (.inl .lam)) (.cons term .nil))

private theorem instantiate_closeTerm {V W : Type} {d : V → MetaArity RuntimeSig}
    {e : W → MetaArity RuntimeSig} (image : Assignment d e)
    {Γ : List Unit} {sort : Unit} (term : Term (signature RuntimeSig d) Γ sort) :
    instantiate image (closeTerm term) = closeTerm (instantiate image term) := by
  cases sort
  exact instantiate_abstract image term

private theorem closeTerm_injective {V : Type} {declaration : V → MetaArity RuntimeSig}
    {Γ : List Unit} {sort : Unit} : Function.Injective (@closeTerm V declaration Γ sort) := by
  cases sort
  exact abstract_injective

/-- Supplying a closure constrains exactly the declared name, including its
object parameters, at every model of the resumed store. -/
theorem Input.models (input : Input) (branch : Work D)
    {W : Type} {declaration : W → MetaArity RuntimeSig} (image : Assignment (fam keys) declaration) :
    Models image (input.refine branch).store ↔ Models image branch.store ∧
      image input.name = Rigid.includeTerm declaration input.value := by
  change Models image (branch.store ++ [input.equation]) ↔ _
  rw [models_append, models_singleton]
  apply and_congr_right
  intro _
  change instantiate image (closeTerm (generator (fam keys) input.name)) =
    instantiate image (closeTerm (Rigid.includeTerm (fam keys) input.value)) ↔ _
  rw [instantiate_closeTerm, instantiate_closeTerm, instantiate_generator, Rigid.instantiate_include]
  exact ⟨fun h => closeTerm_injective h, congrArg closeTerm⟩

/-- A solved head is never watched again. A retained equation watches the
names in its current declaration family, after the saved assignments. -/
def Wait.watches (waiting : Wait D) (key : Name keys) : Prop :=
  match waiting with
  | .input _ name => observe name = observe (generator (fam keys) key)
  | .equations _ (.refuted _) => False
  | .equations _ (.residual saved) =>
    letI := saved.equality
    ∃ name ∈ ContextualActiveSupport.active saved.remaining,
      observe (saved.answer key) = observe (generator saved.declaration name)

/-- Before any rule has admitted, the original call owns the fallback.
All its still undecided clause occurrences receive the same caller input. -/
structure CallWait (D : Discipline RuntimeSig [] ()) where
  caller : Job D
  text : Datum
  candidates : List (Job D)

def CallWait.watches (call : CallWait D) (name : Name keys) (fuel : Nat) : Prop :=
  ∃ candidate ∈ call.candidates,
    (Wait.equations candidate.branch (candidate.attempt fuel)).watches name

structure Owner (D : Discipline RuntimeSig [] ()) where
  returnTo : Option (Nat × Job D)
  ready : Multiset (Job D)
  waiting : Multiset (Wait D)
  answers : List {branch : Work D // branch.Finished (D := D) ∧ Solvable branch.store}
  refuted : Multiset {branch : Work D // ¬ Solvable branch.store}
  reads : ReadSet
  calls : Multiset (CallWait D)

def Owner.start (caller : Option (Nat × Job D)) (job : Job D) : Owner D :=
  ⟨caller, {job}, 0, [], 0, ∅, 0⟩

def Owner.state (owner : Owner D) (world : World keys [] ()) : State keys [] () D :=
  ⟨⟨world, owner.ready.map Job.branch + owner.waiting.map Wait.branch +
    owner.calls.map (fun call => call.caller.branch)⟩,
    owner.answers.map Subtype.val, owner.refuted.map Subtype.val⟩

theorem Owner.valid (owner : Owner D) (world : World keys [] ()) : (owner.state world).Valid := by
  constructor
  · intro branch member
    obtain ⟨answer, _, rfl⟩ := List.mem_map.mp member
    exact answer.property
  · intro branch member
    obtain ⟨answer, _, rfl⟩ := Multiset.mem_map.mp member
    exact answer.property

structure State (D : Discipline RuntimeSig [] ()) where
  live : Finset Nat
  next : Nat
  owner : Nat → Owner D
  world : World keys [] ()
  revisions : Revisions
  heap : Nat → Option (AnswerSpace keys [] () D)

def children (state : State D) (id : Nat) : Finset Nat :=
  state.live.filter (fun k => (state.owner k).returnTo.map Prod.fst = some id)

inductive Encloses (state : State D) : Nat → Nat → Prop where
  | same (id : Nat) : Encloses state id id
  | parent {outer inner next : Nat} (held : inner ∈ children state next)
      (above : Encloses state outer next) : Encloses state outer inner

def State.Current (state : State D) : Prop :=
  ∀ id ∈ state.live, (state.owner id).reads.ValidAt state.revisions

def put (state : State D) (id : Nat) (owner : Owner D) : State D :=
  { state with owner := Function.update state.owner id owner }

def park (state : State D) (id : Nat) (waiting : Wait D) (rest : Multiset (Job D)) : State D :=
  put state id {(state.owner id) with ready := rest, waiting := waiting ::ₘ (state.owner id).waiting}

def enter (state : State D) (id : Nat) (caller : Job D) (body : Comp keys [] () D.Ty)
    (others : Multiset (Job D)) : State D :=
  let parent := {(state.owner id) with ready := others}
  let child := Owner.start (some (id, caller))
    ⟨{caller.branch with focus := .eval body, frames := []}, caller.checked⟩
  { (put (put state id parent) state.next child) with
    live := insert state.next state.live, next := state.next + 1 }

def deliver (state : State D) (id parent : Nat) (caller : Job D)
    (bag : AnswerSpace keys [] () D) : State D :=
  let old := state.owner parent
  let value := caller.withFocus (.value (token id))
  { (put state parent {old with ready := value ::ₘ old.ready}) with
    live := state.live.erase id, heap := Function.update state.heap id (some bag) }

noncomputable def rememberRead (state : State D) (id : Nat) (address : Region) (rev : Nat) : State D := by
  classical
  exact {state with owner := fun k =>
    let old := state.owner k
    if k ≠ 0 ∧ k ∈ state.live ∧ Encloses state k id then
      {old with reads := old.reads ∪ {readStamp address rev}}
    else old}

def observedAt (state : State D) (id : Nat) (address : Region) (rev : Nat) : Prop :=
  ∀ k ∈ state.live, k ≠ 0 → Encloses state k id →
    ∀ seen ∈ (state.owner k).reads, seen.read.storeId = address → seen.read.revision = rev

noncomputable def afterMove (state : State D) (id : Nat) (world : World keys [] ())
    (branches : Multiset (Job D)) : State D := by
  exact { (put state id {(state.owner id) with ready := branches}) with
    world := world, revisions := afterWrite state.revisions state.world world }

def resumeInput (job : Job D) (input : Input) (fuel : Nat) :
    ContextualFrameWorklist.Result (problem (input.refine job.branch).store) :=
  resumeStore (job.attempt fuel) fuel [input.equation] rfl

def offerInput (job : Job D) (input : Input) (fuel : Nat) : Job D :=
  ⟨input.refine job.branch, some (resumeInput job input fuel)⟩

theorem resumeInput_models (job : Job D) (input : Input) (fuel : Nat)
    {V : Type} {declaration : V → MetaArity RuntimeSig} (point : Assignment (fam keys) declaration) :
    Query.NativeSolver.modelsThrough (resumeInput job input fuel) point ↔
      Models point job.branch.store ∧
        point input.name = Rigid.includeTerm declaration input.value :=
  (Query.NativeSolver.modelsThrough_exact _ _).trans <|
    (ContextualResidual.models_observeProblem _ _).trans (input.models job.branch point)

noncomputable def wakeOne (input : Input) (fuel : Nat) (waiting : Wait D) :
    Sum (Job D) (Wait D) := by
  classical
  exact if waiting.watches input.name then
    let response := offerInput waiting.job input fuel
    if ContextualQueryAnswers.closed (response.attempt fuel) then .inl response
    else .inr (.equations response.branch (response.attempt fuel))
  else .inr waiting

/-- A reply that decides a wait puts the certified decision on the ready
queue. A later budget applies only to new equations. -/
theorem wake_keeps_decision (input : Input) (fuel later : Nat) (waiting : Wait D)
    (watches : waiting.watches input.name)
    (closed : ContextualQueryAnswers.closed (resumeInput waiting.job input fuel) = true) :
    ∃ job, wakeOne input fuel waiting = .inl job ∧ job.branch = input.refine waiting.branch ∧
      ContextualQueryAnswers.closed (job.attempt later) = true ∧
      ContextualQueryAnswers.successful (job.attempt later) =
        ContextualQueryAnswers.successful (resumeInput waiting.job input fuel) := by
  exact ⟨⟨input.refine waiting.branch, some (resumeInput waiting.job input fuel)⟩,
    by simp [wakeOne, watches, closed, Wait.branch, offerInput, Job.attempt], rfl, closed, rfl⟩

private def pendingCandidates (fuel : Nat) (candidates : List (Job D)) : List (Job D) :=
  candidates.filter fun candidate => !(ContextualQueryAnswers.closed (candidate.attempt fuel))

structure CallWake (D : Discipline RuntimeSig [] ()) where
  bodies : Multiset (Job D)
  waiting : Multiset (Wait D)
  calls : Multiset (CallWait D)

noncomputable def CallWait.wake (call : CallWait D) (input : Input) (fuel : Nat) : CallWake D := by
  classical
  exact if call.watches input.name fuel then
    let candidates := call.candidates.map (fun candidate => offerInput candidate input fuel)
    let hits := candidates.filter fun candidate => ContextualQueryAnswers.successful (candidate.attempt fuel)
    let pending := pendingCandidates fuel candidates
    let caller := offerInput call.caller input fuel
    if hits.isEmpty then
      if pending.isEmpty then ⟨{caller.withFocus (.value call.text)}, 0, 0⟩
      else ⟨0, 0, {⟨caller, call.text, pending⟩}⟩
    else
      let waits := pending.map fun candidate => Wait.equations candidate.branch (candidate.attempt fuel)
      ⟨hits, waits, 0⟩
  else ⟨0, 0, {call}⟩

theorem CallWait.wake_after_refuting (call : CallWait D) (input : Input) (fuel : Nat)
    (watched : call.watches input.name fuel)
    (refuted : ∀ candidate ∈ call.candidates,
      ∃ proof, (offerInput candidate input fuel).attempt fuel = .refuted proof) :
    call.wake input fuel =
      ⟨{(offerInput call.caller input fuel).withFocus (.value call.text)}, 0, 0⟩ := by
  let candidates := call.candidates.map (fun candidate => offerInput candidate input fuel)
  have rejects (job : Job D) (member : job ∈ candidates) :
      ∃ proof, job.attempt fuel = .refuted proof := by
    obtain ⟨candidate, found, same⟩ := List.mem_map.mp member
    rw [← same]
    exact refuted candidate found
  have hits : (candidates.filter fun job => ContextualQueryAnswers.successful (job.attempt fuel)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro job member
    obtain ⟨_, known⟩ := rejects job member
    simp [known, ContextualQueryAnswers.successful]
  have still : pendingCandidates fuel candidates = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro job member
    obtain ⟨_, known⟩ := rejects job member
    simp [known, ContextualQueryAnswers.closed]
  simp only [CallWait.wake, if_pos watched, candidates, hits, still, List.isEmpty_nil, if_true]

theorem CallWait.wake_after_admitting (call : CallWait D) (input : Input) (fuel : Nat)
    (watched : call.watches input.name fuel)
    (matched : ∃ candidate ∈ call.candidates,
      ContextualQueryAnswers.successful ((offerInput candidate input fuel).attempt fuel) = true) :
    (call.wake input fuel).calls = 0 := by
  let candidates := call.candidates.map (fun candidate => offerInput candidate input fuel)
  have gotOne : (candidates.filter fun job => ContextualQueryAnswers.successful (job.attempt fuel)).isEmpty = false := by
    obtain ⟨candidate, member, success⟩ := matched
    refine List.isEmpty_eq_false_iff_exists_mem.mpr ⟨offerInput candidate input fuel, ?_⟩
    exact List.mem_filter.mpr ⟨List.mem_map_of_mem member, success⟩
  simp only [CallWait.wake, if_pos watched, candidates, gotOne, Bool.false_eq_true, if_false]

noncomputable def wakeOwner (owner : Owner D) (input : Input) (fuel : Nat) : Owner D :=
  let candidates := owner.waiting.map (wakeOne input fuel)
  let ready := candidates.filterMap (fun t => match t with
    | .inl work => some work | .inr _ => none)
  let waiting := candidates.filterMap (fun t => match t with
    | .inl _ => none | .inr wait => some wait)
  let responses := owner.calls.map (fun call => call.wake input fuel)
  { owner with
    ready := ready + owner.ready + responses.bind CallWake.bodies
    waiting := waiting + responses.bind CallWake.waiting
    calls := responses.bind CallWake.calls }

/-- All matching waits across the live inventory see the same input. -/
noncomputable def wake (state : State D) (input : Input) (fuel : Nat) : State D :=
  {state with owner := fun k =>
    if k ∈ state.live then wakeOwner (state.owner k) input fuel else state.owner k}

inductive Mode where | source | transform

open ResourcePublication (destinations slice)

/-- A public arena edit can interleave with the scheduler. Its occurrence
catalogue projects the live cut to the same spaces the hosted reads see. -/
structure PublicEdit (s : State D) (T Sub O : Type) [DecidableEq O] where
  action : SubstitutionAction T Sub
  label : O → T
  row : T → Row keys [] ()
  region : O → Region
  firing : AnnotatedRuns.Firing T Sub O
  snapshot : Configuration T O
  live : Finset O
  guards : List Region
  old : Region → Nat
  prepared : Region → Bool
  admitted : firing.Valid action label snapshot
  publicView : ∀ regionName, s.world.spaces regionName =
    (slice region regionName live).val.map (row ∘ label)
  revisionsSound : ∀ regionName, old regionName = s.revisions.current regionName →
    slice region regionName snapshot.present = slice region regionName live
  checkCoverage : ∀ pattern, (∃ quantifier, Check.predicate quantifier pattern ∈ firing.rule.checks) ∨
      (∃ count, Check.count pattern count ∈ firing.rule.checks) →
    ∀ σ o, action.E (action.apply σ pattern) (action.apply σ (label o)) → region o ∈ guards
  queryCoverage : ∀ query ∈ firing.queries,
    ∀ σ o, query.region σ (label o) = true → region o ∈ guards

namespace PublicEdit

variable {s : State D} {T Sub O : Type} [DecidableEq O] (edit : PublicEdit s T Sub O)

def writes : List Region := destinations edit.region (edit.firing.selection.taken ++ edit.firing.selection.made)
def reads : List Region := edit.writes ++ destinations edit.region edit.firing.selection.read ++ edit.guards

def validates : Prop :=
  (∀ r ∈ edit.reads, edit.old r = s.revisions.current r) ∧ (∀ r ∈ edit.writes, edit.prepared r = true)

def publish? : Option (Configuration T O) :=
  Publication.publish? edit.region edit.label edit.firing.selection edit.firing.rule edit.snapshot edit.live
    edit.guards edit.old s.revisions.current edit.prepared edit.admitted.firing

def liveCut : Configuration T O := {edit.snapshot with present := edit.live}

def accepted (mode : Mode) (next : Configuration T O) : Prop :=
  match mode with
  | .source => edit.publish? = some next
  | .transform => edit.validates ∧ edit.firing.Valid edit.action edit.label edit.liveCut ∧
      next = edit.firing.result edit.label edit.liveCut

theorem accepted_exact (next : Configuration T O) :
    edit.accepted .source next ↔ edit.accepted .transform next := by
  have gate : (edit.reads.all (fun r => edit.old r == s.revisions.current r) &&
      edit.writes.all edit.prepared) = true ↔ edit.validates := by
    simp only [validates, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  have commits {result : Configuration T O} (success : edit.publish? = some result) :
      edit.firing.Valid edit.action edit.label edit.liveCut ∧ result = edit.firing.result edit.label edit.liveCut :=
    Publication.committed_firing_is_live edit.action edit.label edit.region edit.firing _ result edit.live
      edit.guards edit.old s.revisions.current edit.prepared edit.admitted edit.revisionsSound
      edit.checkCoverage edit.queryCoverage success
  constructor
  · intro success
    refine ⟨?_, commits success⟩
    change edit.publish? = some next at success
    simp only [publish?, Publication.publish?] at success
    split at success
    · exact gate.mp ‹_›
    · contradiction
  · rintro ⟨ready, _, rfl⟩
    have installed : ∃ result, edit.publish? = some result := by
      have verified := gate.mpr ready
      unfold reads writes at verified
      simp only [publish?, Publication.publish?, if_pos verified]
      exact ⟨_, rfl⟩
    obtain ⟨result, success⟩ := installed
    exact success.trans (congrArg some (commits success).2)

def install (next : Configuration T O) : State D :=
  { s with
    world := {s.world with spaces := fun address => (slice edit.region address next.present).val.map (edit.row ∘ edit.label)}
    revisions := ⟨fun address => if address ∈ edit.writes then s.revisions.current address + 1
      else s.revisions.current address⟩ }

theorem preserves_unwritten_region (mode : Mode) (next : Configuration T O) (address : Region)
    (accepted : edit.accepted mode next) (unchanged : address ∉ edit.writes) :
    (edit.install next).world.spaces address = s.world.spaces address ∧
      (edit.install next).revisions.current address = s.revisions.current address := by
  have success : edit.publish? = some next := by
    cases mode
    · exact accepted
    · exact (edit.accepted_exact next).mpr accepted
  have keeps : slice edit.region address next.present = slice edit.region address edit.live := by
    ext o
    simp only [ResourcePublication.mem_slice]
    by_cases located : edit.region o = address
    · have outside : edit.region o ∉ edit.writes := located.symm ▸ unchanged
      have preserved := Publication.outside_preserved edit.region edit.label edit.firing.selection edit.firing.rule
        edit.snapshot next edit.live edit.guards edit.old s.revisions.current edit.prepared outside
        edit.admitted.firing success
      exact and_congr_left fun _ => preserved
    · simp [located]
  refine ⟨(congrArg (fun cut : Finset O => cut.val.map (edit.row ∘ edit.label)) keeps).trans
    (edit.publicView address).symm, ?_⟩
  simp [install, unchanged]

theorem write_stales_snapshot (next : Configuration T O) (address : Region) (id : Nat)
    (live : id ∈ s.live) (written : address ∈ edit.writes)
    (observed : readStamp address (s.revisions.current address) ∈ (s.owner id).reads) :
    ¬ (edit.install next).Current := by
  intro current
  have now := current id live _ observed
  simp [install, readStamp, written] at now

end PublicEdit

def settled (fuel : Nat) (job : Job D) : Prop :=
  ContextualQueryAnswers.successful (job.attempt fuel) = true

theorem Job.solves (job : Job D) (fuel : Nat) (success : settled fuel job) : Solvable job.branch.store := by
  have closed : ContextualQueryAnswers.closed (job.attempt fuel) = true := by
    unfold settled at success
    cases decision : job.attempt fuel <;> simp_all [ContextualQueryAnswers.successful, ContextualQueryAnswers.closed]
  obtain ⟨_, declaration, point, known⟩ :=
    (Query.NativeSolver.closed_successful_iff (job.attempt fuel) closed).mp success
  exact ⟨_, declaration, point, (ContextualResidual.models_observeProblem _ _).mp known⟩

theorem Job.refutes (job : Job D) (fuel : Nat)
    (closed : ContextualQueryAnswers.closed (job.attempt fuel) = true)
    (unsolved : ¬ settled fuel job) : ¬ Solvable job.branch.store := by
  rintro ⟨V, declaration, point, models⟩
  apply unsolved
  exact (Query.NativeSolver.closed_successful_iff _ closed).mpr
    ⟨V, declaration, point, (ContextualResidual.models_observeProblem _ _).mpr models⟩

def countRequest (focus : Focus keys [] () D.Ty) (value : Datum) : Prop :=
  focus = .eval (.apply (unary "count" value)) ∨ focus = .eval (.apply (unary "size" value))

noncomputable def callCandidate (world : World keys [] ()) (caller : Job D)
    (text : Datum) (fuel : Nat) (rule : Equation keys [] () D.Ty) : Job D :=
  caller.follow fuel (callBranch D world.scope caller.branch.store text caller.branch.frames
    caller.branch.pending rule)

noncomputable def waitForCall (p : Program keys [] () D.Ty) (s : State D) (id : Nat) (job : Job D)
    (rest : Multiset (Job D)) (text : Datum) (fuel : Nat) : State D :=
  let candidates := p.equations.map (callCandidate s.world job text fuel)
  let pending := pendingCandidates fuel candidates
  let owner := s.owner id
  { (put s id {owner with ready := rest, calls := ⟨job, text, pending⟩ ::ₘ owner.calls}) with
    world := s.world.fresh }

/-- Dispatch is enabled by a certified admission or by completed examination
of every equation occurrence. Undecided candidates cannot justify fallback. -/
noncomputable def callReady (p : Program keys [] () D.Ty) (world : World keys [] ())
    (job : Job D) (fuel : Nat) : Prop :=
  match job.branch.focus with
  | .eval (.apply text) =>
    (∃ rule ∈ p.equations, settled fuel (callCandidate world job text fuel rule)) ∨
      (∀ rule ∈ p.equations,
        ContextualQueryAnswers.closed ((callCandidate world job text fuel rule).attempt fuel) = true)
  | _ => True

theorem fallback_refutes_every_candidate (p : Program keys [] () D.Ty) (world : World keys [] ())
    (job : Job D) (fuel : Nat) (text : Datum)
    (focus : job.branch.focus = .eval (.apply text)) (enabled : callReady p world job fuel)
    (absent : ∀ rule ∈ p.equations,
      ¬ Solvable (job.branch.store ++ [(instantiate (copyAt keys world.scope) rule.lhs, text)])) :
    ∀ rule ∈ p.equations, ∃ proof, (callCandidate world job text fuel rule).attempt fuel = .refuted proof := by
  have impossible (rule : Equation keys [] () D.Ty) (member : rule ∈ p.equations) :
      ¬ settled fuel (callCandidate world job text fuel rule) := by
    intro success
    apply absent rule member
    simpa only [callCandidate, Job.follow_branch, callBranch] using Job.solves _ fuel success
  rw [callReady, focus] at enabled
  have closed := enabled.resolve_left fun ⟨rule, member, hit⟩ => impossible rule member hit
  intro rule member
  have decided := closed rule member
  have noSuccess := impossible rule member
  unfold settled at noSuccess
  cases computed : (callCandidate world job text fuel rule).attempt fuel with
  | refuted proof => exact ⟨proof, rfl⟩
  | residual remaining =>
    rw [computed] at decided noSuccess
    exact False.elim (noSuccess decided)

noncomputable def replies (mode : Mode) (control scope : Nat) (caller : Work D)
    (space pattern body : Datum) (address : Region) (view : Store (Row keys [] ())) : List (Work D) := by
  classical
  exact match mode with
  | .source => ((selectRows caller pattern body scope view).map Prod.snd).filter
      (fun b => decide (Solvable b.store))
  | .transform => (Read.admittedRows control scope caller space pattern body address view).map
      (fun (i, row) => selectedBranch caller pattern body (scope + i) row)

noncomputable def remainingReads (fuel : Nat) (work : List (Work D)) : Multiset (Work D) := by
  classical
  exact (work : Multiset (Work D)).filter fun a =>
    ¬ Solvable a.store ∧ ContextualQueryAnswers.closed (Query.NativeSolver.attempt fuel (problem a.store)) = false

noncomputable def acceptRead (mode : Mode) (fuel : Nat) (s : State D) (id : Nat) (caller : Job D)
    (rest : Multiset (Job D)) (space pattern body : Datum) (address : Region)
    (view : Store (Row keys [] ())) : State D :=
  let next := {s with world := {s.world with scope := s.world.scope + view.next + 1}}
  let admitted := (replies mode id s.world.scope caller.branch space pattern body address view : Multiset (Work D))
  let deferred := remainingReads fuel ((selectRows caller.branch pattern body s.world.scope view).map Prod.snd)
  let ready := (admitted + deferred).map (caller.follow fuel) + rest
  rememberRead (put next id {(s.owner id) with ready}) id address view.clock

noncomputable def mayClose (mode : Mode) (state : State D) (id : Nat) : Prop :=
  let s := (state.owner id).state state.world
  match mode with
  | .source => s.current.branches = 0 ∧ children state id = ∅
  | .transform => CloseFiring.close.Valid CloseFiring.action CloseFiring.label
      (CloseFiring.table s (children state id).card)

theorem mayClose_exact (state : State D) (id : Nat) :
    mayClose .transform state id ↔ mayClose .source state id := by
  simp [mayClose, CloseFiring.admitted_iff_outstanding]

def closeResult (mode : Mode) (s : State D) (id : Nat)
    (valid : ((s.owner id).state s.world).Valid) : Option (AnswerSpace keys [] () D) :=
  let state := (s.owner id).state s.world
  match mode with
  | .source => reify state valid
  | .transform =>
    if state.current.branches.card = 0 then some (CloseFiring.answerSpace state valid (children s id).card)
    else none

theorem closeResult_exact (mode : Mode) (s : State D) (id : Nat)
    (valid : ((s.owner id).state s.world).Valid) :
    closeResult mode s id valid = reify ((s.owner id).state s.world) valid := by
  cases mode with
  | source => rfl
  | transform =>
    simp only [closeResult, reify]
    split
    · simp [CloseFiring.answerSpace, CloseFiring.journal_eq]
    · rfl

structure CanDeliver (mode : Mode) (s : State D) (id parent : Nat) (caller : Job D)
    (bag : AnswerSpace keys [] () D) : Prop where
  live : id ∈ s.live
  parentLive : parent ∈ s.live
  order : parent < id
  link : (s.owner id).returnTo = some (parent, caller)
  empty : mayClose mode s id
  current : (s.owner id).reads.ValidAt s.revisions
  frozen : closeResult mode s id ((s.owner id).valid s.world) = some bag

/-- The owner table schedules the common evaluator. Scoped read and close
admission can be derived from the source store or from the transform rules. -/
inductive Step (D : Discipline RuntimeSig [] ()) (mode : Mode)
    (p : Program keys [] () D.Ty) (supply : Nat → Region) (fuel : Nat) : State D → State D → Prop where
  | ordinary (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D))
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (enabled : permitsMove (id = 0) b.branch.focus)
      (ordinary : ∀ value, ¬ countRequest (D := D) b.branch.focus value)
      (dispatch : callReady p s.world b fuel) (solved : settled fuel b)
      {after out} (step : Move D p supply s.world b.branch after out) :
      Step D mode p supply fuel s (afterMove s id after (out.map (b.follow fuel) + rest))
  | run (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D)) (text : Datum)
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (request : b.branch.focus = .eval (.run text)) (solved : settled fuel b)
      {body} (active : Activation p b.branch.store text body) :
      Step D mode p supply fuel s
        (put s id {(s.owner id) with ready := b.withFocus (.eval body) ::ₘ rest})
  | collect (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D)) (head : String) (arg : Datum)
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (fresh : s.next ∉ s.live) (collector : collectorHead head)
      (request : b.branch.focus = .eval (.apply (unary head arg))) (solved : settled fuel b) :
      Step D mode p supply fuel s (enter s id b (p.reflect arg) rest)
  | parked (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D)) (key : Datum)
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (bareName : bare key = true) (waiting : Awaits b.branch key) (solved : settled fuel b) :
      Step D mode p supply fuel s (park s id (.input ⟨b.branch, some (b.attempt fuel)⟩ key) rest)
  | residual (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D))
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (openStore : ContextualQueryAnswers.closed (b.attempt fuel) = false) :
      Step D mode p supply fuel s (park s id (.equations b.branch (b.attempt fuel)) rest)
  | callPending (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D)) (text : Datum)
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (request : b.branch.focus = .eval (.apply text))
      (enabled : permitsMove (id = 0) b.branch.focus)
      (ordinary : ∀ value, ¬ countRequest (D := D) b.branch.focus value)
      (pending : ¬ callReady p s.world b fuel) (solved : settled fuel b) :
      Step D mode p supply fuel s (waitForCall p s id b rest text fuel)
  | read (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D))
      (space pattern body : Datum) (address : Region) (view : Store (Row keys [] ()))
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (request : b.branch.focus = .eval (.query space pattern (.ret body))) (solved : settled fuel b)
      (addressed : Determines b.branch.store space address) (snapshot : snapshotRows view = s.world.spaces address)
      (current : s.revisions.current address = view.clock)
      (unchanged : observedAt s id address view.clock) :
      Step D mode p supply fuel s (acceptRead mode fuel s id b rest space pattern body address view)
  | answered (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D))
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (finished : b.branch.Finished (D := D)) (solved : settled fuel b) :
      Step D mode p supply fuel s
        (put s id {(s.owner id) with ready := rest, answers := ⟨b.branch, finished, b.solves fuel solved⟩ :: (s.owner id).answers})
  | rejected (s : State D) (id : Nat) (b : Job D) (rest : Multiset (Job D))
      (live : id ∈ s.live) (ready : (s.owner id).ready = b ::ₘ rest)
      (reject : ContextualQueryAnswers.closed (b.attempt fuel) = true)
      (unsolved : ¬ settled fuel b) :
      Step D mode p supply fuel s
        (put s id {(s.owner id) with ready := rest, refuted := ⟨b.branch, b.refutes fuel reject unsolved⟩ ::ₘ (s.owner id).refuted})
  | input (s : State D) (message : Input) (current : s.Current)
      (waiting : ∃ id ∈ s.live,
        (∃ job ∈ (s.owner id).waiting, job.watches message.name) ∨
        (∃ call ∈ (s.owner id).calls, call.watches message.name fuel)) :
      Step D mode p supply fuel s (wake s message fuel)
  | publicEdit (s : State D) {T Sub O : Type} [DecidableEq O]
      (edit : PublicEdit s T Sub O) (next : Configuration T O)
      (committed : edit.accepted mode next) :
      Step D mode p supply fuel s (edit.install next)
  | close (s : State D) (id parent : Nat) (caller : Job D)
      {bag} (receipt : CanDeliver mode s id parent caller bag) :
      Step D mode p supply fuel s (deliver s id parent caller bag)
  | reflect (s : State D) (owner : Nat) (b : Job D) (rest : Multiset (Job D))
      (arg : Datum) (handle : Nat) (bag : AnswerSpace keys [] () D)
      (live : owner ∈ s.live) (ready : (s.owner owner).ready = b ::ₘ rest)
      (request : b.branch.focus = .eval (.apply (unary "reflect" arg))) (solved : settled fuel b)
      (found : s.heap handle = some bag)
      (addressed : Determines b.branch.store arg (.op (.inr (.mk handle)) .nil : Region)) :
      Step D mode p supply fuel s
        (put s owner {(s.owner owner) with ready := (bag.reflect s.world b.branch).branches.map (b.follow fuel) + rest})
  | count (s : State D) (owner : Nat) (b : Job D) (rest : Multiset (Job D))
      (arg : Datum) (handle : Nat) (bag : AnswerSpace keys [] () D)
      (live : owner ∈ s.live) (ready : (s.owner owner).ready = b ::ₘ rest)
      (request : countRequest (D := D) b.branch.focus arg) (solved : settled fuel b)
      (found : s.heap handle = some bag)
      (addressed : Determines b.branch.store arg (.op (.inr (.mk handle)) .nil : Region)) :
      Step D mode p supply fuel s (put s owner {(s.owner owner) with
        ready := b.withFocus (.value (embed (SourceLanguage.Elaboration.num bag.rows.card))) ::ₘ rest})

section Correspondence
variable {p : Program keys [] () D.Ty} {supply : Nat → Region} {fuel : Nat}

private theorem reads_agree (first second : Mode) (fuel : Nat) (s : State D)
    (id : Nat) (caller : Job D) (rest : Multiset (Job D)) (space pattern body : Datum)
    (address : Region) (view : Store (Row keys [] ())) (addressed : Determines caller.branch.store space address) :
    acceptRead first fuel s id caller rest space pattern body address view =
      acceptRead second fuel s id caller rest space pattern body address view := by
  have same : replies .transform id s.world.scope caller.branch space pattern body address view =
      replies .source id s.world.scope caller.branch space pattern body address view :=
    Read.admittedRows_exact id s.world.scope caller.branch space pattern body address view addressed
  cases first <;> cases second <;> simp only [acceptRead, same]

theorem Step.transfer {mode : Mode} (replacement : Mode) {s after : State D}
    (step : Step D mode p supply fuel s after) : Step D replacement p supply fuel s after := by
  cases step with
  | ordinary id b rest live ready enabled ordinary dispatch solved moved =>
    exact .ordinary s id b rest live ready enabled ordinary dispatch solved moved
  | run id b rest text live ready request solved active =>
    exact .run s id b rest text live ready request solved active
  | collect id b rest head arg live ready fresh collector request solved =>
    exact .collect s id b rest head arg live ready fresh collector request solved
  | parked id b rest key live ready bareName waiting solved =>
    exact .parked s id b rest key live ready bareName waiting solved
  | residual id b rest live ready openStore =>
    exact .residual s id b rest live ready openStore
  | callPending id b rest text live ready request enabled ordinary pending solved =>
    exact .callPending s id b rest text live ready request enabled ordinary pending solved
  | read id b rest space pattern body addr view live ready request solved addressed snapshot current unchanged =>
    rw [reads_agree mode replacement fuel s id b rest space pattern body addr view addressed]
    exact .read s id b rest space pattern body addr view live ready request solved addressed snapshot current unchanged
  | answered id b rest live ready finished solved =>
    exact .answered s id b rest live ready finished solved
  | rejected id b rest live ready reject unsolved =>
    exact .rejected s id b rest live ready reject unsolved
  | input msg current waiting => exact .input s msg current waiting
  | publicEdit edit next committed =>
    have agrees : edit.accepted mode next ↔ edit.accepted replacement next := by
      cases mode <;> cases replacement <;>
        first | rfl | exact edit.accepted_exact next | exact (edit.accepted_exact next).symm
    exact .publicEdit s edit next (agrees.mp committed)
  | close id parent caller receipt =>
    have shape : mayClose replacement s id := by
      cases mode <;> cases replacement <;>
        first | exact receipt.empty | exact (mayClose_exact s id).mp receipt.empty |
          exact (mayClose_exact s id).mpr receipt.empty
    refine .close s id parent caller {receipt with empty := shape, frozen := ?_}
    rw [closeResult_exact, ← closeResult_exact mode]
    exact receipt.frozen
  | reflect id b rest arg handle bag live ready request solved found addressed =>
    exact .reflect s id b rest arg handle bag live ready request solved found addressed
  | count id b rest arg handle bag live ready request solved found addressed =>
    exact .count s id b rest arg handle bag live ready request solved found addressed

abbrev Runs (mode : Mode) (p : Program keys [] () D.Ty) (supply : Nat → Region) (fuel : Nat) :=
  Relation.ReflTransGen (Step D mode p supply fuel)

/-- The same finite interleaving has exactly the same complete state and
retained work when using the independently admitted transform replies and
close firings. -/
theorem runs_iff {s after : State D} :
    Runs .source p supply fuel s after ↔ Runs .transform p supply fuel s after := by
  constructor
  · apply Relation.ReflTransGen.mono
    intro _ _ step
    exact step.transfer .transform
  · apply Relation.ReflTransGen.mono
    intro _ _ step
    exact step.transfer .source

end Correspondence

section Ownership

variable {p : Program keys [] () D.Ty} {supply : Nat → Region} {fuel : Nat} {mode : Mode}

def start (world : World keys [] ()) (revisions : Revisions) (work : Work D) : State D :=
  ⟨{0}, 1, fun _ => Owner.start none (.fresh work), world, revisions, fun _ => none⟩

@[simp] theorem put_here (s : State D) (id : Nat) (owner : Owner D) :
    (put s id owner).owner id = owner := by simp [put]

@[simp] theorem put_other (s : State D) (id other : Nat) (owner : Owner D) (different : other ≠ id) :
    (put s id owner).owner other = s.owner other := by simp [put, different]

theorem wake_at (s : State D) (input : Input) (fuel id : Nat) (live : id ∈ s.live) :
    (wake s input fuel).owner id = wakeOwner (s.owner id) input fuel := by simp [wake, live]

theorem wake_preserves_returns (s : State D) (input : Input) (fuel id : Nat) :
    ((wake s input fuel).owner id).returnTo = (s.owner id).returnTo ∧
      ((wake s input fuel).owner id).reads = (s.owner id).reads ∧
      ((wake s input fuel).owner id).answers = (s.owner id).answers := by
  by_cases live : id ∈ s.live <;> simp [wake, live, wakeOwner]

theorem wake_conserves_work (owner : Owner D) (input : Input) (fuel : Nat) (noCalls : owner.calls = 0) :
    (wakeOwner owner input fuel).ready.card + (wakeOwner owner input fuel).waiting.card =
      owner.ready.card + owner.waiting.card := by
  have partition (m : Multiset (Sum (Job D) (Wait D))) :
      (m.filterMap (fun t => match t with | .inl w => some w | .inr _ => none)).card +
        (m.filterMap (fun t => match t with | .inl _ => none | .inr w => some w)).card =
        m.card := by
    induction m using Multiset.induction_on with
    | empty => simp
    | cons item tail ih =>
      cases item <;> simp <;> omega
  have work := partition (owner.waiting.map (wakeOne input fuel))
  simp only [Multiset.card_map] at work
  simp only [wakeOwner, noCalls, Multiset.map_zero, Multiset.zero_bind, add_zero, Multiset.card_add]
  omega

/-- This holds for each live owner, including independent owners watching
the same name. The saved decision travels with the newly ready work. -/
theorem wake_readies_wait (s : State D) (input : Input) (fuel later id : Nat)
    (live : id ∈ s.live) (waiting : Wait D) (present : waiting ∈ (s.owner id).waiting)
    (watches : waiting.watches input.name)
    (closed : ContextualQueryAnswers.closed (resumeInput waiting.job input fuel) = true) :
    ∃ job ∈ ((wake s input fuel).owner id).ready, job.branch = input.refine waiting.branch ∧
      ContextualQueryAnswers.closed (job.attempt later) = true := by
  obtain ⟨job, readied, refined, kept, _⟩ := wake_keeps_decision input fuel later waiting watches closed
  refine ⟨job, ?_, refined, kept⟩
  rw [wake_at s input fuel id live]
  apply Multiset.mem_add.mpr
  left
  apply Multiset.mem_add.mpr
  left
  rw [Multiset.mem_filterMap]
  exact ⟨wakeOne input fuel waiting, Multiset.mem_map_of_mem _ present, by rw [readied]⟩

theorem parent_waits_for_child (s : State D) (id child : Nat) (holds : child ∈ children s id) :
    ¬ mayClose mode s id := by
  cases mode with
  | source => exact fun closed => (Finset.notMem_empty child) (closed.2 ▸ holds)
  | transform => exact fun closed =>
      (Finset.notMem_empty child) (((mayClose_exact s id).mp closed).2 ▸ holds)

theorem waits_block_close (s : State D) (id : Nat) {waiting : Wait D}
    (present : waiting ∈ (s.owner id).waiting) : ¬ mayClose mode s id := by
  intro close
  have empty : ((s.owner id).state s.world).current.branches = 0 := by
    cases mode
    · exact close.1
    · exact ((mayClose_exact s id).mp close).1
  have waitingIn : waiting.branch ∈ ((s.owner id).state s.world).current.branches :=
    Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ present))))
  rw [empty] at waitingIn
  exact Multiset.notMem_zero _ waitingIn

theorem deliver_parent (s : State D) (id parent : Nat) (caller : Job D) (bag : AnswerSpace keys [] () D) :
    (deliver s id parent caller bag).owner parent =
      {(s.owner parent) with ready := caller.withFocus (.value (token id)) ::ₘ (s.owner parent).ready} := by
  simp [deliver, put]

@[simp] theorem deliver_closed (s : State D) (id parent : Nat) (caller : Job D) (bag : AnswerSpace keys [] () D) :
    id ∉ (deliver s id parent caller bag).live := Finset.notMem_erase _ _

@[simp] theorem deliver_heap (s : State D) (id parent : Nat) (caller : Job D) (bag : AnswerSpace keys [] () D) :
    (deliver s id parent caller bag).heap id = some bag := by simp [deliver]

theorem children_after_delivery (s : State D) (id parent : Nat) (caller : Job D)
    (bag : AnswerSpace keys [] () D) (other : Nat) :
    children (deliver s id parent caller bag) other = (children s other).erase id := by
  ext k
  have link : ((deliver s id parent caller bag).owner k).returnTo = (s.owner k).returnTo := by
    by_cases same : k = parent
    · subst k
      rw [deliver_parent]
    · simp [deliver, put, same]
  have live : (deliver s id parent caller bag).live = s.live.erase id := rfl
  simp only [children, Finset.mem_filter, live, Finset.mem_erase, link]
  exact and_assoc

/-- Closing two already finished siblings in either order delivers the same
owned handles. Their bodies remain distinct even for equal answer lists. -/
theorem sibling_deliveries_commute (s : State D) (left right parent : Nat) (different : left ≠ right)
    (leftCaller rightCaller : Job D) (leftBag rightBag : AnswerSpace keys [] () D) :
    deliver (deliver s left parent leftCaller leftBag) right parent rightCaller rightBag =
      deliver (deliver s right parent rightCaller rightBag) left parent leftCaller leftBag := by
  have erased : (s.live.erase left).erase right = (s.live.erase right).erase left := by
    ext i
    simp [and_left_comm]
  simp only [deliver, put, Function.update_self, Function.update_idem]
  rw [erased, Function.update_comm different]
  rw [Multiset.cons_swap]

theorem CanDeliver.after_sibling {s : State D} {left right parent : Nat} (different : right ≠ left)
    {leftCaller rightCaller : Job D} {leftBag rightBag : AnswerSpace keys [] () D}
    (one : CanDeliver mode s left parent leftCaller leftBag)
    (two : CanDeliver mode s right parent rightCaller rightBag) :
    CanDeliver mode (deliver s left parent leftCaller leftBag) right parent rightCaller rightBag := by
  let next := deliver s left parent leftCaller leftBag
  have unchanged : next.owner right = s.owner right := by
    simp [next, deliver, put, (Nat.ne_of_lt two.order).symm]
  have remaining : children next right = (children s right).erase left :=
    children_after_delivery _ _ _ _ _ _
  have was : ((s.owner right).state s.world).current.branches = 0 ∧ children s right = ∅ := by
    cases mode
    · exact two.empty
    · exact (mayClose_exact s right).mp two.empty
  have after : mayClose .source next right := by
    change ((next.owner right).state next.world).current.branches = 0 ∧ children next right = ∅
    rw [unchanged, remaining, was.2]
    exact ⟨was.1, rfl⟩
  have ready : mayClose mode next right := by
    cases mode
    · exact after
    · exact (mayClose_exact next right).mpr after
  have keeps : (next.owner right).state next.world = (s.owner right).state s.world := by rw [unchanged]; rfl
  refine ⟨Finset.mem_erase.mpr ⟨different, two.live⟩,
    Finset.mem_erase.mpr ⟨Nat.ne_of_lt one.order, two.parentLive⟩,
    two.order, unchanged.symm ▸ two.link, ready, ?_, ?_⟩
  · rw [unchanged]
    exact two.current
  · have frozen : ∀ valid : ((s.owner right).state s.world).Valid,
        reify ((s.owner right).state s.world) valid = some rightBag := fun _ => by
      simpa only [closeResult_exact] using two.frozen
    rw [closeResult_exact]
    exact (keeps.symm ▸ frozen) _

/-- Both closing orders are admitted on the same parked parent. They lead to
one shared continuation frontier with both independently owned results. -/
theorem sibling_closes {s : State D} {left right parent : Nat} (different : left ≠ right)
    {leftCaller rightCaller : Job D} {leftBag rightBag : AnswerSpace keys [] () D}
    (one : CanDeliver mode s left parent leftCaller leftBag)
    (two : CanDeliver mode s right parent rightCaller rightBag) :
    let after := deliver (deliver s left parent leftCaller leftBag) right parent rightCaller rightBag
    (∃ middle, Step D mode p supply fuel s middle ∧ Step D mode p supply fuel middle after ∧
      middle.heap left = some leftBag) ∧
    (∃ middle, Step D mode p supply fuel s middle ∧ Step D mode p supply fuel middle after ∧
      middle.heap right = some rightBag) := by
  dsimp only
  refine ⟨⟨_, .close s left parent leftCaller one,
    .close _ right parent rightCaller (one.after_sibling different.symm two), deliver_heap _ _ _ _ _⟩, ?_⟩
  rw [sibling_deliveries_commute s left right parent different leftCaller rightCaller leftBag rightBag]
  exact ⟨_, .close s right parent rightCaller two,
    .close _ left parent leftCaller (two.after_sibling different one), deliver_heap _ _ _ _ _⟩

theorem Step.closed_stays_closed {s after : State D} (step : Step D mode p supply fuel s after)
    (id : Nat) (allocated : id < s.next) (closed : id ∉ s.live) :
    id < after.next ∧ id ∉ after.live := by
  cases step <;> try exact ⟨allocated, closed⟩
  · exact ⟨Nat.lt_succ_of_lt allocated, fun member => by
      rcases Finset.mem_insert.mp member with same | prior
      · exact (Nat.ne_of_lt allocated) same
      · exact closed prior⟩
  · exact ⟨allocated, fun member => closed (Finset.mem_of_mem_erase member)⟩

theorem Runs.retains_closed_owner {s after : State D} (run : Runs mode p supply fuel s after)
    (id : Nat) (allocated : id < s.next) (closed : id ∉ s.live) :
    id < after.next ∧ id ∉ after.live := by
  induction run with
  | refl => exact ⟨allocated, closed⟩
  | tail _ step ih => exact step.closed_stays_closed id ih.1 ih.2

theorem Step.keeps_closed_answer {s after : State D} (step : Step D mode p supply fuel s after)
    (id : Nat) (closed : id ∉ s.live) : after.heap id = s.heap id := by
  cases step <;> try rfl
  rename_i child parent caller bag receipt
  have different : id ≠ child := fun same => closed (same ▸ receipt.live)
  simp [deliver, different]

/-- Later wakeups and collector completions leave retired answer spaces intact. -/
theorem Runs.keeps_closed_answer {s after : State D} (run : Runs mode p supply fuel s after)
    (id : Nat) (allocated : id < s.next) (closed : id ∉ s.live) : after.heap id = s.heap id := by
  induction run with
  | refl => rfl
  | tail earlier step ih =>
    exact (step.keeps_closed_answer id (Runs.retains_closed_owner earlier id allocated closed).2).trans ih

def completed (s : State D) : Option (AnswerSpace keys [] () D) :=
  if s.live = {0} then reify ((s.owner 0).state s.world) ((s.owner 0).valid s.world) else none

theorem completed_runs_iff {s after : State D} (bag : AnswerSpace keys [] () D) :
    (Runs .source p supply fuel s after ∧ completed after = some bag) ↔
    (Runs .transform p supply fuel s after ∧ completed after = some bag) :=
  and_congr_left fun _ => runs_iff

end Ownership

end Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Frontier
