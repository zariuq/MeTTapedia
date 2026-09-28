import Mettapedia.GSLT.LanguageDef.HostCallMachine

/-!
# Host calls compose with output-first refinement

`DestinationPassingRefinement` shows that the output-first machine refines the
output-at-return machine on programs related by `ProgramBindsAhead`.  Here both
machines gain host calls (`HostCallMachine.withHost`) for the relations `isHost`
selects.  On the reference side a reference evaluator `R` serves the goal
(`hostedAtReturn`): the goal runs inline, its answers pulled on the same
frontier and returned to the pending frames, which unify their patterns with
them.  On the output-first side a host `H` serves it (`hostedFirst`): the goal
arrives with its destination `E` and is evaluated as `(let E G E)`, so its
answers are the goal's answers whose value unifies with `E`, in the goal's
order.

**The per-call hypothesis** (`HostCorrect`).  Take a host call made by the
reference in the store `σA` and on the output-first side in `σF`, whose
solutions are `σA`'s intersected with a context `Q`, with destination `dest`.
The host's state and the reference evaluator's are related (`start`), and
related states progress together (`pull`, `Matches`): both goals are exhausted;
or both deliver the same value `v`, the host's store having the solutions of
the reference's intersected with `v` meeting `dest` and with `Q`, and the same
supply (`PullRel.yield`); or the reference delivers an answer without solution
there, which the host omits (`prune`); or one side suspends, the host only
finitely often before the next event (`hostDelay`, `refDelay`).  The hypothesis
is about one goal's answers in two stores; it says nothing about
continuations, frames or the rest of the run.  `RefinesStore` asks of the
reference evaluator only that its answers refine the store of its call.
Answers carry a store and never a frame: they bind only the goal's own
variables, and the continuation's captured slots come from its frame.

**The law.**  `hosted_simulates`: from corresponding states and on a moded
reference run, after `n` reference steps there are output-first steps after
which the states still correspond (`HRelated`, `HDoomed`).  Hence
`hosted_answers`, the prefix law (every answer list the reference has
delivered, the output-first machine with host calls has delivered, answer for
answer), and `hosted_terminates` (when the reference exhausts its frontier, so
does the output-first run, with the same ordered answers).
`hosted_query_answers` and `hosted_query_terminates` start from a query
control.  `SameAnswer` compares answers as before: the same value, and stores
with the same solutions and supply.

**Collections.**  `collect_host`: when the reference evaluator exhausts a goal,
the host exhausts it too, and its collection is the reference's with the
answers that have no solution in the context omitted and every other answer
corresponding, in order.  `collect_host_start` states it for a goal with no
destination and no context, where nothing is omitted.  `outputFirst_collect`
and `hosted_collect` do the same for whole runs, the former through
`outputFirst_terminates`, within `n' ≤ n` steps.  When the reference does not
terminate, no collection is published (`collectRun_eq_none`), and the prefix
law still holds.

**Inhabitation.**  `enumCorrect`: the host that enumerates a goal's values
against its destination in the refined store meets the specification relative
to the reference that enumerates them in the call's store.

**Not covered.**  Cut: host goals are assumed cut-free, and cut is not
modelled.  The evaluation of a goal by CeTTa's enclosing machine: `R` and `H`
are parameters, and `HostCorrect` is what a host must satisfy, not a proof that
the enclosing machine does.  Whether a given run is moded, as in
`DestinationPassingRefinement`.  Step bounds: host suspensions make the
output-first step count unbounded by the reference's.  Mutation of the program
between answers.  This is a model, not a verified translation of the C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostCalls

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

section Tier

variable {Term Store Rel Op RState HState : Type}

/-- A call of a host relation is a host goal: the call itself, with its
instantiated arguments, its store and, on the output-first side, its
destination. -/
def hostGoal {γ : Type} (isHost : Rel → Bool) (c : Rel × γ) : Option (Rel × γ) :=
  if isHost c.1 then some c else none

theorem hostGoal_hit {γ : Type} {isHost : Rel → Bool} {c : Rel × γ} (hit : isHost c.1 = true) :
    hostGoal isHost c = some c := by
  simp [hostGoal, hit]

theorem hostGoal_miss {γ : Type} {isHost : Rel → Bool} {c : Rel × γ} (miss : ¬ isHost c.1 = true) :
    hostGoal isHost c = none := by
  simp [hostGoal, miss]

variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [Inhabited Term] [DecidableEq Rel]

/-- The reference: the output-at-return machine, whose host calls are served by
the reference evaluator `R` of the goal. -/
def hostedAtReturn (isHost : Rel → Bool) (PA : EqProgram L Rel Op)
    (R : Host (Call Term Store Rel) RState (Answer Term Store)) :=
  withHost (compiled L S PA) (hostGoal isHost) R

/-- The output-first machine, whose host calls are served by the host `H`; a
host goal carries its destination. -/
def hostedFirst (isHost : Rel → Bool) (PF : EqProgram L Rel Op)
    (H : Host (DestCall Term Store Rel) HState (Answer Term Store)) :=
  withHost (outputFirst L S PF) (hostGoal isHost) H

end Tier

/-! ## Specifications of the reference evaluator and of the host -/

section Specification

variable {Term Store Rel Op RState HState : Type}
variable {S : StoreAlgebra Term Store Op} (X : ExactStore S)

/-- A pull whose answers are well formed and lie in `within`, and whose next
state satisfies `W`. -/
inductive PullWithin (W : RState → Prop) (within : Set X.Valuation) :
    Pull RState (Answer Term Store) → Prop
  | done : PullWithin W within .done
  | yield {v : Term} {σ : Store} {r : RState} (good : X.WellFormed σ)
      (sub : X.solutions σ ⊆ within) (next : W r) : PullWithin W within (.yield (v, σ) r)
  | suspend {r : RState} (next : W r) : PullWithin W within (.suspend r)

/-- The reference evaluator only refines the store of its call: every answer of
a goal started in `σ` is well formed and its solutions are among `σ`'s. -/
structure RefinesStore (isHost : Rel → Bool)
    (R : Host (Call Term Store Rel) RState (Answer Term Store)) where
  Within : Set X.Valuation → RState → Prop
  start : ∀ {rel : Rel} {args : List Term} {σ : Store}, isHost rel = true → X.WellFormed σ →
    Within (X.solutions σ) (R.start (rel, args, σ))
  pull : ∀ {within : Set X.Valuation} {r : RState}, Within within r →
    PullWithin X (Within within) within (R.pull r)

/-- One pull of each side that correspond: both goals are exhausted, or both
deliver the same value, the host's store being the reference's intersected with
the destination meeting the value and with the context `Q`. -/
inductive PullRel (Corr : RState → HState → Prop) (Q : Set X.Valuation) (dest : Option Term) :
    Pull RState (Answer Term Store) → Pull HState (Answer Term Store) → Prop
  | done : PullRel Corr Q dest .done .done
  | yield {v : Term} {σA σF : Store} {r : RState} {h : HState}
      (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
      (sols : X.solutions σF = X.solutions σA ∩ meets X (some v) dest ∩ Q)
      (keys : X.supply σF = X.supply σA) (next : Corr r h) :
      PullRel Corr Q dest (.yield (v, σA) r) (.yield (v, σF) h)

/-- How a reference state `r` and a host state `h` progress together:
corresponding pulls; a host suspension (finitely many before the next event); a
reference suspension; or a reference answer that has no solution in the context
and against the destination, which the host never delivers. -/
inductive Matches (R : Host (Call Term Store Rel) RState (Answer Term Store))
    (H : Host (DestCall Term Store Rel) HState (Answer Term Store))
    (Corr : RState → HState → Prop) (Q : Set X.Valuation) (dest : Option Term) :
    RState → HState → Prop
  | pulls {r : RState} {h : HState} {pr : Pull RState (Answer Term Store)}
      {ph : Pull HState (Answer Term Store)} :
      R.pull r = pr → H.pull h = ph → PullRel X Corr Q dest pr ph → Matches R H Corr Q dest r h
  | hostDelay {r : RState} {h h' : HState} :
      H.pull h = .suspend h' → Matches R H Corr Q dest r h' → Matches R H Corr Q dest r h
  | refDelay {r r' : RState} {h : HState} :
      R.pull r = .suspend r' → Corr r' h → Matches R H Corr Q dest r h
  | prune {r r' : RState} {h : HState} {v : Term} {σA : Store} :
      R.pull r = .yield (v, σA) r' → X.WellFormed σA →
      X.solutions σA ∩ meets X (some v) dest ∩ Q = ∅ → Corr r' h → Matches R H Corr Q dest r h

/-- **The per-call specification of a host.**  For every host call, made in the
reference at `σA` and on the output-first side at `σF` with destination `dest`,
where `σF`'s solutions are `σA`'s intersected with the context `Q`: the host's
answers to the goal against its destination are the reference evaluator's
answers to the goal, in order, each intersected with the destination meeting its
value and with `Q`; answers without solution there are the ones the host omits.
`Corr` is the witness relating the two states between pulls. -/
structure HostCorrect (isHost : Rel → Bool)
    (R : Host (Call Term Store Rel) RState (Answer Term Store))
    (H : Host (DestCall Term Store Rel) HState (Answer Term Store)) where
  Corr : Set X.Valuation → Option Term → RState → HState → Prop
  start : ∀ {rel : Rel} {args : List Term} {σA σF : Store} {dest : Option Term}
    {Q : Set X.Valuation}, isHost rel = true → X.WellFormed σA → X.WellFormed σF →
    X.solutions σF = X.solutions σA ∩ Q → X.supply σF = X.supply σA →
    Corr Q dest (R.start (rel, args, σA)) (H.start (rel, args, σF, dest))
  pull : ∀ {Q : Set X.Valuation} {dest : Option Term} {r : RState} {h : HState},
    Corr Q dest r h → Matches X R H (Corr Q dest) Q dest r h

end Specification

/-! ## Corresponding tasks -/

section Correspondence

variable {Term Store Rel Op RState HState : Type}
variable (L : TemplateLanguage Term) {S : StoreAlgebra Term Store Op} (X : ExactStore S)
variable [Inhabited Term] {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}

/-- A task of the reference with host calls. -/
abbrev RTask (L : TemplateLanguage Term) (Rel Op Store RState : Type) :=
  Task Unit (Node (Control L Rel Op Store) RState (Answer Term Store)) (ReturnFrame L Rel Op)

/-- A task of the output-first machine with host calls. -/
abbrev FTask (L : TemplateLanguage Term) (Rel Op Store HState : Type) :=
  Task Unit (Node (DestControl L Rel Op Store) HState (Answer Term Store)) (DestFrame L Rel Op)

/-- Corresponding tasks: corresponding tier tasks (`Related`); answers a host
delivered to corresponding frames, related as corresponding returns are; host
states related by the host's specification, in the context the frames owe. -/
inductive HRelated (spec : HostCorrect X isHost R H) :
    RTask L Rel Op Store RState → FTask L Rel Op Store HState → Prop
  | tier {cA : Control L Rel Op Store} {cF : DestControl L Rel Op Store}
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
      (related : Related L X ⟨(), cA, fs⟩ ⟨(), cF, gs⟩) :
      HRelated spec ⟨(), .run cA, fs⟩ ⟨(), .run cF, gs⟩
  | answer {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
      {P : Set X.Valuation} (v : Term) (σA σF : Store) (frames : FramesRel L X dest fs gs P)
      (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
      (sols : X.solutions σF = X.solutions σA ∩ meets X (some v) dest ∩ P)
      (keys : X.supply σF = X.supply σA) :
      HRelated spec ⟨(), .answer (v, σA), fs⟩ ⟨(), .answer (v, σF), gs⟩
  | host {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
      {P : Set X.Valuation} {r : RState} {h : HState} (frames : FramesRel L X dest fs gs P)
      (corr : spec.Corr P dest r h) :
      HRelated spec ⟨(), .host r, fs⟩ ⟨(), .host h, gs⟩

/-- A reference task that can deliver no answer: a doomed tier task; an answer
without solution against its frames' destination and context; a host state
whose answers lie in a set without solution in its frames' context. -/
inductive HDoomed (ref : RefinesStore X isHost R) : RTask L Rel Op Store RState → Prop
  | tier {c : Control L Rel Op Store} {fs : List (ReturnFrame L Rel Op)}
      (doomed : Doomed L X ⟨(), c, fs⟩) : HDoomed ref ⟨(), .run c, fs⟩
  | answer {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
      {P : Set X.Valuation} (v : Term) (σ : Store) (frames : FramesRel L X dest fs gs P)
      (good : X.WellFormed σ) (empty : X.solutions σ ∩ meets X (some v) dest ∩ P = ∅) :
      HDoomed ref ⟨(), .answer (v, σ), fs⟩
  | host {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
      {P within : Set X.Valuation} {r : RState} (frames : FramesRel L X dest fs gs P)
      (inside : ref.Within within r) (empty : within ∩ P = ∅) :
      HDoomed ref ⟨(), .host r, fs⟩

/-- The tier tasks of a reference run are moded; delivered answers and host
states run no tests or primitives of the tier. -/
inductive HModed : RTask L Rel Op Store RState → Prop
  | tier {c : Control L Rel Op Store} {fs : List (ReturnFrame L Rel Op)}
      (moded : Moded L X ⟨(), c, fs⟩) : HModed ⟨(), .run c, fs⟩
  | answer (a : Answer Term Store) (fs : List (ReturnFrame L Rel Op)) :
      HModed ⟨(), .answer a, fs⟩
  | host (r : RState) (fs : List (ReturnFrame L Rel Op)) : HModed ⟨(), .host r, fs⟩

omit [Inhabited Term] in
/-- When every tier task is moded, every task of the reference with host calls
is. -/
theorem hmoded_of
    (moded : ∀ t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op), Moded L X t)
    (t : RTask L Rel Op Store RState) : HModed L X t := by
  rcases t with ⟨⟨⟩, c | a | r, fs⟩
  · exact .tier (moded _)
  · exact .answer a fs
  · exact .host r fs

omit [Inhabited Term] in
/-- Every program binds ahead of itself. -/
theorem programBindsAhead_refl (P : EqProgram L Rel Op) : ProgramBindsAhead L P P := by
  induction P with
  | nil => exact .nil
  | cons e rest ih =>
      rcases e with ⟨rel, ⟨k, params, rhs⟩⟩
      exact .cons ⟨rfl, .mk params (BindsAhead.refl rhs)⟩ ih

end Correspondence

/-! ## Expansions -/

section Expansions

variable {Term Store Rel Op RState HState : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}
  {PA PF : EqProgram L Rel Op}

omit [DecidableEq Rel] in
/-- Corresponding tier successors stay corresponding in the machines with host
calls. -/
theorem lift_embeds (spec : HostCorrect X isHost R H) (ref : RefinesStore X isHost R)
    {as : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    {bs : List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))}
    (h : Embeds (Related L X) (Doomed L X) as bs) :
    Embeds (HRelated L X spec) (HDoomed L X ref)
      (as.map (liftTask (HState := RState) (Answer := Answer Term Store)))
      (bs.map (liftTask (HState := HState) (Answer := Answer Term Store))) :=
  Embeds.map _ _
    (fun a b r => by
      rcases a with ⟨⟨⟩, cA, fs⟩
      rcases b with ⟨⟨⟩, cF, gs⟩
      exact .tier r)
    (fun a d => by
      rcases a with ⟨⟨⟩, c, fs⟩
      exact .tier d) h

/-- A doomed instruction of the reference yields only doomed tasks and no answer,
including when it is a host call. -/
theorem hsuccessors_doomed (aligned : ProgramBindsAhead L PA PF) (ref : RefinesStore X isHost R)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P)
    {i : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
    (doomed : DoomedInstruction L X dest P i) :
    (∀ t ∈ (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction i)).1,
        HDoomed L X ref t) ∧
      (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction i)).2 = [] := by
  have lifted : (∀ c, calleeOf i = some c → hostGoal isHost c = none) →
      (∀ t ∈ (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction i)).1,
          HDoomed L X ref t) ∧
        (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction i)).2 = [] := by
    intro base
    obtain ⟨all, none⟩ := successors_doomed X aligned frames doomed
    unfold hostedAtReturn
    rw [expandWith_lift _ _ _ _ _ _ base]
    refine ⟨fun t member => ?_, none⟩
    simp only [List.mem_map] at member
    obtain ⟨t', member', rfl⟩ := member
    rcases t' with ⟨⟨⟩, c, fs'⟩
    exact .tier (all _ member')
  cases doomed with
  | ret v σ good empty => exact lifted fun c h => by cases h
  | fail => exact lifted fun c h => by cases h
  | call rel args σ p captured origin ahead agrees good empty =>
      by_cases hit : isHost rel = true
      · unfold hostedAtReturn
        rw [expandWith_hostCall _ _ _ _ _ _ _ (hostGoal_hit (c := (rel, args, σ)) hit)]
        refine ⟨fun t member => ?_, rfl⟩
        simp only [List.mem_singleton] at member
        subst member
        exact .host (.cons p captured origin dest ahead agrees frames) (ref.start hit good)
          (by rw [← Set.inter_assoc]; exact empty)
      · exact lifted fun c h => by
          simp only [calleeOf, Option.some.injEq] at h
          subst h
          exact hostGoal_miss hit
  | tail rel args σ good empty =>
      by_cases hit : isHost rel = true
      · unfold hostedAtReturn
        rw [expandWith_hostTail _ _ _ _ _ _ (hostGoal_hit (c := (rel, args, σ)) hit)]
        refine ⟨fun t member => ?_, rfl⟩
        simp only [List.mem_singleton] at member
        subst member
        exact .host frames (ref.start hit good) empty
      · exact lifted fun c h => by
          simp only [calleeOf, Option.some.injEq] at h
          subst h
          exact hostGoal_miss hit

/-- Corresponding tier instructions yield corresponding successors in the
machines with host calls.  A host call on both sides starts the reference
evaluator and the host on the same goal, in stores related by the context the
return frames owe. -/
theorem hsuccessors_related (aligned : ProgramBindsAhead L PA PF)
    (spec : HostCorrect X isHost R H) (ref : RefinesStore X isHost R)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P)
    {iA : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
    {iF : Instruction (DestCall Term Store Rel) (DestFrame L Rel Op) (Answer Term Store)}
    (related : InspectRelated L X dest P iA iF) :
    Embeds (HRelated L X spec) (HDoomed L X ref)
        (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction iA)).1
        (expandWith (hostedFirst L S isHost PF H) () gs (liftInstruction iF)).1 ∧
      List.Forall₂ (SameAnswer X)
        (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction iA)).2
        (expandWith (hostedFirst L S isHost PF H) () gs (liftInstruction iF)).2 := by
  have lifted : (∀ c, calleeOf iA = some c → hostGoal isHost c = none) →
      (∀ c, calleeOf iF = some c → hostGoal isHost c = none) →
      Embeds (HRelated L X spec) (HDoomed L X ref)
          (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction iA)).1
          (expandWith (hostedFirst L S isHost PF H) () gs (liftInstruction iF)).1 ∧
        List.Forall₂ (SameAnswer X)
          (expandWith (hostedAtReturn L S isHost PA R) () fs (liftInstruction iA)).2
          (expandWith (hostedFirst L S isHost PF H) () gs (liftInstruction iF)).2 := by
    intro baseA baseF
    obtain ⟨tasks, answers⟩ := successors_related X aligned frames related
    unfold hostedAtReturn hostedFirst
    rw [expandWith_lift _ _ _ _ _ _ baseA, expandWith_lift _ _ _ _ _ _ baseF]
    exact ⟨lift_embeds spec ref tasks, answers⟩
  cases related with
  | ret v σA σF goodA goodF sols keys =>
      exact lifted (fun c h => by cases h) (fun c h => by cases h)
  | fail => exact lifted (fun c h => by cases h) (fun c h => by cases h)
  | call rel args σA σF p captured origin ahead agrees goodA goodF sols keys =>
      by_cases hit : isHost rel = true
      · unfold hostedAtReturn hostedFirst
        rw [expandWith_hostCall _ _ _ _ _ _ _ (hostGoal_hit (c := (rel, args, σA)) hit),
          expandWith_hostCall _ _ _ _ _ _ _
            (hostGoal_hit (c := (rel, args, σF, some (L.inst p (reconstruct captured)))) hit)]
        exact ⟨.keep (.host (.cons p captured origin dest ahead agrees frames)
          (spec.start hit goodA goodF (by rw [sols, Set.inter_assoc]) keys)) .nil, .nil⟩
      · refine lifted (fun c h => ?_) (fun c h => ?_) <;>
        · simp only [calleeOf, Option.some.injEq] at h
          subst h
          exact hostGoal_miss hit
  | tail rel args σA σF goodA goodF sols keys =>
      by_cases hit : isHost rel = true
      · unfold hostedAtReturn hostedFirst
        rw [expandWith_hostTail _ _ _ _ _ _ (hostGoal_hit (c := (rel, args, σA)) hit),
          expandWith_hostTail _ _ _ _ _ _ (hostGoal_hit (c := (rel, args, σF, dest)) hit)]
        exact ⟨.keep (.host frames (spec.start hit goodA goodF sols keys)) .nil, .nil⟩
      · refine lifted (fun c h => ?_) (fun c h => ?_) <;>
        · simp only [calleeOf, Option.some.injEq] at h
          subst h
          exact hostGoal_miss hit
  | doomed d =>
      obtain ⟨all, none⟩ := hsuccessors_doomed aligned ref frames d
      refine ⟨Embeds.of_forall all, ?_⟩
      rw [none]
      exact .nil

/-- A reference state and a host state related by the specification expand to
corresponding tasks and answers, the host after finitely many suspensions and
the reference after one pull. -/
theorem host_related (spec : HostCorrect X isHost R H) (ref : RefinesStore X isHost R)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P) {r : RState} {h : HState}
    (progress : Matches X R H (spec.Corr P dest) P dest r h) :
    ∃ ts as, ExpandsTo (hostedFirst L S isHost PF H) ⟨(), .host h, gs⟩ ts as ∧
      Embeds (HRelated L X spec) (HDoomed L X ref)
        (expand (hostedAtReturn L S isHost PA R) ⟨(), .host r, fs⟩).1 ts ∧
      List.Forall₂ (SameAnswer X)
        (expand (hostedAtReturn L S isHost PA R) ⟨(), .host r, fs⟩).2 as := by
  induction progress with
  | pulls pulledR pulledH pulls =>
      refine ⟨_, _, .one _, ?_⟩
      unfold hostedAtReturn hostedFirst
      rw [expand_host, expand_host, pulledR, pulledH]
      cases pulls with
      | done => exact ⟨.nil, .nil⟩
      | yield goodA goodF sols keys next =>
          exact ⟨.keep (.answer _ _ _ frames goodA goodF sols keys)
            (.keep (.host frames next) .nil), .nil⟩
  | hostDelay pulled _ ih =>
      obtain ⟨ts, as, expands, tasks, answers⟩ := ih
      refine ⟨ts, as, .stutter ?_ expands, tasks, answers⟩
      unfold hostedFirst
      rw [expand_host, pulled]
      rfl
  | refDelay pulled corr =>
      refine ⟨_, _, .stay _, ?_⟩
      unfold hostedAtReturn
      rw [expand_host, pulled]
      exact ⟨.keep (.host frames corr) .nil, .nil⟩
  | prune pulled good empty corr =>
      refine ⟨_, _, .stay _, ?_⟩
      unfold hostedAtReturn
      rw [expand_host, pulled]
      exact ⟨.drop (.answer _ _ frames good empty) (.keep (.host frames corr) .nil), .nil⟩

/-- A reference host state whose answers lie in a set without solution in its
frames' context yields only doomed tasks and no answer. -/
theorem host_doomed (ref : RefinesStore X isHost R)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P within : Set X.Valuation} {r : RState} (frames : FramesRel L X dest fs gs P)
    (inside : ref.Within within r) (empty : within ∩ P = ∅) :
    (∀ t ∈ (expand (hostedAtReturn L S isHost PA R) ⟨(), .host r, fs⟩).1, HDoomed L X ref t) ∧
      (expand (hostedAtReturn L S isHost PA R) ⟨(), .host r, fs⟩).2 = [] := by
  refine ⟨fun t member => ?_, rfl⟩
  have pulled := ref.pull inside
  unfold hostedAtReturn at member
  rw [expand_host] at member
  generalize R.pull r = p at pulled member
  cases pulled with
  | done => simp [pullBranches] at member
  | yield good sub next =>
      simp only [pullBranches, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · refine .answer _ _ frames good (Set.subset_eq_empty ?_ empty)
        rintro w ⟨⟨inSol, _⟩, inP⟩
        exact ⟨sub inSol, inP⟩
      · exact .host frames next empty
  | suspend next =>
      simp only [pullBranches, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at member
      subst member
      exact .host frames next empty

/-- Corresponding tasks expand to corresponding tasks and answers; the
output-first side may first pass over host suspensions. -/
theorem hexpand_related (aligned : ProgramBindsAhead L PA PF) (spec : HostCorrect X isHost R H)
    (ref : RefinesStore X isHost R) {a : RTask L Rel Op Store RState}
    {b : FTask L Rel Op Store HState} (related : HRelated L X spec a b) (moded : HModed L X a) :
    ∃ ts as, ExpandsTo (hostedFirst L S isHost PF H) b ts as ∧
      Embeds (HRelated L X spec) (HDoomed L X ref) (expand (hostedAtReturn L S isHost PA R) a).1 ts ∧
      List.Forall₂ (SameAnswer X) (expand (hostedAtReturn L S isHost PA R) a).2 as := by
  cases related with
  | tier related =>
      refine ⟨_, _, .one _, ?_⟩
      cases moded with
      | tier moded =>
      cases related with
      | mk frame origin σA σF dest ahead agrees frames goodA goodF sols keys =>
          exact hsuccessors_related aligned spec ref frames
            (inspect_related ahead frame origin dest _ σA σF goodA goodF agrees sols keys moded)
  | answer v σA σF frames goodA goodF sols keys =>
      refine ⟨_, _, .one _, ?_⟩
      unfold hostedAtReturn hostedFirst
      rw [expand_answer, expand_answer]
      obtain ⟨tasks, answers⟩ :=
        successors_related X aligned frames (.ret v σA σF goodA goodF sols keys)
      exact ⟨lift_embeds spec ref tasks, answers⟩
  | host frames corr => exact host_related spec ref frames (spec.pull corr)

/-- A doomed reference task yields only doomed tasks and no answer. -/
theorem hexpand_doomed (aligned : ProgramBindsAhead L PA PF) (ref : RefinesStore X isHost R)
    {a : RTask L Rel Op Store RState} (doomed : HDoomed L X ref a) :
    (∀ t ∈ (expand (hostedAtReturn L S isHost PA R) a).1, HDoomed L X ref t) ∧
      (expand (hostedAtReturn L S isHost PA R) a).2 = [] := by
  cases doomed with
  | tier doomed =>
      cases doomed with
      | failing frame σ fs =>
          exact ⟨fun _ member => by
            simp [expand, expandWith, hostedAtReturn, withHost, compiled, inspectCode,
              liftInstruction] at member, rfl⟩
      | unsatisfiable frame origin σ dest ahead agrees frames good empty =>
          exact hsuccessors_doomed aligned ref frames
            (inspect_doomed ahead frame origin dest _ σ good agrees empty)
  | answer v σ frames good empty =>
      obtain ⟨all, none⟩ := successors_doomed X aligned frames (.ret v σ good empty)
      unfold hostedAtReturn
      rw [expand_answer]
      refine ⟨fun t member => ?_, none⟩
      simp only [List.mem_map] at member
      obtain ⟨t', member', rfl⟩ := member
      rcases t' with ⟨⟨⟩, c, fs'⟩
      exact .tier (all _ member')
  | host frames inside empty => exact host_doomed ref frames inside empty

end Expansions

/-! ## Runs -/

section Runs

variable {Term Store Rel Op RState HState : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}
  {PA PF : EqProgram L Rel Op}

/-- **Host calls compose with output-first refinement.**  For programs related
by `ProgramBindsAhead`, a reference evaluator that refines stores, a host meeting
its per-call specification, corresponding start states and a moded reference
run: after `n` reference steps, the output-first machine with host calls has
taken some number of steps after which the states still correspond. -/
theorem hosted_simulates (aligned : ProgramBindsAhead L PA PF) (spec : HostCorrect X isHost R H)
    (ref : RefinesStore X isHost R)
    {sA : State Unit (Node (Control L Rel Op Store) RState (Answer Term Store))
      (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (Node (DestControl L Rel Op Store) HState (Answer Term Store))
      (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (HRelated L X spec) (HDoomed L X ref) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA R)) m sA).frontier,
      HModed L X t)
    (n : ℕ) :
    ∃ n', Simulates (HRelated L X spec) (HDoomed L X ref) (SameAnswer X)
      (repeats (step (hostedAtReturn L S isHost PA R)) n sA)
      (repeats (step (hostedFirst L S isHost PF H)) n' sF) :=
  simulates_repeats_stutter _ _ (HModed L X)
    (fun _ _ related m => hexpand_related aligned spec ref related m)
    (fun _ doomed => hexpand_doomed aligned ref doomed) n sA sF start (fun m _ => moded m)

/-- **The prefix law with host calls.**  Every answer list the reference has
delivered within `n` steps, the output-first machine with host calls has
delivered after some number of steps, answer for answer. -/
theorem hosted_answers (aligned : ProgramBindsAhead L PA PF) (spec : HostCorrect X isHost R H)
    (ref : RefinesStore X isHost R)
    {sA : State Unit (Node (Control L Rel Op Store) RState (Answer Term Store))
      (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (Node (DestControl L Rel Op Store) HState (Answer Term Store))
      (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (HRelated L X spec) (HDoomed L X ref) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA R)) m sA).frontier,
      HModed L X t)
    (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X) (repeats (step (hostedAtReturn L S isHost PA R)) n sA).emitted
      (repeats (step (hostedFirst L S isHost PF H)) n' sF).emitted :=
  let ⟨n', sim⟩ := hosted_simulates aligned spec ref start moded n
  ⟨n', sim.2⟩

/-- **Termination with host calls.**  When the reference exhausts its frontier
within `n` steps, the output-first machine with host calls exhausts its own
after some number of steps, having delivered the same ordered answers. -/
theorem hosted_terminates (aligned : ProgramBindsAhead L PA PF) (spec : HostCorrect X isHost R H)
    (ref : RefinesStore X isHost R)
    {sA : State Unit (Node (Control L Rel Op Store) RState (Answer Term Store))
      (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (Node (DestControl L Rel Op Store) HState (Answer Term Store))
      (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (HRelated L X spec) (HDoomed L X ref) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA R)) m sA).frontier,
      HModed L X t)
    (n : ℕ) (done : (repeats (step (hostedAtReturn L S isHost PA R)) n sA).frontier = []) :
    ∃ n', (repeats (step (hostedFirst L S isHost PF H)) n' sF).frontier = [] ∧
      List.Forall₂ (SameAnswer X) (repeats (step (hostedAtReturn L S isHost PA R)) n sA).emitted
        (repeats (step (hostedFirst L S isHost PF H)) n' sF).emitted := by
  obtain ⟨n', embeds, answers⟩ := hosted_simulates aligned spec ref start moded n
  rw [done] at embeds
  exact ⟨n', embeds.eq_nil, answers⟩

omit [DecidableEq Rel] in
/-- Corresponding tier states correspond in the machines with host calls. -/
theorem simulates_lift (spec : HostCorrect X isHost R H) (ref : RefinesStore X isHost R)
    {sA : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF) :
    Simulates (HRelated L X spec) (HDoomed L X ref) (SameAnswer X)
      (liftState (HState := RState) sA) (liftState (HState := HState) sF) :=
  ⟨lift_embeds spec ref start.1, start.2⟩

/-- A query control with host calls: the prefix law. -/
theorem hosted_query_answers (aligned : ProgramBindsAhead L PA PF)
    (spec : HostCorrect X isHost R H) (ref : RefinesStore X isHost R) {k : ℕ}
    {late early : Code L Rel Op k} (ahead : BindsAhead L [] late early) (frame : Fin k → Term)
    (σ : Store) (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA R)) m
      (liftState (queryState L late frame σ))).frontier, HModed L X t) (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X)
      (repeats (step (hostedAtReturn L S isHost PA R)) n (liftState (queryState L late frame σ))).emitted
      (repeats (step (hostedFirst L S isHost PF H)) n'
        (liftState (queryStateOut L early frame σ))).emitted :=
  hosted_answers aligned spec ref (simulates_lift spec ref (simulates_query X ahead frame σ good))
    moded n

/-- A query control with host calls: termination with the same ordered answers. -/
theorem hosted_query_terminates (aligned : ProgramBindsAhead L PA PF)
    (spec : HostCorrect X isHost R H) (ref : RefinesStore X isHost R) {k : ℕ}
    {late early : Code L Rel Op k} (ahead : BindsAhead L [] late early) (frame : Fin k → Term)
    (σ : Store) (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA R)) m
      (liftState (queryState L late frame σ))).frontier, HModed L X t) (n : ℕ)
    (done : (repeats (step (hostedAtReturn L S isHost PA R)) n
      (liftState (queryState L late frame σ))).frontier = []) :
    ∃ n', (repeats (step (hostedFirst L S isHost PF H)) n'
        (liftState (queryStateOut L early frame σ))).frontier = [] ∧
      List.Forall₂ (SameAnswer X)
        (repeats (step (hostedAtReturn L S isHost PA R)) n
          (liftState (queryState L late frame σ))).emitted
        (repeats (step (hostedFirst L S isHost PF H)) n'
          (liftState (queryStateOut L early frame σ))).emitted :=
  hosted_terminates aligned spec ref (simulates_lift spec ref (simulates_query X ahead frame σ good))
    moded n done

end Runs

/-! ## Collections -/

section Collection

variable {Term Store Rel Op RState HState : Type}
variable {S : StoreAlgebra Term Store Op} (X : ExactStore S)
variable {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}

/-- A host answer corresponding to a reference answer in the context `Q`
against the destination `dest`. -/
def AnswerRel (Q : Set X.Valuation) (dest : Option Term) (a b : Answer Term Store) : Prop :=
  X.WellFormed a.2 ∧ X.WellFormed b.2 ∧ a.1 = b.1 ∧
    X.solutions b.2 = X.solutions a.2 ∩ meets X (some a.1) dest ∩ Q ∧ X.supply b.2 = X.supply a.2

/-- A reference answer without solution in the context `Q` against `dest`. -/
def AnswerOmitted (Q : Set X.Valuation) (dest : Option Term) (a : Answer Term Store) : Prop :=
  X.WellFormed a.2 ∧ X.solutions a.2 ∩ meets X (some a.1) dest ∩ Q = ∅

variable {X}

theorem Embeds.forall₂ {α β : Type} {R' : α → β → Prop} {D : α → Prop} (never : ∀ a, ¬ D a) :
    ∀ {as : List α} {bs : List β}, Embeds R' D as bs → List.Forall₂ R' as bs
  | _, _, .nil => .nil
  | _, _, .keep r rest => .cons r (Embeds.forall₂ never rest)
  | _, _, .drop d _ => absurd d (never _)

/-- **The host's collection.**  When the reference evaluator exhausts a goal
within `n` pulls, the host exhausts it too; its collection is the reference's
with the answers that have no solution in the context omitted, every other
answer corresponding, in order. -/
theorem collect_host (spec : HostCorrect X isHost R H) {Q : Set X.Valuation}
    {dest : Option Term} :
    ∀ (n : ℕ) {r : RState} {h : HState}, spec.Corr Q dest r h →
      ∀ {as : List (Answer Term Store)}, collect R.pull n r = some as →
        ∃ n' bs, collect H.pull n' h = some bs ∧
          Embeds (AnswerRel X Q dest) (AnswerOmitted X Q dest) as bs
  | 0, _, _, _, _, collected => by simp [collect] at collected
  | n + 1, r, h, corr, as, collected => by
      have progress := spec.pull corr
      clear corr
      induction progress generalizing as with
      | pulls pulledR pulledH pulls =>
          cases pulls with
          | done =>
              simp only [collect, pulledR, Option.some.injEq] at collected
              subst collected
              exact ⟨1, [], by simp [collect, pulledH], .nil⟩
          | @yield v σA σF r' h' goodA goodF sols keys next =>
              simp only [collect, pulledR] at collected
              rw [Option.map_eq_some_iff] at collected
              obtain ⟨rest, restCollected, rfl⟩ := collected
              obtain ⟨n', bs, hostCollected, embeds⟩ := collect_host spec n next restCollected
              exact ⟨n' + 1, (v, σF) :: bs, by simp [collect, pulledH, hostCollected],
                .keep ⟨goodA, goodF, rfl, sols, keys⟩ embeds⟩
      | hostDelay pulled _ ih =>
          obtain ⟨n', bs, hostCollected, embeds⟩ := ih _ collected
          exact ⟨n' + 1, bs, by simp [collect, pulled, hostCollected], embeds⟩
      | refDelay pulled corr =>
          simp only [collect, pulled] at collected
          exact collect_host spec n corr collected
      | prune pulled good empty corr =>
          simp only [collect, pulled] at collected
          rw [Option.map_eq_some_iff] at collected
          obtain ⟨rest, restCollected, rfl⟩ := collected
          obtain ⟨n', bs, hostCollected, embeds⟩ := collect_host spec n corr restCollected
          exact ⟨n', bs, hostCollected, .drop ⟨good, empty⟩ embeds⟩

/-- **The collection of a goal with no destination** (the argument of a
`collapse` whose context adds no constraint): the host's collection is the
reference's, answer for answer: the same values, and stores with the same
solutions and supply. -/
theorem collect_host_start (spec : HostCorrect X isHost R H) {rel : Rel} {args : List Term}
    {σ : Store} (hit : isHost rel = true) (good : X.WellFormed σ) (n : ℕ)
    {as : List (Answer Term Store)} (collected : collect R.pull n (R.start (rel, args, σ)) = some as) :
    ∃ n' bs, collect H.pull n' (H.start (rel, args, σ, none)) = some bs ∧
      List.Forall₂ (AnswerRel X Set.univ none) as bs := by
  obtain ⟨n', bs, hostCollected, embeds⟩ :=
    collect_host spec n (spec.start hit good good (by rw [Set.inter_univ]) rfl) collected
  refine ⟨n', bs, hostCollected, Embeds.forall₂ (fun a omitted => ?_) embeds⟩
  obtain ⟨good', empty⟩ := omitted
  simp only [meets_none_right, Set.inter_univ] at empty
  exact (X.wellFormed_nonempty good').ne_empty empty

end Collection

section RunCollection

variable {Term Store Rel Op RState HState : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}
  {PA PF : EqProgram L Rel Op}

/-- **Collection by output first.**  When the output-at-return run of an
argument publishes its collection within `n` steps, the output-first run of the
same argument publishes within `n' ≤ n` steps a collection corresponding answer
for answer. -/
theorem outputFirst_collect (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m sA).frontier, Moded L X t)
    (n : ℕ) {as : List (Unit × Answer Term Store)}
    (collected : collectRun (compiled L S PA) n sA = some as) :
    ∃ n' ≤ n, ∃ bs, collectRun (outputFirst L S PF) n' sF = some bs ∧
      List.Forall₂ (SameAnswer X) as bs := by
  obtain ⟨done, rfl⟩ := collectRun_eq_some.mp collected
  obtain ⟨n', le, doneF, answers⟩ := outputFirst_terminates X aligned start moded n done
  exact ⟨n', le, _, collectRun_eq_some.mpr ⟨doneF, rfl⟩, answers⟩

/-- **Collection with host calls.**  When the reference run publishes its
collection within `n` steps, the output-first run with host calls publishes,
after some number of steps, a collection corresponding answer for answer. -/
theorem hosted_collect (aligned : ProgramBindsAhead L PA PF) (spec : HostCorrect X isHost R H)
    (ref : RefinesStore X isHost R)
    {sA : State Unit (Node (Control L Rel Op Store) RState (Answer Term Store))
      (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (Node (DestControl L Rel Op Store) HState (Answer Term Store))
      (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (HRelated L X spec) (HDoomed L X ref) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA R)) m sA).frontier,
      HModed L X t)
    (n : ℕ) {as : List (Unit × Answer Term Store)}
    (collected : collectRun (hostedAtReturn L S isHost PA R) n sA = some as) :
    ∃ n' bs, collectRun (hostedFirst L S isHost PF H) n' sF = some bs ∧
      List.Forall₂ (SameAnswer X) as bs := by
  obtain ⟨done, rfl⟩ := collectRun_eq_some.mp collected
  obtain ⟨n', doneF, answers⟩ := hosted_terminates aligned spec ref start moded n done
  exact ⟨n', _, collectRun_eq_some.mpr ⟨doneF, rfl⟩, answers⟩

end RunCollection

/-! ## An enumerating host -/

section Enumeration

variable {Term Store Rel Op : Type}

/-- The reference evaluator of an enumeration goal (a `superpose` of the values
the goal names): each value in order, in the call's store. -/
def enumReference (values : Rel → List Term → List Term) :
    Host (Call Term Store Rel) (List Term × Store) (Answer Term Store) where
  start c := (values c.1 c.2.1, c.2.2)
  pull
    | ([], _) => .done
    | (v :: vs, σ) => .yield (v, σ) (vs, σ)

/-- The same goal served against its destination, as `(let E G E)`: each value
in order, unified with the destination in the host's store; a value that does
not unify with it is passed over with a suspension. -/
def enumHost (S : StoreAlgebra Term Store Op) (values : Rel → List Term → List Term) :
    Host (DestCall Term Store Rel) (List Term × Store × Option Term) (Answer Term Store) where
  start c := (values c.1 c.2.1, c.2.2.1, c.2.2.2)
  pull
    | ([], _, _) => .done
    | (v :: vs, σ, none) => .yield (v, σ) (vs, σ, none)
    | (v :: vs, σ, some e) =>
        match S.unify v e σ with
        | some σ' => .yield (v, σ') (vs, σ, some e)
        | none => .suspend (vs, σ, some e)

variable {S : StoreAlgebra Term Store Op} (X : ExactStore S) (values : Rel → List Term → List Term)

/-- The enumerating reference evaluator refines stores: its answers keep the
call's store. -/
def enumRefines (isHost : Rel → Bool) : RefinesStore X isHost (enumReference values) where
  Within within r := X.WellFormed r.2 ∧ X.solutions r.2 ⊆ within
  start _ good := ⟨good, subset_rfl⟩
  pull {within r} inside := by
    obtain ⟨vs, σ⟩ := r
    cases vs with
    | nil => exact .done
    | cons v vs => exact .yield inside.1 inside.2 inside

/-- **The enumerating host meets the specification.**  It is not the reference:
it runs in the refined store and meets the destination, omitting the values
that do not unify with it. -/
def enumCorrect (isHost : Rel → Bool) :
    HostCorrect X isHost (enumReference values) (enumHost S values) where
  Corr Q dest r h := ∃ (vs : List Term) (σA σF : Store), r = (vs, σA) ∧ h = (vs, σF, dest) ∧
    X.WellFormed σA ∧ X.WellFormed σF ∧ X.solutions σF = X.solutions σA ∩ Q ∧
    X.supply σF = X.supply σA
  start {_ _ σA σF _ _} _ goodA goodF sols keys := ⟨_, σA, σF, rfl, rfl, goodA, goodF, sols, keys⟩
  pull {Q dest r h} corr := by
    obtain ⟨vs, σA, σF, rfl, rfl, goodA, goodF, sols, keys⟩ := corr
    cases vs with
    | nil => exact .pulls rfl rfl .done
    | cons v vs =>
        have next : ∃ (ws : List Term) (σA' σF' : Store), (vs, σA) = (ws, σA') ∧
            (vs, σF, dest) = (ws, σF', dest) ∧ X.WellFormed σA' ∧ X.WellFormed σF' ∧
            X.solutions σF' = X.solutions σA' ∩ Q ∧ X.supply σF' = X.supply σA' :=
          ⟨vs, σA, σF, rfl, rfl, goodA, goodF, sols, keys⟩
        cases dest with
        | none =>
            refine .pulls rfl rfl (.yield goodA goodF ?_ keys next)
            rw [sols, meets_none_right, Set.inter_univ]
        | some e =>
            cases unified : S.unify v e σF with
            | some σF' =>
                refine .pulls rfl (by simp [enumHost, unified])
                  (.yield goodA (X.unify_wellFormed goodF unified) ?_
                    ((X.unify_supply unified).trans keys) next)
                rw [X.unify_some goodF unified, sols]
                ext w
                simp only [Set.mem_inter_iff, mem_meets_some, Set.mem_ofPred_eq]
                tauto
            | none =>
                refine .hostDelay (by simp [enumHost, unified]) (.prune rfl goodA ?_ next)
                have empty := X.unify_none goodF unified
                rw [sols] at empty
                refine Set.subset_eq_empty ?_ empty
                rintro w ⟨⟨inA, inMeets⟩, inQ⟩
                exact ⟨⟨inA, inQ⟩, mem_meets_some.mp inMeets⟩

end Enumeration

end Mettapedia.GSLT.LanguageDef.HostCalls
