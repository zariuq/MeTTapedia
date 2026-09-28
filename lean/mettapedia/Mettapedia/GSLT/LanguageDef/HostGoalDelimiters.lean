import Mettapedia.GSLT.LanguageDef.HostGoalRefinement

/-!
# Delimiters over host goals

**Streams.**  `delivered pull n h` lists the answers a host delivers within `n`
pulls.  `once pull n h` is its first answer: `some none` when the goal is
exhausted without one, `none` when the pulls run out first (`once_some`,
`once_of_delivered`, `once_none`).  `collect_unique`: a published collection
does not depend on the number of pulls allowed.

**The prefix law of a host** (`delivered_host`).  For any host meeting
`HostCorrect`, every answer list the reference evaluator has delivered, the
host has delivered after some number of pulls: the omitted answers removed and
every other one corresponding, in order.  It is the per-goal counterpart of
`hosted_answers`, as `collect_host` is of `hosted_terminates`.

**`once`.**  `once` over a host goal is the first answer of its host.
`once_host`: when the reference's `once` is decided and its first answer, if
any, is not omitted, the host's `once` is decided with the corresponding first
answer, or neither side has one.  It is derived from the prefix law, and from
`collect_host` when there is no answer.  The condition is exact: when the
reference's first answer is omitted, the two `once`s select different answers
(`HostGoalControls.pairs_delimiters`: against the destination `(S $5)` the
reference's `once` of `(pairs)` is `Z` and the output-first host's is `(S Z)`).
With no destination and no context nothing is omitted (`once_host_start`), and
`machines_once` states that case for the machines as hosts.

**`collapse`** is `collect_host`.  `machines_collect`: when the output-at-return
run of a host goal exhausts its frontier and publishes its answers, the
output-first run of the goal, against its destination and in the refined store,
exhausts its own and publishes the same answers with the omitted ones removed
and every other one corresponding, in order.  Neither host publishes a
collection while its run is live (`referenceHost_collect`,
`outputFirstHost_collect`, `collectRun_eq_none`).  With no destination and no
context the two collections correspond answer for answer
(`machines_collapse_start`).

**Not covered.**  A `once` or `collapse` value is the same on both sides only
when nothing is omitted.  A context of bindings made ahead can omit answers of
the goal, and then these results relate the two streams but do not make the two
values equal.  `once` and `collapse` here are delimiters over a host's answer
stream; the programs' equations contain neither.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls

/-! ## Streams of answers -/

section Streams

variable {HState Answer : Type}

/-- The answers a host delivers within `n` pulls, in order. -/
def delivered (pull : HState → Pull HState Answer) : ℕ → HState → List Answer
  | 0, _ => []
  | n + 1, h =>
      match pull h with
      | .done => []
      | .yield a h' => a :: delivered pull n h'
      | .suspend h' => delivered pull n h'

/-- `once` over a goal: its first answer within `n` pulls, `some none` when the
goal is exhausted without one, and `none` when the pulls run out first. -/
def once (pull : HState → Pull HState Answer) : ℕ → HState → Option (Option Answer)
  | 0, _ => none
  | n + 1, h =>
      match pull h with
      | .done => some none
      | .yield a _ => some (some a)
      | .suspend h' => once pull n h'

/-- A first answer is the first answer delivered. -/
theorem once_some {pull : HState → Pull HState Answer} {a : Answer} :
    ∀ {n : ℕ} {h : HState}, once pull n h = some (some a) →
      ∃ rest, delivered pull n h = a :: rest
  | 0, _, decided => by simp [once] at decided
  | n + 1, h, decided => by
      cases pulled : pull h with
      | done => simp [once, pulled] at decided
      | yield b h' =>
          simp only [once, pulled, Option.some.injEq] at decided
          subst decided
          exact ⟨delivered pull n h', by simp [delivered, pulled]⟩
      | suspend h' =>
          simp only [once, pulled] at decided
          obtain ⟨rest, found⟩ := once_some decided
          exact ⟨rest, by simp [delivered, pulled, found]⟩

/-- The first answer delivered is the first answer. -/
theorem once_of_delivered {pull : HState → Pull HState Answer} {a : Answer} {rest : List Answer} :
    ∀ {n : ℕ} {h : HState}, delivered pull n h = a :: rest → once pull n h = some (some a)
  | 0, _, found => by simp [delivered] at found
  | n + 1, h, found => by
      cases pulled : pull h with
      | done => simp [delivered, pulled] at found
      | yield b h' =>
          simp only [delivered, pulled, List.cons.injEq] at found
          simp [once, pulled, found.1]
      | suspend h' =>
          simp only [delivered, pulled] at found
          simp only [once, pulled]
          exact once_of_delivered found

/-- A goal has no first answer exactly when its collection is empty. -/
theorem once_none {pull : HState → Pull HState Answer} :
    ∀ {n : ℕ} {h : HState}, once pull n h = some none ↔ collect pull n h = some []
  | 0, _ => by simp [once, collect]
  | n + 1, h => by
      cases pulled : pull h with
      | done => simp [once, collect, pulled]
      | yield a h' => simp [once, collect, pulled]
      | suspend h' =>
          simp only [once, collect, pulled]
          exact once_none

/-- A published collection does not depend on the number of pulls allowed. -/
theorem collect_unique {pull : HState → Pull HState Answer} :
    ∀ {n m : ℕ} {h : HState} {as bs : List Answer}, collect pull n h = some as →
      collect pull m h = some bs → as = bs
  | 0, _, _, _, _, first, _ => by simp [collect] at first
  | _ + 1, 0, _, _, _, _, second => by simp [collect] at second
  | n + 1, m + 1, h, as, bs, first, second => by
      cases pulled : pull h with
      | done =>
          simp only [collect, pulled, Option.some.injEq] at first second
          rw [← first, ← second]
      | yield a h' =>
          simp only [collect, pulled, Option.map_eq_some_iff] at first second
          obtain ⟨as', first', rfl⟩ := first
          obtain ⟨bs', second', rfl⟩ := second
          rw [collect_unique first' second']
      | suspend h' =>
          simp only [collect, pulled] at first second
          exact collect_unique first second

end Streams

/-! ## The prefix law of a host, and `once` -/

section HostPrefix

variable {Term Store Rel Op RState HState : Type} {S : StoreAlgebra Term Store Op}
  {X : ExactStore S} {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}

/-- **The prefix law of a host.**  Every answer list the reference evaluator
delivers within `n` pulls, the host delivers within some number of pulls: the
reference's answers with those omitted that have no solution in the context
against the destination, every other one corresponding, in order. -/
theorem delivered_host (spec : HostCorrect X isHost R H) {Q : Set X.Valuation}
    {dest : Option Term} :
    ∀ (n : ℕ) {r : RState} {h : HState}, spec.Corr Q dest r h →
      ∃ n', Embeds (AnswerRel X Q dest) (AnswerOmitted X Q dest) (delivered R.pull n r)
        (delivered H.pull n' h)
  | 0, _, _, _ => ⟨0, .nil⟩
  | n + 1, r, h, corr => by
      have progress := spec.pull corr
      clear corr
      induction progress with
      | pulls pulledR pulledH pulls =>
          cases pulls with
          | done => exact ⟨1, by simp only [delivered, pulledR, pulledH]; exact .nil⟩
          | @yield v σA σF r' h' goodA goodF sols keys next =>
              obtain ⟨n', rest⟩ := delivered_host spec n next
              exact ⟨n' + 1, by
                simp only [delivered, pulledR, pulledH]
                exact .keep ⟨goodA, goodF, rfl, sols, keys⟩ rest⟩
      | hostDelay pulled _ ih =>
          obtain ⟨n', rest⟩ := ih
          exact ⟨n' + 1, by simp only [delivered, pulled]; exact rest⟩
      | refDelay pulled corr =>
          obtain ⟨n', rest⟩ := delivered_host spec n corr
          exact ⟨n', by simp only [delivered, pulled]; exact rest⟩
      | prune pulled good empty corr =>
          obtain ⟨n', rest⟩ := delivered_host spec n corr
          exact ⟨n', by simp only [delivered, pulled]; exact .drop ⟨good, empty⟩ rest⟩

/-- **`once` over a host goal.**  When the reference evaluator's `once` is
decided within `n` pulls, and its first answer, if any, is not omitted, the
host's `once` is decided within some number of pulls: the corresponding first
answer, or none on both sides.  Derived from the prefix law, and from
`collect_host` for the goal without answers. -/
theorem once_host (spec : HostCorrect X isHost R H) {Q : Set X.Valuation} {dest : Option Term}
    {n : ℕ} {r : RState} {h : HState} (corr : spec.Corr Q dest r h)
    {first : Option (Answer Term Store)} (decided : once R.pull n r = some first)
    (kept : ∀ a, first = some a → ¬ AnswerOmitted X Q dest a) :
    ∃ n' first', once H.pull n' h = some first' ∧
      Option.Rel (AnswerRel X Q dest) first first' := by
  cases first with
  | none =>
      obtain ⟨n', bs, collected, embeds⟩ := collect_host spec n corr (once_none.mp decided)
      rw [embeds.eq_nil] at collected
      exact ⟨n', none, once_none.mpr collected, .none⟩
  | some a =>
      obtain ⟨rest, found⟩ := once_some decided
      obtain ⟨n', embeds⟩ := delivered_host spec n corr
      rw [found] at embeds
      generalize produced : delivered H.pull n' h = bs at embeds
      cases embeds with
      | @keep _ b _ bs' same _ => exact ⟨n', some b, once_of_delivered produced, .some same⟩
      | drop omitted _ => exact absurd omitted (kept a rfl)

/-- **`once` over a goal with no destination and no context**: nothing is
omitted, so the two first answers correspond, or neither side has one. -/
theorem once_host_start (spec : HostCorrect X isHost R H) {rel : Rel} {args : List Term}
    {σ : Store} (hit : isHost rel = true) (good : X.WellFormed σ) {n : ℕ}
    {first : Option (Answer Term Store)}
    (decided : once R.pull n (R.start (rel, args, σ)) = some first) :
    ∃ n' first', once H.pull n' (H.start (rel, args, σ, none)) = some first' ∧
      Option.Rel (AnswerRel X Set.univ none) first first' :=
  once_host spec (spec.start hit good good (by rw [Set.inter_univ]) rfl) decided
    fun _ _ omitted => by
      obtain ⟨good', empty⟩ := omitted
      simp only [meets_none_right, Set.inter_univ] at empty
      exact (X.wellFormed_nonempty good').ne_empty empty

end HostPrefix

/-! ## Delimiters over the two machines -/

section Machines

variable {Term Store Rel Op : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {PA PF : EqProgram L Rel Op} {isHost : Rel → Bool}

/-- **`once` over a host goal evaluated by the machines.**  When the
output-at-return evaluation of a host goal decides its first answer, the
output-first evaluation of the goal in the same store with no destination
decides a corresponding one, or both have none. -/
theorem machines_once (aligned : ProgramBindsAhead L PA PF)
    (goalsModed : GoalsModed L S X isHost PA) {rel : Rel} {args : List Term} {σ : Store}
    (hit : isHost rel = true) (good : X.WellFormed σ) {n : ℕ}
    {first : Option (Answer Term Store)}
    (decided : once (referenceHost L S PA).pull n (initial L S PA (rel, args, σ)).frontier =
      some first) :
    ∃ n' first',
      once (outputFirstHost L S PF).pull n' (goalTasksOut L S PF (rel, args, σ, none)) =
        some first' ∧ Option.Rel (AnswerRel X Set.univ none) first first' :=
  once_host_start (machinesCorrect L S X aligned goalsModed) hit good decided

/-- **`collapse` over a host goal evaluated by the machines.**  When the
goal's output-at-return run exhausts its frontier within `n` steps, publishing
its answers `as`, the goal's output-first run against the destination `dest`,
in a store refined by the context `Q`, exhausts its own and publishes `bs`:
the answers of `as` with those omitted that have no solution in `Q` against
`dest`, every other one corresponding, in order.  The collection is published
only once the run is exhausted (`referenceHost_collect`, `collectRun_eq_none`). -/
theorem machines_collect (aligned : ProgramBindsAhead L PA PF)
    (goalsModed : GoalsModed L S X isHost PA) {rel : Rel} {args : List Term} {σA σF : Store}
    {dest : Option Term} {Q : Set X.Valuation} (hit : isHost rel = true)
    (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
    (sols : X.solutions σF = X.solutions σA ∩ Q) (keys : X.supply σF = X.supply σA) {n : ℕ}
    {as : List (Unit × Answer Term Store)}
    (collected : collectRun (compiled L S PA) n (initial L S PA (rel, args, σA)) = some as) :
    ∃ n' bs,
      collectRun (outputFirst L S PF) n' ⟨goalTasksOut L S PF (rel, args, σF, dest), []⟩ =
        some bs ∧
      Embeds (AnswerRel X Q dest) (AnswerOmitted X Q dest) (as.map Prod.snd) (bs.map Prod.snd) := by
  have hostCollected : collect (referenceHost L S PA).pull (n + 1)
      ((referenceHost L S PA).start (rel, args, σA)) = some (as.map Prod.snd) := by
    rw [referenceHost_collect, collected]
    rfl
  obtain ⟨n', bs', collectedF, embeds⟩ :=
    collect_host (machinesCorrect L S X aligned goalsModed) (n + 1)
      ((machinesCorrect L S X aligned goalsModed).start hit goodA goodF sols keys) hostCollected
  cases n' with
  | zero => simp [collect] at collectedF
  | succ n' =>
      rw [outputFirstHost_collect] at collectedF
      obtain ⟨bs, run, rfl⟩ := Option.map_eq_some_iff.mp collectedF
      exact ⟨n', bs, run, embeds⟩

/-- **`collapse` over a goal with no destination and no context**: the two
collections correspond answer for answer. -/
theorem machines_collapse_start (aligned : ProgramBindsAhead L PA PF)
    (goalsModed : GoalsModed L S X isHost PA) {rel : Rel} {args : List Term} {σ : Store}
    (hit : isHost rel = true) (good : X.WellFormed σ) {n : ℕ}
    {as : List (Unit × Answer Term Store)}
    (collected : collectRun (compiled L S PA) n (initial L S PA (rel, args, σ)) = some as) :
    ∃ n' bs, collectRun (outputFirst L S PF) n' (initialOut L S PF (rel, args, σ)) = some bs ∧
      List.Forall₂ (fun a b : Unit × Answer Term Store => AnswerRel X Set.univ none a.2 b.2)
        as bs := by
  have hostCollected : collect (referenceHost L S PA).pull (n + 1)
      ((referenceHost L S PA).start (rel, args, σ)) = some (as.map Prod.snd) := by
    rw [referenceHost_collect, collected]
    rfl
  obtain ⟨n', bs', collectedF, same⟩ :=
    collect_host_start (machinesCorrect L S X aligned goalsModed) hit good (n + 1) hostCollected
  cases n' with
  | zero => simp [collect] at collectedF
  | succ n' =>
      rw [outputFirstHost_collect] at collectedF
      obtain ⟨bs, run, rfl⟩ := Option.map_eq_some_iff.mp collectedF
      refine ⟨n', bs, run, ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at same
      exact same

end Machines

end Mettapedia.GSLT.LanguageDef.HostGoals
