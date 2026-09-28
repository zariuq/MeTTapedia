import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters
import Mettapedia.GSLT.LanguageDef.HostGoalElimination

/-!
# `once` under the order doctrine

Search order is not part of the specification: an observation is the bag of a
goal's answers, and `once` answers some witness of it.
`HostGoalDelimiters.once_host` compares the output-first `once` with the
reference's first answer, so it needs that answer to be kept.  Under the order
doctrine the comparison is with the bag.

**Search trees and bags.**  `Spawns P t u`: `u` is `t` or a task of its search
tree.  `InBag P frontier x`: `x` is delivered somewhere in the search tree of a
task of the frontier, in no particular order.  A run's tasks are in the trees
of its start (`spawned_of_run`), and every answer a run used as a host delivers
is in the bag of its start (`delivered_inBag`).  The bag can hold more: a
depth-first run delivers nothing that lies after a branch that never ends.

**For any host meeting `HostCorrect`.**  `once_host_some`: when the reference
delivers an answer that is not omitted, the host's `once` finds an answer; this
follows from the prefix law `delivered_host`.  When the reference's run of the
goal is exhausted, publishing `as`, the host's `once` answers an element of
`as` met with the destination and the context (`once_host_witness`), and finds
none only when every element of `as` is omitted (`once_host_fails`).

**For the machines as hosts, over the bag.**  `once_witness_bag`: the answer the
output-first run's `once` returns corresponds to an answer in the bag of the
related reference frontier.  `once_fails_bag`: it finds none only when every
answer of that bag is omitted.  The output-first run drives the proof: each of
its steps expands the related reference task in place, not in the reference's
order, so the reference need not reach the witness at all.
`machines_once_witness`, `machines_once_fails` and `machines_once_some` state
the three laws for a host call.  Together, the output-first `once` returns a
witness of the reference's answer bag that meets the destination and has a
solution in the context, fails only when no such witness exists, and succeeds
whenever the reference delivers one.

**The side condition.**  `GoalTreesModed`: every task of the search tree of a
host goal's reference evaluation is moded, where `GoalsModed` asks it only
along the reference's run.  It implies `GoalsModed`
(`goalsModed_of_goalTreesModed`) and follows when every task is moded
(`goalTreesModed_of_moded`).

**Not covered.**  Over the reference's delivered answers, rather than its bag,
the witness law fails without termination:
`HostGoalOrderControls.loop_doctrine` has a goal whose reference evaluation runs
a doomed branch forever and delivers nothing, while the output-first `once`
answers a witness from the bag.  `once` is a delimiter over a host's answer
stream, as in `HostGoalDelimiters`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Search trees and answer bags -/

section Bags

variable {C K Call' F A : Type}

/-- `Spawns P t u`: `u` is `t` or a task of its search tree. -/
inductive Spawns (P : Program C K Call' F A) : Task C K F → Task C K F → Prop
  | refl (t : Task C K F) : Spawns P t t
  | step {t u v : Task C K F} : u ∈ (expand P t).1 → Spawns P u v → Spawns P t v

theorem Spawns.tail {P : Program C K Call' F A} {t u v : Task C K F} (spawns : Spawns P t u)
    (next : v ∈ (expand P u).1) : Spawns P t v := by
  induction spawns with
  | refl t => exact .step next (.refl v)
  | step first _ ih => exact .step first (ih next)

/-- **The answer bag** of a frontier: the answers delivered anywhere in the
search trees of its tasks, in no particular order. -/
def InBag (P : Program C K Call' F A) (frontier : List (Task C K F)) (x : C × A) : Prop :=
  ∃ t ∈ frontier, ∃ u, Spawns P t u ∧ x ∈ (expand P u).2

theorem inBag_now {P : Program C K Call' F A} {frontier : List (Task C K F)} {t : Task C K F}
    (member : t ∈ frontier) {x : C × A} (now : x ∈ (expand P t).2) : InBag P frontier x :=
  ⟨t, member, t, .refl t, now⟩

/-- Expanding a task of a frontier in place keeps its bag or shrinks it. -/
theorem inBag_expand {P : Program C K Call' F A} {before after : List (Task C K F)}
    {a : Task C K F} {x : C × A} (found : InBag P (before ++ ((expand P a).1 ++ after)) x) :
    InBag P (before ++ a :: after) x := by
  obtain ⟨t, member, u, spawns, now⟩ := found
  simp only [List.mem_append] at member
  rcases member with inBefore | inSuccessors | inAfter
  · exact ⟨t, by simp [inBefore], u, spawns, now⟩
  · exact ⟨a, by simp, u, .step inSuccessors spawns, now⟩
  · exact ⟨t, by simp [inAfter], u, spawns, now⟩

/-- An answer of the bag is an answer of the task expanded in place, or it is
in the bag after the expansion. -/
theorem inBag_split {P : Program C K Call' F A} {before after : List (Task C K F)}
    {a : Task C K F} {x : C × A} (found : InBag P (before ++ a :: after) x) :
    x ∈ (expand P a).2 ∨ InBag P (before ++ ((expand P a).1 ++ after)) x := by
  obtain ⟨t, member, u, spawns, now⟩ := found
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with inBefore | rfl | inAfter
  · exact .inr ⟨t, by simp [inBefore], u, spawns, now⟩
  · cases spawns with
    | refl => exact .inl now
    | step first rest => exact .inr ⟨_, by simp [first], u, rest, now⟩
  · exact .inr ⟨t, by simp [inAfter], u, spawns, now⟩

/-- The tasks of a run are in the search trees of its start. -/
theorem spawned_of_run (P : Program C K Call' F A) :
    ∀ (m : ℕ) (frontier : List (Task C K F)) (emitted : List (C × A)) {u : Task C K F},
      u ∈ (repeats (step P) m ⟨frontier, emitted⟩).frontier → ∃ t ∈ frontier, Spawns P t u
  | 0, _, _, u, member => ⟨u, member, .refl u⟩
  | m + 1, [], emitted, u, member => by
      rw [show repeats (step P) (m + 1) ⟨[], emitted⟩ = ⟨[], emitted⟩ from
        repeats_idle P emitted (m + 1)] at member
      exact absurd member List.not_mem_nil
  | m + 1, t :: rest, emitted, u, member => by
      simp only [repeats] at member
      rw [step_cons] at member
      obtain ⟨t', member', spawns⟩ := spawned_of_run P m _ _ member
      rcases List.mem_append.mp member' with successor | below
      · exact ⟨t, List.mem_cons_self, .step successor spawns⟩
      · exact ⟨t', List.mem_cons_of_mem _ below, spawns⟩

end Bags

/-! ## Embeddings -/

section Embedding

variable {α β : Type} {R : α → β → Prop} {D : α → Prop}

/-- The first task of the second list is related to a task of the first,
preceded only by removed tasks. -/
theorem Embeds.split : ∀ {as : List α} {b : β} {bs : List β}, Embeds R D as (b :: bs) →
    ∃ before a after, as = before ++ a :: after ∧ (∀ d ∈ before, D d) ∧ R a b ∧
      Embeds R D after bs
  | _ :: _, _, _, .keep related rest =>
      ⟨[], _, _, rfl, fun _ member => absurd member List.not_mem_nil, related, rest⟩
  | d :: _, _, _, .drop removed rest => by
      obtain ⟨before, a, after, rfl, removedBefore, related, rest'⟩ := Embeds.split rest
      refine ⟨d :: before, a, after, rfl, fun x member => ?_, related, rest'⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact removed
      · exact removedBefore x member

/-- Every element of the second list is related to one of the first. -/
theorem Embeds.related_of_mem : ∀ {as : List α} {bs : List β}, Embeds R D as bs →
    ∀ b ∈ bs, ∃ a ∈ as, R a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .keep related rest, b, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self, related⟩
      · obtain ⟨a, inAs, r⟩ := Embeds.related_of_mem rest b member
        exact ⟨a, List.mem_cons_of_mem _ inAs, r⟩
  | _, _, .drop _ rest, b, member => by
      obtain ⟨a, inAs, r⟩ := Embeds.related_of_mem rest b member
      exact ⟨a, List.mem_cons_of_mem _ inAs, r⟩

/-- An element of the first list that is not removable is related to one of the
second. -/
theorem Embeds.kept : ∀ {as : List α} {bs : List β}, Embeds R D as bs →
    ∀ a ∈ as, ¬ D a → ∃ b ∈ bs, R a b
  | _, _, .nil, _, member, _ => absurd member List.not_mem_nil
  | _, _, .keep related rest, a, member, keep => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self, related⟩
      · obtain ⟨b, inBs, r⟩ := Embeds.kept rest a member keep
        exact ⟨b, List.mem_cons_of_mem _ inBs, r⟩
  | _, _, .drop removed rest, a, member, keep => by
      rcases List.mem_cons.mp member with rfl | member
      · exact absurd removed keep
      · exact Embeds.kept rest a member keep

end Embedding

/-! ## The doctrine law for any host -/

section AnyHost

variable {HState' Answer' : Type}

/-- The first answer of a published collection is the first answer, whatever
the number of pulls allowed. -/
theorem once_of_collect {pull : HState' → Pull HState' Answer'} :
    ∀ {n m : ℕ} {h : HState'} {bs : List Answer'} {first : Option Answer'},
      collect pull n h = some bs → once pull m h = some first → first = bs.head?
  | 0, _, _, _, _, collected, _ => by simp [collect] at collected
  | _ + 1, 0, _, _, _, _, found => by simp [once] at found
  | n + 1, m + 1, h, bs, first, collected, found => by
      cases pulled : pull h with
      | done =>
          simp only [collect, pulled, Option.some.injEq] at collected
          simp only [once, pulled, Option.some.injEq] at found
          rw [← collected, ← found]
          rfl
      | yield a h' =>
          simp only [collect, pulled, Option.map_eq_some_iff] at collected
          obtain ⟨rest, _, rfl⟩ := collected
          simp only [once, pulled, Option.some.injEq] at found
          rw [← found]
          rfl
      | suspend h' =>
          simp only [collect, pulled] at collected
          simp only [once, pulled] at found
          exact once_of_collect collected found

variable {Term Store Rel Op RState HState : Type} {S : StoreAlgebra Term Store Op}
  {X : ExactStore S} {isHost : Rel → Bool}
  {R : Host (Call Term Store Rel) RState (Answer Term Store)}
  {H : Host (DestCall Term Store Rel) HState (Answer Term Store)}

/-- **`once` finds a witness when the reference delivers one.**  When the
reference evaluator delivers, within `n` pulls, an answer that is not omitted,
the host's `once` is decided with some answer.  From the prefix law. -/
theorem once_host_some (spec : HostCorrect X isHost R H) {Q : Set X.Valuation}
    {dest : Option Term} {r : RState} {h : HState} (corr : spec.Corr Q dest r h) {n : ℕ}
    {a : Answer Term Store} (found : a ∈ delivered R.pull n r)
    (kept : ¬ AnswerOmitted X Q dest a) :
    ∃ n' a', once H.pull n' h = some (some a') := by
  obtain ⟨n', embeds⟩ := delivered_host spec n corr
  obtain ⟨b, member, _⟩ := Embeds.kept embeds a found kept
  cases produced : delivered H.pull n' h with
  | nil =>
      rw [produced] at member
      exact absurd member List.not_mem_nil
  | cons b' rest => exact ⟨n', b', once_of_delivered produced⟩

/-- **The witness is one the reference delivers**, when the reference's run of
the goal is exhausted and publishes its answers `as`: the host's `once` answers
an element of `as`, met with the destination and the context. -/
theorem once_host_witness (spec : HostCorrect X isHost R H) {Q : Set X.Valuation}
    {dest : Option Term} {r : RState} {h : HState} (corr : spec.Corr Q dest r h) {n : ℕ}
    {as : List (Answer Term Store)} (collected : collect R.pull n r = some as) {m : ℕ}
    {a' : Answer Term Store} (found : once H.pull m h = some (some a')) :
    ∃ a ∈ as, AnswerRel X Q dest a a' := by
  obtain ⟨n', bs, hostCollected, embeds⟩ := collect_host spec n corr collected
  have head := once_of_collect hostCollected found
  cases bs with
  | nil => simp at head
  | cons b rest =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      exact Embeds.related_of_mem embeds _ List.mem_cons_self

/-- **`once` fails only without a witness**, when the reference's run of the goal
is exhausted: if the host's `once` finds no answer, every answer of the
reference is omitted. -/
theorem once_host_fails (spec : HostCorrect X isHost R H) {Q : Set X.Valuation}
    {dest : Option Term} {r : RState} {h : HState} (corr : spec.Corr Q dest r h) {n : ℕ}
    {as : List (Answer Term Store)} (collected : collect R.pull n r = some as) {m : ℕ}
    (failed : once H.pull m h = some none) : ∀ a ∈ as, AnswerOmitted X Q dest a := by
  obtain ⟨n', bs, hostCollected, embeds⟩ := collect_host spec n corr collected
  have head := once_of_collect hostCollected failed
  cases bs with
  | nil => exact Embeds.forall_of_nil embeds
  | cons b rest => simp at head

end AnyHost

/-- The answers a run used as a host delivers are in the bag of its start. -/
theorem delivered_inBag {C K Call' F A : Type} (P : Program C K Call' F A) :
    ∀ (n : ℕ) (frontier : List (Task C K F)) {a : A}, a ∈ delivered (machinePull P) n frontier →
      ∃ c, InBag P frontier (c, a)
  | 0, _, _, found => absurd found List.not_mem_nil
  | n + 1, [], _, found => by simp [delivered, machinePull] at found
  | n + 1, t :: rest, a, found => by
      rcases expand_delivers P t with silent | ⟨y, delivers⟩
      · simp only [delivered, machinePull_silent _ rest silent] at found
        obtain ⟨c, inBag⟩ := delivered_inBag P n _ found
        exact ⟨c, inBag_expand (before := []) inBag⟩
      · simp only [delivered, machinePull_delivers _ rest delivers, List.mem_cons] at found
        rcases found with rfl | found
        · exact ⟨y.1, inBag_now List.mem_cons_self (by rw [delivers]; exact List.mem_cons_self)⟩
        · obtain ⟨c, t', member, u, spawns, now⟩ := delivered_inBag P n rest found
          exact ⟨c, t', List.mem_cons_of_mem _ member, u, spawns, now⟩

/-! ## The doctrine law for the machines, over answer bags -/

section MachineBags

variable {Term Store Rel Op : Type}
variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op) (X : ExactStore S)
variable [Inhabited Term] [DecidableEq Rel]

/-- Every task of the search trees of a frontier is moded. -/
def TreeModed (PA : EqProgram L Rel Op)
    (v : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))) : Prop :=
  ∀ t ∈ v, ∀ u, Spawns (compiled L S PA) t u → Moded L X u

/-- **Host goals are moded throughout their search trees**, not only along the
reference's run. -/
def GoalTreesModed (isHost : Rel → Bool) (PA : EqProgram L Rel Op) : Prop :=
  ∀ {rel : Rel} {args : List Term} {σ : Store}, isHost rel = true → X.WellFormed σ →
    TreeModed L S X PA (initial L S PA (rel, args, σ)).frontier

variable {L S X}
variable {PA PF : EqProgram L Rel Op} {isHost : Rel → Bool}

theorem goalTreesModed_of_moded
    (moded : ∀ t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op), Moded L X t) :
    GoalTreesModed L S X isHost PA :=
  fun _ _ _ _ u _ => moded u

/-- Moded search trees make moded runs: a run's tasks are in the trees of its
start. -/
theorem goalsModed_of_goalTreesModed (trees : GoalTreesModed L S X isHost PA) :
    GoalsModed L S X isHost PA := by
  intro rel args σ hit good m t member
  obtain ⟨t₀, member₀, spawns⟩ := spawned_of_run (compiled L S PA) m _ [] member
  exact trees hit good t₀ member₀ t spawns

theorem TreeModed.head
    {before after : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    {a : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    (moded : TreeModed L S X PA (before ++ a :: after)) : Moded L X a :=
  moded a (by simp) a (.refl a)

theorem TreeModed.expand
    {before after : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    {a : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    (moded : TreeModed L S X PA (before ++ a :: after)) :
    TreeModed L S X PA (before ++ ((expand (compiled L S PA) a).1 ++ after)) := by
  intro t member u spawns
  simp only [List.mem_append] at member
  rcases member with inBefore | inSuccessors | inAfter
  · exact moded t (by simp [inBefore]) u spawns
  · exact moded a (by simp) u (.step inSuccessors spawns)
  · exact moded t (by simp [inAfter]) u spawns

/-- The search tree of a doomed task is doomed. -/
theorem goalDoomed_spawns (aligned : ProgramBindsAhead L PA PF) {Q : Set X.Valuation}
    {dest : Option Term} {t u : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    (spawns : Spawns (compiled L S PA) t u) :
    GoalDoomed L X dest Q t → GoalDoomed L X dest Q u := by
  induction spawns with
  | refl => exact id
  | step first _ ih => exact fun doomed => ih ((goal_expand_doomed aligned doomed).1 _ first)

/-- Every answer in the bag of doomed tasks is omitted. -/
theorem bag_omitted_of_doomed (aligned : ProgramBindsAhead L PA PF) {Q : Set X.Valuation}
    {dest : Option Term} {v : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    (doomed : ∀ t ∈ v, GoalDoomed L X dest Q t) {x : Unit × Answer Term Store}
    (inBag : InBag (compiled L S PA) v x) : AnswerOmitted X Q dest x.2 := by
  obtain ⟨t, member, u, spawns, now⟩ := inBag
  exact (goal_expand_doomed aligned (goalDoomed_spawns aligned spawns (doomed t member))).2 x now

/-- **The witness is in the reference's bag.**  Whatever answer the output-first
run's `once` returns corresponds to an answer in the bag of the reference
frontier it is related to, in any order: the reference need not deliver it
first, or at all. -/
theorem once_witness_bag (aligned : ProgramBindsAhead L PA PF) {Q : Set X.Valuation}
    {dest : Option Term} :
    ∀ (n : ℕ) {v : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
      {h : List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))},
      Embeds (GoalRelated L X dest Q) (GoalDoomed L X dest Q) v h → TreeModed L S X PA v →
      ∀ {a' : Answer Term Store}, once (machinePull (outputFirst L S PF)) n h = some (some a') →
        ∃ a, InBag (compiled L S PA) v ((), a) ∧ AnswerRel X Q dest a a'
  | 0, _, _, _, _, _, found => by simp [once] at found
  | n + 1, _, [], _, _, _, found => by simp [once, machinePull] at found
  | n + 1, _, b :: hs, embeds, moded, a', found => by
      obtain ⟨before, a, after, rfl, doomedBefore, related, rest⟩ := Embeds.split embeds
      obtain ⟨tasks, answers⟩ := goal_expand_related aligned related moded.head
      rcases expand_delivers (outputFirst L S PF) b with silent | ⟨y, delivers⟩
      · simp only [once, machinePull_silent _ hs silent] at found
        obtain ⟨x, inBag, same⟩ := once_witness_bag aligned n
          (Embeds.prepend doomedBefore (tasks.append rest)) moded.expand found
        exact ⟨x, inBag_expand inBag, same⟩
      · simp only [once, machinePull_delivers _ hs delivers, Option.some.injEq] at found
        subst found
        rw [delivers] at answers
        obtain ⟨x, member, same⟩ := Embeds.related_of_mem answers y List.mem_cons_self
        exact ⟨x.2, inBag_now (by simp) member, same⟩

/-- **`once` fails only without a witness in the reference's bag.**  When the
output-first run's `once` is decided without an answer, every answer in the bag
of the related reference frontier is omitted: it has no solution in the context
against the destination. -/
theorem once_fails_bag (aligned : ProgramBindsAhead L PA PF) {Q : Set X.Valuation}
    {dest : Option Term} :
    ∀ (n : ℕ) {v : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
      {h : List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))},
      Embeds (GoalRelated L X dest Q) (GoalDoomed L X dest Q) v h → TreeModed L S X PA v →
      once (machinePull (outputFirst L S PF)) n h = some none →
        ∀ x, InBag (compiled L S PA) v x → AnswerOmitted X Q dest x.2
  | 0, _, _, _, _, failed => by simp [once] at failed
  | n + 1, _, [], embeds, _, _ => fun _ inBag =>
      bag_omitted_of_doomed aligned (Embeds.forall_of_nil embeds) inBag
  | n + 1, _, b :: hs, embeds, moded, failed => by
      obtain ⟨before, a, after, rfl, doomedBefore, related, rest⟩ := Embeds.split embeds
      obtain ⟨tasks, answers⟩ := goal_expand_related aligned related moded.head
      rcases expand_delivers (outputFirst L S PF) b with silent | ⟨y, delivers⟩
      · simp only [once, machinePull_silent _ hs silent] at failed
        intro x inBag
        rcases inBag_split inBag with now | later
        · rw [silent] at answers
          exact Embeds.forall_of_nil answers x now
        · exact once_fails_bag aligned n (Embeds.prepend doomedBefore (tasks.append rest))
            moded.expand failed x later
      · simp [once, machinePull_delivers _ hs delivers] at failed

/-- **`once` over a host goal answers a witness of the reference's bag.**  For a
host call made by the reference in `σA` and on the output-first side in `σF`
refined by the context `Q`, with destination `dest`: an answer the output-first
host's `once` returns corresponds to an answer in the bag of the goal's
output-at-return evaluation, which therefore meets `dest` and has a solution in
`Q`. -/
theorem machines_once_witness (aligned : ProgramBindsAhead L PA PF)
    (trees : GoalTreesModed L S X isHost PA) {rel : Rel} {args : List Term} {σA σF : Store}
    {dest : Option Term} {Q : Set X.Valuation} (hit : isHost rel = true)
    (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
    (sols : X.solutions σF = X.solutions σA ∩ Q) (keys : X.supply σF = X.supply σA) {n : ℕ}
    {a' : Answer Term Store}
    (found : once (outputFirstHost L S PF).pull n (goalTasksOut L S PF (rel, args, σF, dest)) =
      some (some a')) :
    ∃ a, InBag (compiled L S PA) (initial L S PA (rel, args, σA)).frontier ((), a) ∧
      AnswerRel X Q dest a a' :=
  once_witness_bag aligned n
    (goal_activations_embed aligned rel args σA σF goodA goodF keys dest .base sols)
    (trees hit goodA) found

/-- **`once` over a host goal fails only without a witness**: when the
output-first host's `once` finds no answer, every answer in the bag of the
goal's output-at-return evaluation is omitted. -/
theorem machines_once_fails (aligned : ProgramBindsAhead L PA PF)
    (trees : GoalTreesModed L S X isHost PA) {rel : Rel} {args : List Term} {σA σF : Store}
    {dest : Option Term} {Q : Set X.Valuation} (hit : isHost rel = true)
    (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
    (sols : X.solutions σF = X.solutions σA ∩ Q) (keys : X.supply σF = X.supply σA) {n : ℕ}
    (failed : once (outputFirstHost L S PF).pull n (goalTasksOut L S PF (rel, args, σF, dest)) =
      some none) :
    ∀ a, InBag (compiled L S PA) (initial L S PA (rel, args, σA)).frontier ((), a) →
      AnswerOmitted X Q dest a :=
  fun a inBag => once_fails_bag aligned n
    (goal_activations_embed aligned rel args σA σF goodA goodF keys dest .base sols)
    (trees hit goodA) failed ((), a) inBag

/-- **`once` over a host goal finds a witness whenever the reference delivers
one**: when the goal's output-at-return evaluation delivers, within `n` pulls,
an answer that is not omitted, the output-first host's `once` is decided with
an answer. -/
theorem machines_once_some (aligned : ProgramBindsAhead L PA PF)
    (trees : GoalTreesModed L S X isHost PA) {rel : Rel} {args : List Term} {σA σF : Store}
    {dest : Option Term} {Q : Set X.Valuation} (hit : isHost rel = true)
    (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
    (sols : X.solutions σF = X.solutions σA ∩ Q) (keys : X.supply σF = X.supply σA) {n : ℕ}
    {a : Answer Term Store}
    (found : a ∈ delivered (referenceHost L S PA).pull n (initial L S PA (rel, args, σA)).frontier)
    (kept : ¬ AnswerOmitted X Q dest a) :
    ∃ n' a', once (outputFirstHost L S PF).pull n' (goalTasksOut L S PF (rel, args, σF, dest)) =
      some (some a') :=
  once_host_some (machinesCorrect L S X aligned (goalsModed_of_goalTreesModed trees))
    ((machinesCorrect L S X aligned (goalsModed_of_goalTreesModed trees)).start hit goodA goodF
      sols keys) found kept

end MachineBags

end Mettapedia.GSLT.LanguageDef.HostGoals
