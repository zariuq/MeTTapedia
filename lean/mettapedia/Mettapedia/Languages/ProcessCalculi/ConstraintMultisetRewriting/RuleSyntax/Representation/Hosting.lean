import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Effective

/-!
# Three senses in which the one-match step hosts a transition system

`OperationalCorrespondence source target` (in `Mettapedia.GSLT.Core.OperationalReadback`) relates the states of
two systems: a target step is read back as no source step or one, and a source step is realized by a finite
target path. This module states what that notion does not say, and two senses beside it.

## The notion says nothing without an observation

* **The total relation** (`total`): for every two systems, relating every state to every state is an
  `OperationalCorrespondence`: every target step is read back as no step and every source step is realized by
  the empty path. So every system on the naturals corresponds to the step of the empty program
  (`every_system_corresponds`). What excludes it is an observation of the target that tells source states
  apart and is sound for the relation (`total_not_sound`).

## The weak sense: silent firings that end, and one observed firing per source step

* **`WeakCorrespondence`**: a relation, a potential and an observation `shows`, functional
  (`shows_unique`). Every target step either stays related to the same source state and lowers the potential
  (silent), or is a source step landing on a state that shows the new state (observed). Every source step is a
  path of silent steps followed by one observed step. It is an `OperationalCorrespondence` (`toCorrespondence`).
* **No added divergence** (`acc_of_acc`, `infinite_run_reflected`): from a related state, an infinite target run
  gives an infinite source run. Silent runs end because the potential falls.
* **Finitely many successors are necessary** (`successors_finite_of_view`): if every target state has finitely
  many successors read through a view, and the observation is read off the view, every source state related to
  a viewed state has finitely many successors: the silent paths are no longer than the potential, so only
  finitely many views are reached before the next observed step, and each shows one source state. Instances:
  finitely branching targets (`successors_finite_of_branching`) and the step of every finite list of
  range-restricted positive rules, read as bags (`successors_finite_of_program`, by `successors_finite`).
* **The observed step must be one step.** An `OperationalCorrespondence` with a potential that falls on silent
  steps does not force finite branching: a source state with a step to itself may realize a step to any of
  infinitely many states by a target path that reads back as several steps (`loopingSource`, `loopingTarget`,
  `looping`, `looping_branches_infinitely`).

## The may sense: runs, both ways, through an observation

* **`MayHosting`**: a readback, an observation `represents` held only by related states and sound for the
  relation, and every source step realized from every state that represents its origin. Then the source reaches
  `b` from `a` exactly when the target reaches a state representing `b` from a state representing `a`
  (`MayHosting.reachable_iff`): every source run is realized, and every target run that ends in a representing
  state is a source run to its number. The may sense sees runs, so it determines a system up to its
  reflexive-transitive closure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Hosting

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open NamesOnTheStep (Expr)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation
  (successors_finite)

universe uS uT uV uO

/-! ## Runs -/

/-- A finite run of a system is a path of its steps. -/
theorem reflTransGen_of_multiStep {S : GSLT} {a b : S.Term} (path : S.MultiStep a b) :
    Relation.ReflTransGen S.Step a b := by
  induction path with
  | refl => exact .refl
  | step stepped _ reached => exact Relation.ReflTransGen.head stepped reached

/-! ## The total relation -/

/-- **The total relation is an operational correspondence**, between every two systems. -/
def total (source : GSLT.{uS}) (target : GSLT.{uT}) : OperationalCorrespondence source target where
  related _ _ := True
  readStep := fun _ _ => Or.inl trivial
  forward := fun {_ _ current} _ _ => ⟨current, ⟨.refl current⟩, trivial⟩

/-- **Every system on the naturals corresponds to the step of the empty program**, through the total
relation. -/
theorem every_system_corresponds (R : ℕ → ℕ → Prop) :
    Nonempty (OperationalCorrespondence (equalityGSLT ℕ R) (stepSystem ℕ [])) :=
  ⟨total _ _⟩

/-- **A sound observation excludes the total relation**: a state that represents `b` is related by the total
relation to every `a`, so soundness would make every two source states equal. -/
theorem total_not_sound {source : GSLT.{uS}} {target : GSLT.{uT}}
    (represents : source.Term → target.Term → Prop) {a b : source.Term} (different : a ≠ b)
    {t : target.Term} (shown : represents b t) :
    ¬ ∀ {a' b' : source.Term} {t' : target.Term}, (total source target).related a' t' → represents b' t' → a' = b' :=
  fun sound => different (sound trivial shown)

/-! ## The weak sense -/

/-- **A silent step** for a relation and a potential: a target step that stays related to the same source state
and lowers the potential. -/
def SilentStep (target : GSLT.{uT}) {A : Type uS} (related : A → target.Term → Prop)
    (potential : A → target.Term → ℕ) (a : A) (t t' : target.Term) : Prop :=
  target.Step t t' ∧ related a t' ∧ potential a t' < potential a t

/-- **A weak correspondence whose silent steps end, with one observed step per source step.** Every target step
is silent (it stays related to the same source state and lowers the potential) or observed (it is a source step,
and lands on a state that shows the new source state); every source step is silent steps followed by one
observed step. The observation is functional: a state shows at most one source state. -/
structure WeakCorrespondence (source : GSLT.{uS}) (target : GSLT.{uT}) where
  related : source.Term → target.Term → Prop
  shows : source.Term → target.Term → Prop
  shows_unique : ∀ {a b : source.Term} {t : target.Term}, shows a t → shows b t → a = b
  potential : source.Term → target.Term → ℕ
  readStep : ∀ {a : source.Term} {t t' : target.Term}, related a t → target.Step t t' →
    (related a t' ∧ potential a t' < potential a t) ∨ ∃ b, source.Step a b ∧ related b t' ∧ shows b t'
  forward : ∀ {a b : source.Term} {t : target.Term}, related a t → source.Step a b →
    ∃ t₁ t₂, Relation.ReflTransGen (SilentStep target related potential a) t t₁ ∧ target.Step t₁ t₂ ∧
      related b t₂ ∧ shows b t₂

namespace WeakCorrespondence

variable {source : GSLT.{uS}} {target : GSLT.{uT}}

/-- A path of silent steps is a run of the target. -/
theorem multiStep_of_silent (C : WeakCorrespondence source target) {a : source.Term} {t t' : target.Term}
    (path : Relation.ReflTransGen (SilentStep target C.related C.potential a) t t') : target.MultiStep t t' := by
  induction path with
  | refl => exact .refl _
  | tail _ silent reached => exact multiStepAppend reached (.step silent.1 (.refl _))

/-- **A weak correspondence is an operational correspondence.** -/
def toCorrespondence (C : WeakCorrespondence source target) : OperationalCorrespondence source target where
  related := C.related
  readStep := by
    intro a t t' related stepped
    rcases C.readStep related stepped with ⟨silent, -⟩ | ⟨b, sourceStep, related', -⟩
    · exact Or.inl silent
    · exact Or.inr ⟨b, sourceStep, related'⟩
  forward := by
    intro a b t related sourceStep
    obtain ⟨t₁, t₂, silentPath, stepped, related', -⟩ := C.forward related sourceStep
    exact ⟨t₂, (executionPath_nonempty_iff_multiStep target _ _).mpr
      (multiStepAppend (C.multiStep_of_silent silentPath) (.step stepped (.refl _))), related'⟩

/-- **No added divergence**: from a state related to a source state from which the source has no infinite run,
the target has no infinite run. The inner induction is on the potential; it restarts after each observed
step. -/
theorem acc_of_acc (C : WeakCorrespondence source target) {a : source.Term}
    (accessible : Acc (fun after before => source.Step before after) a) :
    ∀ {t : target.Term}, C.related a t → Acc (fun next state => target.Step state next) t := by
  induction accessible with
  | intro a _ ih =>
      have run : ∀ (bound : ℕ) (t : target.Term), C.potential a t = bound → C.related a t →
          Acc (fun next state => target.Step state next) t := by
        intro bound
        refine Nat.strong_induction_on bound ?_
        intro bound smaller t atBound related
        refine Acc.intro t fun t' stepped => ?_
        rcases C.readStep related stepped with ⟨related', lower⟩ | ⟨b, sourceStep, related', -⟩
        · exact smaller _ (atBound ▸ lower) t' rfl related'
        · exact ih b sourceStep related'
      intro t related
      exact run _ t rfl related

/-- **An infinite target run from a related state gives an infinite source run.** -/
theorem infinite_run_reflected (C : WeakCorrespondence source target) {a : source.Term} {t : target.Term}
    (related : C.related a t) (run : ℕ → target.Term) (starts : run 0 = t)
    (steps : ∀ i, target.Step (run i) (run (i + 1))) :
    ∃ sourceRun : ℕ → source.Term, sourceRun 0 = a ∧ ∀ i, source.Step (sourceRun i) (sourceRun (i + 1)) := by
  have targetDiverges : ¬ Acc (fun next state => target.Step state next) t :=
    not_acc_iff_exists_descending_chain.mpr ⟨run, starts, steps⟩
  have sourceDiverges : ¬ Acc (fun after before => source.Step before after) a :=
    fun accessible => targetDiverges (C.acc_of_acc accessible related)
  exact not_acc_iff_exists_descending_chain.mp sourceDiverges

end WeakCorrespondence

/-! ## Finitely many successors are necessary -/

/-- **Views within `k` steps** of a branching of views. -/
inductive Within {V : Type uV} (next : V → Set V) : ℕ → V → V → Prop
  | refl (k : ℕ) (v : V) : Within next k v v
  | step {k : ℕ} {v w u : V} : w ∈ next v → Within next k w u → Within next (k + 1) v u

namespace Within

variable {V : Type uV} {next : V → Set V}

theorem mono {k : ℕ} {v u : V} (within : Within next k v u) : ∀ {k' : ℕ}, k ≤ k' → Within next k' v u := by
  induction within with
  | refl k v => exact fun {k'} _ => .refl k' v
  | @step k v w u member _ ih =>
      intro k' le
      obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
      exact .step member (ih (by omega))

theorem snoc {k : ℕ} {v u x : V} (within : Within next k v u) (member : x ∈ next u) :
    Within next (k + 1) v x := by
  induction within with
  | refl k v => exact .step member (.refl k x)
  | step first _ ih => exact .step first (ih member)

/-- **Finitely many views within `k` steps**, when every view has finitely many next views. -/
theorem finite (finiteNext : ∀ v, (next v).Finite) : ∀ (k : ℕ) (v : V), {u | Within next k v u}.Finite := by
  intro k
  induction k with
  | zero =>
      intro v
      refine (Set.finite_singleton v).subset ?_
      intro u within
      cases within with
      | refl => exact rfl
  | succ k ih =>
      intro v
      refine ((finiteNext v).biUnion fun w _ => ih w).insert v |>.subset ?_
      intro u within
      cases within with
      | refl => exact Set.mem_insert _ _
      | step member rest => exact Set.mem_insert_of_mem _ (Set.mem_biUnion member rest)

end Within

section Necessity

variable {source : GSLT.{uS}} {target : GSLT.{uT}} {V : Type uV}

/-- **A silent path stays within as many steps of the views as the potential allows.** -/
theorem silent_within (C : WeakCorrespondence source target) (view : target.Term → V → Prop)
    (next : V → Set V) (stepView : ∀ {t : target.Term} {v : V} {t' : target.Term}, view t v → target.Step t t' →
      ∃ v', v' ∈ next v ∧ view t' v')
    {a : source.Term} {t₀ t₁ : target.Term}
    (path : Relation.ReflTransGen (SilentStep target C.related C.potential a) t₀ t₁) :
    ∀ {v₀ : V}, view t₀ v₀ → ∃ u, Within next (C.potential a t₀) v₀ u ∧ view t₁ u := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun {v₀} viewed => ⟨v₀, .refl _ v₀, viewed⟩
  | head silent _ ih =>
      intro v₀ viewed
      obtain ⟨vy, member, viewedY⟩ := stepView viewed silent.1
      obtain ⟨u, within, viewedEnd⟩ := ih viewedY
      exact ⟨u, (Within.step member within).mono (by have := silent.2.2; omega), viewedEnd⟩

/-- **Finitely many successors are necessary for the weak sense.** If the target branches finitely through a
view, and the observation is read off the view, a source state related to a viewed target state has finitely
many successors. -/
theorem successors_finite_of_view (C : WeakCorrespondence source target) (view : target.Term → V → Prop)
    (next : V → Set V) (finiteNext : ∀ v, (next v).Finite)
    (stepView : ∀ {t : target.Term} {v : V} {t' : target.Term}, view t v → target.Step t t' →
      ∃ v', v' ∈ next v ∧ view t' v')
    (showsView : ∀ {b b' : source.Term} {t t' : target.Term} {v : V}, view t v → view t' v →
      C.shows b t → C.shows b' t' → b = b')
    {a : source.Term} {t : target.Term} {v : V} (related : C.related a t) (viewed : view t v) :
    {b | source.Step a b}.Finite := by
  refine ((Within.finite finiteNext (C.potential a t + 1) v).biUnion
    (t := fun u => {b | ∃ t₂, view t₂ u ∧ C.shows b t₂}) fun u _ => ?_).subset ?_
  · refine Set.Subsingleton.finite ?_
    rintro b ⟨t₂, viewed₂, shown⟩ b' ⟨t₂', viewed₂', shown'⟩
    exact showsView viewed₂ viewed₂' shown shown'
  · intro b sourceStep
    obtain ⟨t₁, t₂, silentPath, stepped, -, shown⟩ := C.forward related sourceStep
    obtain ⟨u₁, within, viewed₁⟩ := silent_within C view next stepView silentPath viewed
    obtain ⟨u₂, member, viewed₂⟩ := stepView viewed₁ stepped
    exact Set.mem_biUnion (Within.snoc within member) ⟨t₂, viewed₂, shown⟩

/-- **For a finitely branching target**: a source state related to a target state has finitely many
successors. -/
theorem successors_finite_of_branching (C : WeakCorrespondence source target)
    (branching : ∀ t : target.Term, {t' | target.Step t t'}.Finite) {a : source.Term} {t : target.Term}
    (related : C.related a t) : {b | source.Step a b}.Finite :=
  successors_finite_of_view C (fun t v => t = v) (fun v => {t' | target.Step v t'}) branching
    (fun {_ _ t'} viewed stepped => ⟨t', viewed ▸ stepped, rfl⟩)
    (fun viewed viewed' shown shown' => by
      subst viewed
      subst viewed'
      exact C.shows_unique shown shown')
    related rfl

end Necessity

/-- **For the step of a finite program**: a weak correspondence to the step of a finite list of range-restricted
positive rules, whose observation is read off the bag a state reads as, gives every source state related to a
state that reads as a bag finitely many successors. The view is the bag (`ReadsBag`), and a bag has finitely
many successors (`successors_finite`). -/
theorem successors_finite_of_program {O : Type uO} [DecidableEq O] {rules : List SRule}
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {source : GSLT.{uS}}
    (C : WeakCorrespondence source (stepSystem O rules))
    (showsBag : ∀ {b b' : source.Term} {s s' : SState O} {M : Multiset Expr}, ReadsBag s M → ReadsBag s' M →
      C.shows b s → C.shows b' s' → b = b')
    {a : source.Term} {s : SState O} {M : Multiset Expr} (related : C.related a s) (reads : ReadsBag s M) :
    {b | source.Step a b}.Finite :=
  successors_finite_of_view C ReadsBag (fun M => {M' | Rewrites rules M M'})
    (fun M => successors_finite rules (fun r member => (fragment r member).2.2) M)
    (fun {_ _ _} readsHere stepped => by
      obtain ⟨g, admitted, rfl⟩ := stepped
      obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward fragment readsHere g admitted
      exact ⟨bag', rewrites, reads'⟩)
    showsBag related reads

/-! ## Control: one observed step is needed -/

/-- The source of the control: `0` steps to itself and to every positive number. -/
def loopingStep (a : ℕ) (_ : ℕ) : Prop := a = 0

/-- The source of the control, as a system. -/
def loopingSource : GSLT := equalityGSLT ℕ loopingStep

/-- The states of the target of the control: a chain `chain i` and an exit `exit j`. -/
inductive LoopState where
  | chain (i : ℕ)
  | exit (j : ℕ)

/-- The step of the target of the control: the chain moves on, returns to its start, or exits at its
position. -/
def LoopStep : LoopState → LoopState → Prop
  | .chain i, .chain j => j = i + 1 ∨ j = 0
  | .chain i, .exit j => j = i
  | .exit _, _ => False

/-- The target of the control: every state has at most three successors. -/
def loopingTarget : GSLT := equalityGSLT LoopState LoopStep

/-- The relation of the control: `0` with every state of the chain, a positive number `j + 1` with the exit
`j`. -/
def loopingRelated (a : ℕ) : LoopState → Prop
  | .chain _ => a = 0
  | .exit j => a = j + 1

/-- The path of the chain from any position back to its start and on to a position. -/
theorem chain_path (i j : ℕ) : loopingTarget.MultiStep (LoopState.chain i) (LoopState.chain j) := by
  have up : ∀ k, loopingTarget.MultiStep (LoopState.chain 0) (LoopState.chain k) := by
    intro k
    induction k with
    | zero => exact .refl _
    | succ k ih =>
        exact multiStepAppend ih (.step (show loopingTarget.Step (LoopState.chain k) (LoopState.chain (k + 1)) from
          (Or.inl rfl : LoopStep (.chain k) (.chain (k + 1)))) (.refl _))
  exact .step (show loopingTarget.Step (LoopState.chain i) (LoopState.chain 0) from
    (Or.inr rfl : LoopStep (.chain i) (.chain 0))) (up j)

/-- **An operational correspondence with no silent step at all**, from a source state with infinitely many
successors to a target that branches finitely. A step `0 → j + 1` is realized by returning along the chain to
the start, moving to position `j`, and exiting: a path that reads back as the step `0 → 0` repeated, then
`0 → j + 1`. -/
def looping : OperationalCorrespondence loopingSource loopingTarget where
  related := loopingRelated
  readStep := by
    intro a t t' related stepped
    cases t with
    | chain i =>
        have isZero : @Eq ℕ a 0 := related
        subst isZero
        cases t' with
        | chain j => exact Or.inr ⟨(0 : ℕ), (rfl : loopingStep 0 0), (rfl : loopingRelated 0 (.chain j))⟩
        | exit j => exact Or.inr ⟨(j + 1 : ℕ), (rfl : loopingStep 0 (j + 1)), (rfl : loopingRelated (j + 1) (.exit j))⟩
    | exit j => cases t' <;> exact False.elim stepped
  forward := by
    intro a b t related sourceStep
    have isZero : @Eq ℕ a 0 := sourceStep
    subst isZero
    cases t with
    | chain i =>
        cases b with
        | zero => exact ⟨LoopState.chain 0, (executionPath_nonempty_iff_multiStep loopingTarget _ _).mpr
            (chain_path i 0), (rfl : loopingRelated 0 (.chain 0))⟩
        | succ j => exact ⟨LoopState.exit j, (executionPath_nonempty_iff_multiStep loopingTarget _ _).mpr
            (multiStepAppend (chain_path i j)
              (.step (show loopingTarget.Step (LoopState.chain j) (LoopState.exit j) from
                (rfl : LoopStep (.chain j) (.exit j))) (.refl _))),
            (rfl : loopingRelated (j + 1) (.exit j))⟩
    | exit j => exact absurd (show (0 : ℕ) = j + 1 from related) (by omega)

/-- **The target of the control branches finitely.** -/
theorem loopingTarget_branching (t : LoopState) : {t' | LoopStep t t'}.Finite := by
  cases t with
  | chain i =>
      refine (((Set.finite_singleton (LoopState.exit i)).insert (LoopState.chain 0)).insert
        (LoopState.chain (i + 1))).subset ?_
      intro t' stepped
      cases t' with
      | chain j =>
          rcases (stepped : j = i + 1 ∨ j = 0) with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
      | exit j =>
          have same : j = i := stepped
          subst same
          exact Or.inr (Or.inr rfl)
  | exit j =>
      refine (Set.finite_empty).subset ?_
      intro t' stepped
      cases t' <;> exact False.elim stepped

/-- **Yet the source state `0` has infinitely many successors.** So an operational correspondence with no
silent step, a functional relation and a finitely branching target does not force finite branching; the weak
sense asks that the observed step of a source step be one step. -/
theorem looping_branches_infinitely : {b : ℕ | loopingStep 0 b}.Infinite := by
  have everything : {b : ℕ | loopingStep 0 b} = Set.univ := Set.eq_univ_of_forall fun _ => rfl
  rw [everything]
  exact Set.infinite_univ

/-- **The control is no weak correspondence**: no weak correspondence from the source of the control to its
finitely branching target relates `0` to a state of the chain. -/
theorem looping_not_weak (C : WeakCorrespondence loopingSource loopingTarget) {i : ℕ}
    (related : C.related (0 : ℕ) (LoopState.chain i)) : False :=
  looping_branches_infinitely (successors_finite_of_branching C loopingTarget_branching related)

/-- The relation of the control is functional on the target. -/
theorem looping_functional {a b : ℕ} {t : LoopState} (first : loopingRelated a t) (second : loopingRelated b t) :
    a = b := by
  cases t with
  | chain i => exact (first : a = 0).trans (second : b = 0).symm
  | exit j => exact (first : a = j + 1).trans (second : b = j + 1).symm

/-! ## The may sense -/

/-- **The may sense**: a readback (every target step is no source step or one), an observation `represents`
held only by related states and sound for the relation (a state related to `a` represents no other source
state), and every source step realized from every state that represents its origin. -/
structure MayHosting (source : GSLT.{uS}) (target : GSLT.{uT}) extends OperationalReadback source target where
  represents : source.Term → target.Term → Prop
  related_of_represents : ∀ {a : source.Term} {t : target.Term}, represents a t → related a t
  sound : ∀ {a b : source.Term} {t : target.Term}, related a t → represents b t → a = b
  realize : ∀ {a b : source.Term} {t : target.Term}, represents a t → source.Step a b →
    ∃ t', target.MultiStep t t' ∧ represents b t'

namespace MayHosting

variable {source : GSLT.{uS}} {target : GSLT.{uT}}

/-- **A state represents at most one source state.** -/
theorem represents_unique (H : MayHosting source target) {a b : source.Term} {t : target.Term}
    (first : H.represents a t) (second : H.represents b t) : a = b :=
  H.sound (H.related_of_represents first) second

/-- **Runs, both ways**: from a state that represents `a`, the target reaches a state that represents `b`
exactly when the source reaches `b` from `a`. Every source run is realized, and every target run that ends in a
representing state is a source run to its source state. -/
theorem reachable_iff (H : MayHosting source target) {a : source.Term} {t : target.Term}
    (start : H.represents a t) (b : source.Term) :
    Relation.ReflTransGen source.Step a b ↔ ∃ t', target.MultiStep t t' ∧ H.represents b t' := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨t, .refl _, start⟩
    | tail _ stepped reached =>
        obtain ⟨t₁, run, represented⟩ := reached
        obtain ⟨t₂, run', represented'⟩ := H.realize represented stepped
        exact ⟨t₂, multiStepAppend run run', represented'⟩
  · rintro ⟨t', run, represented⟩
    obtain ⟨after, sourceRun, related⟩ :=
      H.toOperationalReadback.reflectMultiStep (H.related_of_represents start) run
    have same : after = b := H.sound related represented
    subst same
    exact reflTransGen_of_multiStep sourceRun

end MayHosting

#print axioms total
#print axioms every_system_corresponds
#print axioms total_not_sound
#print axioms WeakCorrespondence.toCorrespondence
#print axioms WeakCorrespondence.acc_of_acc
#print axioms WeakCorrespondence.infinite_run_reflected
#print axioms Within.finite
#print axioms silent_within
#print axioms successors_finite_of_view
#print axioms successors_finite_of_branching
#print axioms successors_finite_of_program
#print axioms looping
#print axioms loopingTarget_branching
#print axioms looping_branches_infinitely
#print axioms looping_functional
#print axioms looping_not_weak
#print axioms MayHosting.represents_unique
#print axioms MayHosting.reachable_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Hosting
