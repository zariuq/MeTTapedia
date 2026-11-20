import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundTwoPresentations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplines

/-!
# The runtime's round: a bag whose members fire one after another, in every order, to its result

The runtime's step setting `round` admits a bag of matches with the guards at the joint information, its
members opened with fresh unknowns each, and keeps it when its members, fired one at a time from the
entry state, reach its result in every order. Its five choices: a bag store (or the set store, through
`SetStoreSyntax.SerialRound`); the commit `round`; guards asked after the tells, at the joint information
for the bag and at each member's own information for the members fired one at a time; a fixed set of
rules; one store of knowledge. The runtime compares end states by their canonical form; `RuntimeRound`
compares them by structural congruence, which is finer. So `runtimeRound_of_admitsOwn` proves more than
the runtime asks, and `admitsOwn_of_runtimeRound` uses no comparison of end states at all.

## Firing members one after another

* `stateAfter`, `FiresInOrder`: the members of a list fired one after another from a state, each by the
  one-match step at the state its predecessors reached; such a list is a run of the one-match step
  (`run_of_firesInOrder`).
* **`stateAfter_eq_result`**: whenever a bag fits and its selection is enabled as one commit, its members
  fired one after another end at its result. No guard is used.
* **`firesInOrder_of_admitsOwn`**: the members of a bag of positive rules admitted on its own fire one
  after another, in their order.

## The runtime's round agrees with the round of `RoundTwoPresentations`

* `RuntimeRound`: a bag admitted at the joint information whose members fire one after another in every
  order, to a state structurally congruent to its result (`Scope.Congruent`: the same present rows, the
  same labels on them, the same equations).
* **`admitsOwn_of_runtimeRound`**: a runtime round is admitted on its own, for every rule: each member
  fires first in some order.
* **`runtimeRound_of_admitsOwn`**, **`runtimeRound_iff_admitsOwn`**: for positive rules, the runtime's
  round on the bag store is the bag admitted on its own.
* **`runtimeRound_of_round`**: a round of the base layer at a configuration, whose members are images of
  members with jointly fresh openings at its embedding and one seen set per collect pattern, is a runtime
  round at the embedded state, for every rule.
* **`runtimeRound_iff_round`**: for positive rules, at an embedded state, keeping labels, the runtime's
  round is the round of the base layer of jointly fresh images; **`runtimeRound_iff_round_canonical`**:
  at every state at the one frame, under the labels of its round.
* **The set store** (`serialRound_iff_admitsOwn`, `serialRound_iff_runtimeRound`,
  `serialRound_iff_round`): for positive programs, `SetStoreSyntax.SerialRound` at a set-represented
  state is the bag admitted on its own, the runtime round there, and the round of the base layer of its
  image under the labels of its round, with jointly fresh openings.

## Runs of the one-match step and runs of the base layer

* **`stateAfter_embed`**, **`executable_of_firesInOrder`**, **`firesInOrder_of_executable`**: members that
  keep labels and fire one after another at an embedded state reach the embedding of what their images
  reach, and their images run in the base layer from a consistent configuration; conversely images that
  run in the base layer fire one after another at the embedded state when the openings are jointly fresh
  and there is one seen set per collect pattern. **`result_embed`**: a bag that fits, with its selection enabled as one commit and members that
  keep labels, has as result the embedding of the configuration its images reach, the bag form of
  `OneFrame.result_toFirstOrder`.
* **`every_order_one_trace`**: so every order of a bag of positive rules admitted on its own at an
  embedded state, keeping labels, fires in the one-match step, its run is the embedding of the base run of
  its images, and the images of any two orders are one contextual trace of the base layer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds

open MeTTaCalculus.OccurrenceCommits (Enabled)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext embed)
open JointFirings (OneMember bagOf)
open Scope (Positive Congruent)

universe uT uS uO

section EveryOrder

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]
  {P : Program (Terms T)}

/-- **The state reached by firing members one after another** from a state, each by the one-match step
at the state its predecessors reached. -/
def stateAfter (s : State (Terms T) O) : List (OneMember A O P) → State (Terms T) O
  | [] => s
  | m :: rest => stateAfter (m.firing.result (frames A) s) rest

/-- **Members fire one after another**: each is admitted by the one-match step at the state its
predecessors reached. -/
def FiresInOrder : State (Terms T) O → List (OneMember A O P) → Prop
  | _, [] => True
  | s, m :: rest => m.firing.Admits (frames A) s ∧ FiresInOrder (m.firing.result (frames A) s) rest

/-- **Members that fire one after another are a run of the one-match step.** -/
theorem run_of_firesInOrder : ∀ (s : State (Terms T) O) (l : List (OneMember A O P)),
    FiresInOrder A s l →
      Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s (stateAfter A s l)
  | _, [], _ => Relation.ReflTransGen.refl
  | _, m :: rest, fires =>
      Relation.ReflTransGen.head ⟨m.firing, fires.1, rfl⟩ (run_of_firesInOrder _ rest fires.2)

/-- **Firing the members of a bag one after another ends at the bag's result**, whenever the bag fits
and its selection is enabled as one commit. No guard is used. -/
theorem stateAfter_eq_result : ∀ (s : State (Terms T) O) (l : List (OneMember A O P)),
    JointFirings.Bag.Fits (frames A) s (bagOf A l) →
      Enabled (fun _ : O => ()) s.present ((bagOf A l).selection.commit (T := Unit)) →
        stateAfter A s l = JointFirings.Bag.result (frames A) s (bagOf A l)
  | s, [], _, _ => (JointFirings.result_nil A s).symm
  | s, m :: rest, fits, enabled => by
      have shapes : m.firing.Shapes (frames A) s :=
        ⟨JointFirings.Bag.fresh_member (frames A) (fun _ _ => ⟨A.identity⟩) fits.1 List.mem_cons_self,
          (List.nodup_flatMap.mp fits.2.1).1 m List.mem_cons_self,
          (List.nodup_flatMap.mp fits.2.2.1).1 m List.mem_cons_self, fits.2.2.2 m List.mem_cons_self⟩
      have enabledM := JointFirings.Bag.enabled_member (m := m) enabled List.mem_cons_self
      have fitsRest : JointFirings.Bag.Fits (frames A) (m.firing.result (frames A) s) (bagOf A rest) :=
        ⟨JointFirings.fresh_after A shapes enabledM fits.1,
          (List.nodup_append.mp
            (show (m.selection.taken ++ (bagOf A rest).selection.taken).Nodup from fits.2.1)).2.1,
          (List.nodup_append.mp
            (show (m.selection.made ++ (bagOf A rest).selection.made).Nodup from fits.2.2.1)).2.1,
          fun r inside => fits.2.2.2 r (List.mem_cons_of_mem _ inside)⟩
      have enabledRest := JointFirings.enabled_after A fits.2.1 fits.2.2.1 enabled
      show stateAfter A (m.firing.result (frames A) s) rest = _
      rw [stateAfter_eq_result _ rest fitsRest enabledRest]
      exact JointFirings.result_after A fits enabled

/-- **The members of a bag of positive rules admitted on its own fire one after another**, in their
order. -/
theorem firesInOrder_of_admitsOwn : ∀ (s : State (Terms T) O) (l : List (OneMember A O P)),
    (∀ m ∈ l, Positive m.rule) → JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l) →
      FiresInOrder A s l
  | _, [], _, _ => trivial
  | _, m :: rest, positive, own => by
      obtain ⟨head, later, -⟩ :=
        JointFirings.peel A (fun r inside => positive r (List.mem_cons_of_mem _ inside)) own
      exact ⟨head, firesInOrder_of_admitsOwn _ rest
        (fun r inside => positive r (List.mem_cons_of_mem _ inside)) later⟩

/-- **Reordering a bag's members gives a structurally congruent result.** -/
theorem result_perm_congruent {s : State (Terms T) O} {l l' : List (OneMember A O P)}
    (perm : l.Perm l') (fits : JointFirings.Bag.Fits (frames A) s (bagOf A l)) :
    Congruent (JointFirings.Bag.result (frames A) s (bagOf A l'))
      (JointFirings.Bag.result (frames A) s (bagOf A l)) := by
  obtain ⟨present, labels, knowledge⟩ := JointFirings.Bag.result_perm (frames A) perm fits
  exact ⟨fun _ => knowledge.mem_iff, present, fun o _ => congrFun labels o⟩

/-! ## The runtime's round -/

/-- **The runtime's round, on the bag store**: a bag admitted with the guards at the joint information
whose members, fired one after another from the entry state, reach a state structurally congruent to its
result, in every order. -/
def RuntimeRound (s : State (Terms T) O) (l : List (OneMember A O P)) : Prop :=
  JointFirings.Bag.Admits (frames A) s (bagOf A l) ∧
    ∀ l' : List (OneMember A O P), l'.Perm l →
      FiresInOrder A s l' ∧
        Congruent (stateAfter A s l') (JointFirings.Bag.result (frames A) s (bagOf A l))

/-- **A runtime round is a bag admitted on its own**, for every rule: each member fires first in some
order. -/
theorem admitsOwn_of_runtimeRound {s : State (Terms T) O} {l : List (OneMember A O P)}
    (round : RuntimeRound A s l) : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l) := by
  obtain ⟨⟨fits, enabled, solvable, -⟩, orders⟩ := round
  refine ⟨fits, enabled, solvable, fun (m : OneMember A O P) (inside : m ∈ l) => ?_⟩
  obtain ⟨before, after, rfl⟩ := List.append_of_mem inside
  exact ((orders (m :: (before ++ after)) List.perm_middle.symm).1.1).2.2.2

/-- **A bag admitted on its own whose members fire one after another in every order is a runtime
round**: the end states are then congruent to its result. -/
theorem runtimeRound_of_fires {s : State (Terms T) O} {l : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l))
    (fires : ∀ l' : List (OneMember A O P), l'.Perm l → FiresInOrder A s l') :
    RuntimeRound A s l := by
  refine ⟨JointFirings.Bag.admits_of_admitsOwn (frames A) own, fun l' perm => ⟨fires l' perm, ?_⟩⟩
  have ownPerm := JointFirings.Bag.admitsOwn_perm (frames A) perm.symm own
  rw [stateAfter_eq_result A s l' ownPerm.1 ownPerm.2.1]
  exact result_perm_congruent A perm.symm own.1

/-- **For positive rules, a bag admitted on its own is a runtime round.** -/
theorem runtimeRound_of_admitsOwn {s : State (Terms T) O} {l : List (OneMember A O P)}
    (positive : ∀ m ∈ l, Positive m.rule)
    (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l)) : RuntimeRound A s l :=
  runtimeRound_of_fires A own fun l' perm =>
    firesInOrder_of_admitsOwn A s l' (fun m inside => positive m (perm.subset inside))
      (JointFirings.Bag.admitsOwn_perm (frames A) perm.symm own)

/-- **For positive rules, the runtime's round on the bag store is the bag admitted on its own.** -/
theorem runtimeRound_iff_admitsOwn {s : State (Terms T) O} {l : List (OneMember A O P)}
    (positive : ∀ m ∈ l, Positive m.rule) :
    RuntimeRound A s l ↔ JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l) :=
  ⟨admitsOwn_of_runtimeRound A, runtimeRound_of_admitsOwn A positive⟩

/-! ## Runs of the one-match step and runs of the base layer -/

/-- **At an embedded state, members that keep labels fire one after another to the embedding of the
state their images reach in the base layer.** -/
theorem stateAfter_embed (label : O → T) : ∀ (C : Configuration T O) (l : List (OneMember A O P)),
    (∀ m ∈ l, KeepsLabels A label m) →
      stateAfter A (embed label C) l = embed label (AnnotatedRuns.follow label C (image A l))
  | _, [], _ => rfl
  | C, m :: rest, keeps => by
      have reached := OneFrame.result_toFirstOrder (A := A) (label := label) (P := P) C m.firing
        (keeps m List.mem_cons_self)
      show stateAfter A (m.firing.result (frames A) (embed label C)) rest =
        embed label (AnnotatedRuns.follow label ((baseFiring A m).result label C) (image A rest))
      rw [reached]
      exact stateAfter_embed label _ rest fun r inside => keeps r (List.mem_cons_of_mem _ inside)

/-- **The result of a bag at an embedded state is the embedding of the configuration its images reach in
the base layer**, whenever the bag fits, its selection is enabled as one commit, and its members keep
labels: the bag form of `OneFrame.result_toFirstOrder`. -/
theorem result_embed {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (fits : JointFirings.Bag.Fits (frames A) (embed label C) (bagOf A l))
    (enabled : Enabled (fun _ : O => ()) C.present ((bagOf A l).selection.commit (T := Unit)))
    (keeps : ∀ m ∈ l, KeepsLabels A label m) :
    JointFirings.Bag.result (frames A) (embed label C) (bagOf A l) =
      embed label (AnnotatedRuns.follow label C (image A l)) :=
  (stateAfter_eq_result A (embed label C) l fits enabled).symm.trans (stateAfter_embed A label C l keeps)

/-- **Members that keep labels and fire one after another at an embedded state run in the base
layer**, from a consistent configuration. -/
theorem executable_of_firesInOrder (label : O → T) : ∀ (C : Configuration T O)
    (l : List (OneMember A O P)), FiresInOrder A (embed label C) l →
      (∀ m ∈ l, KeepsLabels A label m) → A.Consistent C.equations →
        AnnotatedRuns.Executable A label C (image A l)
  | _, [], _, _, consistent => consistent
  | C, m :: rest, fires, keeps, _ => by
      have valid := ((OneFrame.admits_toFirstOrder_iff (A := A) (label := label) (P := P) C
        m.firing).mp ⟨fires.1, keeps m List.mem_cons_self⟩).1
      have reached := OneFrame.result_toFirstOrder (A := A) (label := label) (P := P) C m.firing
        (keeps m List.mem_cons_self)
      have later := fires.2
      rw [reached] at later
      exact ⟨valid, executable_of_firesInOrder label _ rest later
        (fun r inside => keeps r (List.mem_cons_of_mem _ inside)) valid.firing.consistent⟩

/-- **Images that run in the base layer fire one after another at the embedded state**, when the
openings are jointly fresh and there is one seen set per collect pattern. -/
theorem firesInOrder_of_executable (label : O → T) : ∀ (C : Configuration T O)
    (l : List (OneMember A O P)), AnnotatedRuns.Executable A label C (image A l) →
      JointFirings.Bag.Fresh (frames A) (embed label C) (bagOf A l) →
        (∀ m ∈ l, m.rule.collect.length = m.seen.length) → FiresInOrder A (embed label C) l
  | _, [], _, _, _ => trivial
  | C, m :: rest, executable, fresh, collect => by
      have freshM :=
        JointFirings.Bag.fresh_member (frames A) (fun _ _ => ⟨A.identity⟩) fresh List.mem_cons_self
      obtain ⟨admitted, keeps⟩ := (OneFrame.admits_toFirstOrder_iff (A := A) (label := label) (P := P)
        C m.firing).mpr ⟨executable.1, freshM, collect m List.mem_cons_self⟩
      have reached := OneFrame.result_toFirstOrder (A := A) (label := label) (P := P) C m.firing keeps
      have freshRest := JointFirings.fresh_after A admitted.1 admitted.2.1 fresh
      rw [reached] at freshRest
      refine ⟨admitted, ?_⟩
      show FiresInOrder A (m.firing.result (frames A) (embed label C)) rest
      rw [reached]
      exact firesInOrder_of_executable label _ rest executable.2 freshRest
        (fun r inside => collect r (List.mem_cons_of_mem _ inside))

/-- **A round of the base layer whose members are images of members with jointly fresh openings is a
runtime round**, for every rule. -/
theorem runtimeRound_of_round {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (round : AnnotatedRuns.Round A label C (image A l))
    (fresh : JointFirings.Bag.Fresh (frames A) (embed label C) (bagOf A l))
    (collect : ∀ m ∈ l, m.rule.collect.length = m.seen.length) : RuntimeRound A (embed label C) l := by
  obtain ⟨own, -⟩ := admitsOwn_of_round A round fresh collect
  refine runtimeRound_of_fires A own fun l' perm => ?_
  exact firesInOrder_of_executable A label C l' (round.executable_perm A label (perm.map (baseFiring A)))
    (fun b g => (JointFirings.realized_perm (frames A) perm).mpr (fresh b g))
    (fun m inside => collect m (perm.subset inside))

/-- **For positive rules, at an embedded state, keeping labels, the runtime's round is the round of the
base layer of jointly fresh images.** -/
theorem runtimeRound_iff_round {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (positive : ∀ m ∈ l, Positive m.rule) :
    (RuntimeRound A (embed label C) l ∧ ∀ m ∈ l, KeepsLabels A label m) ↔
      AnnotatedRuns.Round A label C (image A l) ∧
        JointFirings.Bag.Fresh (frames A) (embed label C) (bagOf A l) ∧
        ∀ m ∈ l, m.rule.collect.length = m.seen.length := by
  rw [runtimeRound_iff_admitsOwn A positive]
  exact admitsOwn_iff_round A positive

/-- **For positive rules, at every state at the one frame, the runtime's round is the round of the base
layer of its image under the labels of its round**, with jointly fresh openings and one seen set per
collect pattern. -/
theorem runtimeRound_iff_round_canonical {s : State (Terms T) O} {l : List (OneMember A O P)}
    (positive : ∀ m ∈ l, Positive m.rule) :
    RuntimeRound A s l ↔
      AnnotatedRuns.Round A (roundLabel A s l) (configurationOf s) (image A l) ∧
        JointFirings.Bag.Fresh (frames A) s (bagOf A l) ∧
        ∀ m ∈ l, m.rule.collect.length = m.seen.length :=
  (runtimeRound_iff_admitsOwn A positive).trans (admitsOwn_iff_round_canonical A positive)

/-- **Every order of a bag of positive rules admitted on its own, at an embedded state, keeping labels,
fires in the one-match step; its run is the embedding of the base run of its image; and the images of
any two orders are one contextual trace of the base layer.** -/
theorem every_order_one_trace {label : O → T} {C : Configuration T O}
    {l l₁ l₂ : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l))
    (keeps : ∀ m ∈ l, KeepsLabels A label m) (positive : ∀ m ∈ l, Positive m.rule)
    (first : l₁.Perm l) (second : l₂.Perm l) :
    FiresInOrder A (embed label C) l₁ ∧
      stateAfter A (embed label C) l₁ = embed label (AnnotatedRuns.follow label C (image A l₁)) ∧
      AnnotatedRuns.RoundEquiv A label C (image A l₁) (image A l₂) :=
  ⟨((runtimeRound_of_admitsOwn A positive own).2 l₁ first).1,
    stateAfter_embed A label C l₁ fun m inside => keeps m (first.subset inside),
    orders_equivalent A (round_image_of_positive A own keeps positive) first second⟩

end EveryOrder

/-! ## The set store -/

section SetStore

open Mettapedia.Logic.LP

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

/-- **For positive programs, the set store's serial round is the bag admitted on its own**, at every
set-represented state. -/
theorem serialRound_iff_admitsOwn (positive : ∀ r ∈ P, Positive r) (rows : Finset (Term signature))
    (bag : SetStore.Candidate P) :
    SetStoreSyntax.SerialRound rows bag ↔
      bag.AdmitsOwn SetStoreSyntax.X (SetStore.represent rows) := by
  constructor
  · exact fun round => round.1
  · intro own
    obtain ⟨⟨⟩, members⟩ := bag
    exact ⟨own, members, rfl, fun later perm =>
      JointFirings.any_order (FirstOrder.action signature)
        (fun member _ => positive member.rule member.member) own perm⟩

/-- **For positive programs, the set store's serial round is the runtime round** at the set-represented
state. -/
theorem serialRound_iff_runtimeRound (positive : ∀ r ∈ P, Positive r) (rows : Finset (Term signature))
    (members : List (OneMember (FirstOrder.action signature) (Term signature × ℕ) P)) :
    SetStoreSyntax.SerialRound rows (bagOf (FirstOrder.action signature) members) ↔
      RuntimeRound (FirstOrder.action signature) (SetStore.represent rows) members := by
  rw [serialRound_iff_admitsOwn positive,
    runtimeRound_iff_admitsOwn _ fun m _ => positive m.rule m.member]

/-- **For positive programs, the set store's serial round is the round of the base layer** of its image
under the labels of its round, at the set-represented state, with jointly fresh openings and one seen set
per collect pattern. -/
theorem serialRound_iff_round (positive : ∀ r ∈ P, Positive r) (rows : Finset (Term signature))
    (members : List (OneMember (FirstOrder.action signature) (Term signature × ℕ) P)) :
    SetStoreSyntax.SerialRound rows (bagOf (FirstOrder.action signature) members) ↔
      AnnotatedRuns.Round (FirstOrder.action signature)
          (roundLabel (FirstOrder.action signature) (SetStore.represent rows) members)
          (configurationOf (SetStore.represent rows)) (image (FirstOrder.action signature) members) ∧
        JointFirings.Bag.Fresh (frames (FirstOrder.action signature)) (SetStore.represent rows)
          (bagOf (FirstOrder.action signature) members) ∧
        ∀ m ∈ members, m.rule.collect.length = m.seen.length :=
  (serialRound_iff_admitsOwn positive rows _).trans
    (admitsOwn_iff_round_canonical _ fun m _ => positive m.rule m.member)

end SetStore

#print axioms run_of_firesInOrder
#print axioms stateAfter_eq_result
#print axioms firesInOrder_of_admitsOwn
#print axioms result_perm_congruent
#print axioms admitsOwn_of_runtimeRound
#print axioms runtimeRound_of_fires
#print axioms runtimeRound_of_admitsOwn
#print axioms runtimeRound_iff_admitsOwn
#print axioms stateAfter_embed
#print axioms result_embed
#print axioms executable_of_firesInOrder
#print axioms firesInOrder_of_executable
#print axioms runtimeRound_of_round
#print axioms runtimeRound_iff_round
#print axioms every_order_one_trace
#print axioms serialRound_iff_admitsOwn
#print axioms serialRound_iff_runtimeRound
#print axioms runtimeRound_iff_round_canonical
#print axioms serialRound_iff_round

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds
