import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelWave

/-!
# Two receivers racing for one message: rho reduction is not confluent

The reduction relation of the rho calculus, communication closed under parallel
composition and structural congruence (`Reduction.Reduces`, with its
reflexive-transitive closure `ReducesStar`), is not confluent. The witness is
one message wanted by two receivers on its channel:

`@0!(for(w <- @0){0}) | for(y <- @0){*y} | for(z <- @0){0}`.

The first receiver runs what it receives; the second discards it. If the first
takes the message, two receivers are left waiting on `@0`: the message itself,
now running, and the discarder. If the second takes it, the first receiver is
left waiting alone. Neither reduct contains an output, and every reduction
needs one, so neither reduces again. Structural congruence keeps the number of
input prefixes, two in one reduct and one in the other. The two reducts
therefore have no common reduct, not even up to structural congruence: the
fork breaks local confluence, and with it confluence. Distinct reducts of a
race, as in `PresentMoment.race_nondeterminism`, are thereby strengthened to
nonjoinable ones for this race.

The twin: the same two receivers on two channels, each channel with its own
copy of the message, commute, and the diamond closes after one step on each
side.

## Main results

* `constructorCount_eq_of_structuralCongruence`: structural congruence keeps
  the count of every constructor other than the null process, quotation and
  drop.
* `one_le_outputs_of_reduces`: the source of every reduction contains an output.
* `joinable_iff_of_no_output`: two processes without outputs are joinable, up to
  structural congruence, exactly when they are structurally congruent.
* `race_nonjoinable_fork`, `race_no_common_reduct`, `not_locallyConfluent`,
  `not_confluent`: the race.
* `separate_channels_square`, `twin_square`, `twin_joinable`: the twin.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-! ## Constructor counts

The occurrences of one constructor anywhere in a pattern. For a constructor
other than the null process, quotation and drop, structural congruence keeps
the count: the parallel laws add or remove null processes and rearrange
components, and quote/drop cancellation removes one quotation and one drop. -/

mutual
/-- The occurrences of the constructor `f` in a pattern. -/
def constructorCount (f : String) : Pattern → Nat
  | .bvar _ => 0
  | .fvar _ => 0
  | .apply g args => (if g = f then 1 else 0) + constructorCountList f args
  | .lambda _ body => constructorCount f body
  | .multiLambda _ _ body => constructorCount f body
  | .subst body replacement => constructorCount f body + constructorCount f replacement
  | .collection _ elements _ => constructorCountList f elements

/-- The occurrences of the constructor `f` in a list of patterns. -/
def constructorCountList (f : String) : List Pattern → Nat
  | [] => 0
  | p :: ps => constructorCount f p + constructorCountList f ps
end

theorem constructorCount_apply_self (f : String) (args : List Pattern) :
    constructorCount f (.apply f args) = constructorCountList f args + 1 := by
  show (if f = f then 1 else 0) + constructorCountList f args = _
  rw [if_pos rfl, Nat.add_comm]

theorem constructorCount_apply_of_ne {f g : String} (h : g ≠ f) (args : List Pattern) :
    constructorCount f (.apply g args) = constructorCountList f args := by
  show (if g = f then 1 else 0) + constructorCountList f args = _
  rw [if_neg h, Nat.zero_add]

theorem constructorCountList_append (f : String) :
    (l₁ l₂ : List Pattern) →
      constructorCountList f (l₁ ++ l₂) = constructorCountList f l₁ + constructorCountList f l₂
  | [], l₂ => (Nat.zero_add _).symm
  | p :: ps, l₂ => by
      show constructorCount f p + constructorCountList f (ps ++ l₂) =
        (constructorCount f p + constructorCountList f ps) + constructorCountList f l₂
      rw [constructorCountList_append f ps l₂, Nat.add_assoc]

theorem constructorCountList_perm (f : String) {l₁ l₂ : List Pattern} (h : l₁.Perm l₂) :
    constructorCountList f l₁ = constructorCountList f l₂ := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
      show constructorCount f p + _ = constructorCount f p + _
      rw [ih]
  | swap p q l =>
      show constructorCount f q + (constructorCount f p + constructorCountList f l) =
        constructorCount f p + (constructorCount f q + constructorCountList f l)
      exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem constructorCountList_of_pointwise (f : String) :
    (ps qs : List Pattern) → ps.length = qs.length →
      (∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
        constructorCount f (ps.get ⟨i, h₁⟩) = constructorCount f (qs.get ⟨i, h₂⟩)) →
      constructorCountList f ps = constructorCountList f qs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, [], h, _ => (Nat.succ_ne_zero _ h).elim
  | p :: ps, q :: qs, h, pointwise => by
      have head : constructorCount f p = constructorCount f q :=
        pointwise 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have tail := constructorCountList_of_pointwise f ps qs (Nat.succ.inj h)
        (fun i h₁ h₂ => pointwise (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂))
      show constructorCount f p + constructorCountList f ps =
        constructorCount f q + constructorCountList f qs
      rw [head, tail]

/-- **Structural congruence keeps the count** of every constructor other than
the null process, quotation and drop. -/
theorem constructorCount_eq_of_structuralCongruence {f : String}
    (notZero : "PZero" ≠ f) (notQuote : "NQuote" ≠ f) (notDrop : "PDrop" ≠ f)
    {p q : Pattern} (h : StructuralCongruence p q) :
    constructorCount f p = constructorCount f q := by
  induction h with
  | alpha _ _ e => rw [e]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | par_singleton p => rfl
  | par_nil_left p =>
      show constructorCount f (.apply "PZero" []) + (constructorCount f p + 0) =
        constructorCount f p
      rw [constructorCount_apply_of_ne notZero]
      exact Nat.zero_add _
  | par_nil_right p =>
      show constructorCount f p + (constructorCount f (.apply "PZero" []) + 0) =
        constructorCount f p
      rw [constructorCount_apply_of_ne notZero]
      rfl
  | par_comm p q =>
      show constructorCount f p + (constructorCount f q + 0) =
        constructorCount f q + (constructorCount f p + 0)
      exact Nat.add_comm _ _
  | par_assoc p q r =>
      show (constructorCount f p + (constructorCount f q + 0)) + (constructorCount f r + 0) =
        constructorCount f p + ((constructorCount f q + (constructorCount f r + 0)) + 0)
      exact Nat.add_assoc _ _ _
  | par_cong ps qs hlen _ ih => exact constructorCountList_of_pointwise f ps qs hlen ih
  | par_flatten ps qs =>
      show constructorCountList f (ps ++ [.collection .hashBag qs none]) =
        constructorCountList f (ps ++ qs)
      rw [constructorCountList_append, constructorCountList_append]
      rfl
  | par_perm _ _ hperm => exact constructorCountList_perm f hperm
  | set_perm _ _ hperm => exact constructorCountList_perm f hperm
  | set_cong es₁ es₂ hlen _ ih => exact constructorCountList_of_pointwise f es₁ es₂ hlen ih
  | lambda_cong _ _ _ _ ih => exact ih
  | apply_cong g args₁ args₂ hlen _ ih =>
      show (if g = f then 1 else 0) + constructorCountList f args₁ =
        (if g = f then 1 else 0) + constructorCountList f args₂
      rw [constructorCountList_of_pointwise f args₁ args₂ hlen ih]
  | collection_general_cong _ es₁ es₂ _ hlen _ ih =>
      exact constructorCountList_of_pointwise f es₁ es₂ hlen ih
  | multiLambda_cong _ _ _ _ _ ih => exact ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      show constructorCount f _ + constructorCount f _ = constructorCount f _ + constructorCount f _
      rw [ih₁, ih₂]
  | quote_drop n =>
      rw [constructorCount_apply_of_ne notQuote]
      show constructorCount f (.apply "PDrop" [n]) + 0 = constructorCount f n
      rw [constructorCount_apply_of_ne notDrop]
      rfl
  | par_empty =>
      show 0 = constructorCount f (.apply "PZero" [])
      rw [constructorCount_apply_of_ne notZero]
      rfl

/-! ## Every reduction needs an output -/

/-- The outputs of a pattern. -/
abbrev outputs (p : Pattern) : Nat := constructorCount "POutput" p

/-- The input prefixes of a pattern. -/
abbrev inputs (p : Pattern) : Nat := constructorCount "PInput" p

theorem outputs_eq_of_structuralCongruence {p q : Pattern} (h : StructuralCongruence p q) :
    outputs p = outputs q :=
  constructorCount_eq_of_structuralCongruence (by decide) (by decide) (by decide) h

theorem inputs_eq_of_structuralCongruence {p q : Pattern} (h : StructuralCongruence p q) :
    inputs p = inputs q :=
  constructorCount_eq_of_structuralCongruence (by decide) (by decide) (by decide) h

/-- **The source of every reduction contains an output.** -/
theorem one_le_outputs_of_reduces {p q : Pattern} (h : p ⇝ q) : 1 ≤ outputs p := by
  induction h with
  | @comm n q body rest =>
      show 1 ≤ constructorCount "POutput" (.apply "POutput" [n, q]) + _
      rw [constructorCount_apply_self]
      exact Nat.le_add_right_of_le (Nat.le_add_left 1 _)
  | equiv hsc _ _ ih =>
      rw [outputs_eq_of_structuralCongruence hsc]
      exact ih
  | par _ ih => exact Nat.le_add_right_of_le ih
  | @par_any p q before after _ ih =>
      show 1 ≤ constructorCountList "POutput" (before ++ [p] ++ after)
      rw [constructorCountList_append, constructorCountList_append]
      exact Nat.le_add_right_of_le (Nat.le_add_left_of_le ih)

/-- A process without an output does not reduce. -/
theorem not_reduces_of_no_output {p : Pattern} (noOutput : outputs p = 0) (q : Pattern) :
    IsEmpty (p ⇝ q) :=
  ⟨fun step => by
    have needed := one_le_outputs_of_reduces step
    rw [noOutput] at needed
    exact Nat.not_succ_le_zero 0 needed⟩

/-- A process without an output reaches only itself. -/
theorem eq_of_reducesStar_of_no_output {p q : Pattern} (noOutput : outputs p = 0)
    (run : p ⇝* q) : p = q := by
  cases run with
  | refl => rfl
  | step step _ => exact ((not_reduces_of_no_output noOutput _).false step).elim

/-- Joinability up to structural congruence: some reduct of the one process is
structurally congruent to some reduct of the other. -/
def Joinable (A B : Pattern) : Prop :=
  ∃ C₁ C₂ : Pattern, Nonempty (A ⇝* C₁) ∧ Nonempty (B ⇝* C₂) ∧ StructuralCongruence C₁ C₂

/-- **Among processes without outputs, joinability is structural congruence.** -/
theorem joinable_iff_of_no_output {A B : Pattern} (noOutputA : outputs A = 0)
    (noOutputB : outputs B = 0) : Joinable A B ↔ StructuralCongruence A B := by
  constructor
  · rintro ⟨C₁, C₂, ⟨run₁⟩, ⟨run₂⟩, congruent⟩
    rw [← eq_of_reducesStar_of_no_output noOutputA run₁,
      ← eq_of_reducesStar_of_no_output noOutputB run₂] at congruent
    exact congruent
  · intro congruent
    exact ⟨A, B, ⟨.refl A⟩, ⟨.refl B⟩, congruent⟩

/-! ## The race -/

/-- Both communications of a race: an output on `x` sending `P`, wanted by the
receivers with continuations `Q` and `R`. -/
theorem race_steps (x P Q R : Pattern) :
    Nonempty (bag [commOut x P, commIn x Q, commIn x R] ⇝ bag [commRes Q P, commIn x R]) ∧
      Nonempty (bag [commOut x P, commIn x Q, commIn x R] ⇝ bag [commRes R P, commIn x Q]) :=
  ⟨⟨comm_at_head x P Q [commIn x R]⟩,
    ⟨comm_anywhere (bag_perm (List.Perm.cons _ (List.Perm.swap _ _ _)))⟩⟩

/-- The name `@0`. -/
def quoteZero : Pattern := .apply "NQuote" [.apply "PZero" []]

/-- The message `for(w <- @0){0}`: a process that is itself a receiver. -/
def message : Pattern := commIn quoteZero (.apply "PZero" [])

/-- The continuation `*y`: run the received process. -/
def runReceived : Pattern := .apply "PDrop" [.bvar 0]

/-- The continuation `0`: discard the received process. -/
def discardReceived : Pattern := .apply "PZero" []

/-- `@0!(for(w <- @0){0}) | for(y <- @0){*y} | for(z <- @0){0}`. -/
def race : Pattern :=
  bag [commOut quoteZero message, commIn quoteZero runReceived, commIn quoteZero discardReceived]

/-- The runner took the message and runs it: `for(w <- @0){0} | for(z <- @0){0}`. -/
def runnerWon : Pattern := bag [message, commIn quoteZero discardReceived]

/-- The discarder took the message: `0 | for(y <- @0){*y}`. -/
def discarderWon : Pattern := bag [discardReceived, commIn quoteZero runReceived]

theorem commRes_runReceived : commRes runReceived message = message := by
  decide

theorem commRes_discardReceived : commRes discardReceived message = discardReceived := by
  decide

/-- **The fork**: either receiver can take the message. -/
theorem race_forks : Nonempty (race ⇝ runnerWon) ∧ Nonempty (race ⇝ discarderWon) := by
  obtain ⟨runner, discarder⟩ := race_steps quoteZero message runReceived discardReceived
  rw [commRes_runReceived] at runner
  rw [commRes_discardReceived] at discarder
  exact ⟨runner, discarder⟩

theorem runnerWon_outputs : outputs runnerWon = 0 := by decide

theorem discarderWon_outputs : outputs discarderWon = 0 := by decide

/-- Two receivers are left after the runner won. -/
theorem runnerWon_inputs : inputs runnerWon = 2 := by decide

/-- One receiver is left after the discarder won. -/
theorem discarderWon_inputs : inputs discarderWon = 1 := by decide

/-- The two reducts are not structurally congruent: they differ in the number
of input prefixes. -/
theorem runnerWon_not_congruent_discarderWon :
    ¬ StructuralCongruence runnerWon discarderWon := fun congruent => by
  have counts := inputs_eq_of_structuralCongruence congruent
  rw [runnerWon_inputs, discarderWon_inputs] at counts
  exact absurd counts (by decide)

/-- **The race is not joinable**: its two reducts have no common reduct, not even
up to structural congruence. -/
theorem race_not_joinable : ¬ Joinable runnerWon discarderWon := fun joinable =>
  runnerWon_not_congruent_discarderWon
    ((joinable_iff_of_no_output runnerWon_outputs discarderWon_outputs).mp joinable)

/-- In particular the two reducts have no common reduct. -/
theorem race_no_common_reduct :
    ¬ ∃ C : Pattern, Nonempty (runnerWon ⇝* C) ∧ Nonempty (discarderWon ⇝* C) :=
  fun ⟨C, runner, discarder⟩ => race_not_joinable ⟨C, C, runner, discarder, .refl C⟩

/-- **A nonjoinable fork**: the race steps to both reducts, and they have no
common reduct, not even up to structural congruence. -/
theorem race_nonjoinable_fork :
    Nonempty (race ⇝ runnerWon) ∧ Nonempty (race ⇝ discarderWon) ∧
      ¬ Joinable runnerWon discarderWon :=
  ⟨race_forks.1, race_forks.2, race_not_joinable⟩

/-- **Rho reduction is not locally confluent**, even up to structural congruence. -/
theorem not_locallyConfluent :
    ¬ ∀ p A B : Pattern, Nonempty (p ⇝ A) → Nonempty (p ⇝ B) → Joinable A B :=
  fun locallyConfluent =>
    race_not_joinable (locallyConfluent race runnerWon discarderWon race_forks.1 race_forks.2)

/-- **Rho reduction is not confluent**, even up to structural congruence. -/
theorem not_confluent :
    ¬ ∀ p A B : Pattern, Nonempty (p ⇝* A) → Nonempty (p ⇝* B) → Joinable A B :=
  fun confluent => not_locallyConfluent fun p A B ⟨first⟩ ⟨second⟩ =>
    confluent p A B ⟨ReducesStar.single first⟩ ⟨ReducesStar.single second⟩

/-! ## The twin: separate channels commute -/

/-- Two communications on four separate components close the diamond after one
step on each side, at the same process. -/
theorem separate_channels_square (x₁ P₁ Q x₂ P₂ R : Pattern) (rest : List Pattern) :
    Nonempty (bag (commOut x₁ P₁ :: commIn x₁ Q :: commOut x₂ P₂ :: commIn x₂ R :: rest) ⇝
        bag (commRes Q P₁ :: commOut x₂ P₂ :: commIn x₂ R :: rest)) ∧
      Nonempty (bag (commOut x₁ P₁ :: commIn x₁ Q :: commOut x₂ P₂ :: commIn x₂ R :: rest) ⇝
        bag (commRes R P₂ :: commOut x₁ P₁ :: commIn x₁ Q :: rest)) ∧
      Nonempty (bag (commRes Q P₁ :: commOut x₂ P₂ :: commIn x₂ R :: rest) ⇝
        bag (commRes R P₂ :: commRes Q P₁ :: rest)) ∧
      Nonempty (bag (commRes R P₂ :: commOut x₁ P₁ :: commIn x₁ Q :: rest) ⇝
        bag (commRes R P₂ :: commRes Q P₁ :: rest)) := by
  have secondFirst : (commOut x₁ P₁ :: commIn x₁ Q :: commOut x₂ P₂ :: commIn x₂ R :: rest).Perm
      (commOut x₂ P₂ :: commIn x₂ R :: commOut x₁ P₁ :: commIn x₁ Q :: rest) :=
    (List.perm_append_comm (l₁ := [commOut x₁ P₁, commIn x₁ Q])
      (l₂ := [commOut x₂ P₂, commIn x₂ R])).append_right rest
  have secondAfterFirst : (commRes Q P₁ :: commOut x₂ P₂ :: commIn x₂ R :: rest).Perm
      (commOut x₂ P₂ :: commIn x₂ R :: commRes Q P₁ :: rest) :=
    (List.perm_middle (a := commRes Q P₁) (l₁ := [commOut x₂ P₂, commIn x₂ R])
      (l₂ := rest)).symm
  have firstAfterSecond : (commRes R P₂ :: commOut x₁ P₁ :: commIn x₁ Q :: rest).Perm
      (commOut x₁ P₁ :: commIn x₁ Q :: commRes R P₂ :: rest) :=
    (List.perm_middle (a := commRes R P₂) (l₁ := [commOut x₁ P₁, commIn x₁ Q])
      (l₂ := rest)).symm
  exact ⟨⟨comm_at_head x₁ P₁ Q _⟩,
    ⟨comm_anywhere (n := x₂) (q := P₂) (p := R) (rest := commOut x₁ P₁ :: commIn x₁ Q :: rest)
      (bag_perm secondFirst)⟩,
    ⟨comm_anywhere (n := x₂) (q := P₂) (p := R) (rest := commRes Q P₁ :: rest)
      (bag_perm secondAfterFirst)⟩,
    ⟨Reduces.equiv (bag_perm firstAfterSecond) (comm_at_head x₁ P₁ Q (commRes R P₂ :: rest))
      (bag_perm (List.Perm.swap _ _ _))⟩⟩

/-- The second name `@(for(w <- @0){0})`. -/
def quoteMessage : Pattern := .apply "NQuote" [message]

theorem quoteZero_ne_quoteMessage : quoteZero ≠ quoteMessage := by decide

/-- The same two receivers on separate channels, each channel with its own copy
of the message: `@0!(M) | for(y <- @0){*y} | @M!(M) | for(z <- @M){0}`, where
`M = for(w <- @0){0}`. -/
def twin : Pattern :=
  bag [commOut quoteZero message, commIn quoteZero runReceived,
    commOut quoteMessage message, commIn quoteMessage discardReceived]

/-- The runner communicated first. -/
def twinRunnerFirst : Pattern :=
  bag [message, commOut quoteMessage message, commIn quoteMessage discardReceived]

/-- The discarder communicated first. -/
def twinDiscarderFirst : Pattern :=
  bag [discardReceived, commOut quoteZero message, commIn quoteZero runReceived]

/-- Both communicated. -/
def twinJoined : Pattern := bag [discardReceived, message]

/-- **The twin closes the diamond**: either communication can go first, and the
other one then reaches the same process. -/
theorem twin_square :
    Nonempty (twin ⇝ twinRunnerFirst) ∧ Nonempty (twin ⇝ twinDiscarderFirst) ∧
      Nonempty (twinRunnerFirst ⇝ twinJoined) ∧ Nonempty (twinDiscarderFirst ⇝ twinJoined) := by
  obtain ⟨first, second, firstThen, secondThen⟩ :=
    separate_channels_square quoteZero message runReceived quoteMessage message discardReceived []
  rw [commRes_runReceived] at first firstThen secondThen
  rw [commRes_discardReceived] at second firstThen secondThen
  exact ⟨first, second, firstThen, secondThen⟩

/-- The twin's two one-step reducts are joinable. -/
theorem twin_joinable : Joinable twinRunnerFirst twinDiscarderFirst := by
  obtain ⟨-, -, ⟨firstThen⟩, ⟨secondThen⟩⟩ := twin_square
  exact ⟨twinJoined, twinJoined, ⟨ReducesStar.single firstThen⟩,
    ⟨ReducesStar.single secondThen⟩, .refl _⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence
