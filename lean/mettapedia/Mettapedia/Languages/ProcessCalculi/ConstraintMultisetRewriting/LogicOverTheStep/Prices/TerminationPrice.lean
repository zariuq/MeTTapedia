import Mettapedia.Logic.ReverseMathematics.WeakKoenig
import Mettapedia.Logic.ReverseMathematics.Omniscience

/-!
# The price of a budget: "every run finishes" against "runs have a bound"

A **binary system** gives each state an optional left and right successor (`BinarySystem`); a run
follows a binary choice sequence, taking the other branch when the chosen one is not present, and finishes
when it reaches a state with no successor (`walk`). Three readings of "every run finishes", and the
bound a budget needs:

* `Barred`: every choice sequence reaches a finished stage (the positive, bar form);
* `NoInfiniteRun`: no choice sequence runs forever (the negative form);
* `Acc`: the inductive form, well-foundedness of the step from the state;
* `Bounded`: one stage by which every run has finished.

## The prices

* **The fan theorem for decidable bars** (`FAN`, added here: every decidable bar of the binary fan is
  uniform) is exactly what turns the bar form into a bound: `barBound_iff_fan`. The bound is read off
  the uniform bar (`bounded_of_barred`); conversely the binary fan itself, stopped at a decidable bar, is
  a binary system (`fanSystem`), so a bound for it is a uniform bar (`fan_of_barBound`).
* **The negative form costs the fan theorem and Markov's principle**: `runBound_iff`. Markov's principle
  turns "no run is infinite" into the bar form (`barred_of_noInfiniteRun`); conversely a line that stops
  where a binary sequence is `true` turns a bound into a `true` entry (`mp_of_runBound`).
* **A rank or an inductive proof needs no principle**: a rank into the naturals bounds every run by the
  rank (`bounded_of_rank`), and well-foundedness proved by induction (`Acc`) gives a bound by recursion
  on the proof (`bounded_of_acc`). So a budget is derived, not guessed, whenever termination is proved
  inductively or by a rank, and the branching is finite.

The fan theorem holds in Lean's classical logic, from the tree's König lemma
(`WeakKoenig.exists_path`): `fan_classical` (it uses `Classical.choice`, as `lpo_classical` does). It
fails in the computable reading, even without asking the bound to be computed: the complement of
Kleene's tree is a computable bar of every computable sequence and is not uniform
(`not_computableFAN`), while Markov's principle is realized by unbounded search there
(`computable_reading`, with the tree's `Omniscience.computableMP`). So a computing runtime cannot
supply the fan theorem: a budget must come from a rank or an inductive proof. The theorems of the
computable reading use classical logic about computability; every other theorem here uses no
`Classical.choice`.

## Controls

* `Controls.fan_acc` and `Controls.fan_unbounded`: with infinite branching (a root stepping to every
  `pos n`, each `pos (n + 1)` to `pos n`), every run finishes, inductively, and runs have every length,
  so no bound exists in any logic; finite branching is needed. A lexicographic rank (`(1, 0)` at the
  root, `(0, n)` at `pos n`) decreases along every step of this system, so a lexicographic rank alone
  gives no budget.
* `Controls.stop_bounded`, `Controls.fan_system_barred`: the principles' instances on actual systems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.TerminationPrice

open Mettapedia.Logic.ReverseMathematics.Omniscience

universe u

theorem boolCases (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Binary sequences and the fan theorem -/

/-- The first `n` entries of a binary sequence. -/
def initial (α : ℕ → Bool) (n : ℕ) : List Bool := (List.range n).map α

theorem initial_succ (α : ℕ → Bool) (n : ℕ) : initial α (n + 1) = initial α n ++ [α n] := by
  simp [initial, List.range_succ]

theorem length_initial (α : ℕ → Bool) (n : ℕ) : (initial α n).length = n := by
  simp [initial]

theorem initial_take (α : ℕ → Bool) {k : ℕ} : ∀ {n : ℕ}, k ≤ n → (initial α n).take k = initial α k
  | 0, le => by
      have zero : k = 0 := by omega
      subst zero
      rfl
  | n + 1, le => by
      rcases Nat.lt_or_ge k (n + 1) with lt | ge
      · rw [initial_succ, List.take_append_of_le_length (by rw [length_initial]; omega),
          initial_take α (by omega)]
      · have same : k = n + 1 := by omega
        subst same
        exact List.take_of_length_le (le_of_eq (length_initial α _))

/-- **The fan theorem for decidable bars**: every decidable bar of the binary fan is uniform. -/
def FAN : Prop :=
  ∀ B : List Bool → Bool, (∀ α : ℕ → Bool, ∃ n, B (initial α n) = true) →
    ∃ N, ∀ α : ℕ → Bool, ∃ n ≤ N, B (initial α n) = true

/-! ## Binary systems and their runs -/

/-- **A binary system**: an optional left and right successor at every state. -/
structure BinarySystem (S : Type u) where
  step : S → Bool → Option S

namespace BinarySystem

variable {S : Type u} (G : BinarySystem S)

/-- The successor chosen by `b`, or the other one when the chosen one is not present. -/
def choose (t : S) (b : Bool) : Option S :=
  match G.step t b with
  | some next => some next
  | none => G.step t (!b)

/-- The run along a choice sequence; `none` once it has finished. -/
def walk (s : S) (α : ℕ → Bool) : ℕ → Option S
  | 0 => some s
  | n + 1 => (walk s α n).bind fun t => G.choose t (α n)

/-- **Every run finishes, as a bar.** -/
def Barred (s : S) : Prop := ∀ α : ℕ → Bool, ∃ n, G.walk s α n = none

/-- **No run is infinite.** -/
def NoInfiniteRun (s : S) : Prop := ¬ ∃ α : ℕ → Bool, ∀ n, G.walk s α n ≠ none

/-- **Runs have a bound.** -/
def Bounded (s : S) : Prop := ∃ N, ∀ α : ℕ → Bool, G.walk s α N = none

/-- `t` is a successor of `u`. -/
def Succ (t u : S) : Prop := G.step u false = some t ∨ G.step u true = some t

/-- The run along a finite list of choices. -/
def walkAlong (s : S) (choices : List Bool) : Option S :=
  choices.foldl (fun current b => current.bind fun t => G.choose t b) (some s)

theorem walk_none_mono {s : S} {α : ℕ → Bool} {n m : ℕ} (le : n ≤ m)
    (finished : G.walk s α n = none) : G.walk s α m = none := by
  induction le with
  | refl => exact finished
  | step _ ih =>
    show (G.walk s α _).bind _ = none
    rw [ih]
    rfl

theorem walkAlong_initial (s : S) (α : ℕ → Bool) (n : ℕ) :
    G.walkAlong s (initial α n) = G.walk s α n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have unfold : G.walkAlong s (initial α (n + 1)) =
        (G.walkAlong s (initial α n)).bind fun t => G.choose t (α n) := by
      rw [initial_succ]
      unfold walkAlong
      rw [List.foldl_append]
      rfl
    rw [unfold, ih]
    rfl

theorem choose_succ {t next : S} {b : Bool} (chosen : G.choose t b = some next) : G.Succ next t := by
  unfold choose at chosen
  cases b <;> cases hb : G.step t _ with
  | none => rw [hb] at chosen; first | exact Or.inr chosen | exact Or.inl chosen
  | some other => rw [hb] at chosen; cases chosen; first | exact Or.inl hb | exact Or.inr hb

/-- The run from `s` after its first choice is a run from the chosen successor. -/
theorem walk_succ_left (s : S) (α : ℕ → Bool) (n : ℕ) :
    G.walk s α (n + 1) = (G.choose s (α 0)).bind fun t => G.walk t (fun k => α (k + 1)) n := by
  induction n with
  | zero =>
    show G.choose s (α 0) = (G.choose s (α 0)).bind fun t => G.walk t (fun k => α (k + 1)) 0
    cases G.choose s (α 0) <;> rfl
  | succ n ih =>
    show (G.walk s α (n + 1)).bind (fun t => G.choose t (α (n + 1))) = _
    rw [ih]
    cases G.choose s (α 0) with
    | none => rfl
    | some t => rfl

end BinarySystem

/-! ## The fan theorem is the price of a bound from a bar -/

/-- **The fan theorem turns "every run finishes" (bar form) into a bound.** -/
theorem bounded_of_barred (fan : FAN) {S : Type u} (G : BinarySystem S) {s : S}
    (barred : G.Barred s) : G.Bounded s := by
  obtain ⟨N, uniform⟩ := fan (fun choices => (G.walkAlong s choices).isNone) fun α => by
    obtain ⟨n, finished⟩ := barred α
    exact ⟨n, by rw [G.walkAlong_initial, finished]; rfl⟩
  refine ⟨N, fun α => ?_⟩
  obtain ⟨n, le, finished⟩ := uniform α
  rw [G.walkAlong_initial] at finished
  exact G.walk_none_mono le (Option.isNone_iff_eq_none.mp finished)

/-- A bound for every barred state of every binary system. -/
def BarBound : Prop := ∀ (S : Type) (G : BinarySystem S) (s : S), G.Barred s → G.Bounded s

/-- The monotone closure of a bar: some initial part of the node is in it. -/
def closure (B : List Bool → Bool) (node : List Bool) : Bool :=
  (List.range (node.length + 1)).any fun k => B (node.take k)

/-- **The binary fan as a binary system**, each node stepping to both extensions until it meets the
bar. -/
def fanSystem (B : List Bool → Bool) : BinarySystem (List Bool) where
  step node b := if closure B node = true then none else some (node ++ [b])

theorem fanSystem_choose_closed {B : List Bool → Bool} {node : List Bool}
    (closed : closure B node = true) (b : Bool) : (fanSystem B).choose node b = none := by
  simp [BinarySystem.choose, fanSystem, closed]

theorem fanSystem_choose_open {B : List Bool → Bool} {node : List Bool}
    (open' : closure B node = false) (b : Bool) : (fanSystem B).choose node b = some (node ++ [b]) := by
  simp [BinarySystem.choose, fanSystem, open']

theorem closure_of_bar {B : List Bool → Bool} {node : List Bool} (hit : B node = true) :
    closure B node = true :=
  List.any_eq_true.mpr ⟨node.length, List.mem_range.mpr (Nat.lt_succ_self _), by
    rw [List.take_of_length_le (le_refl _)]
    exact hit⟩

theorem bar_of_closure {B : List Bool → Bool} {α : ℕ → Bool} {m : ℕ}
    (closed : closure B (initial α m) = true) : ∃ k ≤ m, B (initial α k) = true := by
  obtain ⟨k, member, hit⟩ := List.any_eq_true.mp closed
  have le : k ≤ m := by
    have := List.mem_range.mp member
    rw [length_initial] at this
    omega
  exact ⟨k, le, by rw [← initial_take α le]; exact hit⟩

/-- The run of the fan along a choice sequence: alive at its initial part, or finished after meeting
the bar. -/
theorem fan_walk (B : List Bool → Bool) (α : ℕ → Bool) : ∀ n,
    ((fanSystem B).walk [] α n = some (initial α n) ∧ ∀ m < n, closure B (initial α m) = false) ∨
      ((fanSystem B).walk [] α n = none ∧ ∃ m < n, closure B (initial α m) = true)
  | 0 => Or.inl ⟨rfl, fun _ lt => absurd lt (Nat.not_lt_zero _)⟩
  | n + 1 => by
      rcases fan_walk B α n with ⟨alive, before⟩ | ⟨finished, m, lt, closed⟩
      · rcases boolCases (closure B (initial α n)) with open' | closed
        · left
          refine ⟨?_, fun m lt => ?_⟩
          · show ((fanSystem B).walk [] α n).bind _ = _
            rw [alive]
            show (fanSystem B).choose (initial α n) (α n) = _
            rw [fanSystem_choose_open open', initial_succ]
          · rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
            · exact before m lt
            · exact open'
        · right
          refine ⟨?_, n, Nat.lt_succ_self n, closed⟩
          show ((fanSystem B).walk [] α n).bind _ = _
          rw [alive]
          exact fanSystem_choose_closed closed (α n)
      · right
        exact ⟨(fanSystem B).walk_none_mono (Nat.le_succ n) finished, m, Nat.lt_succ_of_lt lt, closed⟩

/-- **A bound for every barred binary system gives the fan theorem.** -/
theorem fan_of_barBound (bound : BarBound) : FAN := by
  intro B bar
  have barred : (fanSystem B).Barred [] := by
    intro α
    obtain ⟨n, hit⟩ := bar α
    refine ⟨n + 1, ?_⟩
    rcases fan_walk B α n with ⟨alive, _⟩ | ⟨finished, _⟩
    · show ((fanSystem B).walk [] α n).bind _ = none
      rw [alive]
      exact fanSystem_choose_closed (closure_of_bar hit) (α n)
    · exact (fanSystem B).walk_none_mono (Nat.le_succ n) finished
  obtain ⟨N, uniform⟩ := bound (List Bool) (fanSystem B) [] barred
  refine ⟨N, fun α => ?_⟩
  rcases fan_walk B α N with ⟨alive, _⟩ | ⟨_, m, lt, closed⟩
  · rw [uniform α] at alive
    exact nomatch alive
  · obtain ⟨k, le, hit⟩ := bar_of_closure closed
    exact ⟨k, by omega, hit⟩

/-- **"Every run finishes" (bar form) gives a bound exactly under the fan theorem.** -/
theorem barBound_iff_fan : BarBound ↔ FAN :=
  ⟨fan_of_barBound, fun fan _ G _ barred => bounded_of_barred fan G barred⟩

/-! ## The negative form costs the fan theorem and Markov's principle -/

/-- A bound for every binary system with no infinite run. -/
def RunBound : Prop := ∀ (S : Type) (G : BinarySystem S) (s : S), G.NoInfiniteRun s → G.Bounded s

theorem noInfiniteRun_of_barred {S : Type u} (G : BinarySystem S) {s : S} (barred : G.Barred s) :
    G.NoInfiniteRun s := by
  rintro ⟨α, alive⟩
  obtain ⟨n, finished⟩ := barred α
  exact alive n finished

/-- **Markov's principle turns "no run is infinite" into the bar form.** -/
theorem barred_of_noInfiniteRun (mp : MP) {S : Type u} (G : BinarySystem S) {s : S}
    (noInfinite : G.NoInfiniteRun s) : G.Barred s := by
  intro α
  obtain ⟨n, finished⟩ := mp (fun n => (G.walk s α n).isNone) fun allAlive =>
    noInfinite ⟨α, fun n finished => by
      have alive := allAlive n
      rw [finished] at alive
      exact Bool.noConfusion alive⟩
  exact ⟨n, Option.isNone_iff_eq_none.mp finished⟩

/-- A line that stops where the sequence is `true`. -/
def stopSystem (α : ℕ → Bool) : BinarySystem ℕ where
  step n _ := if α n = true then none else some (n + 1)

theorem stop_walk (α : ℕ → Bool) (β : ℕ → Bool) : ∀ n,
    ((stopSystem α).walk 0 β n = some n ∧ ∀ m < n, α m = false) ∨
      ((stopSystem α).walk 0 β n = none ∧ ∃ m < n, α m = true)
  | 0 => Or.inl ⟨rfl, fun _ lt => absurd lt (Nat.not_lt_zero _)⟩
  | n + 1 => by
      rcases stop_walk α β n with ⟨alive, before⟩ | ⟨finished, m, lt, hit⟩
      · rcases boolCases (α n) with clear | hit
        · left
          refine ⟨?_, fun m lt => ?_⟩
          · show ((stopSystem α).walk 0 β n).bind _ = _
            rw [alive]
            simp [BinarySystem.choose, stopSystem, clear]
          · rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
            · exact before m lt
            · exact clear
        · right
          refine ⟨?_, n, Nat.lt_succ_self n, hit⟩
          show ((stopSystem α).walk 0 β n).bind _ = _
          rw [alive]
          simp [BinarySystem.choose, stopSystem, hit]
      · right
        exact ⟨(stopSystem α).walk_none_mono (Nat.le_succ n) finished, m, Nat.lt_succ_of_lt lt, hit⟩

/-- **A bound for every system with no infinite run gives Markov's principle.** -/
theorem mp_of_runBound (bound : RunBound) : MP := by
  intro α notAll
  have noInfinite : (stopSystem α).NoInfiniteRun 0 := by
    rintro ⟨β, alive⟩
    refine notAll fun n => ?_
    rcases stop_walk α β (n + 1) with ⟨_, before⟩ | ⟨finished, _⟩
    · exact before n (Nat.lt_succ_self n)
    · exact absurd finished (alive (n + 1))
  obtain ⟨N, finished⟩ := bound ℕ (stopSystem α) 0 noInfinite
  rcases stop_walk α (fun _ => false) N with ⟨alive, _⟩ | ⟨_, m, _, hit⟩
  · rw [finished (fun _ => false)] at alive
    exact nomatch alive
  · exact ⟨m, hit⟩

/-- **"No run is infinite" gives a bound exactly under the fan theorem and Markov's principle.** -/
theorem runBound_iff : RunBound ↔ FAN ∧ MP := by
  constructor
  · intro bound
    exact ⟨fan_of_barBound fun S G s barred => bound S G s (noInfiniteRun_of_barred G barred),
      mp_of_runBound bound⟩
  · rintro ⟨fan, mp⟩ S G s noInfinite
    exact bounded_of_barred fan G (barred_of_noInfiniteRun mp G noInfinite)

/-! ## A rank, or an inductive proof, needs no principle -/

/-- **A rank bounds every run.** -/
theorem bounded_of_rank {S : Type u} (G : BinarySystem S) (rank : S → ℕ)
    (decreasing : ∀ {t u : S}, G.Succ t u → rank t < rank u) (s : S) : G.Bounded s := by
  refine ⟨rank s + 1, fun α => ?_⟩
  have descent : ∀ n t, G.walk s α n = some t → rank t + n ≤ rank s := by
    intro n
    induction n with
    | zero =>
      intro t reached
      have same : t = s := (Option.some.inj reached).symm
      rw [same]
      omega
    | succ n ih =>
      intro t reached
      have unfolded : (G.walk s α n).bind (fun t => G.choose t (α n)) = some t := reached
      cases previous : G.walk s α n with
      | none =>
        rw [previous] at unfolded
        exact nomatch unfolded
      | some p =>
        rw [previous] at unfolded
        have lower := decreasing (G.choose_succ unfolded)
        have earlier := ih p previous
        omega
  cases final : G.walk s α (rank s + 1) with
  | none => rfl
  | some t =>
    have := descent _ t final
    omega

/-- **An inductive proof of termination gives a bound**, by recursion on the proof. -/
theorem bounded_of_acc {S : Type u} (G : BinarySystem S) {s : S} (acc : Acc G.Succ s) :
    G.Bounded s := by
  induction acc with
  | intro s _ ih =>
    have each : ∀ b : Bool, ∃ N, ∀ t, G.step s b = some t → ∀ β : ℕ → Bool, G.walk t β N = none := by
      intro b
      cases hb : G.step s b with
      | none => exact ⟨0, fun t ht => nomatch ht⟩
      | some t =>
        have succ : G.Succ t s := by
          cases b
          · exact Or.inl hb
          · exact Or.inr hb
        obtain ⟨N, bound⟩ := ih t succ
        exact ⟨N, fun t' ht' β => by
          have same : t = t' := Option.some.inj ht'
          rw [← same]
          exact bound β⟩
    obtain ⟨Nf, boundF⟩ := each false
    obtain ⟨Nt, boundT⟩ := each true
    refine ⟨max Nf Nt + 1, fun α => ?_⟩
    rw [G.walk_succ_left]
    cases chosen : G.choose s (α 0) with
    | none => rfl
    | some t =>
      show G.walk t _ (max Nf Nt) = none
      have succ := G.choose_succ chosen
      rcases succ with stepF | stepT
      · exact G.walk_none_mono (le_max_left Nf Nt) (boundF t stepF _)
      · exact G.walk_none_mono (le_max_right Nf Nt) (boundT t stepT _)

/-! ## The fan theorem in classical logic -/

/-- **The fan theorem holds classically**, from the tree's König lemma; this proof uses
`Classical.choice`. -/
theorem fan_classical : FAN := by
  classical
  intro B bar
  by_contra notUniform
  let T : Set (List Bool) := {node | ∀ k ≤ node.length, B (node.take k) = false}
  have tree : Mettapedia.Logic.ReverseMathematics.IsTree T := by
    intro node inside k j le
    rw [List.take_take]
    exact inside _ (le_trans (Nat.min_le_left _ _) (le_trans le (by simp)))
  have levels : Mettapedia.Logic.ReverseMathematics.HasAllLevels T := by
    intro N
    by_contra none
    apply notUniform
    refine ⟨N, fun α => ?_⟩
    by_contra noHit
    apply none
    refine ⟨initial α N, fun k le => ?_, length_initial α N⟩
    rw [length_initial] at le
    rw [initial_take α le]
    cases hB : B (initial α k) with
    | false => rfl
    | true => exact absurd ⟨k, le, hB⟩ noHit
  obtain ⟨X, path⟩ := Mettapedia.Logic.ReverseMathematics.exists_path tree levels
  obtain ⟨n, hit⟩ := bar fun i => decide (i ∈ X)
  have inside := path n
  have same : Mettapedia.Logic.ReverseMathematics.prefixOf X n = initial (fun i => decide (i ∈ X)) n :=
    rfl
  have clear := inside n (by rw [Mettapedia.Logic.ReverseMathematics.length_prefixOf])
  rw [List.take_of_length_le (by rw [Mettapedia.Logic.ReverseMathematics.length_prefixOf]), same] at clear
  rw [clear] at hit
  exact Bool.noConfusion hit

/-! ## The computable reading: the fan theorem fails, by Kleene's tree -/

section ComputableReading

open Mettapedia.Logic.ReverseMathematics (codeOf kleeneTree kleeneTree_isTree kleeneWitness
  kleeneWitness_mem length_kleeneWitness isDNR_of_isPath_kleeneTree not_computable_of_isDNR indicator
  prefixOf getD_eq_getElem' IsPath codeOf_kleeneTree_recursive)

/-- **The fan theorem read over computable sequences and computable bars**, with no uniformity asked
of the bound. -/
def ComputableFAN : Prop :=
  ∀ B : List Bool → Bool, Computable B →
    (∀ α : ℕ → Bool, Computable α → ∃ n, B (initial α n) = true) →
      ∃ N, ∀ α : ℕ → Bool, ∃ n ≤ N, B (initial α n) = true

theorem mem_codeOf_encode {T : Set (List Bool)} {s : List Bool} :
    Encodable.encode s ∈ codeOf T ↔ s ∈ T := by
  constructor
  · rintro ⟨t, ht, same⟩
    exact Encodable.encode_injective same ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

/-- **The fan theorem fails in the computable reading**: the complement of Kleene's tree bars every
computable sequence (a computable path would be a computable diagonally noncomputable function), and it
is not uniform (the tree has nodes at every level). A runtime that computes cannot supply the bound. -/
theorem not_computableFAN : ¬ ComputableFAN := by
  classical
  intro fan
  obtain ⟨inst, decideTree⟩ := codeOf_kleeneTree_recursive
  let B : List Bool → Bool := fun s => !(@decide (Encodable.encode s ∈ codeOf kleeneTree) (inst _))
  have computableB : Computable B := Primrec.not.to_comp.comp (decideTree.comp Computable.encode)
  have barIff : ∀ s, B s = true ↔ s ∉ kleeneTree := by
    intro s
    rw [← mem_codeOf_encode (T := kleeneTree)]
    simp [B]
  obtain ⟨N, uniform⟩ := fan B computableB fun α computableα => by
    by_contra noHit
    have inTree : ∀ n, initial α n ∈ kleeneTree := fun n => by
      by_contra notIn
      exact noHit ⟨n, (barIff _).mpr notIn⟩
    have path : IsPath {i | α i = true} kleeneTree := by
      intro n
      have same : prefixOf {i | α i = true} n = initial α n := by
        unfold prefixOf initial
        refine List.map_congr_left fun i _ => ?_
        cases hα : α i with
        | false => exact @decide_eq_false _ (Classical.propDecidable _) (by simp [hα])
        | true => exact @decide_eq_true _ (Classical.propDecidable _) (by simp [hα])
      rw [same]
      exact inTree n
    apply not_computable_of_isDNR (isDNR_of_isPath_kleeneTree path)
    have indicatorEq : indicator {i | α i = true} = fun n => bif α n then 1 else 0 := by
      funext n
      unfold indicator
      cases h : α n <;> simp [h]
    rw [indicatorEq]
    exact Computable.cond computableα (Computable.const 1) (Computable.const 0)
  let α : ℕ → Bool := fun i => (kleeneWitness N).getD i false
  have prefixWitness : ∀ n, n ≤ N → initial α n = (kleeneWitness N).take n := by
    intro n le
    apply List.ext_getElem
    · simp [initial, length_kleeneWitness, Nat.min_eq_left le]
    · intro i h₁ _
      have short : i < n := by simpa [initial] using h₁
      have iN : i < (kleeneWitness N).length := by rw [length_kleeneWitness]; omega
      rw [List.getElem_take]
      simp only [initial, List.getElem_map, List.getElem_range]
      exact getD_eq_getElem' iN
  obtain ⟨n, le, hit⟩ := uniform α
  have inside : initial α n ∈ kleeneTree := by
    rw [prefixWitness n le]
    exact kleeneTree_isTree _ (kleeneWitness_mem N) n
  exact (barIff _).mp hit inside

/-- **The computable reading separates the prices**: Markov's principle is realized by unbounded search,
the fan theorem is not. -/
theorem computable_reading :
    Mettapedia.Logic.ReverseMathematics.Omniscience.ComputableMP ∧ ¬ ComputableFAN :=
  ⟨Mettapedia.Logic.ReverseMathematics.Omniscience.computableMP, not_computableFAN⟩

end ComputableReading

/-! ## Controls -/

namespace Controls

/-- The states of the infinitely branching control. -/
inductive FanState
  | root
  | pos (n : ℕ)

/-- The root steps to every `pos n`; `pos (n + 1)` steps to `pos n`. -/
def fanStep : FanState → FanState → Prop
  | .root, .pos _ => True
  | .pos (n + 1), .pos m => m = n
  | _, _ => False

/-- A run of length `n` from a state. -/
def HasRun {S : Type u} (R : S → S → Prop) : S → ℕ → Prop
  | _, 0 => True
  | s, n + 1 => ∃ t, R s t ∧ HasRun R t n

theorem acc_pos : ∀ n, Acc (fun t s => fanStep s t) (FanState.pos n)
  | 0 => Acc.intro _ fun t step => by
      cases t with
      | root => exact absurd step id
      | pos m => exact absurd step id
  | n + 1 => Acc.intro _ fun t step => by
      cases t with
      | root => exact absurd step id
      | pos m =>
        have same : m = n := step
        rw [same]
        exact acc_pos n

/-- **Every run of the infinitely branching control finishes**, inductively. -/
theorem fan_acc : Acc (fun t s => fanStep s t) FanState.root :=
  Acc.intro _ fun t step => by
    cases t with
    | root => exact absurd step id
    | pos n => exact acc_pos n

theorem run_pos : ∀ n, HasRun fanStep (FanState.pos n) n
  | 0 => trivial
  | n + 1 => ⟨FanState.pos n, rfl, run_pos n⟩

/-- **The infinitely branching control has runs of every length**: no bound exists, in any logic. -/
theorem fan_unbounded (N : ℕ) : HasRun fanStep FanState.root (N + 1) :=
  ⟨FanState.pos N, trivial, run_pos N⟩

/-- The lexicographic rank of the control decreases along every step. -/
def lexRank : FanState → ℕ × ℕ
  | .root => (1, 0)
  | .pos n => (0, n)

theorem lexRank_decreases {s t : FanState} (step : fanStep s t) :
    Prod.Lex (· < ·) (· < ·) (lexRank t) (lexRank s) := by
  cases s with
  | root =>
    cases t with
    | root => exact absurd step id
    | pos n => exact Prod.Lex.left _ _ Nat.zero_lt_one
  | pos n =>
    cases t with
    | root => cases n <;> exact absurd step id
    | pos m =>
      cases n with
      | zero => exact absurd step id
      | succ n =>
        have same : m = n := step
        rw [same]
        exact Prod.Lex.right _ (Nat.lt_succ_self n)

/-- Positive control: the line of the zero sequence has no bound and is not barred: its run along
any choice sequence is alive at every stage. -/
theorem stop_zero_alive (β : ℕ → Bool) (n : ℕ) : (stopSystem fun _ => false).walk 0 β n = some n := by
  rcases stop_walk (fun _ => false) β n with ⟨alive, _⟩ | ⟨_, _, _, hit⟩
  · exact alive
  · exact Bool.noConfusion hit

/-- Positive control: a pulse at `3` stops every run by stage `4`, with no principle. -/
theorem stop_bounded : (stopSystem fun n => decide (n = 3)).Bounded 0 := by
  refine ⟨4, fun β => ?_⟩
  rcases stop_walk (fun n => decide (n = 3)) β 4 with ⟨_, before⟩ | ⟨finished, _⟩
  · exact absurd (before 3 (by decide)) (by decide)
  · exact finished

/-- Positive control: the fan stopped at length `2` is barred. -/
theorem fan_system_barred : (fanSystem fun node => decide (node.length = 2)).Barred [] := by
  intro α
  refine ⟨3, ?_⟩
  rcases fan_walk (fun node => decide (node.length = 2)) α 3 with ⟨_, before⟩ | ⟨finished, _⟩
  · have closed := closure_of_bar (B := fun node => decide (node.length = 2)) (node := initial α 2)
      (by simp [length_initial])
    rw [before 2 (by decide)] at closed
    exact Bool.noConfusion closed
  · exact finished

end Controls

#print axioms bounded_of_barred
#print axioms fan_of_barBound
#print axioms barBound_iff_fan
#print axioms barred_of_noInfiniteRun
#print axioms mp_of_runBound
#print axioms runBound_iff
#print axioms bounded_of_rank
#print axioms bounded_of_acc
#print axioms fan_classical
#print axioms not_computableFAN
#print axioms computable_reading
#print axioms Controls.fan_acc
#print axioms Controls.fan_unbounded
#print axioms Controls.lexRank_decreases
#print axioms Controls.stop_zero_alive
#print axioms Controls.stop_bounded
#print axioms Controls.fan_system_barred

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.TerminationPrice
