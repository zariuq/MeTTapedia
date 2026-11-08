import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSpectrum

/-!
# The race pair inside the step

The textbook pair `a.(b + c)` and `a.b + a.c`, as two configurations of one program of the
first-order step, with transitions labelled by **rules**. It is built for every term syntax and
every substitution action: the firings are ground (`RaceSpectrum.Ground`), so admission is decided on
occurrences alone (`Ground.valid_iff`).

* Rule `A` takes `a` and `go` and makes `k`; rule `B` takes `k` and makes `b`; rule `C` takes `k` and
  makes `c`. The occurrences `p` and `q` both carry `go`; `k`, `kb` and `kc` all carry `k`.
* **`P = {a, p}` takes `a`, then leaves a race**: `A` fires at `{a, p}` and makes `k`; then `B` and
  `C` are both admitted and both take `k` (`race_at_K`).
* **`Q = {a, q}` races at once**: two firings of `A`, one making `kb` and one making `kc`, are both
  admitted and both take `a` and `q` (`race_at_Q`); after either, the other is refused. Only `B`
  takes `kb`, only `C` takes `kc`.

## Results

* **The same traces** (`traceEquivalent_P_Q`): `ε, A, AB, AC` for both (`hasTrace_P`, `hasTrace_Q`).
* **The same answer bags at every budget** (`approx_P_eq_approx_Q`, `collect_P_eq_collect_Q`): the
  bounded searches of the step agree at every budget; at budget 3 both are finished and collect the
  two distinct final configurations once each (`collect_P`, `answers_distinct`).
* **Not bisimilar** (`not_bisimilar_P_Q`), separated by `⟨A⟩(⟨B⟩⊤ ∧ ⟨C⟩⊤)`, which holds at `P`
  (`separating_holds_P`) and fails at `Q` (`separating_fails_Q`). The program is finite, so the
  Hennessy–Milner characterization applies (`offers_finite`, `RaceSpectrum.bisimilar_iff_sat`).
* **Rung one is blind** (`rung_one_blind`, `traces_and_bags_do_not_decide`): equal traces and equal
  answer bags at every budget do not determine the bisimulation class.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.GSLT.HennessyMilner (Formula)

universe uT uS

/-- The occurrence identities of the race pair. -/
inductive Site
  | a | p | q | k | kb | kc | ob | oc
  deriving DecidableEq

/-- The five terms the race pair uses: the atoms `a` and `go`, the intermediate `k`, and the two
answers `b` and `c`. -/
structure Tags (T : Type uT) where
  a : T
  go : T
  k : T
  b : T
  c : T

variable {T : Type uT} {S : Type uS} (t : Tags T)

/-- Labels: `p` and `q` both carry `go`; `k`, `kb` and `kc` all carry `k`. -/
def label : Site → T
  | .a => t.a
  | .p => t.go
  | .q => t.go
  | .k => t.k
  | .kb => t.k
  | .kc => t.k
  | .ob => t.b
  | .oc => t.c

/-- Rule `A`: take `a` and `go`, make `k`. -/
def ruleA : RuleInstance T := ⟨[t.a, t.go], [], [], [], [t.k]⟩

/-- Rule `B`: take `k`, make `b`. -/
def ruleB : RuleInstance T := ⟨[t.k], [], [], [], [t.b]⟩

/-- Rule `C`: take `k`, make `c`. -/
def ruleC : RuleInstance T := ⟨[t.k], [], [], [], [t.c]⟩

/-- `A` at `{a, p}`, making `k`. -/
def aP : Firing T S Site := ⟨ruleA t, [], ⟨[.a, .p], [], [.k]⟩⟩
/-- `A` at `{a, q}`, making `kb`. -/
def aQb : Firing T S Site := ⟨ruleA t, [], ⟨[.a, .q], [], [.kb]⟩⟩
/-- `A` at `{a, q}`, making `kc`. -/
def aQc : Firing T S Site := ⟨ruleA t, [], ⟨[.a, .q], [], [.kc]⟩⟩
/-- `B` at `k`. -/
def bP : Firing T S Site := ⟨ruleB t, [], ⟨[.k], [], [.ob]⟩⟩
/-- `C` at `k`. -/
def cP : Firing T S Site := ⟨ruleC t, [], ⟨[.k], [], [.oc]⟩⟩
/-- `B` at `kb`. -/
def bQ : Firing T S Site := ⟨ruleB t, [], ⟨[.kb], [], [.ob]⟩⟩
/-- `C` at `kc`. -/
def cQ : Firing T S Site := ⟨ruleC t, [], ⟨[.kc], [], [.oc]⟩⟩

/-- The program's alphabet. -/
def alphabet : List (Firing T S Site) := [aP t, aQb t, aQc t, bP t, cP t, bQ t, cQ t]

/-- **Labels are rules**: the program offers each member of its alphabet under its rule. -/
def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := f ∈ alphabet t ∧ f.rule = r

/-- The equations after `A`. -/
def E₁ : EquationStore T := [(t.a, t.a), (t.go, t.go)]
/-- The equations after `A` and then `B` or `C`. -/
def E₂ : EquationStore T := [(t.a, t.a), (t.go, t.go), (t.k, t.k)]

/-- `a.(b + c)`. -/
def P : Configuration T Site := ⟨[], {.a, .p}⟩
/-- `a.b + a.c`. -/
def Q : Configuration T Site := ⟨[], {.a, .q}⟩
/-- After `A` at `P`: the race between `B` and `C` on `k`. -/
def K : Configuration T Site := ⟨E₁ t, {.k}⟩
/-- After the `A` of `Q` that commits to `b`. -/
def Kb : Configuration T Site := ⟨E₁ t, {.kb}⟩
/-- After the `A` of `Q` that commits to `c`. -/
def Kc : Configuration T Site := ⟨E₁ t, {.kc}⟩
/-- The final configuration with answer `b`. -/
def Fb : Configuration T Site := ⟨E₂ t, {.ob}⟩
/-- The final configuration with answer `c`. -/
def Fc : Configuration T Site := ⟨E₂ t, {.oc}⟩

/-! ## Admission is decided on occurrences -/

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem ground : ∀ f ∈ alphabet (S := S) t, Ground (label t) f := by
  intro f member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem reflexive_E₁ : Reflexive (E₁ t) := by
  intro e member
  simp only [E₁, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem reflexive_E₂ : Reflexive (E₂ t) := by
  intro e member
  simp only [E₂, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

variable (A : SubstitutionAction T S)

theorem valid_iff {f : Firing T S Site} (member : f ∈ alphabet t) {C : Configuration T Site}
    (refl : Reflexive C.equations) :
    f.Valid A (label t) C ↔ Enabled (label t) C.present (f.selection.commit (T := T)) :=
  (ground t f member).valid_iff A refl

theorem result_aP : (aP (S := S) t).result (label t) P = K t := config_eq rfl (of_decide_eq_true rfl)
theorem result_aQb : (aQb (S := S) t).result (label t) Q = Kb t := config_eq rfl (of_decide_eq_true rfl)
theorem result_aQc : (aQc (S := S) t).result (label t) Q = Kc t := config_eq rfl (of_decide_eq_true rfl)
theorem result_bP : (bP (S := S) t).result (label t) (K t) = Fb t := config_eq rfl (of_decide_eq_true rfl)
theorem result_cP : (cP (S := S) t).result (label t) (K t) = Fc t := config_eq rfl (of_decide_eq_true rfl)
theorem result_bQ : (bQ (S := S) t).result (label t) (Kb t) = Fb t := config_eq rfl (of_decide_eq_true rfl)
theorem result_cQ : (cQ (S := S) t).result (label t) (Kc t) = Fc t := config_eq rfl (of_decide_eq_true rfl)

theorem mem_aP : aP (S := S) t ∈ alphabet t := by simp [alphabet]
theorem mem_aQb : aQb (S := S) t ∈ alphabet t := by simp [alphabet]
theorem mem_aQc : aQc (S := S) t ∈ alphabet t := by simp [alphabet]
theorem mem_bP : bP (S := S) t ∈ alphabet t := by simp [alphabet]
theorem mem_cP : cP (S := S) t ∈ alphabet t := by simp [alphabet]
theorem mem_bQ : bQ (S := S) t ∈ alphabet t := by simp [alphabet]
theorem mem_cQ : cQ (S := S) t ∈ alphabet t := by simp [alphabet]

/-! ## The races -/

/-- **`Q` races at once**: both firings of `A` are admitted at `Q` and take the same occurrence `a`;
after either, the other is refused. -/
theorem race_at_Q :
    (aQb t).Valid A (label t) Q ∧ (aQc t).Valid A (label t) Q ∧
      Site.a ∈ (aQb (S := S) t).selection.taken ∧ Site.a ∈ (aQc (S := S) t).selection.taken ∧
      ¬ (aQc t).Valid A (label t) ((aQb (S := S) t).result (label t) Q) ∧
      ¬ (aQb t).Valid A (label t) ((aQc (S := S) t).result (label t) Q) := by
  refine ⟨(valid_iff t A (mem_aQb t) reflexive_nil).mpr (of_decide_eq_true rfl),
    (valid_iff t A (mem_aQc t) reflexive_nil).mpr (of_decide_eq_true rfl), of_decide_eq_true rfl, of_decide_eq_true rfl, ?_, ?_⟩
  · rw [result_aQb, valid_iff t A (mem_aQc t) (reflexive_E₁ t)]
    exact of_decide_eq_false rfl
  · rw [result_aQc, valid_iff t A (mem_aQb t) (reflexive_E₁ t)]
    exact of_decide_eq_false rfl

/-- **`P` races after `A`**: `B` and `C` are both admitted at `K` and both take `k`; after either,
the other is refused. -/
theorem race_at_K :
    (bP t).Valid A (label t) (K t) ∧ (cP t).Valid A (label t) (K t) ∧
      Site.k ∈ (bP (S := S) t).selection.taken ∧ Site.k ∈ (cP (S := S) t).selection.taken ∧
      ¬ (cP t).Valid A (label t) ((bP (S := S) t).result (label t) (K t)) ∧
      ¬ (bP t).Valid A (label t) ((cP (S := S) t).result (label t) (K t)) := by
  refine ⟨(valid_iff t A (mem_bP t) (reflexive_E₁ t)).mpr (of_decide_eq_true rfl),
    (valid_iff t A (mem_cP t) (reflexive_E₁ t)).mpr (of_decide_eq_true rfl), of_decide_eq_true rfl, of_decide_eq_true rfl, ?_, ?_⟩
  · rw [result_bP, valid_iff t A (mem_cP t) (reflexive_E₂ t)]
    exact of_decide_eq_false rfl
  · rw [result_cP, valid_iff t A (mem_bP t) (reflexive_E₂ t)]
    exact of_decide_eq_false rfl

/-! ## The labelled transitions -/

theorem moves_P {r : RuleInstance T} {D : Configuration T Site} :
    Moves A (label t) (offers t) P r D ↔ r = ruleA t ∧ D = K t := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff t A member reflexive_nil] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, result_aP t⟩
    all_goals exact absurd valid (of_decide_eq_false rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨aP t, ⟨mem_aP t, rfl⟩, (valid_iff t A (mem_aP t) reflexive_nil).mpr (of_decide_eq_true rfl),
      (result_aP t).symm⟩

theorem moves_K {r : RuleInstance T} {D : Configuration T Site} :
    Moves A (label t) (offers t) (K t) r D ↔ (r = ruleB t ∧ D = Fb t) ∨ (r = ruleC t ∧ D = Fc t) := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff t A member (reflexive_E₁ t)] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact .inl ⟨rfl, result_bP t⟩
    · exact .inr ⟨rfl, result_cP t⟩
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨bP t, ⟨mem_bP t, rfl⟩, (race_at_K t A).1, (result_bP t).symm⟩
    · exact ⟨cP t, ⟨mem_cP t, rfl⟩, (race_at_K t A).2.1, (result_cP t).symm⟩

theorem moves_Q {r : RuleInstance T} {D : Configuration T Site} :
    Moves A (label t) (offers t) Q r D ↔ (r = ruleA t ∧ D = Kb t) ∨ (r = ruleA t ∧ D = Kc t) := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff t A member reflexive_nil] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd valid (of_decide_eq_false rfl)
    · exact .inl ⟨rfl, result_aQb t⟩
    · exact .inr ⟨rfl, result_aQc t⟩
    all_goals exact absurd valid (of_decide_eq_false rfl)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨aQb t, ⟨mem_aQb t, rfl⟩, (race_at_Q t A).1, (result_aQb t).symm⟩
    · exact ⟨aQc t, ⟨mem_aQc t, rfl⟩, (race_at_Q t A).2.1, (result_aQc t).symm⟩

theorem moves_Kb {r : RuleInstance T} {D : Configuration T Site} :
    Moves A (label t) (offers t) (Kb t) r D ↔ r = ruleB t ∧ D = Fb t := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff t A member (reflexive_E₁ t)] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact ⟨rfl, result_bQ t⟩
    · exact absurd valid (of_decide_eq_false rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨bQ t, ⟨mem_bQ t, rfl⟩, (valid_iff t A (mem_bQ t) (reflexive_E₁ t)).mpr (of_decide_eq_true rfl),
      (result_bQ t).symm⟩

theorem moves_Kc {r : RuleInstance T} {D : Configuration T Site} :
    Moves A (label t) (offers t) (Kc t) r D ↔ r = ruleC t ∧ D = Fc t := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff t A member (reflexive_E₁ t)] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact ⟨rfl, result_cQ t⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨cQ t, ⟨mem_cQ t, rfl⟩, (valid_iff t A (mem_cQ t) (reflexive_E₁ t)).mpr (of_decide_eq_true rfl),
      (result_cQ t).symm⟩

theorem dead_Fb {r : RuleInstance T} {D : Configuration T Site} :
    ¬ Moves A (label t) (offers t) (Fb t) r D := by
  rintro ⟨f, ⟨member, _⟩, valid, _⟩
  rw [valid_iff t A member (reflexive_E₂ t)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd valid (of_decide_eq_false rfl)

theorem dead_Fc {r : RuleInstance T} {D : Configuration T Site} :
    ¬ Moves A (label t) (offers t) (Fc t) r D := by
  rintro ⟨f, ⟨member, _⟩, valid, _⟩
  rw [valid_iff t A member (reflexive_E₂ t)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd valid (of_decide_eq_false rfl)

/-! ## Traces -/

theorem hasTrace_of_dead {C : Configuration T Site}
    (dead : ∀ r D, ¬ Moves A (label t) (offers t) C r D) {w : List (RuleInstance T)} :
    HasTrace A (label t) (offers t) w C ↔ w = [] := by
  cases w with
  | nil => exact ⟨fun _ => rfl, fun _ => hasTrace_nil _⟩
  | cons r w =>
      rw [hasTrace_cons]
      constructor
      · rintro ⟨D, moved, _⟩
        exact absurd moved (dead r D)
      · intro h
        cases h

theorem hasTrace_K {w : List (RuleInstance T)} :
    HasTrace A (label t) (offers t) w (K t) ↔ w = [] ∨ w = [ruleB t] ∨ w = [ruleC t] := by
  cases w with
  | nil => exact ⟨fun _ => .inl rfl, fun _ => hasTrace_nil _⟩
  | cons r w =>
      rw [hasTrace_cons]
      constructor
      · rintro ⟨D, moved, traced⟩
        rcases (moves_K t A).mp moved with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hasTrace_of_dead t A (fun _ _ => dead_Fb t A)] at traced
          subst traced
          exact .inr (.inl rfl)
        · rw [hasTrace_of_dead t A (fun _ _ => dead_Fc t A)] at traced
          subst traced
          exact .inr (.inr rfl)
      · rintro (h | h | h)
        · cases h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Fb t, (moves_K t A).mpr (.inl ⟨rfl, rfl⟩), hasTrace_nil _⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Fc t, (moves_K t A).mpr (.inr ⟨rfl, rfl⟩), hasTrace_nil _⟩

theorem hasTrace_Kb {w : List (RuleInstance T)} :
    HasTrace A (label t) (offers t) w (Kb t) ↔ w = [] ∨ w = [ruleB t] := by
  cases w with
  | nil => exact ⟨fun _ => .inl rfl, fun _ => hasTrace_nil _⟩
  | cons r w =>
      rw [hasTrace_cons]
      constructor
      · rintro ⟨D, moved, traced⟩
        obtain ⟨rfl, rfl⟩ := (moves_Kb t A).mp moved
        rw [hasTrace_of_dead t A (fun _ _ => dead_Fb t A)] at traced
        subst traced
        exact .inr rfl
      · rintro (h | h)
        · cases h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Fb t, (moves_Kb t A).mpr ⟨rfl, rfl⟩, hasTrace_nil _⟩

theorem hasTrace_Kc {w : List (RuleInstance T)} :
    HasTrace A (label t) (offers t) w (Kc t) ↔ w = [] ∨ w = [ruleC t] := by
  cases w with
  | nil => exact ⟨fun _ => .inl rfl, fun _ => hasTrace_nil _⟩
  | cons r w =>
      rw [hasTrace_cons]
      constructor
      · rintro ⟨D, moved, traced⟩
        obtain ⟨rfl, rfl⟩ := (moves_Kc t A).mp moved
        rw [hasTrace_of_dead t A (fun _ _ => dead_Fc t A)] at traced
        subst traced
        exact .inr rfl
      · rintro (h | h)
        · cases h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Fc t, (moves_Kc t A).mpr ⟨rfl, rfl⟩, hasTrace_nil _⟩

/-- **The traces of `P`**: `ε, A, AB, AC`. -/
theorem hasTrace_P {w : List (RuleInstance T)} :
    HasTrace A (label t) (offers t) w P ↔
      w = [] ∨ w = [ruleA t] ∨ w = [ruleA t, ruleB t] ∨ w = [ruleA t, ruleC t] := by
  cases w with
  | nil => exact ⟨fun _ => .inl rfl, fun _ => hasTrace_nil _⟩
  | cons r w =>
      rw [hasTrace_cons]
      constructor
      · rintro ⟨D, moved, traced⟩
        obtain ⟨rfl, rfl⟩ := (moves_P t A).mp moved
        rcases (hasTrace_K t A).mp traced with rfl | rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inr (.inr rfl))
      · rintro (h | h | h | h)
        · cases h
        all_goals
          obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨K t, (moves_P t A).mpr ⟨rfl, rfl⟩, (hasTrace_K t A).mpr (by simp)⟩

/-- **The traces of `Q`**: `ε, A, AB, AC`. -/
theorem hasTrace_Q {w : List (RuleInstance T)} :
    HasTrace A (label t) (offers t) w Q ↔
      w = [] ∨ w = [ruleA t] ∨ w = [ruleA t, ruleB t] ∨ w = [ruleA t, ruleC t] := by
  cases w with
  | nil => exact ⟨fun _ => .inl rfl, fun _ => hasTrace_nil _⟩
  | cons r w =>
      rw [hasTrace_cons]
      constructor
      · rintro ⟨D, moved, traced⟩
        rcases (moves_Q t A).mp moved with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases (hasTrace_Kb t A).mp traced with rfl | rfl
          · exact .inr (.inl rfl)
          · exact .inr (.inr (.inl rfl))
        · rcases (hasTrace_Kc t A).mp traced with rfl | rfl
          · exact .inr (.inl rfl)
          · exact .inr (.inr (.inr rfl))
      · rintro (h | h | h | h)
        · cases h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Kb t, (moves_Q t A).mpr (.inl ⟨rfl, rfl⟩), hasTrace_nil _⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Kb t, (moves_Q t A).mpr (.inl ⟨rfl, rfl⟩), (hasTrace_Kb t A).mpr (.inr rfl)⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨Kc t, (moves_Q t A).mpr (.inr ⟨rfl, rfl⟩), (hasTrace_Kc t A).mpr (.inr rfl)⟩

/-- **`P` and `Q` have the same traces.** -/
theorem traceEquivalent_P_Q : TraceEquivalent A (label t) (offers t) P Q :=
  fun _ => (hasTrace_P t A).trans (hasTrace_Q t A).symm

/-! ## The separating formula -/

/-- `⟨A⟩(⟨B⟩⊤ ∧ ⟨C⟩⊤)`: after `A`, both `B` and `C` remain possible. -/
def separating : Formula PEmpty.{1} (RuleInstance T) :=
  .dia (ruleA t) (.conj (.dia (ruleB t) .top) (.dia (ruleC t) .top))

theorem separating_holds_P : Sat A (label t) (offers t) (separating t) P :=
  sat_dia.mpr ⟨K t, (moves_P t A).mpr ⟨rfl, rfl⟩, sat_conj.mpr
    ⟨sat_dia.mpr ⟨Fb t, (moves_K t A).mpr (.inl ⟨rfl, rfl⟩), sat_top _⟩,
      sat_dia.mpr ⟨Fc t, (moves_K t A).mpr (.inr ⟨rfl, rfl⟩), sat_top _⟩⟩⟩

theorem ruleB_ne_ruleC (apart : t.b ≠ t.c) : ruleB t ≠ ruleC t := fun same =>
  apart (by simpa [ruleB, ruleC] using congrArg RuleInstance.produce same)

theorem separating_fails_Q (apart : t.b ≠ t.c) : ¬ Sat A (label t) (offers t) (separating t) Q := by
  intro holds
  obtain ⟨D, moved, both⟩ := sat_dia.mp holds
  obtain ⟨afterB, afterC⟩ := sat_conj.mp both
  rcases (moves_Q t A).mp moved with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨E, step, _⟩ := sat_dia.mp afterC
    exact ruleB_ne_ruleC t apart ((moves_Kb t A).mp step).1.symm
  · obtain ⟨E, step, _⟩ := sat_dia.mp afterB
    exact ruleB_ne_ruleC t apart ((moves_Kc t A).mp step).1

/-- **`P` and `Q` are not bisimilar.** -/
theorem not_bisimilar_P_Q (apart : t.b ≠ t.c) : ¬ Bisimilar A (label t) (offers t) P Q :=
  not_bisimilar_of_sat (separating_holds_P t A) (separating_fails_Q t A apart)

/-- The program offers finitely many firings under each rule, so the Hennessy–Milner
characterization applies to it. -/
theorem offers_finite (r : RuleInstance T) : {f | offers (S := S) t r f}.Finite :=
  (alphabet t).finite_toSet.subset fun _ offered => offered.1

/-! ## The answer bags of the step's search -/

theorem alphabet_nodup : (alphabet (S := S) t).Nodup := by
  simp [alphabet, aP, aQb, aQc, bP, cP, bQ, cQ]

/-- The search of the program: its alternatives enumerate the admitted firings. -/
noncomputable abbrev search := (alternatives A (label t) (alphabet t)).space

theorem next_P : ((alternatives A (label t) (alphabet t)).next P).map (fun g => g.1.1) = [aP t] := by
  rw [next_map_of_ground (ground t) reflexive_nil]
  rfl

theorem next_K :
    ((alternatives A (label t) (alphabet t)).next (K t)).map (fun g => g.1.1) = [bP t, cP t] := by
  rw [next_map_of_ground (ground t) (reflexive_E₁ t)]
  rfl

theorem next_Q :
    ((alternatives A (label t) (alphabet t)).next Q).map (fun g => g.1.1) = [aQb t, aQc t] := by
  rw [next_map_of_ground (ground t) reflexive_nil]
  rfl

theorem next_Kb :
    ((alternatives A (label t) (alphabet t)).next (Kb t)).map (fun g => g.1.1) = [bQ t] := by
  rw [next_map_of_ground (ground t) (reflexive_E₁ t)]
  rfl

theorem next_Kc :
    ((alternatives A (label t) (alphabet t)).next (Kc t)).map (fun g => g.1.1) = [cQ t] := by
  rw [next_map_of_ground (ground t) (reflexive_E₁ t)]
  rfl

theorem next_Fb : ((alternatives A (label t) (alphabet t)).next (Fb t)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground t) (reflexive_E₂ t)]
  rfl

theorem next_Fc : ((alternatives A (label t) (alphabet t)).next (Fc t)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground t) (reflexive_E₂ t)]
  rfl

theorem approx_P (n : ℕ) : (search t A).approx (n + 1) (.inr P) = (search t A).approx n (.inr (K t)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_P t A)]
  simp [result_aP]

theorem approx_K (n : ℕ) : (search t A).approx (n + 1) (.inr (K t)) =
    (search t A).approx n (.inr (Fb t)) + (search t A).approx n (.inr (Fc t)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_K t A)]
  simp [result_bP, result_cP]

theorem approx_Q (n : ℕ) : (search t A).approx (n + 1) (.inr Q) =
    (search t A).approx n (.inr (Kb t)) + (search t A).approx n (.inr (Kc t)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_Q t A)]
  simp [result_aQb, result_aQc]

theorem approx_Kb (n : ℕ) :
    (search t A).approx (n + 1) (.inr (Kb t)) = (search t A).approx n (.inr (Fb t)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_Kb t A)]
  simp [result_bQ]

theorem approx_Kc (n : ℕ) :
    (search t A).approx (n + 1) (.inr (Kc t)) = (search t A).approx n (.inr (Fc t)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_Kc t A)]
  simp [result_cQ]

theorem approx_Fb (n : ℕ) : (search t A).approx (n + 1) (.inr (Fb t)) = Search.Outcome.pure (Fb t) := by
  rw [Search.Space.approx_succ, unfold_of_nil (next_Fb t A)]
  simp [Search.Space.approx_inl]

theorem approx_Fc (n : ℕ) : (search t A).approx (n + 1) (.inr (Fc t)) = Search.Outcome.pure (Fc t) := by
  rw [Search.Space.approx_succ, unfold_of_nil (next_Fc t A)]
  simp [Search.Space.approx_inl]

/-- **The bounded searches of `P` and `Q` agree at every budget.** -/
theorem approx_P_eq_approx_Q : ∀ n, (search t A).approx n (.inr P) = (search t A).approx n (.inr Q)
  | 0 => by rw [Search.Space.approx_zero, Search.Space.approx_zero]
  | 1 => by
      rw [approx_P, approx_Q, Search.Space.approx_zero, Search.Space.approx_zero,
        Search.Space.approx_zero]
      ext1 <;> simp
  | n + 2 => by
      rw [approx_P, approx_K, approx_Q, approx_Kb, approx_Kc]

/-- **The same answer bags at every budget.** -/
theorem collect_P_eq_collect_Q (n : ℕ) :
    Search.Outcome.collect ((search t A).approx n (.inr P)) =
      Search.Outcome.collect ((search t A).approx n (.inr Q)) := by
  rw [approx_P_eq_approx_Q]

theorem answers_distinct : Fb t ≠ Fc t := fun same => by
  exact absurd (congrArg Configuration.present same) (of_decide_eq_false rfl)

/-- At budget 3 the search of `P` is finished and collects both final configurations, once each. -/
theorem collect_P :
    Search.Outcome.collect ((search t A).approx 3 (.inr P)) =
      Search.Outcome.pure ({Fb t, Fc t} : Multiset (Configuration T Site)) := by
  rw [approx_P, approx_K, approx_Fb, approx_Fc]
  rfl

/-! ## Rung one is blind -/

/-- **The step analogue of Proposition 8**: `P` and `Q` have the same traces and the same answer
bags at every budget, and they are not bisimilar. -/
theorem rung_one_blind (apart : t.b ≠ t.c) :
    TraceEquivalent A (label t) (offers t) P Q ∧
      (∀ n, Search.Outcome.collect ((search t A).approx n (.inr P)) =
        Search.Outcome.collect ((search t A).approx n (.inr Q))) ∧
      ¬ Bisimilar A (label t) (offers t) P Q :=
  ⟨traceEquivalent_P_Q t A, collect_P_eq_collect_Q t A, not_bisimilar_P_Q t A apart⟩

/-- **Traces and answer bags do not decide bisimilarity**, for any term syntax with two distinct
terms and any substitution action. -/
theorem traces_and_bags_do_not_decide (apart : t.b ≠ t.c) :
    ¬ ∀ C D : Configuration T Site, TraceEquivalent A (label t) (offers t) C D →
      (∀ n, Search.Outcome.collect ((search t A).approx n (.inr C)) =
        Search.Outcome.collect ((search t A).approx n (.inr D))) →
      Bisimilar A (label t) (offers t) C D :=
  fun decides => not_bisimilar_P_Q t A apart
    (decides P Q (traceEquivalent_P_Q t A) (collect_P_eq_collect_Q t A))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms race_at_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms race_at_K
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms traceEquivalent_P_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms separating_holds_P
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms separating_fails_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms not_bisimilar_P_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms offers_finite
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms approx_P_eq_approx_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms collect_P_eq_collect_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms collect_P
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms rung_one_blind
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Pair in
#print axioms traces_and_bags_do_not_decide
