import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceWeakDeterminate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps

/-!
# Controls for weak identity

One program, every occurrence carrying one term `τ`, so all firings are ground and admission is
decided on occurrences (`RaceSpectrum.Ground.valid_iff`), for every term syntax and substitution
action. Labels are the names `A`, `B`, `C` and the internal name `t`. The three controls use
disjoint occurrences.

## The private-token race pair (`Private.private_pair`)

Meredith's pair `a.(b + c)` against `a.b + a.c`, with the commit hidden.

* `P = {a₁}`: `A` takes `a₁` and makes `k₁`; then `B` and `C` race for `k₁` in the open.
* `Q = {a₂, tok}`: `A` takes `a₂` and makes `m`; then two internal firings race for `m` and the
  private token `tok`, one making `kb` and one making `kc`; then only `B` takes `kb`, only `C` takes
  `kc`. No visible firing takes `tok`.

They have the same weak traces (`weakTraceEquivalent_P_Q`, by weak simulations both ways), and they
are not weakly bisimilar (`not_weakBisimilar_P_Q`): the weak formula `⟨⟨A⟩⟩¬⟨⟨C⟩⟩⊤` holds at `Q`,
which can commit to `b` silently, and fails at `P`. The hidden commit is not inert
(`commit_not_inert`), the program is not weakly determinate (`not_weaklyDeterminate`), and it is
outside the fragment of `RaceWeakDeterminate` (`not_fragment`): its internal firings race.

## Strong is strictly finer than weak (`Prefix.strictly_finer`)

`X = {x}`: an internal firing takes `x` and makes `y`, then `A` takes `y`. `Z = {z}`: `A` takes `z`.
`τ.a` against `a`: weakly bisimilar, and not bisimilar, separated by `⟨t⟩⊤`.

## Divergence (`Loop.divergence_control`)

A configuration holding `l` runs an internal firing that reads `l` and makes nothing, forever. It is
weakly bisimilar to the configuration `{n}`, which has no firing at all: weak bisimilarity does not
see the infinite internal loop. It diverges and `{n}` does not, so the two are not bisimilar for the
weak system that also observes divergence.

## An inert internal firing in the fragment (`Inert.inert_control`)

A second program: an internal firing takes `x`, and `B` takes `z`. It is in the race-free,
independent fragment of `RaceWeakDeterminate`, so its internal firing is inert: `{x, z}` and `{z}`
are weakly bisimilar, and they are not bisimilar, separated by `⟨t⟩⊤`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls

open AnnotatedRuns (Firing StaticIndependent)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.GSLT.HennessyMilner (Formula)

universe uT uS

/-- Occurrence identities. -/
inductive Site
  | a₁ | k₁ | b₁ | c₁ | a₂ | tok | m | kb | kc | b₂ | c₂ | x | y | z | l | n
  deriving DecidableEq

/-- Label names: `t` is internal. -/
inductive Act
  | A | B | C | t
  deriving DecidableEq

/-- The internal labels. -/
abbrev internal (ℓ : Act) : Prop := ℓ = .t

variable {T : Type uT} {S : Type uS} (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

/-- The ground firing that reads `read` and makes nothing. -/
def reader (read : List Site) : Firing T S Site :=
  ⟨⟨[], read.map (label τ), [], [], []⟩, [], ⟨[], read, []⟩⟩

def pA : Firing T S Site := firing τ [.a₁] [.k₁]
def pB : Firing T S Site := firing τ [.k₁] [.b₁]
def pC : Firing T S Site := firing τ [.k₁] [.c₁]
def qA : Firing T S Site := firing τ [.a₂] [.m]
def qb : Firing T S Site := firing τ [.m, .tok] [.kb]
def qc : Firing T S Site := firing τ [.m, .tok] [.kc]
def qB : Firing T S Site := firing τ [.kb] [.b₂]
def qC : Firing T S Site := firing τ [.kc] [.c₂]
def tx : Firing T S Site := firing τ [.x] [.y]
def ay : Firing T S Site := firing τ [.y] []
def az : Firing T S Site := firing τ [.z] []
def spin : Firing T S Site := reader τ [.l]

/-- The program's alphabet. -/
def alphabet : List (Act × Firing T S Site) :=
  [(.A, pA τ), (.B, pB τ), (.C, pC τ), (.A, qA τ), (.t, qb τ), (.t, qc τ), (.B, qB τ), (.C, qC τ),
    (.t, tx τ), (.A, ay τ), (.A, az τ), (.t, spin τ)]

/-- The program offers each member of its alphabet under its name. -/
def offers (ℓ : Act) (f : Firing T S Site) : Prop := (ℓ, f) ∈ alphabet (S := S) τ

/-- `n` copies of `(τ, τ)`. -/
def E (n : ℕ) : EquationStore T := List.replicate n (τ, τ)

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem reflexive_E (n : ℕ) : Reflexive (E τ n) := by
  intro e member
  rw [List.eq_of_mem_replicate member]

theorem ground : ∀ x ∈ alphabet (S := S) τ, Ground (label τ) x.2 := by
  intro x member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

variable (A : SubstitutionAction T S)

/-- The step of the control program. -/
abbrev sys := system A (label τ) (offers (S := S) τ)

theorem moves_iff {C : Configuration T Site} (refl : Reflexive C.equations) {ℓ : Act}
    {D : Configuration T Site} :
    Moves A (label τ) (offers τ) C ℓ D ↔ ∃ f, (ℓ, f) ∈ alphabet (S := S) τ ∧
      Enabled (label τ) C.present (f.selection.commit (T := T)) ∧ D = f.result (label τ) C := by
  constructor
  · rintro ⟨f, member, valid, rfl⟩
    exact ⟨f, member, ((ground τ (ℓ, f) member).valid_iff A refl).mp valid, rfl⟩
  · rintro ⟨f, member, enabled, rfl⟩
    exact ⟨f, member, ((ground τ (ℓ, f) member).valid_iff A refl).mpr enabled, rfl⟩

/-- **The moves at a configuration are read off the enabled members of the alphabet.** -/
theorem moves_of_filter {C : Configuration T Site} (refl : Reflexive C.equations) {p : Finset Site}
    (present : C.present = p) {l : List (Act × Firing T S Site)}
    (filtered : (alphabet (S := S) τ).filter
      (fun x => decide (Enabled (label τ) p (x.2.selection.commit (T := T)))) = l)
    {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) C ℓ D) :
    ∃ f, (ℓ, f) ∈ l ∧ D = f.result (label τ) C := by
  obtain ⟨f, member, enabled, rfl⟩ := (moves_iff τ A refl).mp moved
  rw [present] at enabled
  exact ⟨f, filtered ▸ List.mem_filter.mpr ⟨member, decide_eq_true enabled⟩, rfl⟩

theorem move_of {C : Configuration T Site} (refl : Reflexive C.equations) {ℓ : Act}
    {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet τ)
    (enabled : Enabled (label τ) C.present (f.selection.commit (T := T))) {D : Configuration T Site}
    (result : f.result (label τ) C = D) : Moves A (label τ) (offers τ) C ℓ D :=
  (moves_iff τ A refl).mpr ⟨f, member, enabled, result.symm⟩

theorem step {C D : Configuration T Site} {ℓ : Act} (moved : Moves A (label τ) (offers τ) C ℓ D) :
    Weak.Act (sys τ A) internal ℓ C D :=
  Weak.act_of_act moved

theorem stay (C : Configuration T Site) : Weak.Act (sys τ A) internal .t C C :=
  Weak.act_of_silently (M := sys τ A) (internal := internal) (show internal Act.t from rfl)
    (Weak.silently_refl (M := sys τ A) (internal := internal) C)

/-! ## The private-token race pair -/

namespace Private

def P : Configuration T Site := ⟨[], {.a₁}⟩
def K : Configuration T Site := ⟨E τ 1, {.k₁}⟩
def Fb : Configuration T Site := ⟨E τ 2, {.b₁}⟩
def Fc : Configuration T Site := ⟨E τ 2, {.c₁}⟩
def Q : Configuration T Site := ⟨[], {.a₂, .tok}⟩
def Mid : Configuration T Site := ⟨E τ 1, {.m, .tok}⟩
def Kb : Configuration T Site := ⟨E τ 3, {.kb}⟩
def Kc : Configuration T Site := ⟨E τ 3, {.kc}⟩
def Gb : Configuration T Site := ⟨E τ 4, {.b₂}⟩
def Gc : Configuration T Site := ⟨E τ 4, {.c₂}⟩

theorem moves_P {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) P ℓ D) :
    ℓ = .A ∧ D = K τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A reflexive_nil rfl (l := [(.A, pA τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_K {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) (K τ) ℓ D) :
    (ℓ = .B ∧ D = Fb τ) ∨ (ℓ = .C ∧ D = Fc τ) := by
  obtain ⟨f, member, rfl⟩ :=
    moves_of_filter τ A (reflexive_E τ 1) rfl (l := [(.B, pB τ), (.C, pC τ)]) rfl moved
  rcases List.mem_pair.mp member with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  · exact .inl ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩
  · exact .inr ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem dead_Fb {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) (Fb τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 2) rfl (l := []) rfl moved
    exact List.not_mem_nil member

theorem dead_Fc {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) (Fc τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 2) rfl (l := []) rfl moved
    exact List.not_mem_nil member

theorem moves_Q {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) Q ℓ D) :
    ℓ = .A ∧ D = Mid τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A reflexive_nil rfl (l := [(.A, qA τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_Mid {ℓ : Act} {D : Configuration T Site}
    (moved : Moves A (label τ) (offers τ) (Mid τ) ℓ D) :
    (ℓ = .t ∧ D = Kb τ) ∨ (ℓ = .t ∧ D = Kc τ) := by
  obtain ⟨f, member, rfl⟩ :=
    moves_of_filter τ A (reflexive_E τ 1) rfl (l := [(.t, qb τ), (.t, qc τ)]) rfl moved
  rcases List.mem_pair.mp member with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  · exact .inl ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩
  · exact .inr ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_Kb {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) (Kb τ) ℓ D) :
    ℓ = .B ∧ D = Gb τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A (reflexive_E τ 3) rfl (l := [(.B, qB τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_Kc {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) (Kc τ) ℓ D) :
    ℓ = .C ∧ D = Gc τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A (reflexive_E τ 3) rfl (l := [(.C, qC τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem dead_Gb {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) (Gb τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 4) rfl (l := []) rfl moved
    exact List.not_mem_nil member

theorem dead_Gc {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) (Gc τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 4) rfl (l := []) rfl moved
    exact List.not_mem_nil member

theorem move_P : Moves A (label τ) (offers τ) P .A (K τ) :=
  move_of τ A reflexive_nil (f := pA τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_K_B : Moves A (label τ) (offers τ) (K τ) .B (Fb τ) :=
  move_of τ A (reflexive_E τ 1) (f := pB τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_K_C : Moves A (label τ) (offers τ) (K τ) .C (Fc τ) :=
  move_of τ A (reflexive_E τ 1) (f := pC τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Q : Moves A (label τ) (offers τ) Q .A (Mid τ) :=
  move_of τ A reflexive_nil (f := qA τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Mid_b : Moves A (label τ) (offers τ) (Mid τ) .t (Kb τ) :=
  move_of τ A (reflexive_E τ 1) (f := qb τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Mid_c : Moves A (label τ) (offers τ) (Mid τ) .t (Kc τ) :=
  move_of τ A (reflexive_E τ 1) (f := qc τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Kb : Moves A (label τ) (offers τ) (Kb τ) .B (Gb τ) :=
  move_of τ A (reflexive_E τ 3) (f := qB τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Kc : Moves A (label τ) (offers τ) (Kc τ) .C (Gc τ) :=
  move_of τ A (reflexive_E τ 3) (f := qC τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))

/-! ### Weak simulations both ways -/

/-- `P`'s side, simulated by `Q`'s. -/
def forth (X Y : Configuration T Site) : Prop :=
  (X = P ∧ Y = Q) ∨ (X = K τ ∧ Y = Mid τ) ∨ (X = Fb τ ∧ Y = Gb τ) ∨ (X = Fc τ ∧ Y = Gc τ)

/-- `Q`'s side, simulated by `P`'s. -/
def back (X Y : Configuration T Site) : Prop :=
  (X = Q ∧ Y = P) ∨ (X = Mid τ ∧ Y = K τ) ∨ (X = Kb τ ∧ Y = K τ) ∨ (X = Kc τ ∧ Y = K τ) ∨
    (X = Gb τ ∧ Y = Fb τ) ∨ (X = Gc τ ∧ Y = Fc τ)

theorem silent_Mid_b : Weak.Silent (sys τ A) internal (Mid τ) (Kb τ) := ⟨.t, rfl, move_Mid_b τ A⟩
theorem silent_Mid_c : Weak.Silent (sys τ A) internal (Mid τ) (Kc τ) := ⟨.t, rfl, move_Mid_c τ A⟩

theorem forth_simulation : Weak.IsWeakSimulation (sys τ A) internal (forth τ) := by
  rintro X Y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ X' moved
  · obtain ⟨rfl, rfl⟩ := moves_P τ A moved
    exact ⟨Mid τ, step τ A (move_Q τ A), .inr (.inl ⟨rfl, rfl⟩)⟩
  · rcases moves_K τ A moved with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Gb τ, Weak.silently_act (Weak.silently_of_silent (silent_Mid_b τ A))
        (step τ A (move_Kb τ A)), .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨Gc τ, Weak.silently_act (Weak.silently_of_silent (silent_Mid_c τ A))
        (step τ A (move_Kc τ A)), .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
  · exact absurd moved (dead_Fb τ A)
  · exact absurd moved (dead_Fc τ A)

theorem back_simulation : Weak.IsWeakSimulation (sys τ A) internal (back τ) := by
  rintro X Y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ X' moved
  · obtain ⟨rfl, rfl⟩ := moves_Q τ A moved
    exact ⟨K τ, step τ A (move_P τ A), .inr (.inl ⟨rfl, rfl⟩)⟩
  · rcases moves_Mid τ A moved with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨K τ, stay τ A _, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨K τ, stay τ A _,
        .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))⟩
  · obtain ⟨rfl, rfl⟩ := moves_Kb τ A moved
    exact ⟨Fb τ, step τ A (move_K_B τ A), .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
  · obtain ⟨rfl, rfl⟩ := moves_Kc τ A moved
    exact ⟨Fc τ, step τ A (move_K_C τ A), .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))⟩
  · exact absurd moved (dead_Gb τ A)
  · exact absurd moved (dead_Gc τ A)

/-- **`P` and `Q` have the same weak traces.** -/
theorem weakTraceEquivalent_P_Q : WeakTraceEquivalent A (label τ) (offers τ) internal P Q :=
  Weak.traceEquivalent_of_simulations (forth_simulation τ A) (back_simulation τ A)
    (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩)

/-! ### The separating weak formula -/

theorem quiet_of {C : Configuration T Site}
    (labels : ∀ ℓ D, Moves A (label τ) (offers τ) C ℓ D → ℓ ≠ .t) (D : Configuration T Site) :
    ¬ Weak.Silent (sys τ A) internal C D := by
  rintro ⟨ℓ, inner, moved⟩
  exact labels ℓ D moved inner

theorem quiet_P : ∀ D, ¬ Weak.Silent (sys τ A) internal P D :=
  quiet_of τ A fun _ _ moved => by rw [(moves_P τ A moved).1]; decide

theorem quiet_K : ∀ D, ¬ Weak.Silent (sys τ A) internal (K τ) D :=
  quiet_of τ A fun _ _ moved => by
    rcases moves_K τ A moved with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem quiet_Kb : ∀ D, ¬ Weak.Silent (sys τ A) internal (Kb τ) D :=
  quiet_of τ A fun _ _ moved => by rw [(moves_Kb τ A moved).1]; decide

theorem quiet_Kc : ∀ D, ¬ Weak.Silent (sys τ A) internal (Kc τ) D :=
  quiet_of τ A fun _ _ moved => by rw [(moves_Kc τ A moved).1]; decide

/-- `⟨⟨C⟩⟩⊤`. -/
def canC : Formula PEmpty.{1} Act := .dia .C .top

/-- `⟨⟨B⟩⟩⊤`. -/
def canB : Formula PEmpty.{1} Act := .dia .B .top

/-- `⟨⟨A⟩⟩¬⟨⟨C⟩⟩⊤`: after `A`, the system can be where `C` is no longer possible. -/
def separating : Formula PEmpty.{1} Act := .dia .A (.neg canC)

theorem not_canC_Kb : ¬ WeakSat A (label τ) (offers τ) internal canC (Kb τ) := by
  rintro ⟨D, moved, -⟩
  obtain ⟨u, v, Kbu, uv, -⟩ := (Weak.act_visible (M := sys τ A) (internal := internal)
    (by decide : ¬ internal Act.C)).mp moved
  have same : Kb τ = u := Weak.equiv_of_silently (quiet_Kb τ A) Kbu
  subst same
  exact absurd (moves_Kb τ A uv).1 (by decide)

theorem not_canB_Kc : ¬ WeakSat A (label τ) (offers τ) internal canB (Kc τ) := by
  rintro ⟨D, moved, -⟩
  obtain ⟨u, v, Kcu, uv, -⟩ := (Weak.act_visible (M := sys τ A) (internal := internal)
    (by decide : ¬ internal Act.B)).mp moved
  have same : Kc τ = u := Weak.equiv_of_silently (quiet_Kc τ A) Kcu
  subst same
  exact absurd (moves_Kc τ A uv).1 (by decide)

theorem canB_Kb : WeakSat A (label τ) (offers τ) internal canB (Kb τ) :=
  ⟨Gb τ, step τ A (move_Kb τ A), trivial⟩

theorem canC_Mid : WeakSat A (label τ) (offers τ) internal canC (Mid τ) :=
  ⟨Gc τ, Weak.silently_act (Weak.silently_of_silent (silent_Mid_c τ A)) (step τ A (move_Kc τ A)),
    trivial⟩

theorem separating_holds_Q : WeakSat A (label τ) (offers τ) internal separating Q :=
  ⟨Kb τ, Weak.act_silently (step τ A (move_Q τ A)) (Weak.silently_of_silent (silent_Mid_b τ A)),
    not_canC_Kb τ A⟩

theorem separating_fails_P : ¬ WeakSat A (label τ) (offers τ) internal separating P := by
  rintro ⟨D, moved, notC⟩
  obtain ⟨u, v, Pu, uv, vD⟩ := (Weak.act_visible (M := sys τ A) (internal := internal)
    (by decide : ¬ internal Act.A)).mp moved
  have same : P = u := Weak.equiv_of_silently (quiet_P τ A) Pu
  subst same
  obtain ⟨-, rfl⟩ := moves_P τ A uv
  have same' : K τ = D := Weak.equiv_of_silently (quiet_K τ A) vD
  subst same'
  exact notC ⟨Fc τ, step τ A (move_K_C τ A), trivial⟩

/-- **`P` and `Q` are not weakly bisimilar.** -/
theorem not_weakBisimilar_P_Q : ¬ WeakBisimilar A (label τ) (offers τ) internal P Q := fun bisimilar =>
  separating_fails_P τ A ((Weak.sat_iff_of_bisimilar bisimilar separating).mpr (separating_holds_Q τ A))

/-- **The private-token race pair**: the same weak traces, not weakly bisimilar. -/
theorem private_pair :
    WeakTraceEquivalent A (label τ) (offers τ) internal P Q ∧
      ¬ WeakBisimilar A (label τ) (offers τ) internal P Q :=
  ⟨weakTraceEquivalent_P_Q τ A, not_weakBisimilar_P_Q τ A⟩

/-- **The hidden commit is not inert**: an internal firing of `Mid` reaches a configuration that is
not weakly bisimilar to `Mid`. -/
theorem commit_not_inert :
    Weak.Silent (sys τ A) internal (Mid τ) (Kb τ) ∧
      ¬ WeakBisimilar A (label τ) (offers τ) internal (Mid τ) (Kb τ) :=
  ⟨silent_Mid_b τ A, Weak.not_bisimilar_of_sat (canC_Mid τ A) (not_canC_Kb τ A)⟩

/-- **The program is not weakly determinate** on any set holding `Mid`. -/
theorem not_weaklyDeterminate {good : Configuration T Site → Prop} (goodMid : good (Mid τ)) :
    ¬ Weak.Determinate (Weak.weak (sys τ A) internal) good := by
  intro determinate
  have bisimilar := determinate (Mid τ) goodMid Act.t (Kb τ) (Kc τ)
    (step τ A (move_Mid_b τ A)) (step τ A (move_Mid_c τ A))
  exact Weak.not_bisimilar_of_sat (canB_Kb τ A) (not_canB_Kc τ A) bisimilar

include A in
/-- **The program leaves the fragment**: its two internal firings race for `m` and `tok`. -/
theorem not_fragment : ¬ Fragment (S := S) (label τ) (offers τ) := by
  intro fragment
  have distinct : qb (S := S) τ ≠ qc τ := by
    intro same
    have := congrArg (fun f : Firing T S Site => f.selection.made) same
    simp [qb, qc, firing] at this
  have independent := fragment.independent _ _ _ _ (by simp [offers, alphabet] : offers (S := S) τ .t (qb τ))
    (by simp [offers, alphabet] : offers (S := S) τ .t (qc τ)) distinct
  exact (independent.2.2 A.identity).1.1 (.inl (of_decide_eq_false rfl))

end Private

/-! ## Strong is strictly finer than weak -/

namespace Prefix

def X : Configuration T Site := ⟨[], {.x}⟩
def X' : Configuration T Site := ⟨E τ 1, {.y}⟩
def F : Configuration T Site := ⟨E τ 2, ∅⟩
def Z : Configuration T Site := ⟨[], {.z}⟩
def F' : Configuration T Site := ⟨E τ 1, ∅⟩

theorem moves_X {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) X ℓ D) :
    ℓ = .t ∧ D = X' τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A reflexive_nil rfl (l := [(.t, tx τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_X' {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) (X' τ) ℓ D) :
    ℓ = .A ∧ D = F τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A (reflexive_E τ 1) rfl (l := [(.A, ay τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_Z {ℓ : Act} {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) Z ℓ D) :
    ℓ = .A ∧ D = F' τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A reflexive_nil rfl (l := [(.A, az τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem dead_F {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) (F τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 2) rfl (l := []) rfl moved
    exact List.not_mem_nil member

theorem dead_F' {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) (F' τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 1) rfl (l := []) rfl moved
    exact List.not_mem_nil member

theorem move_X : Moves A (label τ) (offers τ) X .t (X' τ) :=
  move_of τ A reflexive_nil (f := tx τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_X' : Moves A (label τ) (offers τ) (X' τ) .A (F τ) :=
  move_of τ A (reflexive_E τ 1) (f := ay τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Z : Moves A (label τ) (offers τ) Z .A (F' τ) :=
  move_of τ A reflexive_nil (f := az τ) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))

/-- The weak bisimulation: `τ.a` and its continuation against `a`, and the ends. -/
def relation (U V : Configuration T Site) : Prop :=
  (U = X ∧ V = Z) ∨ (U = X' τ ∧ V = Z) ∨ (U = F τ ∧ V = F' τ)

theorem relation_isWeakBisimulation : Weak.IsWeakBisimulation (sys τ A) internal (relation τ) := by
  refine ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩
  · rintro U V (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ U' moved
    · obtain ⟨rfl, rfl⟩ := moves_X τ A moved
      exact ⟨Z, stay τ A _, .inr (.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := moves_X' τ A moved
      exact ⟨F' τ, step τ A (move_Z τ A), .inr (.inr ⟨rfl, rfl⟩)⟩
    · exact absurd moved (dead_F τ A)
  · rintro V U (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ V' moved
    · obtain ⟨rfl, rfl⟩ := moves_Z τ A moved
      exact ⟨F τ, Weak.silently_act (Weak.silently_of_silent ⟨.t, rfl, move_X τ A⟩)
        (step τ A (move_X' τ A)), .inr (.inr ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := moves_Z τ A moved
      exact ⟨F τ, step τ A (move_X' τ A), .inr (.inr ⟨rfl, rfl⟩)⟩
    · exact absurd moved (dead_F' τ A)

theorem weakBisimilar_X_Z : WeakBisimilar A (label τ) (offers τ) internal X Z :=
  Weak.bisimilar_iff.mpr ⟨relation τ, relation_isWeakBisimulation τ A, .inl ⟨rfl, rfl⟩⟩

theorem not_bisimilar_X_Z : ¬ Bisimilar A (label τ) (offers τ) X Z :=
  not_bisimilar_of_sat (φ := .dia .t .top) ⟨X' τ, move_X τ A, trivial⟩ fun ⟨_, moved, _⟩ =>
    absurd (moves_Z τ A moved).1 (by decide)

/-- **Strong bisimilarity is strictly finer than weak bisimilarity**: it implies it, and `τ.a` against
`a` is weakly bisimilar and not bisimilar. -/
theorem strictly_finer :
    (∀ C D : Configuration T Site, Bisimilar A (label τ) (offers τ) C D →
      WeakBisimilar A (label τ) (offers τ) internal C D) ∧
      WeakBisimilar A (label τ) (offers τ) internal X Z ∧ ¬ Bisimilar A (label τ) (offers τ) X Z :=
  ⟨fun _ _ => weakBisimilar_of_bisimilar, weakBisimilar_X_Z τ A, not_bisimilar_X_Z τ A⟩

end Prefix

/-! ## Divergence -/

namespace Loop

/-- A configuration of the loop: reflexive knowledge, holding `l` only. -/
def Looping (C : Configuration T Site) : Prop := Reflexive C.equations ∧ C.present = {.l}

/-- The configuration without firings. -/
def Z₀ : Configuration T Site := ⟨[], {.n}⟩

def L₀ : Configuration T Site := ⟨[], {.l}⟩

theorem looping_L₀ : Looping (T := T) L₀ := ⟨reflexive_nil, rfl⟩

theorem moves_looping {C : Configuration T Site} (looping : Looping C) {ℓ : Act}
    {D : Configuration T Site} (moved : Moves A (label τ) (offers τ) C ℓ D) :
    ℓ = .t ∧ D = (spin (S := S) τ).result (label τ) C := by
  obtain ⟨f, member, rfl⟩ :=
    moves_of_filter τ A looping.1 looping.2 (l := [(.t, spin τ)]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, rfl⟩

theorem looping_spin {C : Configuration T Site} (looping : Looping C) :
    Looping ((spin (S := S) τ).result (label τ) C) := by
  refine ⟨(ground τ (.t, spin τ) (by simp [alphabet])).reflexive_result looping.1, ?_⟩
  show MeTTaCalculus.OccurrenceCommits.fire C.present _ = _
  rw [looping.2]
  exact of_decide_eq_true rfl

theorem move_looping {C : Configuration T Site} (looping : Looping C) :
    Moves A (label τ) (offers τ) C .t ((spin (S := S) τ).result (label τ) C) :=
  move_of τ A looping.1 (f := spin τ) (by simp [alphabet]) (by rw [looping.2]; exact of_decide_eq_true rfl) rfl

theorem dead_Z₀ {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) Z₀ ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A reflexive_nil rfl (l := []) rfl moved
    exact List.not_mem_nil member

/-- **The loop is weakly bisimilar to the configuration without firings.** -/
theorem weakBisimilar_looping {C : Configuration T Site} (looping : Looping C) :
    WeakBisimilar A (label τ) (offers τ) internal C Z₀ := by
  refine Weak.bisimilar_iff.mpr ⟨fun U V => Looping U ∧ V = Z₀, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
    looping, rfl⟩
  · rintro U V ⟨loopingU, rfl⟩ ℓ U' moved
    obtain ⟨rfl, rfl⟩ := moves_looping τ A loopingU moved
    exact ⟨Z₀, stay τ A _, looping_spin τ loopingU, rfl⟩
  · rintro V _ ⟨_, rfl⟩ ℓ V' moved
    exact absurd moved (dead_Z₀ τ A)

/-- **The loop diverges.** -/
theorem divergent_looping {C : Configuration T Site} (looping : Looping C) :
    Weak.Divergent (sys τ A) internal C :=
  ⟨{U | Looping U}, looping, fun _ loopingU =>
    ⟨_, looping_spin τ loopingU, .t, rfl, move_looping τ A loopingU⟩⟩

/-- **The configuration without firings does not diverge.** -/
theorem not_divergent_Z₀ : ¬ Weak.Divergent (sys τ A) internal (Z₀ : Configuration T Site) := by
  rintro ⟨D, member, closed⟩
  obtain ⟨_, _, ℓ, _, moved⟩ := closed Z₀ member
  exact dead_Z₀ τ A moved

/-- **Divergence control**: the infinite internal loop is weakly bisimilar to the configuration
without firings, and the weak system that observes divergence separates them. -/
theorem divergence_control :
    WeakBisimilar A (label τ) (offers τ) internal L₀ Z₀ ∧
      Weak.Divergent (sys τ A) internal (L₀ : Configuration T Site) ∧
      ¬ Weak.Divergent (sys τ A) internal (Z₀ : Configuration T Site) ∧
      ¬ Weak.DivergenceBisimilar (sys τ A) internal L₀ Z₀ :=
  ⟨weakBisimilar_looping τ A looping_L₀, divergent_looping τ A looping_L₀, not_divergent_Z₀ τ A,
    fun bisimilar => not_divergent_Z₀ τ A
      ((Weak.divergent_iff_of_divergenceBisimilar bisimilar).mp (divergent_looping τ A looping_L₀))⟩

end Loop

/-! ## A program in the weak fragment: an inert internal firing -/

namespace Inert

/-- An internal firing taking `x` and a visible `B` taking `z`: independent, without races. -/
def tz : Firing T S Site := firing τ [.x] []
def bz : Firing T S Site := firing τ [.z] []

def alphabet₂ : List (Act × Firing T S Site) := [(.t, tz τ), (.B, bz τ)]

def offers₂ (ℓ : Act) (f : Firing T S Site) : Prop := (ℓ, f) ∈ alphabet₂ (S := S) τ

def XZ : Configuration T Site := ⟨[], {.x, .z}⟩
def Zonly : Configuration T Site := ⟨E τ 1, {.z}⟩

theorem tz_ne_bz : tz (S := S) τ ≠ bz τ := fun same => by
  have := congrArg (fun f : Firing T S Site => f.selection.taken) same
  simp [tz, bz, firing] at this

include A in
theorem independent : AnnotatedRuns.StaticIndependent (label τ) (tz (S := S) τ) (bz τ) := by
  have : Nonempty S := ⟨A.identity⟩
  exact (staticIndependent_iff_provenance (label τ) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mpr ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩

include A in
/-- **The program is in the race-free, independent fragment.** -/
theorem fragment : Fragment (label τ) (offers₂ (S := S) τ) where
  ground := by
    rintro ℓ f member
    simp only [offers₂, alphabet₂, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩
  oneLabel := by
    rintro ℓ ℓ' f m m'
    simp only [offers₂, alphabet₂, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at m m'
    rcases m with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m' with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rfl
    · exact absurd h (tz_ne_bz τ)
    · exact absurd h.symm (tz_ne_bz τ)
    · rfl
  independent := by
    rintro ℓ ℓ' f g m m' apart
    simp only [offers₂, alphabet₂, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at m m'
    rcases m with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rcases m' with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd rfl apart
    · exact independent τ A
    · exact (independent τ A).symm
    · exact absurd rfl apart

theorem move_XZ : Moves A (label τ) (offers₂ τ) XZ .t (Zonly τ) :=
  ⟨tz τ, by simp [offers₂, alphabet₂],
    (((fragment τ A).ground Act.t (tz τ) (by simp [offers₂, alphabet₂])).valid_iff A reflexive_nil).mpr
      (of_decide_eq_true rfl),
    (config_eq rfl (of_decide_eq_true rfl)).symm⟩

theorem no_internal_Zonly {ℓ : Act} {D : Configuration T Site}
    (moved : Moves A (label τ) (offers₂ τ) (Zonly τ) ℓ D) : ℓ = .B := by
  obtain ⟨f, member, valid, -⟩ := moved
  have ground := (fragment τ A).ground _ _ member
  rw [ground.valid_iff A (reflexive_E τ 1)] at valid
  simp only [offers₂, alphabet₂, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · rfl

/-- **An inert internal firing**: in the fragment, `{x, z}` and its internal successor `{z}` are
weakly bisimilar, and not bisimilar. -/
theorem inert_control :
    Fragment (label τ) (offers₂ (S := S) τ) ∧
      WeakBisimilar A (label τ) (offers₂ τ) internal XZ (Zonly τ) ∧
      ¬ Bisimilar A (label τ) (offers₂ τ) XZ (Zonly τ) :=
  ⟨fragment τ A, (fragment τ A).inert reflexive_nil rfl (move_XZ τ A),
    not_bisimilar_of_sat (φ := .dia .t .top) ⟨Zonly τ, move_XZ τ A, trivial⟩ fun ⟨_, moved, _⟩ =>
      absurd (no_internal_Zonly τ A moved) (by decide)⟩

end Inert

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Private.weakTraceEquivalent_P_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Private.not_weakBisimilar_P_Q
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Private.private_pair
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Private.commit_not_inert
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Private.not_weaklyDeterminate
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Private.not_fragment
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Prefix.strictly_finer
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Loop.divergence_control
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.WeakControls in
#print axioms Inert.inert_control
