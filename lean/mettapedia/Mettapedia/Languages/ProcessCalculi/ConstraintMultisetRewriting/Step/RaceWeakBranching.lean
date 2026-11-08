import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceWeakDeterminate

/-!
# Branching bisimilarity: strong ⊂ branching ⊂ weak

Branching bisimilarity (van Glabbeek and Weijland) asks a weak answer to keep the branching
structure: a move `x →ℓ x'` is answered either, for an internal `ℓ`, by staying (`x'` related to the
other state), or by silent moves to a state still related to `x`, followed by `ℓ` to a state related
to `x'` (`IsBranchingBisimulation`).

* **Strong bisimilarity implies branching bisimilarity** (`branching_of_strong`), and **branching
  bisimilarity implies weak bisimilarity** (`weak_of_branching`): a branching bisimulation is a weak
  bisimulation.
* **Internal moves of a τ-confluent set are branching-inert** (`branching_inert`): Groote and
  Sellink's theorem, in its branching form. In the step, the internal firings of the race-free,
  independent fragment are branching-inert (`Fragment.branching_inert`).

## Weak is strictly coarser than branching (`Milner.weak_not_branching`)

Milner's third τ-law, `a.(τ.b + c) + a.b` against `a.(τ.b + c)`, in the step. `P = {p}` offers `A`
to `K` or to `B`; `Q = {q}` offers `A` to `K` only. `K = {k}` offers an internal firing to `M` and
`C`; `M` and `B` offer `B`. They are weakly bisimilar: `P`'s move to `B` is answered by `A` then the
internal firing. They are not branching bisimilar: that answer passes through `K`, which can still
do `C`, while `B` cannot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (Formula System)

namespace Weak

universe uA uL

section Branching

variable {S : GSLT} (M : System.{uA, uL} S) (internal : M.Label → Prop)

/-- **A branching simulation**: a move is answered by staying, when internal, or by silent moves
to a state still related, then the same label to a related state. -/
def IsBranchingSimulation (R : S.Term → S.Term → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ ℓ ⦃x'⦄, M.act ℓ x x' →
    (internal ℓ ∧ R x' y) ∨ ∃ y₁ y', Silently M internal y y₁ ∧ R x y₁ ∧ M.act ℓ y₁ y' ∧ R x' y'

/-- **A branching bisimulation**: a branching simulation whose converse is one, relating only states
with the same observations. -/
def IsBranchingBisimulation (R : S.Term → S.Term → Prop) : Prop :=
  IsBranchingSimulation M internal R ∧ IsBranchingSimulation M internal (fun x y => R y x) ∧
    ∀ ⦃x y⦄, R x y → ∀ atom, M.observes atom x ↔ M.observes atom y

/-- **Branching bisimilarity.** -/
def BranchingBisimilar (x y : S.Term) : Prop :=
  ∃ R, IsBranchingBisimulation M internal R ∧ R x y

variable {M internal}

theorem weakSimulation_of_branching {R : S.Term → S.Term → Prop}
    (sim : IsBranchingSimulation M internal R) : IsWeakSimulation M internal R := by
  intro x y related ℓ x' moved
  rcases sim related ℓ moved with ⟨inner, rel⟩ | ⟨y₁, y', silently, _, step, rel⟩
  · exact ⟨y, act_of_silently inner (silently_refl y), rel⟩
  · exact ⟨y', silently_act silently (act_of_act step), rel⟩

/-- **Branching bisimilarity implies weak bisimilarity.** -/
theorem weak_of_branching {x y : S.Term} (bisimilar : BranchingBisimilar M internal x y) :
    Bisimilar M internal x y := by
  obtain ⟨R, ⟨forward, backward, atoms⟩, related⟩ := bisimilar
  exact bisimilar_iff.mpr ⟨R, ⟨weakSimulation_of_branching forward,
    weakSimulation_of_branching backward, atoms⟩, related⟩

/-- **Strong bisimilarity implies branching bisimilarity.** -/
theorem branching_of_strong {x y : S.Term} (bisimilar : M.Bisimilar x y) :
    BranchingBisimilar M internal x y := by
  obtain ⟨R, ⟨forward, backward, atoms⟩, related⟩ := bisimilar
  refine ⟨R, ⟨?_, ?_, atoms⟩, related⟩
  · intro a b rel ℓ a' moved
    obtain ⟨b', moved', rel'⟩ := forward rel ℓ moved
    exact .inr ⟨b, b', silently_refl b, rel, moved', rel'⟩
  · intro a b rel ℓ a' moved
    obtain ⟨b', moved', rel'⟩ := backward rel ℓ moved
    exact .inr ⟨b, b', silently_refl b, rel, moved', rel'⟩

/-- **The inertness relation is a branching bisimulation** on a τ-confluent set. -/
theorem inertRelation_isBranchingBisimulation {good : S.Term → Prop}
    (confluent : Confluent M internal good) :
    IsBranchingBisimulation M internal (InertRelation (M := M) (internal := internal) good) := by
  refine ⟨?_, ?_, (inertRelation_isWeakBisimulation confluent).2.2⟩
  · rintro a b related c a₁ moved
    rcases related with bisimilar | ⟨x, x', ax, goodX, ⟨τ, inner, step⟩, x'b⟩
    · obtain ⟨b₁, moved', rel'⟩ := bisimilar_forward M bisimilar moved
      exact .inr ⟨b, b₁, silently_refl b, .inl bisimilar, moved', .inl rel'⟩
    · obtain ⟨x₁, xm, a₁x₁⟩ := bisimilar_forward M ax moved
      rcases confluent.diamond τ c goodX inner step xm with ⟨innerC, x'x₁⟩ | ⟨y₁, y₂, x'y₁, x₁y₂, y₁y₂⟩
      · exact .inl ⟨innerC, .inl (M.bisimilar_trans a₁x₁ (M.bisimilar_trans (M.bisimilar_symm x'x₁) x'b))⟩
      · obtain ⟨b₁, bm, y₁b₁⟩ := bisimilar_forward M x'b x'y₁
        exact .inr ⟨b, b₁, silently_refl b, .inr ⟨x, x', ax, goodX, ⟨τ, inner, step⟩, x'b⟩, bm,
          .inr ⟨x₁, y₂, a₁x₁, confluent.closed c goodX xm, x₁y₂,
            M.bisimilar_trans (M.bisimilar_symm y₁y₂) y₁b₁⟩⟩
  · rintro u v related c u₁ moved
    rcases related with bisimilar | ⟨x, x', vx, goodX, ⟨τ, inner, step⟩, x'u⟩
    · obtain ⟨v₁, moved', rel'⟩ := bisimilar_backward M bisimilar moved
      exact .inr ⟨v, v₁, silently_refl v, .inl bisimilar, moved', .inl rel'⟩
    · obtain ⟨y, x'y, yu₁⟩ := bisimilar_backward M x'u moved
      obtain ⟨v₀, vv₀, v₀x'⟩ := bisimilar_backward M vx step
      obtain ⟨v', v₀v', v'y⟩ := bisimilar_backward M v₀x' x'y
      exact .inr ⟨v₀, v', silently_of_silent ⟨τ, inner, vv₀⟩, .inl (M.bisimilar_trans v₀x' x'u), v₀v',
        .inl (M.bisimilar_trans v'y yu₁)⟩

/-- **Internal moves of a τ-confluent set are branching-inert.** -/
theorem branching_inert {good : S.Term → Prop} (confluent : Confluent M internal good) {x x' : S.Term}
    (goodX : good x) (step : Silent M internal x x') : BranchingBisimilar M internal x x' :=
  ⟨_, inertRelation_isBranchingBisimulation confluent,
    .inr ⟨x, x', M.bisimilar_refl x, goodX, step, M.bisimilar_refl x'⟩⟩

end Branching

end Weak

universe uT uS uO uL

section FragmentBranching

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}
  {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop} {internal : L → Prop}

/-- **Internal firings of the fragment are branching-inert.** -/
theorem Fragment.branching_inert (fragment : Fragment label offers) {C D : Configuration T O}
    (refl : Reflexive C.equations) {τ : L} (inner : internal τ) (moved : Moves A label offers C τ D) :
    Weak.BranchingBisimilar (system A label offers) internal C D :=
  Weak.branching_inert (fragment.confluent internal) refl ⟨τ, inner, moved⟩

end FragmentBranching

variable {T : Type uT} {S : Type uS}

/-! ## Weak is strictly coarser than branching -/

namespace Milner

/-- Occurrence identities. -/
inductive Site
  | p | q | k | j | m
  deriving DecidableEq

/-- Label names: `t` is internal. -/
inductive Act
  | A | B | C | t
  deriving DecidableEq

/-- The internal labels. -/
abbrev inner (ℓ : Act) : Prop := ℓ = .t

variable (τ : T)

/-- Every occurrence carries `τ`. -/
def site : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (site τ), [], [], [], made.map (site τ)⟩, [], ⟨taken, [], made⟩⟩

/-- The program's alphabet. -/
def alphabet : List (Act × Firing T S Site) :=
  [(.A, firing τ [.p] [.k]), (.A, firing τ [.p] [.j]), (.A, firing τ [.q] [.k]),
    (.t, firing τ [.k] [.m]), (.C, firing τ [.k] []), (.B, firing τ [.m] []), (.B, firing τ [.j] [])]

def offers (ℓ : Act) (f : Firing T S Site) : Prop := (ℓ, f) ∈ alphabet (S := S) τ

/-- `n` copies of `(τ, τ)`. -/
def E (n : ℕ) : EquationStore T := List.replicate n (τ, τ)

def P : Configuration T Site := ⟨[], {.p}⟩
def Q : Configuration T Site := ⟨[], {.q}⟩
def K : Configuration T Site := ⟨E τ 1, {.k}⟩
def B : Configuration T Site := ⟨E τ 1, {.j}⟩
def Mid : Configuration T Site := ⟨E τ 2, {.m}⟩
def F₂ : Configuration T Site := ⟨E τ 2, ∅⟩
def F₃ : Configuration T Site := ⟨E τ 3, ∅⟩

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

theorem ground : ∀ x ∈ alphabet (S := S) τ, Ground (site τ) x.2 := by
  intro x member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

variable (A : SubstitutionAction T S)

/-- The step of the program. -/
abbrev sys := system A (site τ) (offers (S := S) τ)

theorem moves_of_filter {C : Configuration T Site} (refl : Reflexive C.equations)
    {l : List (Act × Firing T S Site)}
    (filtered : (alphabet (S := S) τ).filter
      (fun x => decide (Enabled (site τ) C.present (x.2.selection.commit (T := T)))) = l)
    {ℓ : Act} {D : Configuration T Site} (moved : Moves A (site τ) (offers τ) C ℓ D) :
    ∃ f, (ℓ, f) ∈ l ∧ D = f.result (site τ) C := by
  obtain ⟨f, member, valid, rfl⟩ := moved
  have enabled := ((ground τ (ℓ, f) member).valid_iff A refl).mp valid
  exact ⟨f, filtered ▸ List.mem_filter.mpr ⟨member, decide_eq_true enabled⟩, rfl⟩

theorem move_of {C : Configuration T Site} (refl : Reflexive C.equations) {ℓ : Act}
    {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet τ)
    (enabled : Enabled (site τ) C.present (f.selection.commit (T := T))) {D : Configuration T Site}
    (result : f.result (site τ) C = D) : Moves A (site τ) (offers τ) C ℓ D :=
  ⟨f, member, ((ground τ (ℓ, f) member).valid_iff A refl).mpr enabled, result.symm⟩

theorem moves_P {ℓ : Act} {D : Configuration T Site} (moved : Moves A (site τ) (offers τ) P ℓ D) :
    (ℓ = .A ∧ D = K τ) ∨ (ℓ = .A ∧ D = B τ) := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A reflexive_nil
    (l := [(.A, firing τ [.p] [.k]), (.A, firing τ [.p] [.j])]) rfl moved
  rcases List.mem_pair.mp member with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  · exact .inl ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩
  · exact .inr ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_Q {ℓ : Act} {D : Configuration T Site} (moved : Moves A (site τ) (offers τ) Q ℓ D) :
    ℓ = .A ∧ D = K τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A reflexive_nil
    (l := [(.A, firing τ [.q] [.k])]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_B {ℓ : Act} {D : Configuration T Site} (moved : Moves A (site τ) (offers τ) (B τ) ℓ D) :
    ℓ = .B ∧ D = F₂ τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A (reflexive_E τ 1)
    (l := [(.B, firing τ [.j] [])]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem moves_Mid {ℓ : Act} {D : Configuration T Site}
    (moved : Moves A (site τ) (offers τ) (Mid τ) ℓ D) : ℓ = .B ∧ D = F₃ τ := by
  obtain ⟨f, member, rfl⟩ := moves_of_filter τ A (reflexive_E τ 2)
    (l := [(.B, firing τ [.m] [])]) rfl moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl, config_eq rfl (of_decide_eq_true rfl)⟩

theorem dead_F₂ {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (site τ) (offers τ) (F₂ τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 2) (l := []) rfl moved
    exact List.not_mem_nil member

theorem dead_F₃ {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (site τ) (offers τ) (F₃ τ) ℓ D :=
  fun moved => by
    obtain ⟨f, member, -⟩ := moves_of_filter τ A (reflexive_E τ 3) (l := []) rfl moved
    exact List.not_mem_nil member

theorem move_P_K : Moves A (site τ) (offers τ) P .A (K τ) :=
  move_of τ A reflexive_nil (f := firing τ [.p] [.k]) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_P_B : Moves A (site τ) (offers τ) P .A (B τ) :=
  move_of τ A reflexive_nil (f := firing τ [.p] [.j]) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Q : Moves A (site τ) (offers τ) Q .A (K τ) :=
  move_of τ A reflexive_nil (f := firing τ [.q] [.k]) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_K_t : Moves A (site τ) (offers τ) (K τ) .t (Mid τ) :=
  move_of τ A (reflexive_E τ 1) (f := firing τ [.k] [.m]) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_K_C : Moves A (site τ) (offers τ) (K τ) .C (F₂ τ) :=
  move_of τ A (reflexive_E τ 1) (f := firing τ [.k] []) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_B : Moves A (site τ) (offers τ) (B τ) .B (F₂ τ) :=
  move_of τ A (reflexive_E τ 1) (f := firing τ [.j] []) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))
theorem move_Mid : Moves A (site τ) (offers τ) (Mid τ) .B (F₃ τ) :=
  move_of τ A (reflexive_E τ 2) (f := firing τ [.m] []) (by simp [alphabet]) (of_decide_eq_true rfl)
    (config_eq rfl (of_decide_eq_true rfl))

theorem step {C D : Configuration T Site} {ℓ : Act} (moved : Moves A (site τ) (offers τ) C ℓ D) :
    Weak.Act (sys τ A) inner ℓ C D :=
  Weak.act_of_act moved

/-- The weak bisimulation: the identity, the two starts, `B` against `Mid`, and the ends. -/
def relation (U V : Configuration T Site) : Prop :=
  U = V ∨ (U = P ∧ V = Q) ∨ (U = B τ ∧ V = Mid τ) ∨ (U = F₂ τ ∧ V = F₃ τ)

theorem relation_isWeakBisimulation : Weak.IsWeakBisimulation (sys τ A) inner (relation τ) := by
  refine ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩
  · rintro U V (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ U' moved
    · exact ⟨U', step τ A moved, .inl rfl⟩
    · rcases moves_P τ A moved with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨K τ, step τ A (move_Q τ A), .inl rfl⟩
      · exact ⟨Mid τ, Weak.act_silently (step τ A (move_Q τ A))
          (Weak.silently_of_silent ⟨.t, rfl, move_K_t τ A⟩), .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · obtain ⟨rfl, rfl⟩ := moves_B τ A moved
      exact ⟨F₃ τ, step τ A (move_Mid τ A), .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
    · exact absurd moved (dead_F₂ τ A)
  · rintro V U (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ V' moved
    · exact ⟨V', step τ A moved, .inl rfl⟩
    · obtain ⟨rfl, rfl⟩ := moves_Q τ A moved
      exact ⟨K τ, step τ A (move_P_K τ A), .inl rfl⟩
    · obtain ⟨rfl, rfl⟩ := moves_Mid τ A moved
      exact ⟨F₂ τ, step τ A (move_B τ A), .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
    · exact absurd moved (dead_F₃ τ A)

theorem weakBisimilar_P_Q : WeakBisimilar A (site τ) (offers τ) inner P Q :=
  Weak.bisimilar_iff.mpr ⟨relation τ, relation_isWeakBisimulation τ A, .inr (.inl ⟨rfl, rfl⟩)⟩

theorem quiet_Q : ∀ D, ¬ Weak.Silent (sys τ A) inner Q D := by
  rintro D ⟨ℓ, isInternal, moved⟩
  rw [(moves_Q τ A moved).1] at isInternal
  exact absurd isInternal (by decide)

theorem quiet_B : ∀ D, ¬ Weak.Silent (sys τ A) inner (B τ) D := by
  rintro D ⟨ℓ, isInternal, moved⟩
  rw [(moves_B τ A moved).1] at isInternal
  exact absurd isInternal (by decide)

theorem not_branching_P_Q : ¬ Weak.BranchingBisimilar (sys τ A) inner P Q := by
  rintro ⟨R, ⟨forward, backward, _⟩, related⟩
  rcases forward related Act.A (move_P_B τ A) with ⟨isInternal, _⟩ | ⟨y₁, y', Qy₁, _, y₁y', By'⟩
  · exact absurd isInternal (by decide)
  · have same : Q = y₁ := Weak.equiv_of_silently (quiet_Q τ A) Qy₁
    subst same
    obtain ⟨-, rfl⟩ := moves_Q τ A y₁y'
    rcases backward By' Act.C (move_K_C τ A) with ⟨isInternal, _⟩ | ⟨v₁, v', Bv₁, _, v₁v', _⟩
    · exact absurd isInternal (by decide)
    · have same' : B τ = v₁ := Weak.equiv_of_silently (quiet_B τ A) Bv₁
      subst same'
      exact absurd (moves_B τ A v₁v').1 (by decide)

/-- **Weak bisimilarity is strictly coarser than branching bisimilarity**: Milner's third τ-law is
weakly sound and branching unsound. -/
theorem weak_not_branching :
    WeakBisimilar A (site τ) (offers τ) inner P Q ∧ ¬ Weak.BranchingBisimilar (sys τ A) inner P Q :=
  ⟨weakBisimilar_P_Q τ A, not_branching_P_Q τ A⟩

end Milner

#print axioms Weak.weak_of_branching
#print axioms Weak.branching_of_strong
#print axioms Weak.inertRelation_isBranchingBisimulation
#print axioms Weak.branching_inert
#print axioms Fragment.branching_inert
#print axioms Milner.weak_not_branching

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
