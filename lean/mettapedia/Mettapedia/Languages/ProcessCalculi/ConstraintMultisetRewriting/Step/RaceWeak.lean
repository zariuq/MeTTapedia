import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceDeterminate

/-!
# Weak identity: internal labels, weak moves, weak bisimilarity

A program marks some of its labels **internal**. An observer does not see internal firings: it sees
a visible label preceded and followed by any number of internal firings, or nothing at all. This
module builds that reading once, for every Hennessy–Milner system of the tree
(`HennessyMilner.System`), and then for the labelled step of `RaceSpectrum`.

## Weak moves (`Weak.Silent`, `Weak.Silently`, `Weak.Act`, `Weak.weak`)

* An internal move is a move under an internal label (`Silent`); the silent move `τ*` is a chain of
  them, up to the equations (`Silently`).
* The weak move under `ℓ` (`Act`) is `τ*` when `ℓ` is internal and `τ* ℓ τ*` when it is visible
  (Milner's `⇒^ℓ̂`). Every move is a weak move (`act_of_act`).
* The weak moves, with the same observations, form a Hennessy–Milner system again (`weak`). **Weak
  bisimilarity** (`Weak.Bisimilar`) is its bisimilarity, **weak formulas** are its formulas (the
  diamond `⟨⟨ℓ⟩⟩` is its diamond), and **weak traces** are its traces.

## Weak bisimulations are checked one move at a time (`bisimilar_iff`)

A relation is a weak bisimulation (`IsWeakBisimulation`) when each single move of one side is
answered by a weak move of the other. Two states are weakly bisimilar exactly when some weak
bisimulation relates them. Hence **strong bisimilarity implies weak bisimilarity**
(`bisimilar_of_strong`). A weak simulation one move at a time (`IsWeakSimulation`) gives inclusion
of weak traces (`trace_of_simulation`).

## Logic (`bisimilar_iff_sat`)

Weakly bisimilar states satisfy the same weak formulas (`sat_iff_of_bisimilar`). When the weak
system is image-finite modulo the equations, weak formulas characterize weak bisimilarity, by the
tree's adequacy theorem `HennessyMilner.System.logicallyEquivalent_iff_bisimilar`.
The same holds when the weak successors have finite covers by weak bisimilarity
(`bisimilar_iff_sat_of_cover`).

## Determinacy and τ-confluence

* **Milner's determinacy theorem for every system without atoms** (`bisimilar_iff_traceEquivalent`):
  where successors under one label are bisimilar, bisimilarity is trace equivalence. Read on the weak
  system it is the weak theorem (`weak_bisimilar_iff_traceEquivalent`).
* **τ-confluence** (`Confluent`, after Groote and Sellink): an internal move and any other move from
  one state either coincide up to strong bisimilarity, the other being internal too, or close a
  diamond up to strong bisimilarity whose closing move on the other side is internal.
  **Internal moves of a τ-confluent set are inert** (`inert`, `inert_silently`): they are weak
  bisimilarities.
* **Strong determinacy and τ-confluence give weak determinacy** (`weaklyDeterminate`), so on such a
  set weak bisimilarity is weak trace equivalence (`confluent_bisimilar_iff_traceEquivalent`).

## Divergence (`Divergent`, `divergence`)

A state diverges when it starts an infinite chain of internal moves. The weak system that also
observes divergence (`divergence`) has a finer bisimilarity (`DivergenceBisimilar`): related states
diverge together (`divergent_iff_of_divergenceBisimilar`). Weak bisimilarity ignores divergence; the
control is in `RaceWeakControls`.

## The labelled step (`WeakMoves`, `WeakBisimilar`, `WeakSat`)

For the step of a program with internal labels, these are the weak notions of
`system A label offers`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (Formula System)

namespace Weak

universe uA uL

section Saturation

variable {S : GSLT} (M : System.{uA, uL} S) (internal : M.Label → Prop)

/-- **An internal move**: one move under a label the program marks internal. -/
def Silent (x y : S.Term) : Prop := ∃ τ, internal τ ∧ M.act τ x y

/-- **The silent move** `τ*`: a chain of internal moves, then the equations. -/
def Silently (x y : S.Term) : Prop :=
  ∃ z, Relation.ReflTransGen (Silent M internal) x z ∧ S.Equiv z y

/-- **A weak move** `⇒^ℓ̂`: the silent move under an internal label, and `τ* ℓ τ*` under a visible
one. -/
def Act (ℓ : M.Label) (x y : S.Term) : Prop :=
  (internal ℓ ∧ Silently M internal x y) ∨
    (¬ internal ℓ ∧ ∃ x' y', Silently M internal x x' ∧ M.act ℓ x' y' ∧ Silently M internal y' y)

variable {M internal}

theorem silently_refl (x : S.Term) : Silently M internal x x :=
  ⟨x, .refl, S.equations.iseqv.refl x⟩

theorem silently_of_equiv {x y : S.Term} (same : S.Equiv x y) : Silently M internal x y :=
  ⟨x, .refl, same⟩

theorem silently_of_silent {x y : S.Term} (step : Silent M internal x y) : Silently M internal x y :=
  ⟨y, .single step, S.equations.iseqv.refl y⟩

/-- Chains of internal moves transfer along the equations. -/
theorem chain_resp {x x' z : S.Term} (same : S.Equiv x x')
    (chain : Relation.ReflTransGen (Silent M internal) x z) :
    ∃ z', Relation.ReflTransGen (Silent M internal) x' z' ∧ S.Equiv z z' := by
  induction chain with
  | refl => exact ⟨x', .refl, same⟩
  | tail _ step ih =>
      obtain ⟨b', chain', equiv⟩ := ih
      obtain ⟨τ, inner, moved⟩ := step
      obtain ⟨c', moved', equiv'⟩ := M.act_resp_left equiv moved
      exact ⟨c', chain'.tail ⟨τ, inner, moved'⟩, equiv'⟩

theorem silently_trans {x y z : S.Term} (first : Silently M internal x y)
    (second : Silently M internal y z) : Silently M internal x z := by
  obtain ⟨a, chain, equiv⟩ := first
  obtain ⟨b, chain₂, equiv₂⟩ := second
  obtain ⟨b', chain₂', equiv'⟩ := chain_resp (S.equations.iseqv.symm equiv) chain₂
  exact ⟨b', chain.trans chain₂', S.equations.iseqv.trans (S.equations.iseqv.symm equiv') equiv₂⟩

/-- A state without internal moves moves silently only to its equals. -/
theorem equiv_of_silently {x y : S.Term} (quiet : ∀ z, ¬ Silent M internal x z)
    (silently : Silently M internal x y) : S.Equiv x y := by
  obtain ⟨z, chain, equiv⟩ := silently
  rcases chain.cases_head with rfl | ⟨c, step, _⟩
  · exact equiv
  · exact absurd step (quiet c)

theorem act_of_act {ℓ : M.Label} {x y : S.Term} (moved : M.act ℓ x y) : Act M internal ℓ x y := by
  by_cases inner : internal ℓ
  · exact .inl ⟨inner, silently_of_silent ⟨ℓ, inner, moved⟩⟩
  · exact .inr ⟨inner, x, y, silently_refl x, moved, silently_refl y⟩

theorem act_of_silently {τ : M.Label} (inner : internal τ) {x y : S.Term}
    (silently : Silently M internal x y) : Act M internal τ x y :=
  .inl ⟨inner, silently⟩

theorem silently_of_act {τ : M.Label} (inner : internal τ) {x y : S.Term}
    (moved : Act M internal τ x y) : Silently M internal x y := by
  rcases moved with ⟨_, silently⟩ | ⟨visible, _⟩
  · exact silently
  · exact absurd inner visible

theorem act_visible {ℓ : M.Label} (visible : ¬ internal ℓ) {x y : S.Term} :
    Act M internal ℓ x y ↔
      ∃ x' y', Silently M internal x x' ∧ M.act ℓ x' y' ∧ Silently M internal y' y := by
  constructor
  · rintro (⟨inner, _⟩ | ⟨_, moved⟩)
    · exact absurd inner visible
    · exact moved
  · exact fun moved => .inr ⟨visible, moved⟩

theorem silently_act {ℓ : M.Label} {x x' y : S.Term} (first : Silently M internal x x')
    (moved : Act M internal ℓ x' y) : Act M internal ℓ x y := by
  rcases moved with ⟨inner, silently⟩ | ⟨visible, a, b, before, step, after⟩
  · exact .inl ⟨inner, silently_trans first silently⟩
  · exact .inr ⟨visible, a, b, silently_trans first before, step, after⟩

theorem act_silently {ℓ : M.Label} {x y y' : S.Term} (moved : Act M internal ℓ x y)
    (after : Silently M internal y y') : Act M internal ℓ x y' := by
  rcases moved with ⟨inner, silently⟩ | ⟨visible, a, b, before, step, after'⟩
  · exact .inl ⟨inner, silently_trans silently after⟩
  · exact .inr ⟨visible, a, b, before, step, silently_trans after' after⟩

theorem act_resp_left' {ℓ : M.Label} {x x' y : S.Term} (same : S.Equiv x x')
    (moved : Act M internal ℓ x y) : Act M internal ℓ x' y :=
  silently_act (silently_of_equiv (S.equations.iseqv.symm same)) moved

theorem act_resp_right' {ℓ : M.Label} {x y y' : S.Term} (moved : Act M internal ℓ x y)
    (same : S.Equiv y y') : Act M internal ℓ x y' :=
  act_silently moved (silently_of_equiv same)

variable (M internal)

/-- **The weak system**: the weak moves, with the same labels and observations. -/
def weak : System.{uA, uL} S where
  Atom := M.Atom
  observes := M.observes
  observes_resp := M.observes_resp
  Label := M.Label
  act := Act M internal
  act_resp_left := fun same moved => ⟨_, act_resp_left' same moved, S.equations.iseqv.refl _⟩
  act_resp_right := fun moved same => act_resp_right' moved same

/-- **Weak bisimilarity**: bisimilarity of the weak system. -/
def Bisimilar (x y : S.Term) : Prop := (weak M internal).Bisimilar x y

/-- **Weak satisfaction**: the diamond `⟨⟨ℓ⟩⟩` of a weak formula is the weak move under `ℓ`. -/
def Sat (φ : Formula M.Atom M.Label) (x : S.Term) : Prop := (weak M internal).sat φ x

/-- **A weak simulation, checked one move at a time**: every move of the left state is answered by
a weak move of the right state under the same label. -/
def IsWeakSimulation (R : S.Term → S.Term → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ ℓ ⦃x'⦄, M.act ℓ x x' → ∃ y', Act M internal ℓ y y' ∧ R x' y'

/-- **A weak bisimulation, checked one move at a time**: a weak simulation whose converse is one,
relating only states with the same observations. -/
def IsWeakBisimulation (R : S.Term → S.Term → Prop) : Prop :=
  IsWeakSimulation M internal R ∧ IsWeakSimulation M internal (fun x y => R y x) ∧
    ∀ ⦃x y⦄, R x y → ∀ atom, M.observes atom x ↔ M.observes atom y

variable {M internal}

/-- A relation closed under the equations on both sides. -/
def Closure (R : S.Term → S.Term → Prop) (x y : S.Term) : Prop :=
  ∃ x' y', S.Equiv x x' ∧ R x' y' ∧ S.Equiv y' y

theorem chain_transfer {R : S.Term → S.Term → Prop} (sim : IsWeakSimulation M internal R)
    {x y z : S.Term} (related : R x y) (chain : Relation.ReflTransGen (Silent M internal) x z) :
    ∃ w, Silently M internal y w ∧ R z w := by
  induction chain with
  | refl => exact ⟨y, silently_refl y, related⟩
  | tail _ step ih =>
      obtain ⟨w, silently, rel⟩ := ih
      obtain ⟨τ, inner, moved⟩ := step
      obtain ⟨w', moved', rel'⟩ := sim rel τ moved
      exact ⟨w', silently_trans silently (silently_of_act inner moved'), rel'⟩

theorem silently_transfer {R : S.Term → S.Term → Prop} (sim : IsWeakSimulation M internal R)
    {x y x₁ : S.Term} (related : R x y) (silently : Silently M internal x x₁) :
    ∃ y₁, Silently M internal y y₁ ∧ Closure R x₁ y₁ := by
  obtain ⟨z, chain, equiv⟩ := silently
  obtain ⟨w, silently', rel⟩ := chain_transfer sim related chain
  exact ⟨w, silently', z, w, S.equations.iseqv.symm equiv, rel, S.equations.iseqv.refl w⟩

/-- **A weak simulation answers weak moves by weak moves.** -/
theorem act_transfer {R : S.Term → S.Term → Prop} (sim : IsWeakSimulation M internal R)
    {ℓ : M.Label} {x y x₁ : S.Term} (related : R x y) (moved : Act M internal ℓ x x₁) :
    ∃ y₁, Act M internal ℓ y y₁ ∧ Closure R x₁ y₁ := by
  rcases moved with ⟨inner, silently⟩ | ⟨visible, u, v, before, step, after⟩
  · obtain ⟨y₁, silently', closure⟩ := silently_transfer sim related silently
    exact ⟨y₁, .inl ⟨inner, silently'⟩, closure⟩
  · obtain ⟨w₀, toW₀, z, w₀', uz, rel₀, w₀'w₀⟩ := silently_transfer sim related before
    obtain ⟨v', zv', vv'⟩ := M.act_resp_left uz step
    obtain ⟨w₁, moved₁, rel₁⟩ := sim rel₀ ℓ zv'
    have after' : Silently M internal v' x₁ :=
      silently_trans (silently_of_equiv (S.equations.iseqv.symm vv')) after
    obtain ⟨w₂, toW₂, closure⟩ := silently_transfer sim rel₁ after'
    exact ⟨w₂, silently_act (silently_trans toW₀ (silently_of_equiv (S.equations.iseqv.symm w₀'w₀)))
      (act_silently moved₁ toW₂), closure⟩

theorem closure_isBisimulation {R : S.Term → S.Term → Prop}
    (bisimulation : IsWeakBisimulation M internal R) :
    (weak M internal).IsBisimulation (Closure R) := by
  obtain ⟨forward, backward, atoms⟩ := bisimulation
  refine ⟨?_, ?_, ?_⟩
  · rintro a b ⟨a', b', aa', rel, b'b⟩ ℓ a₁ moved
    obtain ⟨b₁, moved', closure⟩ := act_transfer forward rel (act_resp_left' aa' moved)
    exact ⟨b₁, act_resp_left' (S.equations.iseqv.symm (S.equations.iseqv.symm b'b)) moved', closure⟩
  · rintro a b ⟨a', b', aa', rel, b'b⟩ ℓ b₁ moved
    obtain ⟨a₁, moved', u, v, b₁u, vu, va₁⟩ := act_transfer (x := b') (y := a') backward rel
      (act_resp_left' (S.equations.iseqv.symm b'b) moved)
    exact ⟨a₁, act_resp_left' (S.equations.iseqv.symm aa') moved', v, u,
      S.equations.iseqv.symm va₁, vu, S.equations.iseqv.symm b₁u⟩
  · rintro a b ⟨a', b', aa', rel, b'b⟩ atom
    exact (M.observes_resp atom aa').trans ((atoms rel atom).trans (M.observes_resp atom b'b))

/-- **Weak bisimilarity is checked one move at a time**: two states are weakly bisimilar exactly
when some weak bisimulation relates them. -/
theorem bisimilar_iff {x y : S.Term} :
    Bisimilar M internal x y ↔ ∃ R, IsWeakBisimulation M internal R ∧ R x y := by
  constructor
  · rintro ⟨R, ⟨forward, backward, atoms⟩, related⟩
    refine ⟨R, ⟨?_, ?_, atoms⟩, related⟩
    · intro a b rel ℓ a' moved
      exact forward rel ℓ (act_of_act moved)
    · intro a b rel ℓ a' moved
      exact backward rel ℓ (act_of_act moved)
  · rintro ⟨R, bisimulation, related⟩
    exact ⟨Closure R, closure_isBisimulation bisimulation,
      x, y, S.equations.iseqv.refl x, related, S.equations.iseqv.refl y⟩

/-- **Strong bisimilarity implies weak bisimilarity.** -/
theorem bisimilar_of_strong {x y : S.Term} (bisimilar : M.Bisimilar x y) :
    Bisimilar M internal x y := by
  obtain ⟨R, ⟨forward, backward, atoms⟩, related⟩ := bisimilar
  refine bisimilar_iff.mpr ⟨R, ⟨?_, ?_, atoms⟩, related⟩
  · intro a b rel ℓ a' moved
    obtain ⟨b', moved', rel'⟩ := forward rel ℓ moved
    exact ⟨b', act_of_act moved', rel'⟩
  · intro a b rel ℓ a' moved
    obtain ⟨b', moved', rel'⟩ := backward rel ℓ moved
    exact ⟨b', act_of_act moved', rel'⟩

/-- Weakly bisimilar states satisfy the same weak formulas. -/
theorem sat_iff_of_bisimilar {x y : S.Term} (bisimilar : Bisimilar M internal x y)
    (φ : Formula M.Atom M.Label) : Sat M internal φ x ↔ Sat M internal φ y :=
  (weak M internal).logicallyEquivalent_of_bisimilar bisimilar φ

theorem not_bisimilar_of_sat {x y : S.Term} {φ : Formula M.Atom M.Label}
    (holds : Sat M internal φ x) (fails : ¬ Sat M internal φ y) : ¬ Bisimilar M internal x y :=
  fun bisimilar => fails ((sat_iff_of_bisimilar bisimilar φ).mp holds)

variable (M internal) in
/-- **Weak Hennessy–Milner**: on an image-finite weak system, two states are weakly bisimilar
exactly when they satisfy the same weak formulas. -/
theorem bisimilar_iff_sat (finite : (weak M internal).ImageFiniteModulo) (x y : S.Term) :
    Bisimilar M internal x y ↔ ∀ φ : Formula M.Atom M.Label, (Sat M internal φ x ↔ Sat M internal φ y) :=
  ((weak M internal).logicallyEquivalent_iff_bisimilar finite x y).symm

variable (M internal) in
/-- **Weak Hennessy–Milner with finite covers**: when the weak successors under each label have a
finite cover by weak bisimilarity, weak formulas characterize weak bisimilarity. Knowledge that grows
along silent loops breaks image-finiteness modulo the equations, not such covers. -/
theorem bisimilar_iff_sat_of_cover (finite : (weak M internal).ImageFiniteBisimilar) (x y : S.Term) :
    Bisimilar M internal x y ↔ ∀ φ : Formula M.Atom M.Label, (Sat M internal φ x ↔ Sat M internal φ y) :=
  ((weak M internal).logicallyEquivalent_iff_bisimilar_of_imageFiniteBisimilar finite x y).symm

/-- **A weak simulation one move at a time includes weak traces.** -/
theorem trace_of_simulation {R : S.Term → S.Term → Prop} (sim : IsWeakSimulation M internal R) :
    ∀ (w : List M.Label) {x y : S.Term}, R x y →
      Sat M internal (Formula.after w .top) x → Sat M internal (Formula.after w .top) y
  | [], _, _, _, _ => trivial
  | ℓ :: w, _, _, related, ⟨x₁, moved, traced⟩ => by
      obtain ⟨y₁, moved', a, b, x₁a, rel, by₁⟩ := act_transfer sim related moved
      refine ⟨y₁, moved', ?_⟩
      have atA := ((weak M internal).sat_resp _ x₁a).mp traced
      exact ((weak M internal).sat_resp _ by₁).mp (trace_of_simulation sim w rel atA)

end Saturation

/-! ## Strong bisimilarity, one move at a time -/

section Strong

variable {S : GSLT} (M : System.{uA, uL} S)

theorem bisimilar_forward {a b a₁ : S.Term} {c : M.Label} (bisimilar : M.Bisimilar a b)
    (moved : M.act c a a₁) : ∃ b₁, M.act c b b₁ ∧ M.Bisimilar a₁ b₁ := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  obtain ⟨b₁, moved', related'⟩ := bisimulation.1 related c moved
  exact ⟨b₁, moved', R, bisimulation, related'⟩

theorem bisimilar_backward {a b b₁ : S.Term} {c : M.Label} (bisimilar : M.Bisimilar a b)
    (moved : M.act c b b₁) : ∃ a₁, M.act c a a₁ ∧ M.Bisimilar a₁ b₁ := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  obtain ⟨a₁, moved', related'⟩ := bisimulation.2.1 related c moved
  exact ⟨a₁, moved', R, bisimulation, related'⟩

theorem bisimilar_observes {a b : S.Term} (bisimilar : M.Bisimilar a b) (atom : M.Atom) :
    M.observes atom a ↔ M.observes atom b := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  exact bisimulation.2.2 related atom

/-- **Traces**: the diamond-only formulas. -/
def TraceEquivalent (x y : S.Term) : Prop :=
  ∀ w : List M.Label, M.sat (Formula.after w .top) x ↔ M.sat (Formula.after w .top) y

/-- **Determinacy** on a set of states: successors under one label are bisimilar. -/
def Determinate (good : S.Term → Prop) : Prop :=
  ∀ x, good x → ∀ ℓ x₁ x₂, M.act ℓ x x₁ → M.act ℓ x x₂ → M.Bisimilar x₁ x₂

variable {M}

theorem traceEquivalent_of_bisimilar {x y : S.Term} (bisimilar : M.Bisimilar x y) :
    TraceEquivalent M x y :=
  fun _ => M.logicallyEquivalent_of_bisimilar bisimilar _

/-- **Milner's determinacy theorem, for every system without observations**: on a determinate set
closed under moves, trace-equivalent states are bisimilar. -/
theorem bisimilar_of_traceEquivalent [IsEmpty M.Atom] {good : S.Term → Prop}
    (closed : ∀ x ℓ y, good x → M.act ℓ x y → good y) (determinate : Determinate M good)
    {x y : S.Term} (goodX : good x) (goodY : good y) (traces : TraceEquivalent M x y) :
    M.Bisimilar x y := by
  have step : ∀ a b, good a → good b → TraceEquivalent M a b →
      ∀ ℓ a', M.act ℓ a a' → ∃ b', M.act ℓ b b' ∧ good a' ∧ good b' ∧ TraceEquivalent M a' b' := by
    intro a b goodA goodB traces ℓ a' moved
    obtain ⟨b', moved', _⟩ := (traces [ℓ]).mp ⟨a', moved, trivial⟩
    refine ⟨b', moved', closed a ℓ a' goodA moved, closed b ℓ b' goodB moved', fun w => ⟨?_, ?_⟩⟩
    · intro traced
      obtain ⟨b'', moved'', traced''⟩ := (traces (ℓ :: w)).mp ⟨a', moved, traced⟩
      exact (traceEquivalent_of_bisimilar (determinate b goodB ℓ b'' b' moved'' moved') w).mp traced''
    · intro traced
      obtain ⟨a'', moved'', traced''⟩ := (traces (ℓ :: w)).mpr ⟨b', moved', traced⟩
      exact (traceEquivalent_of_bisimilar (determinate a goodA ℓ a'' a' moved'' moved) w).mp traced''
  refine ⟨fun a b => good a ∧ good b ∧ TraceEquivalent M a b, ⟨?_, ?_, ?_⟩, goodX, goodY, traces⟩
  · rintro a b ⟨goodA, goodB, traces⟩ ℓ a' moved
    obtain ⟨b', moved', goodA', goodB', traces'⟩ := step a b goodA goodB traces ℓ a' moved
    exact ⟨b', moved', goodA', goodB', traces'⟩
  · rintro a b ⟨goodA, goodB, traces⟩ ℓ b' moved
    obtain ⟨a', moved', goodB', goodA', traces'⟩ :=
      step b a goodB goodA (fun w => (traces w).symm) ℓ b' moved
    exact ⟨a', moved', goodA', goodB', fun w => (traces' w).symm⟩
  · intro _ _ _ atom
    exact isEmptyElim atom

/-- **On a determinate set, bisimilarity is trace equivalence.** -/
theorem bisimilar_iff_traceEquivalent [IsEmpty M.Atom] {good : S.Term → Prop}
    (closed : ∀ x ℓ y, good x → M.act ℓ x y → good y) (determinate : Determinate M good)
    {x y : S.Term} (goodX : good x) (goodY : good y) :
    M.Bisimilar x y ↔ TraceEquivalent M x y :=
  ⟨traceEquivalent_of_bisimilar, bisimilar_of_traceEquivalent closed determinate goodX goodY⟩

end Strong

/-! ## Weak traces and weak determinacy -/

section WeakDeterminacy

variable {S : GSLT} {M : System.{uA, uL} S} {internal : M.Label → Prop}

/-- Weakly bisimilar states have the same weak traces. -/
theorem traceEquivalent_of_weak {x y : S.Term} (bisimilar : Bisimilar M internal x y) :
    TraceEquivalent (weak M internal) x y :=
  traceEquivalent_of_bisimilar bisimilar

/-- **Weak simulations both ways give weak trace equivalence.** -/
theorem traceEquivalent_of_simulations {R R' : S.Term → S.Term → Prop}
    (sim : IsWeakSimulation M internal R) (sim' : IsWeakSimulation M internal R') {x y : S.Term}
    (forth : R x y) (back : R' y x) : TraceEquivalent (weak M internal) x y :=
  fun w => ⟨trace_of_simulation sim w forth, trace_of_simulation sim' w back⟩

/-- **Milner's weak determinacy theorem**: where weak successors under one label are weakly
bisimilar, on a set closed under weak moves, weak bisimilarity is weak trace equivalence. -/
theorem weak_bisimilar_iff_traceEquivalent [IsEmpty M.Atom] {good : S.Term → Prop}
    (closed : ∀ x ℓ y, good x → Act M internal ℓ x y → good y)
    (determinate : Determinate (weak M internal) good) {x y : S.Term} (goodX : good x)
    (goodY : good y) :
    Bisimilar M internal x y ↔ TraceEquivalent (weak M internal) x y :=
  haveI : IsEmpty (weak M internal).Atom := ‹IsEmpty M.Atom›
  bisimilar_iff_traceEquivalent closed determinate goodX goodY

variable (M internal) in
/-- **τ-confluence** on a set of states, after Groote and Sellink. The set is closed under the
equations and under moves; internal moves keep the observations; and an internal move and any other
move from one state either agree up to strong bisimilarity, the other being internal too, or close a
diamond up to strong bisimilarity whose closing move on the other side is internal. -/
structure Confluent (good : S.Term → Prop) : Prop where
  equiv_closed : ∀ ⦃x y⦄, good x → S.Equiv x y → good y
  closed : ∀ ⦃x y⦄ (ℓ : M.Label), good x → M.act ℓ x y → good y
  observes : ∀ ⦃x y⦄, good x → Silent M internal x y → ∀ atom, M.observes atom x ↔ M.observes atom y
  diamond : ∀ ⦃x x₁ x₂⦄ (τ ℓ : M.Label), good x → internal τ → M.act τ x x₁ → M.act ℓ x x₂ →
    (internal ℓ ∧ M.Bisimilar x₁ x₂) ∨
      ∃ y₁ y₂, M.act ℓ x₁ y₁ ∧ Silent M internal x₂ y₂ ∧ M.Bisimilar y₁ y₂

theorem bisimilar_of_closure {x y : S.Term} (closure : Closure M.Bisimilar x y) : M.Bisimilar x y := by
  obtain ⟨a, b, xa, related, by_⟩ := closure
  exact M.bisimilar_trans (M.bisimilar_of_equiv xa) (M.bisimilar_trans related (M.bisimilar_of_equiv by_))

theorem isWeakSimulation_bisimilar : IsWeakSimulation M internal M.Bisimilar := by
  intro a b related ℓ a' moved
  obtain ⟨b', moved', related'⟩ := bisimilar_forward M related moved
  exact ⟨b', act_of_act moved', related'⟩

/-- **Strongly bisimilar states answer weak moves strongly**: a weak move of one is matched by a weak
move of the other to a strongly bisimilar state. -/
theorem bisimilar_transfer {x y y₁ : S.Term} {ℓ : M.Label} (bisimilar : M.Bisimilar x y)
    (moved : Act M internal ℓ y y₁) : ∃ x₁, Act M internal ℓ x x₁ ∧ M.Bisimilar x₁ y₁ := by
  obtain ⟨x₁, moved', closure⟩ := act_transfer isWeakSimulation_bisimilar (M.bisimilar_symm bisimilar) moved
  exact ⟨x₁, moved', M.bisimilar_symm (bisimilar_of_closure closure)⟩

theorem Confluent.good_of_silently {good : S.Term → Prop} (confluent : Confluent M internal good)
    {x y : S.Term} (goodX : good x) (silently : Silently M internal x y) : good y := by
  obtain ⟨z, chain, equiv⟩ := silently
  have reached : good z := by
    clear equiv
    induction chain with
    | refl => exact goodX
    | tail _ step ih =>
        obtain ⟨τ, _, moved⟩ := step
        exact confluent.closed τ ih moved
  exact confluent.equiv_closed reached equiv

theorem Confluent.good_of_act {good : S.Term → Prop} (confluent : Confluent M internal good)
    {x y : S.Term} {ℓ : M.Label} (goodX : good x) (moved : Act M internal ℓ x y) : good y := by
  rcases moved with ⟨_, silently⟩ | ⟨_, u, v, before, step, after⟩
  · exact confluent.good_of_silently goodX silently
  · exact confluent.good_of_silently
      (confluent.closed ℓ (confluent.good_of_silently goodX before) step) after

/-- The relation of the inertness proof: strong bisimilarity, or one internal move of a good state
between two strong bisimilarities. -/
def InertRelation (good : S.Term → Prop) (a b : S.Term) : Prop :=
  M.Bisimilar a b ∨
    ∃ x x', M.Bisimilar a x ∧ good x ∧ Silent M internal x x' ∧ M.Bisimilar x' b

theorem inertRelation_isWeakBisimulation {good : S.Term → Prop}
    (confluent : Confluent M internal good) :
    IsWeakBisimulation M internal (InertRelation (M := M) (internal := internal) good) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a b (bisimilar | ⟨x, x', ax, goodX, ⟨τ, inner, step⟩, x'b⟩) c a₁ moved
    · obtain ⟨b₁, moved', related⟩ := bisimilar_forward M bisimilar moved
      exact ⟨b₁, act_of_act moved', .inl related⟩
    · obtain ⟨x₁, xm, a₁x₁⟩ := bisimilar_forward M ax moved
      rcases confluent.diamond τ c goodX inner step xm with ⟨innerC, x'x₁⟩ | ⟨y₁, y₂, x'y₁, x₁y₂, y₁y₂⟩
      · exact ⟨b, act_of_silently innerC (silently_refl b),
          .inl (M.bisimilar_trans a₁x₁ (M.bisimilar_trans (M.bisimilar_symm x'x₁) x'b))⟩
      · obtain ⟨b₁, bm, y₁b₁⟩ := bisimilar_forward M x'b x'y₁
        exact ⟨b₁, act_of_act bm, .inr ⟨x₁, y₂, a₁x₁, confluent.closed c goodX xm, x₁y₂,
          M.bisimilar_trans (M.bisimilar_symm y₁y₂) y₁b₁⟩⟩
  · rintro u v (bisimilar | ⟨x, x', vx, goodX, ⟨τ, inner, step⟩, x'u⟩) c u₁ moved
    · obtain ⟨v₁, moved', related⟩ := bisimilar_backward M bisimilar moved
      exact ⟨v₁, act_of_act moved', .inl related⟩
    · obtain ⟨y, x'y, yu₁⟩ := bisimilar_backward M x'u moved
      have xy : Act M internal c x y :=
        silently_act (silently_of_silent ⟨τ, inner, step⟩) (act_of_act x'y)
      obtain ⟨v₁, vm, v₁y⟩ := bisimilar_transfer vx xy
      exact ⟨v₁, vm, .inl (M.bisimilar_trans v₁y yu₁)⟩
  · rintro a b (bisimilar | ⟨x, x', ax, goodX, silent, x'b⟩) atom
    · exact bisimilar_observes M bisimilar atom
    · exact (bisimilar_observes M ax atom).trans
        ((confluent.observes goodX silent atom).trans (bisimilar_observes M x'b atom))

/-- **Internal moves of a τ-confluent set are inert**: an internal move relates weakly bisimilar
states. -/
theorem inert {good : S.Term → Prop} (confluent : Confluent M internal good) {x x' : S.Term}
    (goodX : good x) (step : Silent M internal x x') : Bisimilar M internal x x' :=
  bisimilar_iff.mpr ⟨_, inertRelation_isWeakBisimulation confluent,
    .inr ⟨x, x', M.bisimilar_refl x, goodX, step, M.bisimilar_refl x'⟩⟩

/-- **Silent moves of a τ-confluent set are inert.** -/
theorem inert_silently {good : S.Term → Prop} (confluent : Confluent M internal good)
    {x y : S.Term} (goodX : good x) (silently : Silently M internal x y) : Bisimilar M internal x y := by
  obtain ⟨z, chain, equiv⟩ := silently
  have reached : good z ∧ Bisimilar M internal x z := by
    clear equiv
    induction chain with
    | refl => exact ⟨goodX, (weak M internal).bisimilar_refl x⟩
    | tail _ step ih =>
        obtain ⟨goodB, xb⟩ := ih
        obtain ⟨τ, inner, moved⟩ := step
        exact ⟨confluent.closed τ goodB moved,
          (weak M internal).bisimilar_trans xb (inert confluent goodB ⟨τ, inner, moved⟩)⟩
  exact (weak M internal).bisimilar_trans reached.2 ((weak M internal).bisimilar_of_equiv equiv)

/-- **A visible move is pushed along silent moves**: from a good state, a visible move and a silent
move close, the visible move on the far side and silent moves after the near one, up to strong
bisimilarity. -/
theorem push {good : S.Term → Prop} (confluent : Confluent M internal good) {u v s : S.Term}
    {ℓ : M.Label} (goodU : good u) (visible : ¬ internal ℓ) (moved : M.act ℓ u v)
    (silently : Silently M internal u s) :
    ∃ y z, M.act ℓ s y ∧ Silently M internal v z ∧ M.Bisimilar y z := by
  obtain ⟨s', chain, equiv⟩ := silently
  have key : good s' ∧ ∃ y z, M.act ℓ s' y ∧ Silently M internal v z ∧ M.Bisimilar y z := by
    clear equiv
    induction chain with
    | refl => exact ⟨goodU, v, v, moved, silently_refl v, M.bisimilar_refl v⟩
    | tail _ step ih =>
        obtain ⟨goodB, y, z, by_, vz, yz⟩ := ih
        obtain ⟨τ, inner, bc⟩ := step
        rcases confluent.diamond τ ℓ goodB inner bc by_ with ⟨innerℓ, _⟩ | ⟨y₁, y₂, cy₁, yy₂, y₁y₂⟩
        · exact absurd innerℓ visible
        · obtain ⟨τ', inner', yy₂'⟩ := yy₂
          obtain ⟨z₂, zz₂, y₂z₂⟩ := bisimilar_forward M yz yy₂'
          exact ⟨confluent.closed τ goodB bc, y₁, z₂, cy₁,
            silently_trans vz (silently_of_silent ⟨τ', inner', zz₂⟩), M.bisimilar_trans y₁y₂ y₂z₂⟩
  obtain ⟨_, y, z, s'y, vz, yz⟩ := key
  obtain ⟨y', sy', yy'⟩ := M.act_resp_left equiv s'y
  exact ⟨y', z, sy', vz, M.bisimilar_trans (M.bisimilar_symm (M.bisimilar_of_equiv yy')) yz⟩

/-- **Strong determinacy and τ-confluence give weak determinacy**: weak successors of a good state
under one label are weakly bisimilar. -/
theorem weaklyDeterminate {good : S.Term → Prop} (confluent : Confluent M internal good)
    (determinate : Determinate M good) : Determinate (weak M internal) good := by
  intro x goodX ℓ y₁ y₂ (m₁ : Act M internal ℓ x y₁) (m₂ : Act M internal ℓ x y₂)
  rcases m₁ with ⟨inner, s₁⟩ | ⟨visible, u₁, v₁, xu₁, u₁v₁, v₁y₁⟩
  · exact (weak M internal).bisimilar_trans
      ((weak M internal).bisimilar_symm (inert_silently confluent goodX s₁))
      (inert_silently confluent goodX (silently_of_act (M := M) inner m₂))
  · obtain ⟨u₂, v₂, xu₂, u₂v₂, v₂y₂⟩ := (act_visible (M := M) visible).mp m₂
    have goodU₁ := confluent.good_of_silently goodX xu₁
    have goodU₂ := confluent.good_of_silently goodX xu₂
    have goodV₁ := confluent.closed ℓ goodU₁ u₁v₁
    have goodV₂ := confluent.closed ℓ goodU₂ u₂v₂
    have u₁u₂ : Bisimilar M internal u₁ u₂ :=
      (weak M internal).bisimilar_trans
        ((weak M internal).bisimilar_symm (inert_silently confluent goodX xu₁))
        (inert_silently confluent goodX xu₂)
    obtain ⟨w, u₂w, v₁w⟩ := bisimilar_forward (weak M internal) u₁u₂ (act_of_act (internal := internal) u₁v₁)
    obtain ⟨s, t, u₂s, st, tw⟩ := (act_visible (M := M) visible).mp u₂w
    have goodS := confluent.good_of_silently goodU₂ u₂s
    obtain ⟨y, z, sy, v₂z, yz⟩ := push confluent goodU₂ visible u₂v₂ u₂s
    have ty : M.Bisimilar t y := determinate s goodS ℓ t y st sy
    have chain₁ : Bisimilar M internal y₁ w :=
      (weak M internal).bisimilar_trans
        ((weak M internal).bisimilar_symm (inert_silently confluent goodV₁ v₁y₁)) v₁w
    have chain₂ : Bisimilar M internal w z :=
      (weak M internal).bisimilar_trans
        ((weak M internal).bisimilar_symm
          (inert_silently confluent (confluent.closed ℓ goodS st) tw))
        (bisimilar_of_strong (M.bisimilar_trans ty yz))
    have chain₃ : Bisimilar M internal z y₂ :=
      (weak M internal).bisimilar_trans
        ((weak M internal).bisimilar_symm (inert_silently confluent goodV₂ v₂z))
        (inert_silently confluent goodV₂ v₂y₂)
    exact (weak M internal).bisimilar_trans chain₁ ((weak M internal).bisimilar_trans chain₂ chain₃)

/-- **On a τ-confluent, strongly determinate set, weak bisimilarity is weak trace equivalence.** -/
theorem confluent_bisimilar_iff_traceEquivalent [IsEmpty M.Atom] {good : S.Term → Prop}
    (confluent : Confluent M internal good) (determinate : Determinate M good) {x y : S.Term}
    (goodX : good x) (goodY : good y) :
    Bisimilar M internal x y ↔ TraceEquivalent (weak M internal) x y :=
  weak_bisimilar_iff_traceEquivalent (fun _ _ _ goodX moved => confluent.good_of_act goodX moved)
    (weaklyDeterminate confluent determinate) goodX goodY

end WeakDeterminacy

/-! ## Divergence -/

section Divergence

variable {S : GSLT} (M : System.{uA, uL} S) (internal : M.Label → Prop)

/-- **Divergence**: the state lies in a set every member of which has an internal move into the
set, so it starts an infinite chain of internal moves. -/
def Divergent (x : S.Term) : Prop :=
  ∃ D : Set S.Term, x ∈ D ∧ ∀ d ∈ D, ∃ d' ∈ D, Silent M internal d d'

variable {M internal}

theorem divergent_resp {x y : S.Term} (same : S.Equiv x y) (divergent : Divergent M internal x) :
    Divergent M internal y := by
  obtain ⟨D, member, closed⟩ := divergent
  refine ⟨{y | ∃ d ∈ D, S.Equiv d y}, ⟨x, member, same⟩, ?_⟩
  rintro y' ⟨d, inD, dy'⟩
  obtain ⟨d', inD', τ, inner, moved⟩ := closed d inD
  obtain ⟨e, moved', d'e⟩ := M.act_resp_left dy' moved
  exact ⟨e, ⟨d', inD', d'e⟩, τ, inner, moved'⟩

variable (M internal)

/-- **The weak system that also observes divergence.** -/
def divergence : System.{uA, uL} S where
  Atom := Option M.Atom
  observes atom x := match atom with
    | none => Divergent M internal x
    | some atom => M.observes atom x
  observes_resp atom {_ _} same := match atom with
    | none => ⟨divergent_resp same, divergent_resp (S.equations.iseqv.symm same)⟩
    | some atom => M.observes_resp atom same
  Label := M.Label
  act := Act M internal
  act_resp_left := fun same moved => ⟨_, act_resp_left' same moved, S.equations.iseqv.refl _⟩
  act_resp_right := fun moved same => act_resp_right' moved same

/-- **Divergence-respecting weak bisimilarity**: related states are weakly bisimilar and diverge
together, at every pair the bisimulation relates. -/
def DivergenceBisimilar (x y : S.Term) : Prop := (divergence M internal).Bisimilar x y

variable {M internal}

/-- **Divergence-respecting weak bisimilarity implies weak bisimilarity.** -/
theorem bisimilar_of_divergenceBisimilar {x y : S.Term}
    (bisimilar : DivergenceBisimilar M internal x y) : Bisimilar M internal x y := by
  obtain ⟨R, ⟨forward, backward, atoms⟩, related⟩ := bisimilar
  exact ⟨R, ⟨forward, backward, fun _ _ rel atom => atoms rel (some atom)⟩, related⟩

/-- **Divergence-respecting weakly bisimilar states diverge together.** -/
theorem divergent_iff_of_divergenceBisimilar {x y : S.Term}
    (bisimilar : DivergenceBisimilar M internal x y) :
    Divergent M internal x ↔ Divergent M internal y :=
  bisimilar_observes (divergence M internal) bisimilar none

end Divergence

end Weak

/-! ## The labelled step with internal labels -/

section Step

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}
variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)
  (internal : L → Prop)

/-- **A weak move of the step**: `τ*` under an internal label, `τ* ℓ τ*` under a visible one. -/
def WeakMoves (C : Configuration T O) (ℓ : L) (D : Configuration T O) : Prop :=
  Weak.Act (system A label offers) internal ℓ C D

/-- **Weak bisimilarity of the step**, with the program's internal labels. -/
def WeakBisimilar (C D : Configuration T O) : Prop :=
  Weak.Bisimilar (system A label offers) internal C D

/-- Weak satisfaction in the step: `⟨⟨ℓ⟩⟩` is the weak move under `ℓ`. -/
def WeakSat (φ : Formula PEmpty.{1} L) (C : Configuration T O) : Prop :=
  Weak.Sat (system A label offers) internal φ C

/-- **Weak trace equivalence of the step.** -/
def WeakTraceEquivalent (C D : Configuration T O) : Prop :=
  Weak.TraceEquivalent (Weak.weak (system A label offers) internal) C D

variable {A label offers internal}

/-- **Strong bisimilarity implies weak bisimilarity in the step.** -/
theorem weakBisimilar_of_bisimilar {C D : Configuration T O}
    (bisimilar : Bisimilar A label offers C D) : WeakBisimilar A label offers internal C D :=
  Weak.bisimilar_of_strong bisimilar

/-- Weakly bisimilar configurations have the same weak traces. -/
theorem weakTraceEquivalent_of_weakBisimilar {C D : Configuration T O}
    (bisimilar : WeakBisimilar A label offers internal C D) :
    WeakTraceEquivalent A label offers internal C D :=
  Weak.traceEquivalent_of_weak bisimilar

variable (A label offers internal) in
/-- **Weak Hennessy–Milner in the step**, for programs whose weak system is image-finite. -/
theorem weakBisimilar_iff_sat
    (finite : (Weak.weak (system A label offers) internal).ImageFiniteModulo) (C D : Configuration T O) :
    WeakBisimilar A label offers internal C D ↔
      ∀ φ : Formula PEmpty.{1} L, (WeakSat A label offers internal φ C ↔ WeakSat A label offers internal φ D) :=
  Weak.bisimilar_iff_sat _ _ finite C D

end Step

#print axioms Weak.chain_resp
#print axioms Weak.silently_trans
#print axioms Weak.act_transfer
#print axioms Weak.bisimilar_iff
#print axioms Weak.bisimilar_of_strong
#print axioms Weak.sat_iff_of_bisimilar
#print axioms Weak.bisimilar_iff_sat
#print axioms Weak.bisimilar_iff_sat_of_cover
#print axioms Weak.trace_of_simulation
#print axioms Weak.bisimilar_of_traceEquivalent
#print axioms Weak.weak_bisimilar_iff_traceEquivalent
#print axioms Weak.inert
#print axioms Weak.inert_silently
#print axioms Weak.push
#print axioms Weak.weaklyDeterminate
#print axioms Weak.confluent_bisimilar_iff_traceEquivalent
#print axioms Weak.divergent_resp
#print axioms Weak.bisimilar_of_divergenceBisimilar
#print axioms Weak.divergent_iff_of_divergenceBisimilar
#print axioms weakBisimilar_of_bisimilar
#print axioms weakBisimilar_iff_sat

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
