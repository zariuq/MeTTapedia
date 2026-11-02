import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations.BagInstances
import Mathlib.Data.Set.Finite.List
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching

/-!
# Unification against the matcher specification

The matcher specification of `SourceMatching` is one-way: a pattern with variables against a
**value**, the label of an occurrence. Its obligations are soundness (every answer is a step),
completeness up to the theory (every step, from an equivalent start, is equivalent to an answer)
and minimality (no two answers equivalent). The HE and PeTTa lanes, and the Prime draft's `match`
today, unify instead: a stored atom may contain variables too, and they are bound as well.

## The meaning of a stored atom with variables

A stored atom `q` with variables is read, as decision §10 reads metavariables, as the model
elements it stands for: its **instances** (`Instance`), the values some substitution solves it to.
A pattern `p` meets `q` from `σ` at `τ` when `τ` is a step of `p` to one of those instances
(`UStep`, the ground meaning of unification with `q`'s variables renamed apart).

* **Against a ground stored atom, unification is one-way matching** (`ustep_ground`): the
  instances of a ground atom are the values equal to it, so a two-way step is an ordinary step. A
  unifier restricted to ground stored atoms is a matcher in the specification's sense, and inherits
  its obligations (`onValues_sound`, `onValues_complete`, `onValues_minimal`).
* **Against a stored atom with variables, no finite list of ground answers is complete**
  (`no_finite_complete_ground_answers`): a bare variable against a stored variable has a step for
  every value, and pairwise distinct values need pairwise distinct answers. So unification is not
  a matcher in the specification's sense there. It needs the **two-way generalization**: answers
  are substitutions into patterns (`PSubst`), standing for their ground instances (`GroundOf`),
  and completeness is up to instantiation (`CompleteFor`), the "complete set of unifiers" of
  unification theory. One pattern-valued answer is then complete where no finite list of ground
  answers is (`Controls.variable_against_variable`).
* **Soundness of a two-way matcher needs the occurs check** (`Controls.occurs_no_step`,
  `Controls.answer_without_step_unsound`): `(p $x $x)` against a stored `(p $y (f $y))` has no
  two-way step, since no finite instance has equal arguments, so a matcher that answers there is
  not sound. SWI-PeTTa answers (it unifies without the occurs check); CeTTa's lanes and HE do not.
* **The literal reading separates from the instance reading** (`Controls.literal_vs_instance`):
  reading the stored variable as a constant, the ground pattern `1` does not match the stored
  variable; reading it by its instances, it does. Every lane answers `yes` to `(r 1)` against a
  stored `(r $y)`, so every lane, Prime's draft included, uses the instance reading.

Counting follows the representation: the lanes make one row per stored occurrence and most general
unifier, not one per ground instance, so the bag of answers of a `match` against stored variables
counts representatives. Two answers of one occurrence that are instances of each other would be
counted twice; minimality up to instantiation (`MinimalFor`) is what forbids it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uV uT uP

variable {V : Type uV} {T : Type uT} {P : Type uP} (L : TermLayer V T P)

/-! ## Two-way steps -/

/-- The **instances** of a stored pattern: the values some substitution solves it to. -/
def Instance (q : P) (t : T) : Prop := ∃ ρ : Subst V T, L.Solves ρ q t

/-- **A two-way step**: `p`, from `σ`, steps to `τ` at some instance of the stored pattern `q`. -/
def UStep (σ : Subst V T) (p q : P) (τ : Subst V T) : Prop := ∃ t, Instance L q t ∧ L.Step σ p t τ

variable {L}

/-- **Against a ground stored atom, a two-way step is a one-way step.** -/
theorem ustep_ground {q : P} {t₀ : T} (ground : IsGround L q t₀) {σ τ : Subst V T} {p : P} :
    UStep L σ p q τ ↔ L.Step σ p t₀ τ := by
  constructor
  · rintro ⟨t, ⟨ρ, u, inst, related⟩, step⟩
    rw [ground ρ] at inst
    cases inst
    exact step.of_equiv (L.equivalence.symm related)
  · intro step
    exact ⟨t₀, ⟨fun _ => none, t₀, ground _, L.equivalence.refl t₀⟩, step⟩

/-! ## Two-way matchers restricted to values -/

/-- A two-way matcher: answers, on the pattern's variables, for a pattern against a stored
pattern. -/
abbrev TwoWay (V : Type uV) (T : Type uT) (P : Type uP) := P → Subst V T → P → List (Subst V T)

variable (L)

/-- Soundness of a two-way matcher with ground answers: every answer is a two-way step. -/
def USound (u : TwoWay V T P) : Prop := ∀ {p σ q τ}, τ ∈ u p σ q → UStep L σ p q τ

/-- Completeness up to the theory, with ground answers. -/
def UComplete (u : TwoWay V T P) : Prop :=
  ∀ {p σ σ' q τ'}, SubstEquiv L.E σ σ' → UStep L σ' p q τ' → ∃ τ ∈ u p σ q, SubstEquiv L.E τ τ'

/-- Minimality with ground answers. -/
def UMinimal (u : TwoWay V T P) : Prop :=
  ∀ p σ q, (u p σ q).Pairwise fun τ τ' => ¬ SubstEquiv L.E τ τ'

variable {L}

/-- A two-way matcher used on values, through a way of writing each value as a ground pattern. -/
def onValues (u : TwoWay V T P) (embed : T → P) : Matcher V T P := fun p σ t => u p σ (embed t)

theorem onValues_sound {u : TwoWay V T P} {embed : T → P} (grounds : ∀ t, IsGround L (embed t) t)
    (sound : USound L u) : Matcher.Sound L (onValues u embed) :=
  fun member => (ustep_ground (grounds _)).mp (sound member)

theorem onValues_complete {u : TwoWay V T P} {embed : T → P} (grounds : ∀ t, IsGround L (embed t) t)
    (complete : UComplete L u) : Matcher.Complete L (onValues u embed) :=
  fun same step => complete same ((ustep_ground (grounds _)).mpr step)

theorem onValues_minimal {u : TwoWay V T P} {embed : T → P} (minimal : UMinimal L u) :
    Matcher.Minimal L (onValues u embed) := fun p σ t => minimal p σ (embed t)

/-! ## Stored variables: no finite list of ground answers is complete -/

/-- **Against a stored atom with infinitely many distinct instances, no finite list of ground
answers is complete**: a bare variable has a step to each instance, and distinct instances need
distinct answers. -/
theorem no_finite_complete_ground_list [DecidableEq V] {x : P} {v : V} (var : IsVarPattern L x v)
    {q : P} (ι : ℕ → T) (instances : ∀ n, Instance L q (ι n))
    (distinct : ∀ n k, L.E (ι n) (ι k) → n = k) (answers : List (Subst V T)) :
    ¬ ∀ τ', UStep L (fun _ => none) x q τ' → ∃ τ ∈ answers, SubstEquiv L.E τ τ' := by
  intro complete
  have stepOf : ∀ n, UStep L (fun _ => none) x q (fun w => if w = v then some (ι n) else none) := by
    intro n
    refine ⟨ι n, instances n, fun _ _ bound => (by simp at bound), fun w notIn => ?_,
      ⟨ι n, ?_, L.equivalence.refl _⟩⟩
    · have : w ≠ v := by rw [var.vars_eq] at notIn; simpa using notIn
      simp [this]
    · rw [var.inst_eq]; simp
  choose τ member related using fun n => complete _ (stepOf n)
  have : Finite {τ' // τ' ∈ answers} := (List.finite_toSet answers).to_subtype
  obtain ⟨n, k, ne, same⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨τ n, member n⟩ : {τ' // τ' ∈ answers}))
  have sameτ : τ n = τ k := congrArg Subtype.val same
  apply ne
  apply distinct
  have atN := related n v
  have atK := related k v
  rw [sameτ] at atN
  simp only [ite_true] at atN atK
  rcases optionRel_iff.mp atN with ⟨-, h⟩ | ⟨a, b, hn, hb, rn⟩
  · cases h
  rcases optionRel_iff.mp atK with ⟨-, h⟩ | ⟨a', b', hk, hb', rk⟩
  · cases h
  rw [hn] at hk
  cases hk
  cases hb
  cases hb'
  exact L.equivalence.trans (L.equivalence.symm rn) rk

/-- **So no two-way matcher with ground answers is complete** against such a stored atom. -/
theorem no_finite_complete_ground_answers [DecidableEq V] {x : P} {v : V} (var : IsVarPattern L x v)
    {q : P} (ι : ℕ → T) (instances : ∀ n, Instance L q (ι n))
    (distinct : ∀ n k, L.E (ι n) (ι k) → n = k) (u : TwoWay V T P) : ¬ UComplete L u :=
  fun complete => no_finite_complete_ground_list var ι instances distinct (u x (fun _ => none) q)
    fun _ step => complete (SubstEquiv.refl L.equivalence _) step

/-! ## The two-way generalization: pattern-valued answers, complete up to instantiation -/

/-- Substitutions into patterns: the answers of a unifier, which may bind a variable to a term with
variables of the stored atom. A `Sources.Subst` whose values are patterns. -/
abbrev PSubst (V : Type uV) (P : Type uP) := Subst V P

variable (L)

/-- **The ground instances of a pattern-valued answer**: one grounding `ρ` of the variables its
terms mention, applied to every binding. -/
def GroundOf (θ : PSubst V P) (τ : Subst V T) : Prop :=
  ∃ ρ : Subst V T, ∀ v, Option.Rel (fun r t => L.Solves ρ r t) (θ v) (τ v)

/-- A list of pattern-valued answers is **sound for a query** when every ground instance of each
answer is a two-way step. -/
def SoundFor (answers : List (PSubst V P)) (p q : P) : Prop :=
  ∀ θ ∈ answers, ∀ τ, GroundOf L θ τ → UStep L (fun _ => none) p q τ

/-- **Complete for a query, up to instantiation**: every two-way step is a ground instance of some
answer. -/
def CompleteFor (answers : List (PSubst V P)) (p q : P) : Prop :=
  ∀ τ, UStep L (fun _ => none) p q τ → ∃ θ ∈ answers, GroundOf L θ τ

/-- **Minimal up to instantiation**: no answer's ground instances are all instances of another. -/
def MinimalFor (answers : List (PSubst V P)) : Prop :=
  answers.Pairwise fun θ θ' =>
    ¬ (∀ τ, GroundOf L θ τ → GroundOf L θ' τ) ∧ ¬ (∀ τ, GroundOf L θ' τ → GroundOf L θ τ)

/-! ## Controls -/

namespace Controls

/-- Patterns over numbers: a variable or a literal. -/
inductive Pat where
  | var (k : ℕ)
  | lit (n : ℕ)
  deriving DecidableEq, Repr

/-- The syntactic layer over numbers. -/
def numLayer : TermLayer ℕ ℕ Pat where
  E := (· = ·)
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  vars := fun
    | .var k => {k}
    | .lit _ => ∅
  inst := fun σ p => match p with
    | .var k => σ k
    | .lit n => some n
  inst_bound := by
    intro σ p
    cases p <;> simp
  inst_local := by
    intro σ τ p same
    cases p with
    | var k => exact same k (by simp)
    | lit n => rfl
  inst_congr := by
    intro σ τ p same
    cases p with
    | var k => exact same k (by simp)
    | lit n => exact Option.Rel.some rfl

theorem var_isVarPattern (k : ℕ) : IsVarPattern numLayer (.var k) k :=
  ⟨rfl, fun _ => rfl⟩

theorem lit_isGround (n : ℕ) : IsGround numLayer (.lit n) n := fun _ => rfl

/-- **A bare variable against a stored variable: no finite list of ground answers is complete.** -/
theorem no_ground_unifier (u : TwoWay ℕ ℕ Pat) : ¬ UComplete numLayer u :=
  no_finite_complete_ground_answers (var_isVarPattern 0) (q := .var 1) id
    (fun n => ⟨fun _ => some n, n, rfl, rfl⟩) (fun _ _ h => h) u

/-- The unifier's answer for `$0` against a stored `$1`: bind `$0` to the stored variable. -/
def varToVar : PSubst ℕ Pat := fun k => if k = 0 then some (.var 1) else none

/-- **One pattern-valued answer is complete where no finite list of ground answers is**: the ground
instances of `$0 ↦ $1` are exactly the two-way steps of `$0` against the stored `$1`. -/
theorem groundOf_varToVar_iff (τ : Subst ℕ ℕ) :
    GroundOf numLayer varToVar τ ↔ UStep numLayer (fun _ => none) (.var 0) (.var 1) τ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ρ, rel⟩
    have at0 := rel 0
    simp only [varToVar, ite_true] at at0
    rcases h0 : τ 0 with _ | t
    · rw [h0] at at0; cases at0
    · rw [h0] at at0
      cases at0 with
      | some sol =>
          refine ⟨t, ⟨ρ, sol⟩, fun _ _ bound => (by simp at bound), fun k notIn => ?_,
            ⟨t, h0, rfl⟩⟩
          have ne : k ≠ 0 := by simpa [numLayer] using notIn
          have atk := rel k
          simp only [varToVar, ne, ite_false] at atk
          rcases hk : τ k with _ | t'
          · rfl
          · rw [hk] at atk; cases atk
  · rintro ⟨t, ⟨ρ, w, hw, eq⟩, step⟩
    refine ⟨fun k => if k = 1 then some t else none, fun k => ?_⟩
    by_cases zero : k = 0
    · subst zero
      obtain ⟨u, inst, rel⟩ := step.solves
      have : τ 0 = some u := inst
      simp only [varToVar, ite_true, this]
      exact Option.Rel.some ⟨t, by simp [numLayer], rel.symm⟩
    · have notIn : k ∉ numLayer.vars (.var 0) := by simpa [numLayer] using zero
      have : τ k = none := step.only k notIn
      simp only [varToVar, zero, ite_false, this]
      exact Option.Rel.none

/-- **One pattern-valued answer is sound, complete and minimal up to instantiation, where no
finite list of ground answers is complete.** -/
theorem variable_against_variable :
    SoundFor numLayer [varToVar] (.var 0) (.var 1) ∧ CompleteFor numLayer [varToVar] (.var 0) (.var 1) ∧
      MinimalFor numLayer [varToVar] ∧
      ∀ answers : List (Subst ℕ ℕ),
        ¬ ∀ τ', UStep numLayer (fun _ => none) (.var 0) (.var 1) τ' →
          ∃ τ ∈ answers, SubstEquiv numLayer.E τ τ' := by
  refine ⟨fun θ member τ ground => ?_, fun τ step => ⟨varToVar, List.mem_singleton_self _,
    (groundOf_varToVar_iff τ).mpr step⟩, List.pairwise_singleton _ _, fun answers =>
    no_finite_complete_ground_list (var_isVarPattern 0) (q := .var 1) id
      (fun n => ⟨fun _ => some n, n, rfl, rfl⟩) (fun _ _ h => h) answers⟩
  rw [List.mem_singleton] at member
  subst member
  exact (groundOf_varToVar_iff τ).mp ground

/-- **The literal reading and the instance reading separate**: the ground pattern `1` against a
stored variable. Read literally (the stored variable a constant, compared by equality), there is
no answer; read by its instances, there is a step. -/
theorem literal_vs_instance :
    constMatcher (V := ℕ) (· = ·) (Pat.lit 1) (fun _ => none) (Pat.var 1) = [] ∧
      UStep numLayer (fun _ => none) (.lit 1) (.var 1) (fun _ => none) := by
  refine ⟨by decide, ⟨1, ⟨fun _ => some 1, 1, rfl, rfl⟩, ⟨Extends.refl _, fun _ _ => rfl, ⟨1, rfl, rfl⟩⟩⟩⟩

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative in
/-- No finite tree is a proper subtree of itself. -/
theorem Tm.ne_node_self_left : ∀ (y : Tm ℕ) (f : ℕ) (r : Tm ℕ), y ≠ .node f y r
  | .leaf _, _, _, h => by cases h
  | .node g l m, f, r, h => by
      injection h with _ hl _
      exact Tm.ne_node_self_left l g m hl

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative in
/-- **`(p $x $x)` against a stored `(p $y (f $y))` has no two-way step** in the syntactic layer:
an instance `(p y (f y))` with equal arguments would make `y` a proper subtree of itself. -/
theorem occurs_no_step :
    ∀ τ, ¬ UStep (termLayer (V := ℕ) (F := ℕ) fun _ => false) (fun _ => none)
      (.node 0 (.var 0) (.var 0) : Commutative.Pat ℕ ℕ)
      (.node 0 (.var 1) (.node 1 (.var 1) (.leaf 2))) τ := by
  rintro τ ⟨t, ⟨ρ, u, inst, related⟩, step⟩
  have ut : u = t := syntactic_E_iff.mp related
  subst ut
  obtain ⟨w, instP, relP⟩ := step.solves
  have wu : w = u := syntactic_E_iff.mp relP
  subst wu
  obtain ⟨l, r, hl, hr, rfl⟩ := Pat.inst_node_eq_some.mp instP
  obtain ⟨l', r', hl', hr', same⟩ := Pat.inst_node_eq_some.mp inst
  obtain ⟨l'', r'', hl'', hr'', rfl⟩ := Pat.inst_node_eq_some.mp hr'
  injection same with _ el er
  have vars : l = r := by
    have a : (Commutative.Pat.var 0 : Commutative.Pat ℕ ℕ).inst τ = some l := hl
    have b : (Commutative.Pat.var 0 : Commutative.Pat ℕ ℕ).inst τ = some r := hr
    rw [a] at b
    exact Option.some.inj b
  have y : l'' = l' := by
    have a : (Commutative.Pat.var 1 : Commutative.Pat ℕ ℕ).inst ρ = some l' := hl'
    have b : (Commutative.Pat.var 1 : Commutative.Pat ℕ ℕ).inst ρ = some l'' := hl''
    rw [a] at b
    exact (Option.some.inj b).symm
  have loop : l = .node 1 l r'' :=
    calc l = r := vars
      _ = .node 1 l'' r'' := er
      _ = .node 1 l r'' := by rw [y, ← el]
  exact Tm.ne_node_self_left l 1 r'' loop

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative in
/-- **A two-way matcher that answers at that query is not sound.** -/
theorem answer_without_step_unsound (u : TwoWay ℕ (Tm ℕ) (Commutative.Pat ℕ ℕ))
    (answers : u (.node 0 (.var 0) (.var 0) : Commutative.Pat ℕ ℕ) (fun _ => none)
      (.node 0 (.var 1) (.node 1 (.var 1) (.leaf 2))) ≠ []) :
    ¬ USound (termLayer (V := ℕ) (F := ℕ) fun _ => false) u := by
  intro sound
  obtain ⟨τ, member⟩ := List.exists_mem_of_ne_nil _ answers
  exact occurs_no_step τ (sound member)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations
