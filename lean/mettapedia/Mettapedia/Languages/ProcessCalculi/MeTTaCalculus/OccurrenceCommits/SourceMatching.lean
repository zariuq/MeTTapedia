import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits
import Batteries.Data.List.Pairwise

/-!
# Matching modulo a declared theory, as a parameter

The commits of `Commits` are ground: they name occurrences. A `transform` names them through
patterns with variables. This module fixes what a pattern means, independently of any matching
algorithm, and states what a matcher must do.

## The term layer

A **term layer** (`TermLayer`) has values `T` (the labels of occurrences), patterns `P` with their
variables `vars`, instantiation `inst` of a pattern under a partial substitution, and a declared
equational theory `E`, an equivalence on values. Successful instantiation requires all pattern
variables to be bound (`inst_bound`). Instantiation may also check contextual scope. The stronger
property that every fully bound pattern instantiates is recorded separately as `TermLayer.Total`.
Instantiation depends only on the pattern's variables, up to `E` (`inst_local`, `inst_congr`).
The latter law is where `E` is a congruence.

Metavariables range over values modulo `E`: a pattern `p` **solves** a value `t` under `σ` when
`pσ =_E t` (`Solves`). A **step** of `p` against `t` from `σ` binds exactly the variables of `p`
that `σ` leaves free, and solves (`Step`). A repeated variable therefore means equality modulo
`E`, and syntactic matching is the case where `E` is equality.

## The matcher specification

A matcher returns, for a pattern, a substitution and a value, a list of substitutions. It is

* **sound** when every answer is a step (`Matcher.Sound`);
* **complete** when every step from an `E`-equivalent start is `E`-equivalent to an answer
  (`Matcher.Complete`): starting from `E`-equivalent substitutions is what lets later sources reuse
  the answers of earlier ones;
* **minimal** when no two answers are `E`-equivalent (`Matcher.Minimal`): the answers are
  representatives of the model-level solutions, each once. A row of a transform is counted by
  `every` and by the bag of answers, so a redundant matcher double-counts.

These are hypotheses on a matcher, not properties of an algorithm. `CommutativeMatching` gives two
matchers that satisfy all three; the controls give one that is sound and not complete.

## Regions

The region of a pattern under `σ` is the set of values some step reaches (`Covers`). The matcher
computes it (`region`): a value is in it when the matcher answers. A sound matcher's region lies
inside the semantic region; a complete one's contains it (`region_eq_true_iff`). The semantic
region is closed under `E` (`Covers.of_equiv`), does not change between `E`-equivalent
substitutions (`covers_iff_of_equiv`), and shrinks as the substitution grows
(`Covers.of_extends`): binding more variables never lets a pattern see more. With a sound and
complete matcher the computed region has the same three laws (`RegionMonotone`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uV uT uP

/-- Partial substitutions from variables to values. -/
abbrev Subst (V : Type uV) (T : Type uT) := V → Option T

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-- `τ` extends `σ`: every binding of `σ` is a binding of `τ`. -/
def Extends (σ τ : Subst V T) : Prop := ∀ v t, σ v = some t → τ v = some t

theorem Extends.refl (σ : Subst V T) : Extends σ σ := fun _ _ bound => bound

theorem Extends.trans {σ τ υ : Subst V T} (first : Extends σ τ) (second : Extends τ υ) :
    Extends σ υ := fun v t bound => second v t (first v t bound)

/-- Two substitutions agree modulo `E`: they bind the same variables, to `E`-equal values. -/
def SubstEquiv (E : T → T → Prop) (σ τ : Subst V T) : Prop := ∀ v, Option.Rel E (σ v) (τ v)

section Equiv

variable {E : T → T → Prop}

/-- The two shapes of an `Option.Rel`. -/
theorem optionRel_iff {a b : Option T} :
    Option.Rel E a b ↔ (a = none ∧ b = none) ∨ ∃ x y, a = some x ∧ b = some y ∧ E x y := by
  constructor
  · intro rel
    cases rel with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some related => exact Or.inr ⟨_, _, rfl, rfl, related⟩
  · rintro (⟨rfl, rfl⟩ | ⟨x, y, rfl, rfl, related⟩)
    · exact Option.Rel.none
    · exact Option.Rel.some related

theorem optionRel_refl (equivalence : Equivalence E) (a : Option T) : Option.Rel E a a := by
  cases a with
  | none => exact Option.Rel.none
  | some t => exact Option.Rel.some (equivalence.refl t)

theorem SubstEquiv.refl (equivalence : Equivalence E) (σ : Subst V T) : SubstEquiv E σ σ :=
  fun v => optionRel_refl equivalence (σ v)

theorem SubstEquiv.symm (equivalence : Equivalence E) {σ τ : Subst V T} (same : SubstEquiv E σ τ) :
    SubstEquiv E τ σ := by
  intro v
  rcases optionRel_iff.mp (same v) with ⟨h1, h2⟩ | ⟨x, y, h1, h2, related⟩
  · rw [h1, h2]; exact Option.Rel.none
  · rw [h1, h2]; exact Option.Rel.some (equivalence.symm related)

theorem SubstEquiv.trans (equivalence : Equivalence E) {σ τ υ : Subst V T}
    (first : SubstEquiv E σ τ) (second : SubstEquiv E τ υ) : SubstEquiv E σ υ := by
  intro v
  rcases optionRel_iff.mp (first v) with ⟨h1, h2⟩ | ⟨x, y, h1, h2, related⟩ <;>
    rcases optionRel_iff.mp (second v) with ⟨k1, k2⟩ | ⟨x', y', k1, k2, related'⟩
  · rw [h1, k2]; exact Option.Rel.none
  · rw [h2] at k1; cases k1
  · rw [h2] at k1; cases k1
  · rw [h2] at k1
    cases k1
    rw [h1, k2]
    exact Option.Rel.some (equivalence.trans related related')

/-- Equality of substitutions is equivalence modulo equality. -/
theorem substEquiv_eq_iff {σ τ : Subst V T} : SubstEquiv (· = ·) σ τ ↔ σ = τ := by
  constructor
  · intro same
    funext v
    rcases optionRel_iff.mp (same v) with ⟨h1, h2⟩ | ⟨x, y, h1, h2, related⟩
    · rw [h1, h2]
    · rw [h1, h2, related]
  · rintro rfl
    exact SubstEquiv.refl ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩ σ

end Equiv

/-- **A term layer**: values with a declared equational theory, patterns with variables, and
instantiation. -/
structure TermLayer (V : Type uV) (T : Type uT) (P : Type uP) where
  /-- The declared theory: which values are equal. -/
  E : T → T → Prop
  equivalence : Equivalence E
  /-- The variables of a pattern. -/
  vars : P → Finset V
  /-- Instantiate a pattern, checking bindings and any contextual constraints. -/
  inst : Subst V T → P → Option T
  /-- Successful instantiation requires every pattern variable to be bound. -/
  inst_bound : ∀ σ p, (inst σ p).isSome → ∀ v ∈ vars p, (σ v).isSome
  /-- Instantiation depends only on the pattern's variables. -/
  inst_local : ∀ σ τ p, (∀ v ∈ vars p, σ v = τ v) → inst σ p = inst τ p
  /-- `E` is a congruence for instantiation. -/
  inst_congr : ∀ σ τ p, (∀ v ∈ vars p, Option.Rel E (σ v) (τ v)) →
    Option.Rel E (inst σ p) (inst τ p)

namespace TermLayer

variable (L : TermLayer V T P)

/-- A total layer has no additional refusal after all its variables are bound. -/
def Total : Prop :=
  ∀ σ p, (∀ v ∈ L.vars p, (σ v).isSome) → (L.inst σ p).isSome

/-- Exact definedness is an additional property, not a restriction on scoped layers. -/
theorem Total.inst_isSome (total : L.Total) (σ : Subst V T) (p : P) :
    (L.inst σ p).isSome ↔ ∀ v ∈ L.vars p, (σ v).isSome :=
  ⟨L.inst_bound σ p, total σ p⟩

/-- `pσ =_E t`. -/
def Solves (σ : Subst V T) (p : P) (t : T) : Prop := ∃ u, L.inst σ p = some u ∧ L.E u t

/-- **A step**: `τ` binds the variables of `p` that `σ` leaves free, nothing else, and solves. -/
structure Step (σ : Subst V T) (p : P) (t : T) (τ : Subst V T) : Prop where
  extends_ : Extends σ τ
  only : ∀ v, v ∉ L.vars p → τ v = σ v
  solves : L.Solves τ p t

/-- **The semantic region** of a pattern under a substitution: the values some step reaches. -/
def Covers (σ : Subst V T) (p : P) (t : T) : Prop := ∃ τ, L.Step σ p t τ

variable {L}

/-- A value `E`-equal to a solved value is solved. -/
theorem Solves.of_equiv {σ : Subst V T} {p : P} {t t' : T} (solves : L.Solves σ p t)
    (related : L.E t t') : L.Solves σ p t' := by
  obtain ⟨u, inst, same⟩ := solves
  exact ⟨u, inst, L.equivalence.trans same related⟩

theorem Step.of_equiv {σ τ : Subst V T} {p : P} {t t' : T} (step : L.Step σ p t τ)
    (related : L.E t t') : L.Step σ p t' τ :=
  ⟨step.extends_, step.only, step.solves.of_equiv related⟩

/-- **The semantic region is closed under `E`.** -/
theorem Covers.of_equiv {σ : Subst V T} {p : P} {t t' : T} (covers : L.Covers σ p t)
    (related : L.E t t') : L.Covers σ p t' := by
  obtain ⟨τ, step⟩ := covers
  exact ⟨τ, step.of_equiv related⟩

/-- After a step, a variable is bound exactly when it was bound before or occurs in the pattern. -/
theorem Step.isSome_iff {σ τ : Subst V T} {p : P} {t : T} (step : L.Step σ p t τ) (v : V) :
    (τ v).isSome ↔ (σ v).isSome ∨ v ∈ L.vars p := by
  constructor
  · intro bound
    by_cases inVars : v ∈ L.vars p
    · exact Or.inr inVars
    · rw [step.only v inVars] at bound
      exact Or.inl bound
  · rintro (bound | inVars)
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp bound
      rw [step.extends_ v u hu]
      rfl
    · obtain ⟨u, inst, -⟩ := step.solves
      have defined : (L.inst τ p).isSome := by rw [inst]; rfl
      exact L.inst_bound τ p defined v inVars

section Decidable

variable [DecidableEq V]

/-- Overwrite the variables of a pattern: `σ` outside them, `τ` on them. -/
def onVars (L : TermLayer V T P) (p : P) (σ τ : Subst V T) : Subst V T :=
  fun v => if v ∈ L.vars p then τ v else σ v

/-- **Binding more variables never lets a pattern see more.** -/
theorem Covers.of_extends {σ τ : Subst V T} {p : P} {t : T} (grows : Extends σ τ)
    (covers : L.Covers τ p t) : L.Covers σ p t := by
  obtain ⟨υ, step⟩ := covers
  refine ⟨L.onVars p σ υ, ⟨?_, ?_, ?_⟩⟩
  · intro v u bound
    unfold onVars
    split_ifs with inVars
    · exact step.extends_ v u (grows v u bound)
    · exact bound
  · intro v notIn
    simp [onVars, notIn]
  · obtain ⟨u, inst, same⟩ := step.solves
    refine ⟨u, ?_, same⟩
    rw [← inst]
    exact L.inst_local _ _ p fun v inVars => by simp [onVars, inVars]

/-- **The semantic region does not change between `E`-equivalent substitutions.** -/
theorem Covers.of_substEquiv {σ σ' : Subst V T} {p : P} {t : T} (same : SubstEquiv L.E σ σ')
    (covers : L.Covers σ' p t) : L.Covers σ p t := by
  obtain ⟨τ', step⟩ := covers
  let τ : Subst V T := fun v => if v ∈ L.vars p ∧ σ v = none then τ' v else σ v
  refine ⟨τ, ⟨?_, ?_, ?_⟩⟩
  · intro v u bound
    simp [τ, bound]
  · intro v notIn
    simp [τ, notIn]
  · obtain ⟨u', inst', related'⟩ := step.solves
    have rel : Option.Rel L.E (L.inst τ p) (L.inst τ' p) := by
      refine L.inst_congr τ τ' p fun v inVars => ?_
      by_cases free : σ v = none
      · have : τ v = τ' v := by simp [τ, inVars, free]
        rw [this]
        exact optionRel_refl L.equivalence _
      · obtain ⟨u, bound⟩ := Option.ne_none_iff_exists'.mp free
        have tauV : τ v = some u := by simp [τ, bound]
        rcases optionRel_iff.mp (same v) with ⟨h1, -⟩ | ⟨x, w, h1, h2, related⟩
        · rw [bound] at h1; cases h1
        · rw [bound] at h1
          cases h1
          have tau'V : τ' v = some w := step.extends_ v w h2
          rw [tauV, tau'V]
          exact Option.Rel.some related
    rw [inst'] at rel
    rcases optionRel_iff.mp rel with ⟨-, h2⟩ | ⟨w, x, h1, h2, related⟩
    · cases h2
    · cases h2
      exact ⟨w, h1, L.equivalence.trans related related'⟩

theorem covers_iff_of_substEquiv {σ σ' : Subst V T} {p : P} {t : T}
    (same : SubstEquiv L.E σ σ') : L.Covers σ p t ↔ L.Covers σ' p t :=
  ⟨Covers.of_substEquiv (SubstEquiv.symm L.equivalence same), Covers.of_substEquiv same⟩

end Decidable

end TermLayer

/-! ## Matchers -/

/-- A matcher: for a pattern, a substitution and a value, a list of answers. -/
abbrev Matcher (V : Type uV) (T : Type uT) (P : Type uP) := P → Subst V T → T → List (Subst V T)

namespace Matcher

variable (L : TermLayer V T P) (m : Matcher V T P)

/-- **Soundness**: every answer is a step. -/
def Sound : Prop := ∀ {p σ t τ}, τ ∈ m p σ t → L.Step σ p t τ

/-- **Completeness up to `E`**: every step from an `E`-equivalent start is `E`-equivalent to an
answer. -/
def Complete : Prop :=
  ∀ {p σ σ' t τ'}, SubstEquiv L.E σ σ' → L.Step σ' p t τ' → ∃ τ ∈ m p σ t, SubstEquiv L.E τ τ'

/-- **Minimality**: no two answers are `E`-equivalent. -/
def Minimal : Prop := ∀ p σ t, (m p σ t).Pairwise fun τ τ' => ¬ SubstEquiv L.E τ τ'

/-- A matcher is **unitary** when it gives at most one answer per value. -/
def Unitary : Prop := ∀ p σ t, (m p σ t).length ≤ 1

/-- **The computed region**: the values for which the matcher answers. -/
def region (σ : Subst V T) (p : P) : T → Bool := fun t => !(m p σ t).isEmpty

variable {L m}

theorem region_eq_true_iff_exists {σ : Subst V T} {p : P} {t : T} :
    region m σ p t = true ↔ ∃ τ, τ ∈ m p σ t := by
  unfold region
  cases h : m p σ t with
  | nil => simp
  | cons τ rest => simp

/-- A sound matcher's region lies inside the semantic region. -/
theorem Sound.covers (sound : Sound L m) {σ : Subst V T} {p : P} {t : T}
    (inRegion : region m σ p t = true) : L.Covers σ p t := by
  obtain ⟨τ, answer⟩ := region_eq_true_iff_exists.mp inRegion
  exact ⟨τ, sound answer⟩

/-- A complete matcher's region contains the semantic region. -/
theorem Complete.region (complete : Complete L m) {σ : Subst V T} {p : P} {t : T}
    (covers : L.Covers σ p t) : region m σ p t = true := by
  obtain ⟨τ', step⟩ := covers
  obtain ⟨τ, answer, -⟩ := complete (SubstEquiv.refl L.equivalence σ) step
  exact region_eq_true_iff_exists.mpr ⟨τ, answer⟩

/-- **With a sound and complete matcher the computed region is the semantic region.** -/
theorem region_eq_true_iff (sound : Sound L m) (complete : Complete L m) {σ : Subst V T} {p : P}
    {t : T} : region m σ p t = true ↔ L.Covers σ p t :=
  ⟨sound.covers, complete.region⟩

/-- **The computed regions are monotone**: binding more variables never lets the matcher answer
for more values. This is what an `every` needs for its completeness queries. -/
def RegionMonotone (m : Matcher V T P) : Prop :=
  ∀ {σ τ : Subst V T} {p : P} {t : T}, Extends σ τ → region m τ p t = true → region m σ p t = true

theorem regionMonotone_of_sound_complete [DecidableEq V] (sound : Sound L m)
    (complete : Complete L m) : RegionMonotone m := by
  intro σ τ p t grows inRegion
  exact complete.region (TermLayer.Covers.of_extends grows (sound.covers inRegion))

/-- With a sound and complete matcher, the computed region is the same for `E`-equivalent
substitutions. -/
theorem region_congr [DecidableEq V] (sound : Sound L m) (complete : Complete L m)
    {σ σ' : Subst V T} (same : SubstEquiv L.E σ σ') (p : P) : region m σ p = region m σ' p := by
  funext t
  apply Bool.eq_iff_iff.mpr
  rw [region_eq_true_iff sound complete, region_eq_true_iff sound complete]
  exact TermLayer.covers_iff_of_substEquiv same

end Matcher

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
