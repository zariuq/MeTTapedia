import Mettapedia.Logic.LP.TotalUnification
import Mettapedia.Logic.LP.StandardizeApart

/-!
# A conjunction of patterns as one unification problem

A conjunctive query meets one stored row per pattern.  The rows' variables are
copied apart from the query's and from each other, so the rows of one candidate
solution form a single system of equations, one group per pattern.

**Leg by leg is all at once.**  A most general unifier of a first group,
composed with a most general unifier of the rest under it, is a most general
unifier of the whole system (`IsMGU.comp_append`), and the whole system is
solvable exactly when the rest is solvable under the first group's unifier
(`unifiable_append_iff`).  Solving the groups one after another with the total
unifier (`solveLegs`) accepts exactly the solvable systems and returns a most
general unifier of each (`solveLegs_isMGU`, `solveLegs_eq_none_iff`).

**The order of the legs is free.**  Two most general unifiers of one system
are instances of each other (`IsMGU.instance_of`).  Two orders of the legs
accept the same systems (`solveLegs_perm_isSome`) and instantiate a template
to instances of each other (`solveLegs_perm_instances`), which are equal when
either is ground (`solveLegs_perm_ground`).

**One-way matching.**  Against a ground side, unifying is matching: some
substitution sends the other side to it (`unifiable_ground_right_iff`), and
the occurs check has nothing to find (`occursIn_eq_false_of_isGround`).
Over hash-consed terms two shortcuts are exact: an equation between equal ids
constrains nothing (`unifies_cons_self`), and one between distinct ground ids
has no unifier (`not_unifiable_of_ground_ne`).

**Meeting.**  Two terms meet when they have a common instance, their variables
taken apart (`CommonInstance`).  A matcher that accepts a row, an addition
that a later read would accept and a removal that deletes a row are all cases
of meeting.  An instance of a term meets only what the term meets
(`CommonInstance.of_instances`): a template that meets no pattern has no
instance that meets an instance of the pattern, so a test on templates decides
a property of every solution.  Over ground terms meeting is equality
(`commonInstance_ground_iff`).  Meeting is decided by unifying the two terms
copied into different activation scopes (`commonInstance_iff_unifiable_atScope`).

Controls: a variable equated with a term that contains it has no unifier
(`Controls.occurs_no_unifier`); a stored row whose variables two legs share,
instead of each leg using its own copy, constrains both legs at once and loses
the solution the copies have (`Controls.copies_unifiable`,
`Controls.shared_not_unifiable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.ConjunctiveUnification

open Mettapedia.Logic.LP

variable {σ : LPSignature}

/-- A system of equations between terms. -/
abbrev Equations (σ : LPSignature) := List (Term σ × Term σ)

/-! ## Unifiers of a system -/

/-- Some substitution unifies every equation of the system. -/
def Unifiable (equations : Equations σ) : Prop :=
  ∃ δ : Subst σ, Unifies δ equations

/-- `θ` unifies the system, and every unifier of it is an instance of `θ`. -/
def IsMGU (θ : Subst σ) (equations : Equations σ) : Prop :=
  Unifies θ equations ∧ ∀ δ : Subst σ, Unifies δ equations → θ.moreGeneral δ

theorem moreGeneral_iff {θ δ : Subst σ} :
    θ.moreGeneral δ ↔ ∃ ρ : Subst σ, δ = ρ ∘ₛ θ := by
  constructor
  · rintro ⟨ρ, h⟩
    exact ⟨ρ, funext h⟩
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ, fun _ => rfl⟩

theorem unifies_append {δ : Subst σ} {first rest : Equations σ} :
    Unifies δ (first ++ rest) ↔ Unifies δ first ∧ Unifies δ rest := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
      fun p hp => h p (List.mem_append_right _ hp)⟩
  · rintro ⟨h₁, h₂⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h₁ p hp
    · exact h₂ p hp

theorem unifies_of_subset {δ : Subst σ} {small large : Equations σ}
    (sub : ∀ p ∈ small, p ∈ large) (h : Unifies δ large) : Unifies δ small :=
  fun p hp => h p (sub p hp)

theorem Unifiable.of_subset {small large : Equations σ}
    (sub : ∀ p ∈ small, p ∈ large) : Unifiable large → Unifiable small :=
  fun ⟨δ, h⟩ => ⟨δ, unifies_of_subset sub h⟩

/-- A unifier of the instantiated system is a unifier of the system after the
instantiation. -/
theorem unifies_applyEqs {δ θ : Subst σ} {equations : Equations σ} :
    Unifies δ (θ.applyEqs equations) ↔ Unifies (δ ∘ₛ θ) equations := by
  constructor
  · intro h p hp
    obtain ⟨s, t⟩ := p
    have := h _ (List.mem_map.mpr ⟨(s, t), hp, rfl⟩)
    simpa [Subst.applyTerm_comp] using this
  · intro h q hq
    obtain ⟨⟨s, t⟩, hp, rfl⟩ := List.mem_map.mp hq
    have := h (s, t) hp
    simpa [Subst.applyTerm_comp] using this

theorem unifies_perm {δ : Subst σ} {first second : Equations σ}
    (perm : first.Perm second) : Unifies δ first ↔ Unifies δ second :=
  ⟨fun h p hp => h p (perm.mem_iff.mpr hp), fun h p hp => h p (perm.mem_iff.mp hp)⟩

theorem IsMGU.of_perm {θ : Subst σ} {first second : Equations σ}
    (perm : first.Perm second) (h : IsMGU θ first) : IsMGU θ second :=
  ⟨(unifies_perm perm).mp h.1, fun δ hδ => h.2 δ ((unifies_perm perm).mpr hδ)⟩

/-- The identity is a most general unifier of the empty system. -/
theorem isMGU_nil : IsMGU (Subst.id σ) ([] : Equations σ) :=
  ⟨fun _ h => by simp at h, fun δ _ => Subst.id_moreGeneral δ⟩

/-- **Leg by leg is all at once.**  A most general unifier of the first group,
composed with a most general unifier of the rest under it, is a most general
unifier of the whole system. -/
theorem IsMGU.comp_append {θ₁ θ₂ : Subst σ} {first rest : Equations σ}
    (h₁ : IsMGU θ₁ first) (h₂ : IsMGU θ₂ (θ₁.applyEqs rest)) :
    IsMGU (θ₂ ∘ₛ θ₁) (first ++ rest) := by
  refine ⟨unifies_append.mpr ⟨fun p hp => ?_, unifies_applyEqs.mp h₂.1⟩, fun δ hδ => ?_⟩
  · simp only [Subst.applyTerm_comp]
    rw [h₁.1 p hp]
  · obtain ⟨hfirst, hrest⟩ := unifies_append.mp hδ
    obtain ⟨ρ₁, rfl⟩ := moreGeneral_iff.mp (h₁.2 δ hfirst)
    have restUnified : Unifies ρ₁ (θ₁.applyEqs rest) := unifies_applyEqs.mpr hrest
    obtain ⟨ρ₂, rfl⟩ := moreGeneral_iff.mp (h₂.2 ρ₁ restUnified)
    exact moreGeneral_iff.mpr ⟨ρ₂, Subst.comp_assoc ρ₂ θ₂ θ₁⟩

/-- The whole system is solvable exactly when the rest is solvable under a
most general unifier of the first group. -/
theorem unifiable_append_iff {θ₁ : Subst σ} {first rest : Equations σ}
    (h₁ : IsMGU θ₁ first) :
    Unifiable (first ++ rest) ↔ Unifiable (θ₁.applyEqs rest) := by
  constructor
  · rintro ⟨δ, hδ⟩
    obtain ⟨hfirst, hrest⟩ := unifies_append.mp hδ
    obtain ⟨ρ, rfl⟩ := moreGeneral_iff.mp (h₁.2 δ hfirst)
    exact ⟨ρ, unifies_applyEqs.mpr hrest⟩
  · rintro ⟨δ, hδ⟩
    refine ⟨δ ∘ₛ θ₁, unifies_append.mpr ⟨fun p hp => ?_, unifies_applyEqs.mp hδ⟩⟩
    simp only [Subst.applyTerm_comp]
    rw [h₁.1 p hp]

/-- Two most general unifiers of one system: each instantiates a term to an
instance of what the other makes of it. -/
theorem IsMGU.instance_of {θ θ' : Subst σ} {equations : Equations σ}
    (h : IsMGU θ equations) (h' : IsMGU θ' equations) (t : Term σ) :
    ∃ ρ : Subst σ, θ'.applyTerm t = ρ.applyTerm (θ.applyTerm t) := by
  obtain ⟨ρ, hρ⟩ := moreGeneral_iff.mp (h.2 θ' h'.1)
  exact ⟨ρ, by rw [hρ, Subst.applyTerm_comp]⟩

/-! ## Ground terms -/

/-- Every substitution fixes a ground term. -/
theorem applyTerm_of_isGround (θ : Subst σ) {t : Term σ} (ground : t.isGround) :
    θ.applyTerm t = t := by
  induction t with
  | var v => exact (ground : False).elim
  | const c => rfl
  | app f ts ih =>
      simp only [Subst.applyTerm_app]
      congr 1
      funext i
      exact ih i (ground i)

/-- An instance of a ground term under one most general unifier is the
instance under every other. -/
theorem IsMGU.ground_instance_eq {θ θ' : Subst σ} {equations : Equations σ}
    (h : IsMGU θ equations) (h' : IsMGU θ' equations) {t : Term σ}
    (ground : (θ.applyTerm t).isGround) : θ'.applyTerm t = θ.applyTerm t := by
  obtain ⟨ρ, hρ⟩ := h.instance_of h' t
  rw [hρ, applyTerm_of_isGround ρ ground]

/-- **Identical sides need no work**: equal ids name equal terms, whose
equation constrains nothing. -/
theorem unifies_cons_self {δ : Subst σ} {t : Term σ} {equations : Equations σ} :
    Unifies δ ((t, t) :: equations) ↔ Unifies δ equations := by
  constructor
  · intro h p hp
    exact h p (List.mem_cons_of_mem _ hp)
  · intro h p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    · exact h p hp

/-- **Distinct ground sides fail at once**: ground terms that differ, as
distinct ids of ground terms do, are equated by no substitution. -/
theorem not_unifiable_of_ground_ne {s t : Term σ} (gs : s.isGround) (gt : t.isGround)
    (different : s ≠ t) (equations : Equations σ) : ¬ Unifiable ((s, t) :: equations) := by
  rintro ⟨δ, h⟩
  have equal := h (s, t) List.mem_cons_self
  rw [applyTerm_of_isGround δ gs, applyTerm_of_isGround δ gt] at equal
  exact different equal

/-- **One-way matching.**  Against a ground right side, a system of one
equation is solvable exactly when some substitution sends the left side to
the right side. -/
theorem unifiable_ground_right_iff {s t : Term σ} (ground : t.isGround) :
    Unifiable [(s, t)] ↔ ∃ θ : Subst σ, θ.applyTerm s = t := by
  constructor
  · rintro ⟨δ, hδ⟩
    refine ⟨δ, ?_⟩
    have equal := hδ (s, t) (List.mem_singleton_self _)
    rwa [applyTerm_of_isGround δ ground] at equal
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp
    subst hp
    show θ.applyTerm s = θ.applyTerm t
    rw [hθ, applyTerm_of_isGround θ ground]

/-- The occurs check finds nothing in a ground term. -/
theorem occursIn_eq_false_of_isGround [DecidableEq σ.vars] (v : σ.vars) {t : Term σ}
    (ground : t.isGround) : t.occursIn v = false := by
  induction t with
  | var w => exact (ground : False).elim
  | const c => rfl
  | app f ts ih =>
      simp only [Term.occursIn, List.any_eq_false]
      intro i _
      simp [ih i (ground i)]

/-! ## Solving the legs one after another -/

section Solve

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem isMGU_of_unifyTotal {equations : Equations σ} {θ : Subst σ}
    (h : unifyTotal equations = some θ) : IsMGU θ equations :=
  ⟨unifyTotal_sound equations θ h, fun δ hδ => unifyTotal_mgu equations θ h δ hδ⟩

theorem unifyTotal_eq_none_iff {equations : Equations σ} :
    unifyTotal equations = none ↔ ¬ Unifiable equations :=
  unifyTotal_none_iff_not_unifiable equations

instance (equations : Equations σ) : Decidable (Unifiable equations) :=
  decidable_of_iff ((unifyTotal equations).isSome = true) <| by
    constructor
    · intro h
      obtain ⟨θ, hθ⟩ := Option.isSome_iff_exists.mp h
      exact ⟨θ, unifyTotal_sound equations θ hθ⟩
    · intro h
      cases hu : unifyTotal equations with
      | none => exact absurd h (unifyTotal_eq_none_iff.mp hu)
      | some θ => rfl

/-- The legs' groups of equations, each solved under the unifier of the ones
before it, as a nested query solves its patterns. -/
def solveLegs : Subst σ → List (Equations σ) → Option (Subst σ)
  | θ, [] => some θ
  | θ, leg :: legs =>
      match unifyTotal (θ.applyEqs leg) with
      | none => none
      | some μ => solveLegs (μ ∘ₛ θ) legs

/-- Solving leg by leg returns a most general unifier of everything solved. -/
theorem solveLegs_isMGU : ∀ (legs : List (Equations σ)) {θ θ' : Subst σ}
    {solved : Equations σ},
    IsMGU θ solved → solveLegs θ legs = some θ' → IsMGU θ' (solved ++ legs.flatten)
  | [], θ, θ', solved, h, hs => by
      simp only [solveLegs, Option.some.injEq] at hs
      subst hs
      simpa using h
  | leg :: legs, θ, θ', solved, h, hs => by
      simp only [solveLegs] at hs
      split at hs
      · exact absurd hs (by simp)
      · rename_i μ hμ
        have step := h.comp_append (isMGU_of_unifyTotal hμ)
        have := solveLegs_isMGU legs step hs
        simpa [List.flatten_cons, List.append_assoc] using this

/-- Solving leg by leg fails exactly on an unsolvable system. -/
theorem solveLegs_eq_none_iff : ∀ (legs : List (Equations σ)) {θ : Subst σ}
    {solved : Equations σ},
    IsMGU θ solved → (solveLegs θ legs = none ↔ ¬ Unifiable (solved ++ legs.flatten))
  | [], θ, solved, h => by
      simp only [solveLegs, List.flatten_nil, List.append_nil, reduceCtorEq, false_iff,
        not_not]
      exact ⟨θ, h.1⟩
  | leg :: legs, θ, solved, h => by
      simp only [solveLegs]
      split
      · rename_i hnone
        simp only [true_iff]
        intro whole
        have part : Unifiable (solved ++ leg) :=
          whole.of_subset fun p hp => by
            rcases List.mem_append.mp hp with hp | hp
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (by simp [List.flatten_cons, hp])
        exact unifyTotal_eq_none_iff.mp hnone ((unifiable_append_iff h).mp part)
      · rename_i μ hμ
        have step := h.comp_append (isMGU_of_unifyTotal hμ)
        rw [solveLegs_eq_none_iff legs step]
        simp [List.flatten_cons, List.append_assoc]

theorem solveLegs_isSome_iff (legs : List (Equations σ)) :
    (solveLegs (Subst.id σ) legs).isSome = true ↔ Unifiable legs.flatten := by
  have key := solveLegs_eq_none_iff legs (isMGU_nil (σ := σ))
  rw [List.nil_append] at key
  cases hs : solveLegs (Subst.id σ) legs with
  | none => simpa [hs] using key
  | some θ =>
      simp only [Option.isSome_some, true_iff]
      by_contra hn
      exact absurd (key.mpr hn) (by simp [hs])

/-- **The order of the legs changes no verdict.** -/
theorem solveLegs_perm_isSome {legs legs' : List (Equations σ)} (perm : legs.Perm legs') :
    (solveLegs (Subst.id σ) legs).isSome = (solveLegs (Subst.id σ) legs').isSome := by
  have flat := perm.flatten
  rw [Bool.eq_iff_iff, solveLegs_isSome_iff, solveLegs_isSome_iff]
  exact ⟨fun ⟨δ, h⟩ => ⟨δ, (unifies_perm flat).mp h⟩,
    fun ⟨δ, h⟩ => ⟨δ, (unifies_perm flat).mpr h⟩⟩

/-- **The order of the legs changes an answer only up to instances**: the
template's instances under two orders are instances of each other. -/
theorem solveLegs_perm_instances {legs legs' : List (Equations σ)} (perm : legs.Perm legs')
    {θ θ' : Subst σ} (h : solveLegs (Subst.id σ) legs = some θ)
    (h' : solveLegs (Subst.id σ) legs' = some θ') (t : Term σ) :
    (∃ ρ : Subst σ, θ'.applyTerm t = ρ.applyTerm (θ.applyTerm t)) ∧
      ∃ ρ : Subst σ, θ.applyTerm t = ρ.applyTerm (θ'.applyTerm t) := by
  have m := solveLegs_isMGU legs isMGU_nil h
  have m' := solveLegs_isMGU legs' isMGU_nil h'
  rw [List.nil_append] at m m'
  have moved := m'.of_perm perm.flatten.symm
  exact ⟨m.instance_of moved t, moved.instance_of m t⟩

/-- **A ground answer does not depend on the order of the legs.** -/
theorem solveLegs_perm_ground {legs legs' : List (Equations σ)} (perm : legs.Perm legs')
    {θ θ' : Subst σ} (h : solveLegs (Subst.id σ) legs = some θ)
    (h' : solveLegs (Subst.id σ) legs' = some θ') {t : Term σ}
    (ground : (θ.applyTerm t).isGround) : θ'.applyTerm t = θ.applyTerm t := by
  have m := solveLegs_isMGU legs isMGU_nil h
  have m' := solveLegs_isMGU legs' isMGU_nil h'
  rw [List.nil_append] at m m'
  exact m.ground_instance_eq (m'.of_perm perm.flatten.symm) ground

end Solve

/-! ## Meeting -/

/-- Two terms meet: their variables taken apart, some instance of one is an
instance of the other. -/
def CommonInstance (s t : Term σ) : Prop :=
  ∃ δ₁ δ₂ : Subst σ, δ₁.applyTerm s = δ₂.applyTerm t

theorem CommonInstance.refl (t : Term σ) : CommonInstance t t :=
  ⟨Subst.id σ, Subst.id σ, rfl⟩

theorem CommonInstance.symm {s t : Term σ} (h : CommonInstance s t) : CommonInstance t s := by
  obtain ⟨δ₁, δ₂, h⟩ := h
  exact ⟨δ₂, δ₁, h.symm⟩

/-- **Instances meet only what their terms meet.** -/
theorem CommonInstance.of_instances {s t : Term σ} (θ θ' : Subst σ)
    (h : CommonInstance (θ.applyTerm s) (θ'.applyTerm t)) : CommonInstance s t := by
  obtain ⟨δ₁, δ₂, h⟩ := h
  exact ⟨δ₁ ∘ₛ θ, δ₂ ∘ₛ θ', by
    rw [Subst.applyTerm_comp, Subst.applyTerm_comp, h]⟩

theorem CommonInstance.of_instance_left {s t : Term σ} (θ : Subst σ)
    (h : CommonInstance (θ.applyTerm s) t) : CommonInstance s t :=
  CommonInstance.of_instances θ (Subst.id σ) (by rwa [Subst.applyTerm_id])

theorem CommonInstance.of_instance_right {s t : Term σ} (θ : Subst σ)
    (h : CommonInstance s (θ.applyTerm t)) : CommonInstance s t :=
  CommonInstance.of_instances (Subst.id σ) θ (by rwa [Subst.applyTerm_id])

/-- Terms that one substitution makes equal meet. -/
theorem commonInstance_of_eq {δ : Subst σ} {s t : Term σ}
    (h : δ.applyTerm s = δ.applyTerm t) : CommonInstance s t :=
  ⟨δ, δ, h⟩

/-- A term meets a ground term exactly when some substitution sends it there. -/
theorem commonInstance_ground_right_iff {s t : Term σ} (ground : t.isGround) :
    CommonInstance s t ↔ ∃ δ : Subst σ, δ.applyTerm s = t := by
  constructor
  · rintro ⟨δ₁, δ₂, h⟩
    exact ⟨δ₁, by rw [h, applyTerm_of_isGround δ₂ ground]⟩
  · rintro ⟨δ, h⟩
    exact ⟨δ, Subst.id σ, by rw [h, applyTerm_of_isGround _ ground]⟩

/-- **Over ground terms meeting is equality**: ids decide it. -/
theorem commonInstance_ground_iff {s t : Term σ} (gs : s.isGround) (gt : t.isGround) :
    CommonInstance s t ↔ s = t := by
  rw [commonInstance_ground_right_iff gt]
  constructor
  · rintro ⟨δ, h⟩
    rwa [applyTerm_of_isGround δ gs] at h
  · rintro rfl
    exact ⟨Subst.id σ, Subst.applyTerm_id s⟩

/-! ### Deciding meeting by activation scopes -/

/-- Forget the activation scopes of a term's variables. -/
def collapse : Term σ.scoped → Term σ
  | .var x => .var x.name
  | .const c => .const c
  | .app f ts => .app f (fun i => collapse (ts i))

/-- A substitution read at one scope. -/
def atScopeSubst (δ : Subst σ.scoped) (scope : ℕ) : Subst σ :=
  fun v => collapse (δ (ScopedVar.at scope v))

theorem collapse_applyTerm_atScope (δ : Subst σ.scoped) (scope : ℕ) (t : Term σ) :
    collapse (δ.applyTerm (t.atScope scope)) = (atScopeSubst δ scope).applyTerm t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f ts ih =>
      show Term.app f (fun i => collapse (δ.applyTerm ((ts i).atScope scope))) =
        Term.app f (fun i => (atScopeSubst δ scope).applyTerm (ts i))
      congr 1
      funext i
      exact ih i

/-- **Copies that one substitution unifies meet**, at any two scopes. -/
theorem commonInstance_of_atScope {δ : Subst σ.scoped} {s t : Term σ} {k k' : ℕ}
    (h : δ.applyTerm (s.atScope k) = δ.applyTerm (t.atScope k')) : CommonInstance s t := by
  refine ⟨atScopeSubst δ k, atScopeSubst δ k', ?_⟩
  rw [← collapse_applyTerm_atScope, ← collapse_applyTerm_atScope, h]

/-- Over ground rows, a row that meets two terms makes them meet. -/
theorem CommonInstance.of_ground_row {s t u : Term σ} (ground : u.isGround)
    (hs : CommonInstance s u) (ht : CommonInstance t u) : CommonInstance s t := by
  obtain ⟨δ, hδ⟩ := (commonInstance_ground_right_iff ground).mp hs
  obtain ⟨δ', hδ'⟩ := (commonInstance_ground_right_iff ground).mp ht
  exact ⟨δ, δ', hδ.trans hδ'.symm⟩

/-- One substitution per scope, as a substitution of scoped variables. -/
def scopedSubst (δ₁ δ₂ : Subst σ) : Subst σ.scoped :=
  fun x => if x.scope = 0 then (δ₁ x.name).atScope 0 else (δ₂ x.name).atScope 0

theorem scopedSubst_applyTerm_zero (δ₁ δ₂ : Subst σ) (t : Term σ) :
    (scopedSubst δ₁ δ₂).applyTerm (t.atScope 0) = (δ₁.applyTerm t).atScope 0 := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f ts ih =>
      show (Term.app (σ := σ.scoped) f fun i =>
          (scopedSubst δ₁ δ₂).applyTerm ((ts i).atScope 0)) =
        Term.app (σ := σ.scoped) f fun i => (δ₁.applyTerm (ts i)).atScope 0
      congr 1
      funext i
      exact ih i

theorem scopedSubst_applyTerm_one (δ₁ δ₂ : Subst σ) (t : Term σ) :
    (scopedSubst δ₁ δ₂).applyTerm (t.atScope 1) = (δ₂.applyTerm t).atScope 0 := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f ts ih =>
      show (Term.app (σ := σ.scoped) f fun i =>
          (scopedSubst δ₁ δ₂).applyTerm ((ts i).atScope 1)) =
        Term.app (σ := σ.scoped) f fun i => (δ₂.applyTerm (ts i)).atScope 0
      congr 1
      funext i
      exact ih i

/-- **Meeting is unification of copies at two scopes.** -/
theorem commonInstance_iff_unifiable_atScope (s t : Term σ) :
    CommonInstance s t ↔ Unifiable [(s.atScope 0, t.atScope 1)] := by
  constructor
  · rintro ⟨δ₁, δ₂, h⟩
    refine ⟨scopedSubst δ₁ δ₂, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp
    subst hp
    show (scopedSubst δ₁ δ₂).applyTerm (s.atScope 0) =
      (scopedSubst δ₁ δ₂).applyTerm (t.atScope 1)
    rw [scopedSubst_applyTerm_zero, scopedSubst_applyTerm_one, h]
  · rintro ⟨δ, h⟩
    have equal := congrArg collapse (h _ (List.mem_singleton_self _))
    refine ⟨atScopeSubst δ 0, atScopeSubst δ 1, ?_⟩
    rw [← collapse_applyTerm_atScope, ← collapse_applyTerm_atScope]
    exact equal

instance [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (s t : Term σ) : Decidable (CommonInstance s t) :=
  decidable_of_iff _ (commonInstance_iff_unifiable_atScope s t).symm

/-! ## Controls -/

namespace Controls

/-- Constants of the control signature. -/
inductive Const
  | a
  | b
  deriving DecidableEq

/-- A binary `f` and a unary `g`. -/
inductive Fn
  | f
  | g
  deriving DecidableEq

/-- Two constants, a binary and a unary function, variables numbered. -/
abbrev sig : LPSignature where
  constants := Const
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun e => e.elim
  functionSymbols := Fn
  functionArity := fun
    | .f => 2
    | .g => 1

/-- `g` applied to one argument. -/
def gOf (t : Term sig) : Term sig := Term.app (σ := sig) Fn.g fun _ => t

def cA : Term sig := Term.const (σ := sig) Const.a
def cB : Term sig := Term.const (σ := sig) Const.b
def x (n : ℕ) : Term sig := Term.var (σ := sig) n

theorem gOf_inj {s t : Term sig} (h : gOf s = gOf t) : s = t := by
  have := (Term.app.inj h).2
  exact congrFun (eq_of_heq this) ⟨0, by simp⟩

theorem applyTerm_gOf (δ : Subst sig) (t : Term sig) :
    δ.applyTerm (gOf t) = gOf (δ.applyTerm t) := rfl

/-- **The occurs check is needed**: `$0 = (g $0)` has no unifier, so a binder
that skips the check and reports a solution answers wrongly. -/
theorem occurs_no_unifier : ¬ Unifiable [(x 0, gOf (x 0))] := by
  rintro ⟨δ, h⟩
  have e := h _ (List.mem_singleton_self _)
  change δ 0 = gOf (δ 0) at e
  have lt := Term.size_subterm (σ := sig) (f := Fn.g) (ts := fun _ => δ 0) ⟨0, by simp⟩
  change (δ 0).size < (gOf (δ 0)).size at lt
  rw [← e] at lt
  exact lt_irrefl _ lt

/-- A stored row `(g $0)` meets both patterns `(g a)` and `(g b)`. -/
theorem row_meets_both : CommonInstance (gOf cA) (gOf (x 0)) ∧
    CommonInstance (gOf cB) (gOf (x 0)) := by
  refine ⟨⟨Subst.id sig, fun _ => cA, rfl⟩, ⟨Subst.id sig, fun _ => cB, rfl⟩⟩

/-- **Each leg its own copy**: the conjunction `(g a), (g b)` over the row
`(g $0)`, copied apart as `(g $1)` and `(g $2)`, is solvable. -/
theorem copies_unifiable :
    Unifiable [(gOf cA, gOf (x 1)), (gOf cB, gOf (x 2))] := by
  refine ⟨fun n => if n = 1 then cA else cB, fun p hp => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> rfl

/-- **Without copies the solution is lost**: sharing the row's variable
between the legs asks `$0` to be both `a` and `b`. -/
theorem shared_not_unifiable :
    ¬ Unifiable [(gOf cA, gOf (x 0)), (gOf cB, gOf (x 0))] := by
  rintro ⟨δ, h⟩
  have first : gOf cA = gOf (δ 0) := h (gOf cA, gOf (x 0)) (by simp)
  have second : gOf cB = gOf (δ 0) := h (gOf cB, gOf (x 0)) (by simp)
  have same := (gOf_inj first).trans (gOf_inj second).symm
  injection same with h'
  cases h'

end Controls

end Mettapedia.Logic.LP.ConjunctiveUnification
