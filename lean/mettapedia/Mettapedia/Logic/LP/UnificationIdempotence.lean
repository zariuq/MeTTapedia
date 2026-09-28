import Mettapedia.Logic.LP.TotalUnification

/-!
# Martelli--Montanari unifiers are relevant and idempotent

`unifyFuel_mgu` and `unifyTotal_mgu` say that the returned substitution is a
most general unifier.  A binding store that is read lazily needs two more
facts about it (Lloyd, *Foundations of Logic Programming*, Thm. 4.3; Apt,
*From Logic Programming to Prolog*, Sec. 2.6):

* it is *idempotent*: every variable occurring in its range is unbound, so a
  term read through the store never needs a second reading;
* it is *relevant*: it moves only variables of the solved equations and
  introduces no other variable.

`Subst.RelevantIdempotent θ X` states both for a finite variable set `X`, and
`unifyFuel_relevantIdempotent` / `unifyTotal_relevantIdempotent` prove them for
`X = eqVars equations`.

The supporting algebra is stated once for reuse: congruence of substitution on
free variables, the free variables of a substituted term, and absorption
`δ.Absorbs θ` (`δ ∘ θ = δ`), which for an idempotent `θ` says exactly that `δ`
is an instance of `θ`.
-/

namespace Mettapedia.Logic.LP

variable {σ : LPSignature}

/-! ## Application -/

@[simp] theorem Subst.id_apply (v : σ.vars) : Subst.id σ v = .var v := rfl

@[simp] theorem Subst.comp_apply (θ₁ θ₂ : Subst σ) (v : σ.vars) :
    (θ₁ ∘ₛ θ₂) v = θ₁.applyTerm (θ₂ v) := rfl

/-! ## Absorption -/

/-- `δ` absorbs `θ` when reading through `θ` first changes nothing under `δ`,
i.e. `δ ∘ θ = δ`.  For an idempotent `θ` this says exactly that `δ` is an
instance of `θ`; `θ.Absorbs θ` is idempotence. -/
def Subst.Absorbs (δ θ : Subst σ) : Prop :=
  ∀ v, δ.applyTerm (θ v) = δ v

theorem Subst.Absorbs.comp_eq {δ θ : Subst σ} (absorbs : δ.Absorbs θ) :
    δ ∘ₛ θ = δ :=
  funext absorbs

theorem Subst.Absorbs.applyTerm {δ θ : Subst σ} (absorbs : δ.Absorbs θ)
    (t : Term σ) : δ.applyTerm (θ.applyTerm t) = δ.applyTerm t := by
  rw [← Subst.applyTerm_comp, absorbs.comp_eq]

theorem Subst.Absorbs.trans {δ θ' θ : Subst σ} (outer : δ.Absorbs θ')
    (inner : θ'.Absorbs θ) : δ.Absorbs θ := by
  intro v
  rw [← outer.applyTerm (θ v), inner v, outer v]

/-- A substitution absorbing both factors absorbs their composite. -/
theorem Subst.Absorbs.comp {δ μ θ : Subst σ} (outer : δ.Absorbs μ)
    (inner : δ.Absorbs θ) : δ.Absorbs (μ ∘ₛ θ) := by
  intro v
  change δ.applyTerm (μ.applyTerm (θ v)) = δ v
  rw [outer.applyTerm, inner v]

/-- Composing anything after an idempotent substitution absorbs it. -/
theorem Subst.comp_absorbs {μ θ : Subst σ} (idempotent : θ.Absorbs θ) :
    (μ ∘ₛ θ).Absorbs θ := by
  intro v
  change (μ ∘ₛ θ).applyTerm (θ v) = μ.applyTerm (θ v)
  rw [Subst.applyTerm_comp, idempotent v]

/-- An instance of an idempotent substitution absorbs it. -/
theorem Subst.absorbs_of_moreGeneral {μ δ : Subst σ} (idempotent : μ.Absorbs μ)
    (general : μ.moreGeneral δ) : δ.Absorbs μ := by
  obtain ⟨ρ, instance_⟩ := general
  have factor : δ = ρ ∘ₛ μ := funext instance_
  intro v
  rw [factor, Subst.applyTerm_comp, idempotent v]
  rfl

/-- `μ ∘ θ` is idempotent when both are and `μ` keeps the terms `θ` reads
fixed by `θ`. -/
theorem Subst.comp_idempotent {μ θ : Subst σ} (μIdempotent : μ.Absorbs μ)
    (stable : ∀ v, θ.applyTerm (μ.applyTerm (θ v)) = μ.applyTerm (θ v)) :
    (μ ∘ₛ θ).Absorbs (μ ∘ₛ θ) := by
  intro v
  change (μ ∘ₛ θ).applyTerm (μ.applyTerm (θ v)) = μ.applyTerm (θ v)
  rw [Subst.applyTerm_comp, stable v, μIdempotent.applyTerm]

/-! ## Free variables of terms and substituted terms -/

section FreeVariables

variable [DecidableEq σ.vars]

theorem Term.mem_freeVars_var {v x : σ.vars} :
    x ∈ (Term.var v : Term σ).freeVars ↔ x = v := by
  simp [Term.freeVars]

theorem Term.not_mem_freeVars_const {c : σ.constants} {x : σ.vars} :
    x ∉ (Term.const c : Term σ).freeVars := by
  simp [Term.freeVars]

theorem Term.mem_freeVars_app {f : σ.functionSymbols}
    {ts : Fin (σ.functionArity f) → Term σ} {x : σ.vars} :
    x ∈ (Term.app f ts).freeVars ↔ ∃ i, x ∈ (ts i).freeVars := by
  simp [Term.freeVars]

/-- The boolean occurs check decides membership in the free variables. -/
theorem Term.occursIn_iff_mem_freeVars (v : σ.vars) (t : Term σ) :
    t.occursIn v = true ↔ v ∈ t.freeVars := by
  induction t with
  | var w => simp [Term.occursIn, Term.freeVars]
  | const c => simp [Term.occursIn, Term.freeVars]
  | app f ts ih => simp [Term.occursIn, Term.freeVars, ih]

/-- Substitutions agreeing on the variables of a term agree on the term. -/
theorem Subst.applyTerm_congr {θ θ' : Subst σ} {t : Term σ}
    (agree : ∀ v ∈ t.freeVars, θ v = θ' v) :
    θ.applyTerm t = θ'.applyTerm t := by
  induction t with
  | var v => exact agree v (Term.mem_freeVars_var.mpr rfl)
  | const c => rfl
  | app f ts ih =>
      simp only [Subst.applyTerm_app]
      congr 1
      funext i
      exact ih i fun v member => agree v (Term.mem_freeVars_app.mpr ⟨i, member⟩)

theorem Subst.mem_freeVars_applyTerm {θ : Subst σ} {t : Term σ} {x : σ.vars} :
    x ∈ (θ.applyTerm t).freeVars ↔ ∃ v ∈ t.freeVars, x ∈ (θ v).freeVars := by
  induction t with
  | var v => simp [Term.freeVars]
  | const c => simp [Term.freeVars]
  | app f ts ih =>
      simp only [Subst.applyTerm_app, Term.mem_freeVars_app, ih]
      constructor
      · rintro ⟨i, v, member, occurs⟩
        exact ⟨v, ⟨i, member⟩, occurs⟩
      · rintro ⟨v, ⟨i, member⟩, occurs⟩
        exact ⟨i, v, member, occurs⟩

/-- A substitution fixing every variable of a term fixes the term. -/
theorem Subst.applyTerm_eq_self {θ : Subst σ} {t : Term σ}
    (fixed : ∀ v ∈ t.freeVars, θ v = .var v) : θ.applyTerm t = t :=
  (Subst.applyTerm_congr fixed).trans (Subst.applyTerm_id t)

/-- A substitution fixing a term fixes each of its variables. -/
theorem Subst.var_fixed_of_applyTerm_eq_self {θ : Subst σ} {t : Term σ}
    (fixed : θ.applyTerm t = t) : ∀ v ∈ t.freeVars, θ v = .var v := by
  induction t with
  | var w =>
      intro v member
      rw [Term.mem_freeVars_var] at member
      subst member
      exact fixed
  | const c =>
      intro v member
      exact absurd member Term.not_mem_freeVars_const
  | app f ts ih =>
      intro v member
      obtain ⟨i, memberChild⟩ := Term.mem_freeVars_app.mp member
      simp only [Subst.applyTerm_app, Term.app.injEq, heq_eq_eq, true_and] at fixed
      exact ih i (congrFun fixed i) v memberChild

/-- An idempotent substitution fixes every variable of every term it
returns. -/
theorem Subst.Absorbs.var_fixed {θ : Subst σ} (idempotent : θ.Absorbs θ)
    (t : Term σ) : ∀ v ∈ (θ.applyTerm t).freeVars, θ v = .var v :=
  Subst.var_fixed_of_applyTerm_eq_self (idempotent.applyTerm t)

/-- A substitution already equating `v` with `t` absorbs the binding
`v := t`. -/
theorem Subst.absorbs_single {δ : Subst σ} {v : σ.vars} {t : Term σ}
    (equates : δ v = δ.applyTerm t) : δ.Absorbs (Subst.single v t) :=
  fun w => congrFun (Subst.absorb_single v t δ equates) w

/-- A binding `v := t` with `v` not occurring in `t` is idempotent. -/
theorem Subst.single_idempotent {v : σ.vars} {t : Term σ}
    (notOccurs : v ∉ t.freeVars) : (Subst.single v t).Absorbs (Subst.single v t) := by
  intro w
  by_cases same : w = v
  · subst same
    rw [Subst.single_eq]
    exact Subst.applyTerm_eq_self fun x member => Subst.single_ne _ fun same =>
      notOccurs (same ▸ member)
  · rw [Subst.single_ne _ same, Subst.applyTerm_var, Subst.single_ne _ same]

theorem Subst.freeVars_single_subset (v : σ.vars) (t s : Term σ) :
    ((Subst.single v t).applyTerm s).freeVars ⊆ s.freeVars ∪ t.freeVars := by
  intro x member
  obtain ⟨w, memberW, occurs⟩ := Subst.mem_freeVars_applyTerm.mp member
  by_cases same : w = v
  · subst same
    rw [Subst.single_eq] at occurs
    exact Finset.mem_union_right _ occurs
  · rw [Subst.single_ne _ same, Term.mem_freeVars_var] at occurs
    subst occurs
    exact Finset.mem_union_left _ memberW

theorem Subst.not_mem_freeVars_single {v : σ.vars} {t : Term σ}
    (notOccurs : v ∉ t.freeVars) (s : Term σ) :
    v ∉ ((Subst.single v t).applyTerm s).freeVars := by
  intro member
  obtain ⟨w, _, occurs⟩ := Subst.mem_freeVars_applyTerm.mp member
  by_cases same : w = v
  · subst same
    rw [Subst.single_eq] at occurs
    exact notOccurs occurs
  · rw [Subst.single_ne _ same, Term.mem_freeVars_var] at occurs
    exact same occurs.symm

/-! ## Variables of equation lists -/

theorem mem_eqVars {equations : List (Term σ × Term σ)} {x : σ.vars} :
    x ∈ eqVars equations ↔
      ∃ equation ∈ equations,
        x ∈ equation.1.freeVars ∨ x ∈ equation.2.freeVars := by
  induction equations with
  | nil => simp [eqVars]
  | cons equation rest ih =>
      obtain ⟨s, t⟩ := equation
      simp only [eqVars, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro ((hs | ht) | ⟨e, member, occurs⟩)
        · exact ⟨(s, t), .inl rfl, .inl hs⟩
        · exact ⟨(s, t), .inl rfl, .inr ht⟩
        · exact ⟨e, .inr member, occurs⟩
      · rintro ⟨e, rfl | member, occurs⟩
        · exact .inl occurs
        · exact .inr ⟨e, member, occurs⟩

theorem eqVars_cons_subset (equation : Term σ × Term σ)
    (rest : List (Term σ × Term σ)) : eqVars rest ⊆ eqVars (equation :: rest) := by
  intro x member
  obtain ⟨e, memberE, occurs⟩ := mem_eqVars.mp member
  exact mem_eqVars.mpr ⟨e, List.mem_cons_of_mem _ memberE, occurs⟩

theorem eqVars_applyEqs_single_subset (v : σ.vars) (t : Term σ)
    (rest : List (Term σ × Term σ)) :
    eqVars ((Subst.single v t).applyEqs rest) ⊆ eqVars rest ∪ t.freeVars := by
  intro x member
  obtain ⟨e, memberE, occurs⟩ := mem_eqVars.mp member
  simp only [Subst.applyEqs, List.mem_map] at memberE
  obtain ⟨⟨s, u⟩, memberSU, rfl⟩ := memberE
  rcases occurs with occurs | occurs
  · rcases Finset.mem_union.mp (Subst.freeVars_single_subset v t s occurs) with inS | inT
    · exact Finset.mem_union_left _ (mem_eqVars.mpr ⟨(s, u), memberSU, .inl inS⟩)
    · exact Finset.mem_union_right _ inT
  · rcases Finset.mem_union.mp (Subst.freeVars_single_subset v t u occurs) with inU | inT
    · exact Finset.mem_union_left _ (mem_eqVars.mpr ⟨(s, u), memberSU, .inr inU⟩)
    · exact Finset.mem_union_right _ inT

theorem not_mem_eqVars_applyEqs_single {v : σ.vars} {t : Term σ}
    (notOccurs : v ∉ t.freeVars) (rest : List (Term σ × Term σ)) :
    v ∉ eqVars ((Subst.single v t).applyEqs rest) := by
  intro member
  obtain ⟨e, memberE, occurs⟩ := mem_eqVars.mp member
  simp only [Subst.applyEqs, List.mem_map] at memberE
  obtain ⟨⟨s, u⟩, _, rfl⟩ := memberE
  rcases occurs with occurs | occurs
  · exact Subst.not_mem_freeVars_single notOccurs s occurs
  · exact Subst.not_mem_freeVars_single notOccurs u occurs

theorem eqVars_decompose_subset {f : σ.functionSymbols}
    (ts us : Fin (σ.functionArity f) → Term σ) (rest : List (Term σ × Term σ)) :
    eqVars (finPairsToList ts us ++ rest) ⊆
      eqVars ((Term.app f ts, Term.app f us) :: rest) := by
  intro x member
  obtain ⟨e, memberE, occurs⟩ := mem_eqVars.mp member
  rcases List.mem_append.mp memberE with inPairs | inRest
  · simp only [finPairsToList, List.mem_map, List.mem_finRange, true_and] at inPairs
    obtain ⟨i, rfl⟩ := inPairs
    refine mem_eqVars.mpr ⟨(Term.app f ts, Term.app f us), List.mem_cons_self, ?_⟩
    rcases occurs with occurs | occurs
    · exact .inl (Term.mem_freeVars_app.mpr ⟨i, occurs⟩)
    · exact .inr (Term.mem_freeVars_app.mpr ⟨i, occurs⟩)
  · exact mem_eqVars.mpr ⟨e, List.mem_cons_of_mem _ inRest, occurs⟩

/-! ## Relevant idempotent substitutions -/

/-- `θ` is idempotent and relevant to the variable set `X`: it moves only
variables of `X`, maps them to terms over `X`, and every variable in its
range is unbound. -/
structure Subst.RelevantIdempotent (θ : Subst σ) (X : Finset σ.vars) : Prop where
  fixes : ∀ v, v ∉ X → θ v = .var v
  range : ∀ v ∈ X, (θ v).freeVars ⊆ X
  unbound : ∀ v, ∀ w ∈ (θ v).freeVars, θ w = .var w

theorem Subst.relevantIdempotent_id (X : Finset σ.vars) :
    (Subst.id σ).RelevantIdempotent X where
  fixes _ _ := rfl
  range v member := by
    intro x occurs
    rw [show (Subst.id σ v) = .var v from rfl, Term.mem_freeVars_var] at occurs
    subst occurs
    exact member
  unbound _ _ _ := rfl

namespace Subst.RelevantIdempotent

variable {θ : Subst σ} {X : Finset σ.vars}

theorem absorbs (relevant : θ.RelevantIdempotent X) : θ.Absorbs θ := fun v =>
  Subst.applyTerm_eq_self (relevant.unbound v)

theorem mono (relevant : θ.RelevantIdempotent X) {Y : Finset σ.vars}
    (subset : X ⊆ Y) : θ.RelevantIdempotent Y where
  fixes v notMember := relevant.fixes v fun member => notMember (subset member)
  range v member := by
    by_cases inX : v ∈ X
    · exact (relevant.range v inX).trans subset
    · rw [relevant.fixes v inX]
      intro x occurs
      rw [Term.mem_freeVars_var] at occurs
      subst occurs
      exact member
  unbound := relevant.unbound

/-- A relevant substitution introduces no variable outside `X`. -/
theorem freeVars_applyTerm_subset (relevant : θ.RelevantIdempotent X)
    (t : Term σ) : (θ.applyTerm t).freeVars ⊆ t.freeVars ∪ X := by
  intro x member
  obtain ⟨v, memberV, occurs⟩ := Subst.mem_freeVars_applyTerm.mp member
  by_cases inX : v ∈ X
  · exact Finset.mem_union_right _ (relevant.range v inX occurs)
  · rw [relevant.fixes v inX, Term.mem_freeVars_var] at occurs
    subst occurs
    exact Finset.mem_union_left _ memberV

/-- The Martelli--Montanari elimination step preserves relevance and
idempotence: `μ` solves the equations after `v := t`, and `μ ∘ (v := t)`
solves the equations before. -/
theorem eliminate {μ : Subst σ} {v : σ.vars} {t : Term σ}
    {rest : List (Term σ × Term σ)}
    (child : μ.RelevantIdempotent (eqVars ((Subst.single v t).applyEqs rest)))
    (notOccurs : v ∉ t.freeVars) (memberV : v ∈ X) (termSubset : t.freeVars ⊆ X)
    (restSubset : eqVars rest ⊆ X) :
    (μ ∘ₛ Subst.single v t).RelevantIdempotent X := by
  set Y := eqVars ((Subst.single v t).applyEqs rest)
  have childSubset : Y ⊆ X := fun x member =>
    match Finset.mem_union.mp (eqVars_applyEqs_single_subset v t rest member) with
    | .inl inRest => restSubset inRest
    | .inr inTerm => termSubset inTerm
  have notInY : v ∉ Y := not_mem_eqVars_applyEqs_single notOccurs rest
  have value : ∀ w, (μ ∘ₛ Subst.single v t) w =
      μ.applyTerm ((Subst.single v t) w) := fun _ => rfl
  -- `v` never occurs in the result of the composite.
  have vAbsent : ∀ w, v ∉ ((μ ∘ₛ Subst.single v t) w).freeVars := by
    intro w member
    rw [value] at member
    obtain ⟨x, memberX, occurs⟩ := Subst.mem_freeVars_applyTerm.mp member
    by_cases inY : x ∈ Y
    · exact notInY (child.range x inY occurs)
    · rw [child.fixes x inY, Term.mem_freeVars_var] at occurs
      subst occurs
      by_cases same : w = v
      · subst same
        rw [Subst.single_eq] at memberX
        exact notOccurs memberX
      · rw [Subst.single_ne _ same, Term.mem_freeVars_var] at memberX
        exact same memberX.symm
  refine ⟨?_, ?_, ?_⟩
  · intro w notMember
    have notV : w ≠ v := fun same => notMember (same ▸ memberV)
    rw [value, Subst.single_ne _ notV, Subst.applyTerm_var]
    exact child.fixes w fun member => notMember (childSubset member)
  · intro w _ x occurs
    rw [value] at occurs
    rcases Finset.mem_union.mp (child.freeVars_applyTerm_subset _ occurs) with inside | inY
    · by_cases same : w = v
      · subst same
        rw [Subst.single_eq] at inside
        exact termSubset inside
      · rw [Subst.single_ne _ same, Term.mem_freeVars_var] at inside
        subst inside
        assumption
    · exact childSubset inY
  · intro w x occurs
    have notV : x ≠ v := fun same => vAbsent w (same ▸ occurs)
    rw [value, Subst.single_ne _ notV, Subst.applyTerm_var]
    rw [value] at occurs
    obtain ⟨y, _, occursY⟩ := Subst.mem_freeVars_applyTerm.mp occurs
    exact child.unbound y x occursY

end Subst.RelevantIdempotent

private theorem notOccurs_of_not_occursIn {v : σ.vars} {t : Term σ}
    (notOccurs : ¬ t.occursIn v = true) : v ∉ t.freeVars :=
  fun member => notOccurs ((Term.occursIn_iff_mem_freeVars v t).mpr member)

private theorem eliminate_forward {μ : Subst σ} {v : σ.vars} {t : Term σ}
    {rest : List (Term σ × Term σ)}
    (child : μ.RelevantIdempotent (eqVars ((Subst.single v t).applyEqs rest)))
    (notOccurs : v ∉ t.freeVars) :
    (μ ∘ₛ Subst.single v t).RelevantIdempotent (eqVars ((.var v, t) :: rest)) :=
  child.eliminate notOccurs (by simp [eqVars, Term.freeVars])
    (fun _ member => by simp [eqVars, member])
    (fun _ member => by simp [eqVars, member])

private theorem eliminate_backward {μ : Subst σ} {v : σ.vars} {t : Term σ}
    {rest : List (Term σ × Term σ)}
    (child : μ.RelevantIdempotent (eqVars ((Subst.single v t).applyEqs rest)))
    (notOccurs : v ∉ t.freeVars) :
    (μ ∘ₛ Subst.single v t).RelevantIdempotent (eqVars ((t, .var v) :: rest)) :=
  child.eliminate notOccurs (by simp [eqVars, Term.freeVars])
    (fun _ member => by simp [eqVars, member])
    (fun _ member => by simp [eqVars, member])

end FreeVariables

/-! ## Martelli--Montanari returns relevant idempotent unifiers -/

section Unifiers

variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

/-- Every substitution returned by fuelled Martelli--Montanari unification is
idempotent and relevant to the variables of its equations. -/
theorem unifyFuel_relevantIdempotent (fuel : ℕ)
    (equations : List (Term σ × Term σ)) (θ : Subst σ)
    (accepted : unifyFuel fuel equations = some θ) :
    θ.RelevantIdempotent (eqVars equations) := by
  induction fuel generalizing equations θ with
  | zero => simp [unifyFuel] at accepted
  | succ n ih =>
    match equations with
    | [] =>
        simp only [unifyFuel, Option.some.injEq] at accepted
        subst accepted
        exact Subst.relevantIdempotent_id _
    | (s, t) :: rest =>
      rcases s with v | c | ⟨f, ts⟩ <;> rcases t with w | c' | ⟨g, us⟩ <;>
        simp only [unifyFuel] at accepted
      -- var v = var w
      · split at accepted
        · rename_i same
          subst same
          exact (ih rest θ accepted).mono (eqVars_cons_subset _ rest)
        · rename_i different
          split at accepted <;> [simp at accepted; skip]
          rename_i θ' childAccepted
          simp only [Option.some.injEq] at accepted
          subst accepted
          exact eliminate_forward (ih _ θ' childAccepted)
            (by simpa [Term.freeVars] using different)
      -- var v = const c'
      · split at accepted <;> [simp at accepted; skip]
        split at accepted <;> [simp at accepted; skip]
        rename_i _ _ θ' childAccepted
        simp only [Option.some.injEq] at accepted
        subst accepted
        exact eliminate_forward (ih _ θ' childAccepted) Term.not_mem_freeVars_const
      -- var v = app g us
      · split at accepted <;> [simp at accepted; skip]
        split at accepted <;> [simp at accepted; skip]
        rename_i occurs _ θ' childAccepted
        simp only [Option.some.injEq] at accepted
        subst accepted
        exact eliminate_forward (ih _ θ' childAccepted)
          (notOccurs_of_not_occursIn occurs)
      -- const c = var w
      · split at accepted <;> [simp at accepted; skip]
        split at accepted <;> [simp at accepted; skip]
        rename_i _ _ θ' childAccepted
        simp only [Option.some.injEq] at accepted
        subst accepted
        exact eliminate_backward (ih _ θ' childAccepted) Term.not_mem_freeVars_const
      -- const c = const c'
      · split at accepted
        · rename_i same
          subst same
          exact (ih rest θ accepted).mono (eqVars_cons_subset _ rest)
        · simp at accepted
      -- const c = app g us
      · simp at accepted
      -- app f ts = var w
      · split at accepted <;> [simp at accepted; skip]
        split at accepted <;> [simp at accepted; skip]
        rename_i occurs _ θ' childAccepted
        simp only [Option.some.injEq] at accepted
        subst accepted
        exact eliminate_backward (ih _ θ' childAccepted)
          (notOccurs_of_not_occursIn occurs)
      -- app f ts = const c'
      · simp at accepted
      -- app f ts = app g us
      · split at accepted
        · rename_i same
          subst same
          exact (ih _ θ accepted).mono (eqVars_decompose_subset ts us rest)
        · simp at accepted

/-- Every substitution returned by total Martelli--Montanari unification is
idempotent and relevant to the variables of its equations. -/
theorem unifyTotal_relevantIdempotent (equations : List (Term σ × Term σ))
    (θ : Subst σ) (accepted : unifyTotal equations = some θ) :
    θ.RelevantIdempotent (eqVars equations) := by
  obtain ⟨fuel, fuelAccepted⟩ :=
    unifyTotal_success_has_fuel equations θ accepted
  exact unifyFuel_relevantIdempotent fuel equations θ fuelAccepted

end Unifiers

end Mettapedia.Logic.LP
