import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenamingConversion

/-!
# Executable synthesis and checking commute with context embeddings

Along an embedding of contexts, and for a reduction strategy that commutes with renaming, the
executable bidirectional checker behaves the same on renamed inputs at every budget:

* universe recognition returns the same universe head;
* the subtype test succeeds exactly when it succeeds on the originals;
* synthesis synthesizes the renamed type, and in particular the same universe head for a type;
* checking succeeds exactly when it succeeds on the originals.

No universe level is changed by a renaming, so two type formations related by an embedding
compute syntactically equal levels.
-/

set_option autoImplicit false

universe u v w u' v' w'

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRenaming

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion ExecutableChecking

/-! ## Sequencing corresponding computations -/

section Bind

variable {α : Type u} {β : Type v} {γ : Type w} {α' : Type u'} {β' : Type v'} {γ' : Type w'}

/-- Corresponding computations followed by continuations that correspond on corresponding
results. -/
theorem Corr.bind {f : α → γ} {g : β → γ} {f' : α' → γ'} {g' : β' → γ'} {x : Option α} {y : Option β}
    (h : Corr f g x y) {k : α → Option α'} {k' : β → Option β'}
    (hk : ∀ a b, f a = g b → Corr f' g' (k a) (k' b)) : Corr f' g' (x.bind k) (y.bind k') := by
  rcases h.cases with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, same⟩
  · rfl
  · exact hk a b same

/-- Equal success is correspondence along the trivial projection. -/
theorem Corr.ofIsSome {x : Option α} {y : Option β} (h : x.isSome = y.isSome) :
    Corr (fun _ => PUnit.unit.{1}) (fun _ => PUnit.unit.{1}) x y := by
  rcases isSome_cases h with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ <;> rfl

theorem Corr.self (f : α → γ) (x : Option α) : Corr f f x x := rfl

end Bind

variable {Head : Type} {R : Rules Head} [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)]
variable {reducer : Reducer R}

/-! ## Universe recognition -/

omit [DecidableEq Head] [DecidableRel R.headEq] in
/-- **Universe recognition commutes with renaming**: the renamed type is recognized as the same
universe head. -/
theorem asUniverse_rename (renames : Renames reducer) (fuel : Nat) {n m : Nat} (ρ : Ren n m)
    (type : Tm Head n) :
    Corr Subtype.val Subtype.val (asUniverse R reducer fuel (rename ρ type)) (asUniverse R reducer fuel type) := by
  rw [asUniverse, asUniverse]
  rcases renames.cases fuel ρ type with ⟨h₁, h₂⟩ | ⟨value, p, p', h₁, h₂⟩
  · rw [h₁, h₂]; rfl
  · rw [h₁, h₂]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases value
    all_goals dsimp only [rename]
    case head h => split_ifs <;> rfl
    all_goals rfl

variable [DecidableRel R.cumulative]

/-! ## The subtype test -/

/-- **The subtype test commutes with embeddings** at every budget. -/
theorem below_rename (renames : Renames reducer) (fuel : Nat) :
    ∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ → ∀ first second : Tm Head n,
      (below R reducer fuel Δ (rename ρ first) (rename ρ second)).isSome =
        (below R reducer fuel Γ first second).isSome := by
  induction fuel with
  | zero => intro n m Γ Δ ρ e first second; rw [below, below]; rfl
  | succ fuel ih =>
      intro n m Γ Δ ρ e first second
      have conversion := conversion_commutes renames
      rw [below, below]
      rcases isSome_cases ((conversion (fuel + 1)).2.2.2 e first second) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂⟩
      · rw [h₁, h₂]
        simp only [Option.bind_eq_bind]
        rcases renames.cases (fuel + 1) ρ first with ⟨k₁, k₂⟩ | ⟨lv, lp, lp', k₁, k₂⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]
          simp only [Option.bind_some]
          rcases renames.cases (fuel + 1) ρ second with ⟨l₁, l₂⟩ | ⟨rv, rp, rp', l₁, l₂⟩
          · rw [l₁, l₂]; rfl
          · rw [l₁, l₂]
            simp only [Option.bind_some]
            by_cases former : (∃ a b, lv = .head a ∧ rv = .head b) ∨
                (∃ d c d' c', lv = .pi d c ∧ rv = .pi d' c') ∨ (∃ d c d' c', lv = .sigma d c ∧ rv = .sigma d' c')
            · rcases former with ⟨a, b, rfl, rfl⟩ | ⟨d, c, d', c', rfl, rfl⟩ | ⟨d, c, d', c', rfl, rfl⟩
              · dsimp only [rename]
                split_ifs <;> rfl
              · dsimp only [rename]
                rw [isSome_bind₂, isSome_bind₂, (conversion fuel).2.2.2 e, ih (e.snoc _)]
              · dsimp only [rename]
                rw [isSome_bind₂, isSome_bind₂, ih e, ih (e.snoc _)]
            · cases lv <;> cases rv
              all_goals first
                | exact absurd (.inl ⟨_, _, rfl, rfl⟩) former
                | exact absurd (.inr (.inl ⟨_, _, _, _, rfl, rfl⟩)) former
                | exact absurd (.inr (.inr ⟨_, _, _, _, rfl, rfl⟩)) former
                | (dsimp only [rename]; rfl)
      · rw [h₁, h₂]; rfl

/-! ## Synthesis and checking -/

variable (heads : HeadChoices R)

/-- **Synthesis and checking commute with embeddings at one budget**: synthesis returns the renamed
type, and checking succeeds exactly when it succeeds on the originals. -/
def CheckingCommutes (reducer : Reducer R) (fuel : Nat) : Prop :=
  (∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ → ∀ term : Tm Head n,
    Corr Sigma.fst (fun result => rename ρ result.1)
      (synth R heads reducer fuel Δ (rename ρ term)) (synth R heads reducer fuel Γ term)) ∧
  (∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ → ∀ term type : Tm Head n,
    (check R heads reducer fuel Δ (rename ρ term) (rename ρ type)).isSome =
      (check R heads reducer fuel Γ term type).isSome)

omit [DecidableEq Head] [DecidableRel R.headEq] [DecidableRel R.cumulative] in
/-- One universe level, recognized on corresponding types. -/
private theorem level_corr (renames : Renames reducer) {fuel n m : Nat} {ρ : Ren n m} {T : Tm Head m}
    {T' : Tm Head n} (same : T = rename ρ T') :
    Corr Subtype.val Subtype.val (asUniverse R reducer fuel T) (asUniverse R reducer fuel T') := by
  subst same
  exact asUniverse_rename renames fuel ρ T'

section Step

variable {heads} (renames : Renames reducer) {fuel : Nat} (ih : CheckingCommutes heads reducer fuel)
include renames ih

theorem synth_step {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    (term : Tm Head n) :
    Corr Sigma.fst (fun result => rename ρ result.1)
      (synth R heads reducer (fuel + 1) Δ (rename ρ term)) (synth R heads reducer (fuel + 1) Γ term) := by
  obtain ⟨ihS, ihK⟩ := ih
  have conversion := conversion_commutes renames
  cases term with
  | var i =>
      dsimp only [rename]
      rw [synth, synth]
      exact Corr.some_some (e.lookup i)
  | const c =>
      dsimp only [rename]
      rw [synth, synth]
      split
      · exact Corr.some_some (rename_liftClosed ρ _).symm
      · rfl
  | head h =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      cases heads.typing h <;> rfl
  | pi A B =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      refine Corr.bind (ihS e A) fun a b same => ?_
      refine Corr.bind (level_corr renames same) fun l l' sameL => ?_
      refine Corr.bind (ihS (e.snoc A) B) fun c d same' => ?_
      refine Corr.bind (level_corr renames same') fun k k' sameK => ?_
      obtain ⟨lv, lp⟩ := l
      obtain ⟨lv', lp'⟩ := l'
      obtain ⟨kv, kp⟩ := k
      obtain ⟨kv', kp'⟩ := k'
      dsimp only at sameL sameK
      subst sameL sameK
      refine Corr.bind (Corr.self Subtype.val (heads.join lv kv)) fun j j' sameJ => ?_
      exact Corr.some_some (congrArg Tm.head sameJ)
  | sigma A B =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      refine Corr.bind (ihS e A) fun a b same => ?_
      refine Corr.bind (level_corr renames same) fun l l' sameL => ?_
      refine Corr.bind (ihS (e.snoc A) B) fun c d same' => ?_
      refine Corr.bind (level_corr renames same') fun k k' sameK => ?_
      obtain ⟨lv, lp⟩ := l
      obtain ⟨lv', lp'⟩ := l'
      obtain ⟨kv, kp⟩ := k
      obtain ⟨kv', kp'⟩ := k'
      dsimp only at sameL sameK
      subst sameL sameK
      refine Corr.bind (Corr.self Subtype.val (heads.join lv kv)) fun j j' sameJ => ?_
      exact Corr.some_some (congrArg Tm.head sameJ)
  | id A x y =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      refine Corr.bind (ihS e A) fun a b same => ?_
      refine Corr.bind (level_corr renames same) fun l l' sameL => ?_
      refine Corr.bind (Corr.ofIsSome (ihK e x A)) fun _ _ _ => ?_
      refine Corr.bind (Corr.ofIsSome (ihK e y A)) fun _ _ _ => ?_
      exact Corr.some_some (congrArg Tm.head sameL)
  | refl s =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      refine Corr.bind (ihS e s) fun a b same => ?_
      obtain ⟨T, cT⟩ := a
      obtain ⟨T', cT'⟩ := b
      dsimp only at same
      subst same
      rfl
  | lam body =>
      dsimp only [rename]
      rw [synth, synth]
      rfl
  | pair x y =>
      dsimp only [rename]
      rw [synth, synth]
      rfl
  | app f a =>
      by_cases redex : ∃ body, f = .lam body
      · obtain ⟨body, rfl⟩ := redex
        dsimp only [rename]
        rw [synth, synth]
        simp only [Option.bind_eq_bind]
        refine Corr.bind (ihS e a) fun c d same => ?_
        obtain ⟨T, cT⟩ := c
        obtain ⟨T', cT'⟩ := d
        dsimp only at same
        subst same
        refine Corr.bind (ihS (e.snoc T') body) fun c d same' => ?_
        obtain ⟨U, cU⟩ := c
        obtain ⟨U', cU'⟩ := d
        dsimp only at same'
        subst same'
        exact Corr.some_some (rename_inst0 ρ a U').symm
      · have notLam : ∀ body, f = .lam body → False := fun body same => redex ⟨body, same⟩
        have notLam' : ∀ body, rename ρ f = .lam body → False := by
          intro body same
          cases f <;> simp only [rename, reduceCtorEq] at same
          exact notLam _ rfl
        dsimp only [rename]
        rw [synth.eq_10 R heads reducer _ Δ fuel (rename ρ f) (rename ρ a) notLam',
          synth.eq_10 R heads reducer _ Γ fuel f a notLam]
        simp only [Option.bind_eq_bind]
        refine Corr.bind (ihS e f) fun c d same => ?_
        obtain ⟨T, cT⟩ := c
        obtain ⟨T', cT'⟩ := d
        dsimp only at same
        subst same
        try dsimp only
        rcases renames.cases (fuel + 1) ρ T' with ⟨k₁, k₂⟩ | ⟨value, p, p', k₁, k₂⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]
          simp only [Option.bind_some]
          cases value
          all_goals dsimp only [rename]
          case pi domain body =>
            refine Corr.bind (Corr.ofIsSome (ihK e a domain)) fun _ _ _ => ?_
            exact Corr.some_some (rename_inst0 ρ a body).symm
          all_goals rfl
  | fst p =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      refine Corr.bind (ihS e p) fun c d same => ?_
      obtain ⟨T, cT⟩ := c
      obtain ⟨T', cT'⟩ := d
      dsimp only at same
      subst same
      try dsimp only
      rcases renames.cases (fuel + 1) ρ T' with ⟨k₁, k₂⟩ | ⟨value, q, q', k₁, k₂⟩
      · rw [k₁, k₂]; rfl
      · rw [k₁, k₂]
        simp only [Option.bind_some]
        cases value
        all_goals dsimp only [rename]
        all_goals rfl
  | snd p =>
      dsimp only [rename]
      rw [synth, synth]
      simp only [Option.bind_eq_bind]
      refine Corr.bind (ihS e p) fun c d same => ?_
      obtain ⟨T, cT⟩ := c
      obtain ⟨T', cT'⟩ := d
      dsimp only at same
      subst same
      try dsimp only
      rcases renames.cases (fuel + 1) ρ T' with ⟨k₁, k₂⟩ | ⟨value, q, q', k₁, k₂⟩
      · rw [k₁, k₂]; rfl
      · rw [k₁, k₂]
        simp only [Option.bind_some]
        cases value
        all_goals dsimp only [rename]
        case sigma domain body => exact Corr.some_some (rename_inst0_fst ρ p body).symm
        all_goals rfl

theorem check_step {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    (term type : Tm Head n) :
    (check R heads reducer (fuel + 1) Δ (rename ρ term) (rename ρ type)).isSome =
      (check R heads reducer (fuel + 1) Γ term type).isSome := by
  have conversion := conversion_commutes renames
  obtain ⟨ihS, ihK⟩ := ih
  by_cases introduction : (∃ body, term = .lam body) ∨ (∃ a b, term = .pair a b) ∨ (∃ s, term = .refl s)
  · rcases introduction with ⟨body, rfl⟩ | ⟨a, b, rfl⟩ | ⟨s, rfl⟩
    · dsimp only [rename]
      rw [check, check]
      simp only [Option.bind_eq_bind]
      rcases renames.cases (fuel + 1) ρ type with ⟨k₁, k₂⟩ | ⟨value, p, p', k₁, k₂⟩
      · rw [k₁, k₂]; rfl
      · rw [k₁, k₂]
        simp only [Option.bind_some]
        cases value
        all_goals dsimp only [rename]
        case pi domain codomain =>
          rw [isSome_bind₁, isSome_bind₁]
          exact ihK (e.snoc domain) body codomain
        all_goals rfl
    · dsimp only [rename]
      rw [check, check]
      simp only [Option.bind_eq_bind]
      rcases renames.cases (fuel + 1) ρ type with ⟨k₁, k₂⟩ | ⟨value, p, p', k₁, k₂⟩
      · rw [k₁, k₂]; rfl
      · rw [k₁, k₂]
        simp only [Option.bind_some]
        cases value
        all_goals dsimp only [rename]
        case sigma domain codomain =>
          rw [isSome_bind₂, isSome_bind₂, ← rename_inst0, ihK e a domain, ihK e b (inst0 a codomain)]
        all_goals rfl
    · dsimp only [rename]
      rw [check, check]
      simp only [Option.bind_eq_bind]
      rcases renames.cases (fuel + 1) ρ type with ⟨k₁, k₂⟩ | ⟨value, p, p', k₁, k₂⟩
      · rw [k₁, k₂]; rfl
      · rw [k₁, k₂]
        simp only [Option.bind_some]
        cases value
        all_goals dsimp only [rename]
        case id carrier left right =>
          rw [isSome_bind₃, isSome_bind₃, ihK e s carrier, (conversion fuel).1 e s left carrier,
            (conversion fuel).1 e s right carrier]
        all_goals rfl
  · have notLam : ∀ body, term = .lam body → False := fun body same => introduction (.inl ⟨body, same⟩)
    have notPair : ∀ a b, term = .pair a b → False := fun a b same => introduction (.inr (.inl ⟨a, b, same⟩))
    have notRefl : ∀ s, term = .refl s → False := fun s same => introduction (.inr (.inr ⟨s, same⟩))
    have notLam' : ∀ body, rename ρ term = .lam body → False := by
      intro body same
      cases term <;> simp only [rename, reduceCtorEq] at same
      exact notLam _ rfl
    have notPair' : ∀ a b, rename ρ term = .pair a b → False := by
      intro a b same
      cases term <;> simp only [rename, reduceCtorEq] at same
      exact notPair _ _ rfl
    have notRefl' : ∀ s, rename ρ term = .refl s → False := by
      intro s same
      cases term <;> simp only [rename, reduceCtorEq] at same
      exact notRefl _ rfl
    rw [check.eq_5 R heads reducer _ Δ (rename ρ term) (rename ρ type) fuel notLam' notPair' notRefl',
      check.eq_5 R heads reducer _ Γ term type fuel notLam notPair notRefl]
    simp only [Option.bind_eq_bind]
    rcases (ihS e term).cases with ⟨h₁, h₂⟩ | ⟨⟨T, c⟩, ⟨T', c'⟩, h₁, h₂, same⟩
    · rw [h₁, h₂]; rfl
    · dsimp only at same
      subst same
      rw [h₁, h₂]
      simp only [Option.bind_some]
      rw [isSome_bind₁, isSome_bind₁]
      exact below_rename renames fuel e T' type

end Step

/-- **Executable synthesis and checking commute with embeddings** at every budget, for a strategy
that commutes with renaming. -/
theorem checking_commutes (renames : Renames reducer) : ∀ fuel, CheckingCommutes heads reducer fuel := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨fun _ _ => ?_, fun _ _ _ => ?_⟩
      · (rw [Corr, synth, synth]; rfl)
      · (rw [check, check]; rfl)
  | succ fuel ih => exact ⟨synth_step renames ih, check_step renames ih⟩

/-- Synthesis along an embedding. -/
theorem synth_rename (renames : Renames reducer) (fuel : Nat) {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (term : Tm Head n) :
    Corr Sigma.fst (fun result => rename ρ result.1)
      (synth R heads reducer fuel Δ (rename ρ term)) (synth R heads reducer fuel Γ term) :=
  (checking_commutes heads renames fuel).1 e term

/-- Checking along an embedding. -/
theorem check_rename (renames : Renames reducer) (fuel : Nat) {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (term type : Tm Head n) :
    (check R heads reducer fuel Δ (rename ρ term) (rename ρ type)).isSome =
      (check R heads reducer fuel Γ term type).isSome :=
  (checking_commutes heads renames fuel).2 e term type

/-- **The universe level of a synthesized type is invariant under embeddings**: synthesis followed
by universe recognition returns syntactically the same head on a renamed type. -/
theorem level_rename (renames : Renames reducer) (fuel : Nat) {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (code : Tm Head n) :
    ((synth R heads reducer fuel Δ (rename ρ code)).bind fun s => (asUniverse R reducer fuel s.1).map Subtype.val) =
      ((synth R heads reducer fuel Γ code).bind fun s => (asUniverse R reducer fuel s.1).map Subtype.val) := by
  rcases (synth_rename heads renames fuel e code).cases with ⟨h₁, h₂⟩ | ⟨⟨T, c⟩, ⟨T', c'⟩, h₁, h₂, same⟩
  · rw [h₁, h₂]; rfl
  · dsimp only at same
    subst same
    rw [h₁, h₂]
    exact asUniverse_rename renames fuel ρ T'

end ContextualDependentRenaming
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
