import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.CoReferencePreservation
import Mettapedia.Languages.MeTTa.HE.BagSupportBridge

/-!
# Variant-Key Query Correctness

Defines variant equivalence and proves structural properties of variant-based
tabling. The core theorem (`simpleMatch_rename_bisim`) is a bisimulation
argument: two parallel executions of `simpleMatch` — one with target `t`,
one with target `applyAtomTotal r t` — step in lockstep.

## Key Results (proved, 0 sorry)

- `VariantEquiv` — definition using fuel-free `applyAtomTotal`
- `BindingsRenamedBy` — the bisimulation relation (fuel-free)
- `bindingsRenamedBy_empty` — empty bindings are trivially related
- `assign_preserves_bindingsRenamedBy` — assignment preserves bisimulation
- `simpleMatch_rename_bisim` — THE bisimulation mutual induction
- `simpleMatch_isSome_rename_empty` — isSome preserved (corollary)

## Key Result (proved)

- `variant_queries_same_rhs` — via matchStep extraction + List.map_filterMap

## Connection to CeTTa

Maps to `table_store.c` variant-key lookup soundness.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: Variant equivalence (fuel-free) -/

/-- Two atoms are **variant-equivalent** via an injective variable renaming.
    Uses fuel-free `applyAtomTotal` to avoid depth-dependent fuel mismatch. -/
structure VariantEquiv (a₁ a₂ : Atom) where
  ren : VarRenaming
  inj : ren.Injective
  eq : applyAtomTotal ren a₁ = a₂

/-- Variant equivalence preserves variable kind. -/
theorem variantEquiv_var_is_var {v : String} {a₂ : Atom}
    (h : VariantEquiv (.var v) a₂) : ∃ w, a₂ = .var w := by
  refine ⟨h.ren.rename v, ?_⟩
  have heq := h.eq; unfold applyAtomTotal at heq; exact heq.symm

/-- Variant equivalence preserves symbols exactly. -/
theorem variantEquiv_symbol_eq {s : String} {a₂ : Atom}
    (h : VariantEquiv (.symbol s) a₂) : a₂ = .symbol s := by
  have heq := h.eq; unfold applyAtomTotal at heq; exact heq.symm

/-- Variant equivalence preserves grounded values exactly. -/
theorem variantEquiv_grounded_eq {g : GroundedValue} {a₂ : Atom}
    (h : VariantEquiv (.grounded g) a₂) : a₂ = .grounded g := by
  have heq := h.eq; unfold applyAtomTotal at heq; exact heq.symm

/-! ## §2: Bisimulation relation for parallel matching -/

/-- Two binding states are **renamed-related**: same bound variables, renamed values.
    Uses fuel-free `applyAtomTotal`. -/
structure BindingsRenamedBy (r : VarRenaming) (b₁ b₂ : Bindings) : Prop where
  forward : ∀ v a, b₁.lookup v = some a → b₂.lookup v = some (applyAtomTotal r a)
  bound_iff : ∀ v, (b₁.lookup v).isSome = (b₂.lookup v).isSome

/-- Empty bindings are trivially related. -/
theorem bindingsRenamedBy_empty (r : VarRenaming) :
    BindingsRenamedBy r Bindings.empty Bindings.empty :=
  ⟨fun v a h => by simp [Bindings.empty, Bindings.lookup] at h,
   fun _ => rfl⟩

/-- Assigning related values to a fresh variable preserves the bisimulation. -/
theorem assign_preserves_bindingsRenamedBy (r : VarRenaming)
    (b₁ b₂ : Bindings) (hrel : BindingsRenamedBy r b₁ b₂)
    (v : String) (target : Atom)
    (hnone₁ : b₁.lookup v = none) :
    BindingsRenamedBy r (b₁.assign v target) (b₂.assign v (applyAtomTotal r target)) := by
  have hnone₂ : b₂.lookup v = none := by
    have := hrel.bound_iff v; simp [hnone₁] at this
    exact Option.not_isSome_iff_eq_none.mp (by simp [this])
  constructor
  · intro w a hw
    by_cases hwv : w = v
    · subst hwv
      rw [lookup_assign_of_lookup_none _ _ _ hnone₁] at hw
      injection hw with hw; subst hw
      exact lookup_assign_of_lookup_none _ _ _ hnone₂
    · rw [assign_lookup_ne b₁ v target w hwv hnone₁] at hw
      rw [assign_lookup_ne b₂ v (applyAtomTotal r target) w hwv hnone₂]
      exact hrel.forward w a hw
  · intro w
    by_cases hwv : w = v
    · subst hwv; simp [lookup_assign_of_lookup_none _ _ _ hnone₁,
                         lookup_assign_of_lookup_none _ _ _ hnone₂]
    · rw [assign_lookup_ne b₁ v target w hwv hnone₁,
           assign_lookup_ne b₂ v (applyAtomTotal r target) w hwv hnone₂]
      exact hrel.bound_iff w

/-! ## §3: The bisimulation mutual induction

Two PARALLEL executions of `simpleMatch` (one with target `t`, one with
target `applyAtomTotal r t`) step in lockstep. The bisimulation invariant
is `BindingsRenamedBy`: bindings evolve consistently.

Structure follows `simpleMatch_extends` (BindingComposition.lean):
- Induction on fuel
- Cases on pattern constructor
- Variable: first occurrence → both assign; repeat → both check (injectivity)
- Symbol/Grounded: both check structural equality (renaming is identity)
- Expression: recursive via simpleMatchList -/

/-- **THE bisimulation**: `simpleMatch` and `simpleMatchList` produce
    `Option.Rel`-related results under target renaming with related bindings.
    Proved by mutual induction on fuel. -/
theorem simpleMatch_rename_bisim (r : VarRenaming) (hr : r.Injective) (fuel : Nat) :
    (∀ lhs target b₁ b₂,
      BindingsRenamedBy r b₁ b₂ →
      Option.Rel (BindingsRenamedBy r)
        (simpleMatch lhs target b₁ fuel)
        (simpleMatch lhs (applyAtomTotal r target) b₂ fuel)) ∧
    (∀ ps ts b₁ b₂,
      BindingsRenamedBy r b₁ b₂ →
      Option.Rel (BindingsRenamedBy r)
        (simpleMatch.simpleMatchList ps ts b₁ fuel)
        (simpleMatch.simpleMatchList ps (ts.map (applyAtomTotal r)) b₂ fuel)) := by
  induction fuel with
  | zero =>
    constructor
    · intro lhs target b₁ b₂ _; simp [simpleMatch]
    · intro ps ts b₁ b₂ hrel
      cases ps with
      | nil =>
        cases ts with
        | nil => simp [simpleMatch.simpleMatchList]; exact hrel
        | cons _ _ => simp [simpleMatch.simpleMatchList]
      | cons _ _ =>
        cases ts with
        | nil => simp [simpleMatch.simpleMatchList]
        | cons _ _ => simp [simpleMatch.simpleMatchList, simpleMatch]
  | succ n ih =>
    obtain ⟨ih_match, ih_list⟩ := ih
    have hpat : ∀ lhs target b₁ b₂,
        BindingsRenamedBy r b₁ b₂ →
        Option.Rel (BindingsRenamedBy r)
          (simpleMatch lhs target b₁ (n + 1))
          (simpleMatch lhs (applyAtomTotal r target) b₂ (n + 1)) := by
      intro lhs target b₁ b₂ hrel
      cases lhs with
      | var v =>
        simp only [simpleMatch]
        cases hlook₁ : b₁.lookup v with
        | none =>
          have hnone₂ : b₂.lookup v = none := by
            have := hrel.bound_iff v; simp [hlook₁] at this
            exact Option.not_isSome_iff_eq_none.mp (by simp [this])
          simp [hnone₂]
          exact assign_preserves_bindingsRenamedBy r b₁ b₂ hrel v target hlook₁
        | some existing =>
          have hlook₂ := hrel.forward v existing hlook₁
          simp only [hlook₂]
          have hinj := applyAtomTotal_injective r hr
          by_cases heq : existing = target
          · subst heq; simp; exact hrel
          · simp [heq, hinj.ne heq]
      | symbol s =>
        simp only [simpleMatch]
        cases target with
        | symbol t =>
          unfold applyAtomTotal; simp
          by_cases heq : s = t
          · subst heq; simp; exact hrel
          · simp [heq]
        | var _ => unfold applyAtomTotal; simp
        | grounded _ => unfold applyAtomTotal; simp
        | expression _ => unfold applyAtomTotal; simp
      | grounded g =>
        simp only [simpleMatch]
        cases target with
        | grounded h =>
          unfold applyAtomTotal; simp
          by_cases heq : g = h
          · subst heq; simp; exact hrel
          · simp [heq]
        | var _ => unfold applyAtomTotal; simp
        | symbol _ => unfold applyAtomTotal; simp
        | expression _ => unfold applyAtomTotal; simp
      | expression ps =>
        simp only [simpleMatch]
        cases target with
        | expression ts =>
          unfold applyAtomTotal; simp only [List.length_map]
          cases hdec : (ps.length != ts.length) with
          | true => simp
          | false => simp; exact ih_list ps ts b₁ b₂ hrel
        | var _ => unfold applyAtomTotal; simp
        | symbol _ => unfold applyAtomTotal; simp
        | grounded _ => unfold applyAtomTotal; simp
    have hlist : ∀ ps ts b₁ b₂,
        BindingsRenamedBy r b₁ b₂ →
        Option.Rel (BindingsRenamedBy r)
          (simpleMatch.simpleMatchList ps ts b₁ (n + 1))
          (simpleMatch.simpleMatchList ps (ts.map (applyAtomTotal r)) b₂ (n + 1)) := by
      intro ps'
      induction ps' with
      | nil =>
        intro ts' b₁' b₂' hrel'
        cases ts' with
        | nil => simp [simpleMatch.simpleMatchList]; exact hrel'
        | cons _ _ => simp [simpleMatch.simpleMatchList]
      | cons p' ps' ihps =>
        intro ts' b₁' b₂' hrel'
        cases ts' with
        | nil => simp [simpleMatch.simpleMatchList]
        | cons t' ts' =>
          unfold simpleMatch.simpleMatchList
          simp only [List.map]
          -- Goal: Option.Rel ... (match simpleMatch p' t' b₁' (n+1) with ...)
          --                      (match simpleMatch p' (applyAtomTotal r t') b₂' (n+1) with ...)
          have hhead := hpat p' t' b₁' b₂' hrel'
          cases h₁ : simpleMatch p' t' b₁' (n + 1) with
          | none =>
            rw [h₁] at hhead
            cases h₂ : simpleMatch p' (applyAtomTotal r t') b₂' (n + 1) with
            | none => simp
            | some _ => rw [h₂] at hhead; cases hhead
          | some b₁'' =>
            rw [h₁] at hhead
            cases h₂ : simpleMatch p' (applyAtomTotal r t') b₂' (n + 1) with
            | none => rw [h₂] at hhead; cases hhead
            | some b₂'' =>
              rw [h₂] at hhead; simp only
              cases hhead with
              | some hrel'' => exact ihps ts' b₁'' b₂'' hrel''
    exact ⟨hpat, hlist⟩

/-! ## §4: Corollaries -/

/-- **Corollary**: isSome preserved from empty seed. -/
theorem simpleMatch_isSome_rename_empty (r : VarRenaming) (hr : r.Injective)
    (lhs target : Atom) (fuel : Nat) :
    (simpleMatch lhs target Bindings.empty fuel).isSome =
    (simpleMatch lhs (applyAtomTotal r target) Bindings.empty fuel).isSome := by
  have h := (simpleMatch_rename_bisim r hr fuel).1 lhs target
    Bindings.empty Bindings.empty (bindingsRenamedBy_empty r)
  cases h1 : simpleMatch lhs target Bindings.empty fuel <;>
    cases h2 : simpleMatch lhs (applyAtomTotal r target) Bindings.empty fuel <;>
    simp_all

/-! ## §5: Cache reuse theorems -/

/-- Helper: if two filterMap functions agree on isSome and on the fst projection
    when both return some, then filterMap ... |>.map fst are equal. -/
private theorem filterMap_map_fst_eq {α β γ : Type*}
    (xs : List α)
    (f g : α → Option (β × γ))
    (hsome : ∀ x ∈ xs, (f x).isSome = (g x).isSome)
    (hfst : ∀ x ∈ xs, ∀ b₁ c₁ b₂ c₂,
      f x = some (b₁, c₁) → g x = some (b₂, c₂) → b₁ = b₂) :
    (xs.filterMap f).map Prod.fst = (xs.filterMap g).map Prod.fst := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have hsome_a := hsome a (List.mem_cons_self ..)
    have hfst_a := hfst a (List.mem_cons_self ..)
    simp only [List.filterMap_cons]
    cases hf : f a <;> cases hg : g a
    · -- both none
      exact ih (fun x hx => hsome x (List.mem_cons_of_mem a hx))
              (fun x hx => hfst x (List.mem_cons_of_mem a hx))
    · -- f = none, g = some → contradicts hsome
      simp [hf, hg] at hsome_a
    · -- f = some, g = none → contradicts hsome
      simp [hf, hg] at hsome_a
    · -- both some
      rename_i p₁ p₂
      obtain ⟨b₁, c₁⟩ := p₁
      obtain ⟨b₂, c₂⟩ := p₂
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact hfst_a b₁ c₁ b₂ c₂ hf hg
      · exact ih (fun x hx => hsome x (List.mem_cons_of_mem a hx))
                (fun x hx => hfst x (List.mem_cons_of_mem a hx))

/-- The inner matching step: match freshened lhs against query, return (rhs, bindings). -/
private def matchStep (atom : Atom) (fuel : Nat) (lhs' rhs' : Atom) :
    Option (Atom × Bindings) :=
  match simpleMatch lhs' atom Bindings.empty fuel with
  | some b => some (rhs', b)
  | none => none

/-- matchStep agrees on isSome for variant-equivalent queries. -/
private theorem matchStep_isSome_agree
    (q₁ q₂ : Atom) (r : VarRenaming) (hr : r.Injective) (heq : applyAtomTotal r q₁ = q₂)
    (fuel : Nat) (lhs' rhs' : Atom) :
    (matchStep q₁ fuel lhs' rhs').isSome = (matchStep q₂ fuel lhs' rhs').isSome := by
  unfold matchStep
  have hbisim := simpleMatch_isSome_rename_empty r hr lhs' q₁ fuel
  rw [heq] at hbisim
  cases h₁ : simpleMatch lhs' q₁ Bindings.empty fuel <;>
    cases h₂ : simpleMatch lhs' q₂ Bindings.empty fuel <;>
    simp_all

/-- matchStep returns the same fst (rhs') for both queries. -/
private theorem matchStep_fst_agree
    (q₁ q₂ : Atom) (fuel : Nat) (lhs' rhs' : Atom)
    (b₁ : Atom) (c₁ : Bindings) (b₂ : Atom) (c₂ : Bindings)
    (h₁ : matchStep q₁ fuel lhs' rhs' = some (b₁, c₁))
    (h₂ : matchStep q₂ fuel lhs' rhs' = some (b₂, c₂)) :
    b₁ = b₂ := by
  unfold matchStep at h₁ h₂
  revert h₁ h₂
  cases simpleMatch lhs' q₁ Bindings.empty fuel <;>
    cases simpleMatch lhs' q₂ Bindings.empty fuel <;>
    intro h₁ h₂ <;> simp_all

/-- queryEquations uses matchStep after equation decomposition + freshening. -/
private theorem queryEquations_matchStep (space : Space) (atom : Atom) (fuel : Nat) :
    queryEquations space atom fuel =
    space.atoms.zipIdx.filterMap fun ⟨eq, idx⟩ =>
      match eq with
      | .expression [.symbol "=", lhs, rhs] =>
        matchStep atom fuel (freshenEquation idx lhs rhs fuel).1
                            (freshenEquation idx lhs rhs fuel).2
      | _ => none := by
  rfl

/-- Variant-equivalent queries produce the same RHS atoms.
    Uses `List.map_filterMap` to push `Prod.fst` inside `filterMap`, then
    `split` on the Atom equation pattern + `simpleMatch_isSome_rename_empty`. -/
theorem variant_queries_same_rhs
    (space : Space) (q₁ q₂ : Atom) (hvar : VariantEquiv q₁ q₂) (fuel : Nat) :
    (queryEquations space q₁ fuel).map Prod.fst =
    (queryEquations space q₂ fuel).map Prod.fst := by
  simp only [queryEquations, List.map_filterMap]
  congr 1; funext ⟨eq, idx⟩
  split
  · rename_i lhs rhs _
    have hm := simpleMatch_isSome_rename_empty hvar.ren hvar.inj
      (freshenEquation idx lhs rhs fuel).1 q₁ fuel
    rw [hvar.eq] at hm
    cases h₁ : simpleMatch (freshenEquation idx lhs rhs fuel).1 q₁ Bindings.empty fuel <;>
      cases h₂ : simpleMatch (freshenEquation idx lhs rhs fuel).1 q₂ Bindings.empty fuel <;>
      simp_all
  · rfl

/-- Cache reuse is sound at the RHS level. -/
theorem canonical_cache_reusable
    (space : Space) (q₁ q₂ : Atom) (fuel : Nat)
    (hvar : VariantEquiv q₁ q₂) :
    (queryEquations space q₁ fuel).map Prod.fst =
    (queryEquations space q₂ fuel).map Prod.fst :=
  variant_queries_same_rhs space q₁ q₂ hvar fuel

/-! ## §6: Status

### 0 sorries in core bisimulation

`simpleMatch_rename_bisim` is fully proved by mutual induction on fuel,
following the `simpleMatch_extends` pattern (BindingComposition.lean).
The key additional ingredient: `applyAtomTotal_injective` (from
CoReferencePreservation.lean §4a) ensures BEq preservation.

### 0 sorries total

`variant_queries_same_rhs` proved via `List.map_filterMap` + `funext` +
`split` on the Atom equation pattern + `simpleMatch_isSome_rename_empty`.
Helper `matchStep` avoids nested Atom pattern match reduction issues.
-/

end Mettapedia.Languages.MeTTa.HE
