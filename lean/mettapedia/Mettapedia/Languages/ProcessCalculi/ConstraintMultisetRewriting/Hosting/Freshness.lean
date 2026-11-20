import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Instances

/-!
# Freshness on the source side: data made before a scope, and grafting a copy's names

The source names a copy of an equation at scope `n` by prefixing `n` to every name (`copyAt`). A datum
**depends only on names made before `n`** (`DependsBelow n t`) when any two assignments that agree on
the names that are unopened or whose newest scope is below `n` instantiate it alike. This is a
semantic freshness: no support computation is needed, and copies are fresh by construction
(`dependsBelow_copy`).

`graft n σ θ` reads the copy at scope `n` by `θ` and every other name by `σ`: it agrees with `σ` on
data made before `n` (`instantiate_graft_below`) and reads every copy at `n` as `θ` reads the original
(`graft_copy`). So a solution of a store and a solution of an equation's left side combine into one
solution of the store with the copied equation (`solvable_copy_iff`): this is how two-way unification
against a fresh copy is decomposed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {Ty : Type}

/-- A name made before scope `n`: unopened, or opened at a scope below `n`. -/
def Below (n : ℕ) (x : Name κ) : Prop := ∀ m, x.scopes.head? = some m → m < n

theorem Below.mono {n n' : ℕ} {x : Name κ} (below : Below n x) (le : n ≤ n') : Below n' x :=
  fun m head => Nat.lt_of_lt_of_le (below m head) le

/-- **A datum depends only on names made before `n`.** -/
def DependsBelow (n : ℕ) {Δ : Ctx S} {sort : S.Srt} (t : Term (signature S (fam κ)) Δ sort) : Prop :=
  ∀ {W : Type} {target : W → MetaArity S} (σ σ' : Assignment (fam κ) target),
    (∀ x, Below n x → σ x = σ' x) → instantiate σ t = instantiate σ' t

theorem DependsBelow.mono {n n' : ℕ} {Δ : Ctx S} {sort : S.Srt} {t : Term (signature S (fam κ)) Δ sort}
    (depends : DependsBelow n t) (le : n ≤ n') : DependsBelow n' t :=
  fun σ σ' agree => depends σ σ' fun x below => agree x (below.mono le)

/-- Data whose names are all unopened depend on nothing made at any scope. -/
theorem dependsBelow_of_unopened (n : ℕ) {Δ : Ctx S} {sort : S.Srt} {t : Term (signature S (fam κ)) Δ sort}
    (unopened : ∀ x ∈ support t, x.scopes = []) : DependsBelow n t := by
  intro W target σ σ' agree
  apply instantiate_congr
  intro x member
  apply agree x
  intro m head
  rw [unopened x member] at head
  cases head

/-- **Copies are fresh**: a copy at scope `n` depends only on names made before `n + 1`. -/
theorem dependsBelow_copy (n : ℕ) {Δ : Ctx S} {sort : S.Srt} (t : Term (signature S (fam κ)) Δ sort) :
    DependsBelow (n + 1) (instantiate (copyAt κ n) t) := by
  intro W target σ σ' agree
  rw [instantiate_comp, instantiate_comp]
  apply congrArg (fun ρ => instantiate ρ t)
  funext y
  simp only [copyAt, relabel, instantiate_generator]
  apply agree
  intro m head
  simp only [List.head?_cons, Option.some.injEq] at head
  omega

/-! ## Grafting a copy's names -/

/-- Read the copy at scope `n` by `θ`, every other name by `σ`. -/
def graft (n : ℕ) {W : Type} {target : W → MetaArity S} (σ θ : Assignment (fam κ) target) :
    Assignment (fam κ) target
  | ⟨m :: rest, key⟩ => if m = n then θ ⟨rest, key⟩ else σ ⟨m :: rest, key⟩
  | ⟨[], key⟩ => σ ⟨[], key⟩

theorem graft_below {n : ℕ} {W : Type} {target : W → MetaArity S} (σ θ : Assignment (fam κ) target)
    {x : Name κ} (below : Below n x) : graft n σ θ x = σ x := by
  rcases x with ⟨scopes, key⟩
  cases scopes with
  | nil => rfl
  | cons m rest =>
      have small : m < n := below m rfl
      simp only [graft, if_neg (Nat.ne_of_lt small)]

theorem instantiate_graft_below {n : ℕ} {W : Type} {target : W → MetaArity S}
    (σ θ : Assignment (fam κ) target) {Δ : Ctx S} {sort : S.Srt} {t : Term (signature S (fam κ)) Δ sort}
    (depends : DependsBelow n t) : instantiate (graft n σ θ) t = instantiate σ t :=
  depends _ _ fun _ below => graft_below σ θ below

/-- **The graft reads every copy at `n` as `θ` reads the original.** -/
theorem graft_copy (n : ℕ) {W : Type} {target : W → MetaArity S} (σ θ : Assignment (fam κ) target)
    {Δ : Ctx S} {sort : S.Srt} (t : Term (signature S (fam κ)) Δ sort) :
    instantiate (graft n σ θ) (instantiate (copyAt κ n) t) = instantiate θ t := by
  rw [instantiate_comp]
  apply congrArg (fun ρ => instantiate ρ t)
  funext y
  simp only [copyAt, relabel, instantiate_generator, graft, ↓reduceIte]

/-- A copy read by `σ` is the original read by `σ` after the copy. -/
theorem instantiate_copy {n : ℕ} {W : Type} {target : W → MetaArity S} (σ : Assignment (fam κ) target)
    {Δ : Ctx S} {sort : S.Srt} (t : Term (signature S (fam κ)) Δ sort) :
    instantiate σ (instantiate (copyAt κ n) t) =
      instantiate (fun y => instantiate σ (copyAt κ n y)) t :=
  instantiate_comp _ _ t

/-- A store depends only on names made before `n`. -/
def StoreBelow (n : ℕ) (K : List (Constraint κ Γ star)) : Prop :=
  ∀ e ∈ K, DependsBelow n e.1 ∧ DependsBelow n e.2

theorem StoreBelow.mono {n n' : ℕ} {K : List (Constraint κ Γ star)} (below : StoreBelow n K) (le : n ≤ n') :
    StoreBelow n' K :=
  fun e member => ⟨DependsBelow.mono (below e member).1 le, DependsBelow.mono (below e member).2 le⟩

theorem models_graft {n : ℕ} {W : Type} {target : W → MetaArity S} (σ θ : Assignment (fam κ) target)
    {K : List (Constraint κ Γ star)} (below : StoreBelow n K) :
    Models (graft n σ θ) K ↔ Models σ K := by
  constructor
  · intro solved e member
    have h := solved e member
    rwa [instantiate_graft_below σ θ (below e member).1, instantiate_graft_below σ θ (below e member).2] at h
  · intro solved e member
    rw [instantiate_graft_below σ θ (below e member).1, instantiate_graft_below σ θ (below e member).2]
    exact solved e member

/-- **Two-way unification against a fresh copy, decomposed.** A store with a copy at scope `n` of a
left side equated to a call has a solution exactly when some solution of the store reads the call as
some instance of the left side. -/
theorem solvable_copy_iff {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    (lhs : Data κ Γ star) (below : StoreBelow n K) (callBelow : DependsBelow n t) :
    Solvable (K ++ [(instantiate (copyAt κ n) lhs, t)]) ↔
      ∃ (W : Type) (target : W → MetaArity S) (σ θ : Assignment (fam κ) target),
        Models σ K ∧ instantiate θ lhs = instantiate σ t := by
  constructor
  · rintro ⟨W, target, σ, solved⟩
    obtain ⟨old, new⟩ := (models_append σ K _).mp solved
    refine ⟨W, target, σ, fun y => instantiate σ (copyAt κ n y), old, ?_⟩
    rw [← instantiate_copy]
    exact (models_singleton σ _).mp new
  · rintro ⟨W, target, σ, θ, solved, matched⟩
    refine ⟨W, target, graft n σ θ, (models_append _ K _).mpr ⟨(models_graft σ θ below).mpr solved, ?_⟩⟩
    apply (models_singleton _ _).mpr
    rw [graft_copy, instantiate_graft_below σ θ callBelow]
    exact matched

#print axioms dependsBelow_copy
#print axioms graft_copy
#print axioms solvable_copy_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
