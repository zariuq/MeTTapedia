import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions

/-!
# Codes over several locals, with unknowns applied to lists of locals, as frames

The codes of `CumulativeCodes` have one parameter. Here an equation lives under any number of locals, and an
unknown of arity `k` is applied to a list of `k` locals: `W x̄`. This is the setting of Miller's patterns, where the
locals in an application are distinct, and where unification needs inversion, pruning and intersection.

* Codes: locals `loc i`, a ground code `gnd`, function codes `arr A B`, and applied unknowns `app W args`.
* A context gives each unknown its arity. A **body** of an unknown of arity `k` is a code whose locals are below `k`:
  parameter `i` of the body. Acting by an assignment replaces `app W args` by `W`'s body with parameter `i` renamed
  to the `i`-th argument (`Tm.act`, through `Tm.rename` and `Tm.spread`).
* `frames` is an `Interface.Frames` instance: contexts of arities, scoped codes, assignments of bodies, with
  syntactic equality of codes. Acting commutes with renaming locals (`act_rename`), which gives the composition law.

The model is untyped: the universe questions of the dependent fibre are those of `CumulativeCodes`,
`CrossStoreLevels` and `CodomainNarrowing`; here are the questions of locals.

Positive examples: the identity assignment acts trivially (`act_id`), and a body over two parameters applied to
`[x, y]` reads `x` for parameter 0 and `y` for parameter 1. Negative examples are in `MillerControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace MillerCodes

/-- Codes over locals, with unknowns applied to lists of locals. -/
inductive Tm where
  /-- A local, by its index. -/
  | loc (i : Nat) : Tm
  /-- A ground code. -/
  | gnd : Tm
  /-- The code of functions from `A` to `B`. -/
  | arr (A B : Tm) : Tm
  /-- The unknown `W` applied to a list of locals. -/
  | app (W : Nat) (args : List Nat) : Tm
  deriving DecidableEq, Repr

namespace Tm

/-- Rename the locals of a code. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | loc i => loc (ρ i)
  | gnd => gnd
  | arr A B => arr (rename ρ A) (rename ρ B)
  | app W args => app W (args.map ρ)

/-- Parameter `i` of a body goes to the `i`-th argument. -/
def spread (args : List Nat) (i : Nat) : Nat := (args[i]?).getD 0

/-- The index of a local in a list of locals: the inverse of `spread` on a list without repetitions. -/
def idx (args : List Nat) (j : Nat) : Nat := args.idxOf j

/-- Act by an assignment: `app W args` becomes `W`'s body with its parameters spread over `args`. -/
def act (σ : Nat → Tm) : Tm → Tm
  | loc i => loc i
  | gnd => gnd
  | arr A B => arr (act σ A) (act σ B)
  | app W args => rename (spread args) (σ W)

/-- The size of a code. -/
def size : Tm → Nat
  | loc _ => 1
  | gnd => 1
  | arr A B => size A + size B + 1
  | app _ args => args.length + 1

/-- The unknowns of a code. -/
def unknowns : Tm → Finset Nat
  | loc _ => ∅
  | gnd => ∅
  | arr A B => unknowns A ∪ unknowns B
  | app W _ => {W}

/-- Every local of the code, rigid or an argument of an unknown, satisfies `P`. -/
inductive AllLocals (P : Nat → Prop) : Tm → Prop
  | loc {i : Nat} : P i → AllLocals P (.loc i)
  | gnd : AllLocals P .gnd
  | arr {A B : Tm} : AllLocals P A → AllLocals P B → AllLocals P (.arr A B)
  | app {W : Nat} {args : List Nat} : (∀ i ∈ args, P i) → AllLocals P (.app W args)

theorem spread_of_lt {args : List Nat} {i : Nat} (h : i < args.length) : spread args i = args[i] := by
  simp [spread, List.getElem?_eq_getElem h]

theorem spread_mem {args : List Nat} {i : Nat} (h : i < args.length) : spread args i ∈ args := by
  rw [spread_of_lt h]
  exact List.getElem_mem h

/-- `spread` undoes `idx` on the members of the list. -/
theorem spread_idx {args : List Nat} {j : Nat} (h : j ∈ args) : spread args (idx args j) = j := by
  have lt : args.idxOf j < args.length := List.idxOf_lt_length_of_mem h
  rw [idx, spread_of_lt lt]
  exact List.getElem_idxOf lt

/-- `idx` undoes `spread` below the length, on a list without repetitions. -/
theorem idx_spread {args : List Nat} (nodup : args.Nodup) {i : Nat} (h : i < args.length) :
    idx args (spread args i) = i := by
  rw [spread_of_lt h, idx]
  exact nodup.idxOf_getElem i h

theorem idx_lt {args : List Nat} {j : Nat} (h : j ∈ args) : idx args j < args.length :=
  List.idxOf_lt_length_of_mem h

theorem rename_rename (ρ τ : Nat → Nat) : ∀ t : Tm, rename ρ (rename τ t) = rename (fun i => ρ (τ i)) t
  | loc _ => rfl
  | gnd => rfl
  | arr A B => by simp only [rename, rename_rename ρ τ A, rename_rename ρ τ B]
  | app W args => by simp only [rename, List.map_map]; rfl

theorem AllLocals.mono {P Q : Nat → Prop} (h : ∀ i, P i → Q i) : ∀ {t : Tm}, AllLocals P t → AllLocals Q t
  | _, .loc hi => .loc (h _ hi)
  | _, .gnd => .gnd
  | _, .arr hA hB => .arr (AllLocals.mono h hA) (AllLocals.mono h hB)
  | _, .app hargs => .app fun i hi => h i (hargs i hi)

/-- **Renamings that agree on the locals of a code agree on the code.** -/
theorem rename_congr {ρ τ : Nat → Nat} {P : Nat → Prop} (same : ∀ i, P i → ρ i = τ i) :
    ∀ {t : Tm}, AllLocals P t → rename ρ t = rename τ t
  | _, .loc hi => by simp only [rename, same _ hi]
  | _, .gnd => rfl
  | _, .arr hA hB => by simp only [rename, rename_congr same hA, rename_congr same hB]
  | _, .app hargs => by
      simp only [rename, app.injEq, true_and]
      exact List.map_inj_left.mpr fun i hi => same i (hargs i hi)

theorem rename_id : ∀ t : Tm, rename (fun i => i) t = t
  | loc _ => rfl
  | gnd => rfl
  | arr A B => by simp only [rename, rename_id A, rename_id B]
  | app W args => by simp only [rename, List.map_id']

/-- A renaming that fixes the locals of a code fixes the code. -/
theorem rename_fix {ρ : Nat → Nat} {P : Nat → Prop} (fix : ∀ i, P i → ρ i = i) {t : Tm}
    (h : AllLocals P t) : rename ρ t = t :=
  (rename_congr (τ := fun i => i) fix h).trans (rename_id t)

theorem AllLocals.rename {P Q : Nat → Prop} {ρ : Nat → Nat} (h : ∀ i, P i → Q (ρ i)) :
    ∀ {t : Tm}, AllLocals P t → AllLocals Q (Tm.rename ρ t)
  | _, .loc hi => .loc (h _ hi)
  | _, .gnd => .gnd
  | _, .arr hA hB => .arr (AllLocals.rename h hA) (AllLocals.rename h hB)
  | _, .app hargs => .app fun j hj => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact h i (hargs i hi)

/-- **Two renamings that agree on a code agree on its locals.** -/
theorem AllLocals.of_rename_eq {ρ τ : Nat → Nat} :
    ∀ {t : Tm}, Tm.rename ρ t = Tm.rename τ t → AllLocals (fun i => ρ i = τ i) t
  | Tm.loc _, h => .loc (by simpa [Tm.rename] using h)
  | Tm.gnd, _ => .gnd
  | Tm.arr _ _, h => by
      simp only [Tm.rename, Tm.arr.injEq] at h
      exact .arr (AllLocals.of_rename_eq h.1) (AllLocals.of_rename_eq h.2)
  | Tm.app _ _, h => by
      simp only [Tm.rename, Tm.app.injEq, true_and] at h
      exact .app fun i hi => List.map_inj_left.mp h i hi

theorem AllLocals.and {P Q : Nat → Prop} : ∀ {t : Tm}, AllLocals P t → AllLocals Q t →
    AllLocals (fun i => P i ∧ Q i) t
  | _, .loc hP, .loc hQ => .loc ⟨hP, hQ⟩
  | _, .gnd, _ => .gnd
  | _, .arr hA hB, .arr hA' hB' => .arr (AllLocals.and hA hA') (AllLocals.and hB hB')
  | _, .app hP, .app hQ => .app fun i hi => ⟨hP i hi, hQ i hi⟩

theorem size_rename (ρ : Nat → Nat) : ∀ t : Tm, size (rename ρ t) = size t
  | loc _ => rfl
  | gnd => rfl
  | arr A B => by simp only [rename, size, size_rename ρ A, size_rename ρ B]
  | app _ args => by simp only [rename, size, List.length_map]

theorem size_pos : ∀ t : Tm, 0 < size t
  | loc _ => Nat.one_pos
  | gnd => Nat.one_pos
  | arr _ _ => Nat.succ_pos _
  | app _ _ => Nat.succ_pos _

end Tm

/-! ## Contexts, scope and bodies -/

/-- A context gives each unknown its arity. -/
abbrev Ctx := List Nat

/-- The unknowns of a code are declared by the context, each applied to as many locals as its arity. -/
inductive Scoped (Δ : Ctx) : Tm → Prop
  | loc (i : Nat) : Scoped Δ (.loc i)
  | gnd : Scoped Δ .gnd
  | arr {A B : Tm} : Scoped Δ A → Scoped Δ B → Scoped Δ (.arr A B)
  | app {W : Nat} {args : List Nat} : Δ[W]? = some args.length → Scoped Δ (.app W args)

theorem Scoped.rename {Δ : Ctx} (ρ : Nat → Nat) : ∀ {t : Tm}, Scoped Δ t → Scoped Δ (Tm.rename ρ t)
  | _, .loc i => .loc (ρ i)
  | _, .gnd => .gnd
  | _, .arr hA hB => .arr (Scoped.rename ρ hA) (Scoped.rename ρ hB)
  | _, .app hW => .app (by rw [List.length_map]; exact hW)

theorem Scoped.arr_inv {Δ : Ctx} {A B : Tm} (h : Scoped Δ (.arr A B)) : Scoped Δ A ∧ Scoped Δ B := by
  cases h with
  | arr hA hB => exact ⟨hA, hB⟩

theorem Scoped.app_inv {Δ : Ctx} {W : Nat} {args : List Nat} (h : Scoped Δ (.app W args)) :
    Δ[W]? = some args.length := by
  cases h with
  | app hW => exact hW

/-- A body of an unknown of arity `k` over `Γ`: a scoped code whose locals are below `k`. -/
def Body (Γ : Ctx) (k : Nat) (t : Tm) : Prop := Scoped Γ t ∧ Tm.AllLocals (· < k) t

/-- A typed assignment from `Δ` to `Γ`: each declared unknown gets a body of its arity. -/
def TyA (Δ Γ : Ctx) (σ : Nat → Tm) : Prop := ∀ (W k : Nat), Δ[W]? = some k → Body Γ k (σ W)

/-- The arity of an unknown, `0` when undeclared. -/
def arity (Δ : Ctx) (W : Nat) : Nat := (Δ[W]?).getD 0

theorem arity_of {Δ : Ctx} {W k : Nat} (h : Δ[W]? = some k) : arity Δ W = k := by
  simp [arity, h]

/-- The identity assignment: each unknown applied to its own parameters. -/
def idA (Δ : Ctx) : Nat → Tm := fun W => .app W (List.range (arity Δ W))

/-- First `f`, then `g`. -/
def compA (g f : Nat → Tm) : Nat → Tm := fun W => Tm.act g (f W)

theorem idA_typed (Δ : Ctx) : TyA Δ Δ (idA Δ) := by
  intro W k hW
  refine ⟨.app (by rw [List.length_range, arity_of hW]; exact hW), .app fun i hi => ?_⟩
  rw [List.mem_range, arity_of hW] at hi
  exact hi

/-- **Acting commutes with renaming locals.** -/
theorem act_rename {Δ Γ : Ctx} {σ : Nat → Tm} (hσ : TyA Δ Γ σ) (ρ : Nat → Nat) :
    ∀ {t : Tm}, Scoped Δ t → Tm.act σ (Tm.rename ρ t) = Tm.rename ρ (Tm.act σ t)
  | _, .loc _ => rfl
  | _, .gnd => rfl
  | _, .arr hA hB => by simp only [Tm.rename, Tm.act, act_rename hσ ρ hA, act_rename hσ ρ hB]
  | _, @Scoped.app _ W args hW => by
      show Tm.rename (Tm.spread (args.map ρ)) (σ W) = Tm.rename ρ (Tm.rename (Tm.spread args) (σ W))
      rw [Tm.rename_rename]
      apply Tm.rename_congr _ (hσ W _ hW).2
      intro i hi
      have hi' : i < (args.map ρ).length := by rw [List.length_map]; exact hi
      rw [Tm.spread_of_lt hi', Tm.spread_of_lt hi, List.getElem_map]

theorem Scoped.act {Δ Γ : Ctx} {σ : Nat → Tm} (hσ : TyA Δ Γ σ) :
    ∀ {t : Tm}, Scoped Δ t → Scoped Γ (Tm.act σ t)
  | _, .loc i => .loc i
  | _, .gnd => .gnd
  | _, .arr hA hB => .arr (Scoped.act hσ hA) (Scoped.act hσ hB)
  | _, @Scoped.app _ W args hW => (hσ W _ hW).1.rename _

/-- Acting keeps every property of the locals of a scoped code. -/
theorem AllLocals.act {Δ Γ : Ctx} {σ : Nat → Tm} (hσ : TyA Δ Γ σ) {P : Nat → Prop} :
    ∀ {t : Tm}, Scoped Δ t → Tm.AllLocals P t → Tm.AllLocals P (Tm.act σ t)
  | _, .loc _, .loc hi => .loc hi
  | _, .gnd, _ => .gnd
  | _, .arr sA sB, .arr hA hB => .arr (AllLocals.act hσ sA hA) (AllLocals.act hσ sB hB)
  | _, @Scoped.app _ W args hW, .app hargs =>
      (hσ W _ hW).2.rename fun _ hi => hargs _ (Tm.spread_mem hi)

theorem compA_typed {Δ Γ Θ : Ctx} {f g : Nat → Tm} (hf : TyA Δ Γ f) (hg : TyA Γ Θ g) :
    TyA Δ Θ (compA g f) :=
  fun W k hW => ⟨Scoped.act hg (hf W k hW).1, AllLocals.act hg (hf W k hW).1 (hf W k hW).2⟩

/-- **The identity acts trivially on scoped codes.** -/
theorem act_id {Δ : Ctx} : ∀ {t : Tm}, Scoped Δ t → Tm.act (idA Δ) t = t
  | _, .loc _ => rfl
  | _, .gnd => rfl
  | _, .arr hA hB => by simp only [Tm.act, act_id hA, act_id hB]
  | _, @Scoped.app _ W args hW => by
      show Tm.rename (Tm.spread args) (.app W (List.range (arity Δ W))) = .app W args
      simp only [Tm.rename, arity_of hW, Tm.app.injEq, true_and]
      apply List.ext_getElem (by simp)
      intro i h₁ h₂
      rw [List.getElem_map, List.getElem_range, Tm.spread_of_lt h₂]

/-- **Acting by a composite is acting twice.** -/
theorem act_comp {Δ Γ Θ : Ctx} {g f : Nat → Tm} (hg : TyA Γ Θ g) (hf : TyA Δ Γ f) :
    ∀ {t : Tm}, Scoped Δ t → Tm.act (compA g f) t = Tm.act g (Tm.act f t)
  | _, .loc _ => rfl
  | _, .gnd => rfl
  | _, .arr hA hB => by simp only [Tm.act, act_comp hg hf hA, act_comp hg hf hB]
  | _, @Scoped.app _ W args hW => by
      show Tm.rename (Tm.spread args) (Tm.act g (f W)) = Tm.act g (Tm.rename (Tm.spread args) (f W))
      rw [act_rename hg _ (hf W _ hW).1]

/-- Assignments whose bodies agree on the unknowns of a code act alike on it. -/
theorem act_congr {σ τ : Nat → Tm} : ∀ {t : Tm}, (∀ W ∈ Tm.unknowns t, σ W = τ W) → Tm.act σ t = Tm.act τ t
  | .loc _, _ => rfl
  | .gnd, _ => rfl
  | .arr A B, h => by
      simp only [Tm.act]
      rw [act_congr fun W hW => h W (by simp [Tm.unknowns, hW]),
        act_congr fun W hW => h W (by simp [Tm.unknowns, hW])]
  | .app W _, h => by
      simp only [Tm.act]
      rw [h W (by simp [Tm.unknowns])]

/-! ## The frames -/

/-- The terms over a context: its scoped codes. -/
abbrev Term (Δ : Ctx) : Type := {t : Tm // Scoped Δ t}

/-- The typed assignments. -/
abbrev Assign (Δ Γ : Ctx) : Type := {σ : Nat → Tm // TyA Δ Γ σ}

/-- **The frames of Miller codes.** Two terms are equal when they are the same code. -/
def frames : Frames Term Assign where
  E s t := s.1 = t.1
  equivalence _ := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  act σ t := ⟨Tm.act σ.1 t.1, Scoped.act σ.2 t.2⟩
  id Δ := ⟨idA Δ, idA_typed Δ⟩
  comp g f := ⟨compA g.1 f.1, compA_typed f.2 g.2⟩
  act_id t := Subtype.ext (act_id t.2)
  act_comp g f t := Subtype.ext (act_comp g.2 f.2 t.2)
  preserves := @fun _ _ σ s t h => by
    show Tm.act σ.1 s.1 = Tm.act σ.1 t.1
    rw [show s.1 = t.1 from h]

theorem models_iff {Δ Γ : Ctx} (σ : Assign Δ Γ) (S : EquationStore (Term Δ)) :
    frames.Models σ S ↔ ∀ e ∈ S, Tm.act σ.1 e.1.1 = Tm.act σ.1 e.2.1 :=
  Iff.rfl

/-- **Assignments whose bodies agree on the declared unknowns agree on every term.** -/
theorem agree_of_bodies {Δ Γ : Ctx} {f g : Assign Δ Γ} (same : ∀ W, W < Δ.length → f.1 W = g.1 W) :
    Agree frames f g := by
  rintro ⟨t, sc⟩
  show Tm.act f.1 t = Tm.act g.1 t
  apply act_congr
  intro W hW
  apply same
  clear same
  induction sc with
  | loc _ => simp [Tm.unknowns] at hW
  | gnd => simp [Tm.unknowns] at hW
  | arr _ _ ihA ihB =>
      simp only [Tm.unknowns, Finset.mem_union] at hW
      rcases hW with hW | hW
      · exact ihA hW
      · exact ihB hW
  | app hW' =>
      simp only [Tm.unknowns, Finset.mem_singleton] at hW
      subst hW
      exact (List.getElem?_eq_some_iff.mp hW').1

/-- The body that `idA` gives an unknown acts as the unknown's own body. -/
theorem act_idA_body {Δ Γ : Ctx} {f : Nat → Tm} (hf : TyA Δ Γ f) {W k : Nat} (hW : Δ[W]? = some k) :
    Tm.act f (idA Δ W) = f W := by
  show Tm.rename (Tm.spread (List.range (arity Δ W))) (f W) = f W
  apply Tm.rename_fix _ (hf W k hW).2
  intro i hi
  rw [arity_of hW, Tm.spread_of_lt (by rw [List.length_range]; exact hi), List.getElem_range]

end MillerCodes

#print axioms MillerCodes.act_rename
#print axioms MillerCodes.act_id
#print axioms MillerCodes.act_comp
#print axioms MillerCodes.agree_of_bodies

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
