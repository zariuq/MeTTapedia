import Mettapedia.GSLT.GraphTheory.Basic

/-!
# Graph interpretation, environment action, and beta computation

The interpreter uses the powerset of the existing web. These laws connect its
environment action to the existing de Bruijn operations; no alternative term
syntax or semantic equality oracle is introduced.
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

variable (D : GraphModel)

/-- Environment action corresponding to insertion of fresh de Bruijn indices. -/
def Env.skip (ρ : Env D) (cutoff amount : Nat) : Env D :=
  fun n => if n < cutoff then ρ n else ρ (n + amount)

/-- Environment action corresponding to substitution and removal of one index. -/
def Env.insert (ρ : Env D) (index : Nat) (value : Set D.Carrier) : Env D :=
  fun n => if n < index then ρ n else if n = index then value else ρ (n - 1)

@[simp]
theorem Env.skip_extend (ρ : Env D) (argument : Set D.Carrier) (cutoff amount : Nat) :
    (ρ.extend argument).skip D (cutoff + 1) amount =
      (ρ.skip D cutoff amount).extend argument := by
  funext n
  cases n with
  | zero => simp [Env.skip, Env.extend]
  | succ n => simp [Env.skip, Env.extend, Nat.succ_add]

/-- Syntactic weakening has precisely its expected action on semantic inputs. -/
theorem interpret_shift (term : LambdaTerm) (ρ : Env D) (amount cutoff : Nat) :
    interpret D ρ (term.shift amount cutoff) =
      interpret D (ρ.skip D cutoff amount) term := by
  induction term generalizing ρ cutoff with
  | var n =>
      simp only [LambdaTerm.shift, interpret, Env.skip]
      split <;> rfl
  | lam body ih =>
      simp only [LambdaTerm.shift, interpret]
      congr 1
      funext argument
      rw [ih, Env.skip_extend]
  | app fn arg ihFn ihArg =>
      simp only [LambdaTerm.shift, interpret, ihFn, ihArg]

/-- Extending a weakened environment recovers the original free-variable inputs. -/
@[simp]
theorem Env.skip_extend_zero (ρ : Env D) (argument : Set D.Carrier) :
    (ρ.extend argument).skip D 0 1 = ρ := by
  funext n
  simp [Env.skip, Env.extend]

/-- A term weakened beneath a fresh binder keeps its original denotation. -/
theorem interpret_shift_extend (term : LambdaTerm) (ρ : Env D)
    (argument : Set D.Carrier) :
    interpret D (ρ.extend argument) (term.shift 1 0) = interpret D ρ term := by
  rw [interpret_shift, Env.skip_extend_zero]

@[simp]
theorem Env.insert_extend (ρ : Env D) (argument value : Set D.Carrier) (index : Nat) :
    (ρ.extend argument).insert D (index + 1) value =
      (ρ.insert D index value).extend argument := by
  funext n
  cases n with
  | zero => simp [Env.insert, Env.extend]
  | succ n =>
      simp only [Env.insert, Env.extend, Nat.succ_lt_succ_iff, Nat.succ.injEq,
        Nat.succ_sub_one]
      split_ifs with hlt heq
      · rfl
      · rfl
      · have hn : n ≠ 0 := by omega
        cases n with
        | zero => exact False.elim (hn rfl)
        | succ n => rfl

/-- The semantic substitution square, for every term and substitution index. -/
theorem interpret_subst (term replacement : LambdaTerm) (ρ : Env D) (index : Nat) :
    interpret D ρ (LambdaTerm.subst index replacement term) =
      interpret D (ρ.insert D index (interpret D ρ replacement)) term := by
  induction term generalizing ρ index replacement with
  | var n =>
      simp only [LambdaTerm.subst, interpret, Env.insert, beq_iff_eq]
      split_ifs <;> try rfl
      all_goals omega
  | lam body ih =>
      simp only [LambdaTerm.subst, interpret]
      congr 1
      funext argument
      rw [ih, interpret_shift_extend, Env.insert_extend]
  | app fn arg ihFn ihArg =>
      simp only [LambdaTerm.subst, interpret, ihFn, ihArg]

@[simp]
theorem Env.insert_zero (ρ : Env D) (value : Set D.Carrier) :
    ρ.insert D 0 value = ρ.extend value := by
  funext n
  cases n <;> simp [Env.insert, Env.extend]

/-- In particular, beta substitution evaluates the actual body in the extended
environment, not an unrelated closed representative. -/
theorem interpret_subst_zero (body argument : LambdaTerm) (ρ : Env D) :
    interpret D ρ (LambdaTerm.subst 0 argument body) =
      interpret D (ρ.extend (interpret D ρ argument)) body := by
  rw [interpret_subst, Env.insert_zero]

/-- Interpretation preserves pointwise enlargement of the actual environment. -/
theorem interpret_mono (term : LambdaTerm) {ρ σ : Env D} (h : ∀ n, ρ n ⊆ σ n) :
    interpret D ρ term ⊆ interpret D σ term := by
  induction term generalizing ρ σ with
  | var n => exact h n
  | lam body ih =>
      apply D.abstraction_mono
      intro argument
      apply ih
      intro n
      cases n with
      | zero => exact Set.Subset.rfl
      | succ n => exact h n
  | app fn arg ihFn ihArg => exact D.apply_mono (ihFn h) (ihArg h)

private theorem scottContinuous_eval {ι α : Type*} [Preorder α] (i : ι) :
    ScottContinuous (fun f : ι → α => f i) := by
  intro family _ _ value hLub
  exact (isLUB_pi.mp hLub) i

private theorem scottContinuous_pi {α β ι : Type*} [Preorder α] [Preorder β]
    (f : α → ι → β) (h : ∀ i, ScottContinuous (fun a => f a i)) :
    ScottContinuous f := by
  intro family hNonempty hDirected value hLub
  apply isLUB_pi.mpr
  intro i
  simpa only [Set.image_image, Function.comp_def, Function.eval] using
    h i hNonempty hDirected hLub

/-- Extension is continuous in the incoming argument denotation. -/
theorem Env.scottContinuous_extend_argument (ρ : Env D) :
    ScottContinuous (ρ.extend : Set D.Carrier → Env D) := by
  apply scottContinuous_pi
  intro n
  cases n with
  | zero => exact ScottContinuous.id
  | succ n => exact ScottContinuous.const (ρ n)

/-- Extension is continuous in the retained outer environment. -/
theorem Env.scottContinuous_extend_outer (argument : Set D.Carrier) :
    ScottContinuous (fun ρ : Env D => ρ.extend argument) := by
  apply scottContinuous_pi
  intro n
  cases n with
  | zero => exact ScottContinuous.const argument
  | succ n => exact scottContinuous_eval n

/-- Every term's actual interpretation is Scott-continuous in its environment.
The abstraction case uses finite graph encoding; the application case uses
joint continuity in both denotations. -/
theorem interpret_scottContinuous (term : LambdaTerm) :
    ScottContinuous (fun ρ : Env D => interpret D ρ term) := by
  induction term with
  | var n => exact scottContinuous_eval n
  | lam body ih =>
      apply ScottContinuous.comp
        (f := fun ρ : Env D => fun argument => interpret D (ρ.extend argument) body)
        (g := D.abstraction)
      · apply scottContinuous_pi
        intro argument
        exact (Env.scottContinuous_extend_outer D argument).comp ih
      · exact D.scottContinuous_abstraction
  | app fn arg ihFn ihArg =>
      exact (ihFn.prodMk ihArg).comp D.scottContinuous_apply_pair

/-- The body denotes a continuous function of its actual bound argument. -/
theorem interpret_body_scottContinuous (body : LambdaTerm) (ρ : Env D) :
    ScottContinuous (fun argument => interpret D (ρ.extend argument) body) :=
  (Env.scottContinuous_extend_argument D ρ).comp (interpret_scottContinuous D body)

/-- Beta computation preserves graph denotation. The proof derives continuity
from the term, applies the graph retraction, then uses semantic substitution. -/
theorem interpret_beta (body argument : LambdaTerm) (ρ : Env D) :
    interpret D ρ (.app (.lam body) argument) =
      interpret D ρ (LambdaTerm.subst 0 argument body) := by
  simp only [interpret]
  rw [D.apply_abstraction _ (interpret_body_scottContinuous D body ρ)]
  exact (interpret_subst_zero D body argument ρ).symm

/-- The shared parallel reduction preserves the actual denotation. -/
theorem interpret_parRed {term result : LambdaTerm} (h : term ⇛ result) :
    ∀ ρ : Env D, interpret D ρ term = interpret D ρ result := by
  induction h with
  | var n => intro ρ; rfl
  | lam _ ih =>
      intro ρ
      simp only [interpret]
      congr 1
      funext argument
      exact ih _
  | app _ _ ihFn ihArg =>
      intro ρ
      simp only [interpret, ihFn, ihArg]
  | beta hBody hArg ihBody ihArg =>
      intro ρ
      rw [interpret_beta, interpret_subst_zero, interpret_subst_zero, ihArg ρ]
      exact ihBody _

/-- Evidence for an entire beta computation can be retained without losing its
set-theoretic meaning. -/
theorem interpret_parRedStar {term result : LambdaTerm} (h : term ⇛* result) :
    ∀ ρ : Env D, interpret D ρ term = interpret D ρ result := by
  induction h with
  | refl => intro ρ; rfl
  | tail _ hStep ih => intro ρ; exact (ih ρ).trans (interpret_parRed D hStep ρ)

/-- The graph interpreter induces a genuine lambda theory. All congruence and
beta fields are proved from its actual operations, not supplied as assumptions. -/
def lambdaTheoryOf : LambdaTheory where
  equations := theoryOf D
  refl := fun _ _ => rfl
  symm := fun h ρ => (h ρ).symm
  trans := fun h₁ h₂ ρ => (h₁ ρ).trans (h₂ ρ)
  beta := fun body argument ρ => interpret_beta D body argument ρ
  congLam := fun h ρ => by
    simp only [interpret]
    congr 1
    funext argument
    exact h _
  congAppLeft := fun h ρ => by simp only [interpret, h ρ]
  congAppRight := fun h ρ => by simp only [interpret, h ρ]

/-- The graph-theory interface is inhabited by the same interpreted equations. -/
theorem lambdaTheoryOf_isGraphTheory : IsGraphTheory (lambdaTheoryOf D) :=
  ⟨D, rfl⟩

/-- Identity denotes the finite-input coding of the actual identity function. -/
theorem interpret_I (ρ : Env D) :
    interpret D ρ LambdaTerm.I = D.abstraction id := rfl

/-- K denotes the finite-input coding of a genuinely constant-result function. -/
theorem interpret_K (ρ : Env D) :
    interpret D ρ LambdaTerm.K =
      D.abstraction (fun A => D.abstraction (fun _ => A)) := rfl

/-- Every infinite web's induced theory distinguishes I from K. -/
theorem lambdaTheoryOf_consistent : (lambdaTheoryOf D).Consistent := by
  intro h
  have hIK := h (fun _ => ∅)
  rw [interpret_I, interpret_K] at hIK
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Carrier)
  have hApplied := congrArg (fun functions => D.apply functions ({x} : Set D.Carrier)) hIK
  rw [D.apply_abstraction id ScottContinuous.id] at hApplied
  have hConstContinuous :
      ScottContinuous (fun A : Set D.Carrier => D.abstraction (fun _ => A)) := by
    apply ScottContinuous.comp
      (f := fun A : Set D.Carrier => fun _ : Set D.Carrier => A)
      (g := D.abstraction)
    · apply scottContinuous_pi
      intro _
      exact ScottContinuous.id
    · exact D.scottContinuous_abstraction
  rw [D.apply_abstraction _ hConstContinuous] at hApplied
  change ({x} : Set D.Carrier) = D.abstraction (fun _ => ({x} : Set D.Carrier)) at hApplied
  have hEmpty : D.code (∅ : Finset D.Carrier) x ∈ ({x} : Set D.Carrier) := by
    exact hApplied.symm ▸ (D.code_mem_abstraction _ ∅ x).mpr (Set.mem_singleton x)
  have hSingleton : D.code ({x} : Finset D.Carrier) x ∈ ({x} : Set D.Carrier) := by
    exact hApplied.symm ▸ (D.code_mem_abstraction _ {x} x).mpr (Set.mem_singleton x)
  have hCodes : D.code (∅ : Finset D.Carrier) x = D.code ({x} : Finset D.Carrier) x :=
    (Set.mem_singleton_iff.mp hEmpty).trans (Set.mem_singleton_iff.mp hSingleton).symm
  have hInputs := (D.coding.decode_unique hCodes).1
  have : x ∈ (∅ : Finset D.Carrier) := hInputs ▸ Finset.mem_singleton_self x
  exact Finset.notMem_empty x this

end Mettapedia.GSLT.GraphTheory
