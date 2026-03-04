import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mettapedia.Languages.MeTTa.TensorDSL.Valence

/-!
# MeTTa Tensor DSL Reduction and Equality

Formal one-step reduction rules (structural/algebraic) and an induced
equivalence relation.
-/

namespace Mettapedia.Languages.MeTTa.TensorDSL

open Expr

inductive Reduces : Expr → Expr → Prop where
  | add_comm (a b : Expr) :
      Reduces (.add a b) (.add b a)
  | add_assoc (a b c : Expr) :
      Reduces (.add (.add a b) c) (.add a (.add b c))
  | mul_assoc (a b c : Expr) :
      Reduces (.mul (.mul a b) c) (.mul a (.mul b c))
  | add_left {a a' b : Expr} :
      Reduces a a' → Reduces (.add a b) (.add a' b)
  | add_right {a b b' : Expr} :
      Reduces b b' → Reduces (.add a b) (.add a b')
  | mul_left {a a' b : Expr} :
      Reduces a a' → Reduces (.mul a b) (.mul a' b)
  | mul_right {a b b' : Expr} :
      Reduces b b' → Reduces (.mul a b) (.mul a b')

def Eqv (a b : Expr) : Prop :=
  Relation.ReflTransGen Reduces a b ∧ Relation.ReflTransGen Reduces b a

namespace Eqv

theorem refl (a : Expr) : Eqv a a :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem symm {a b : Expr} (h : Eqv a b) : Eqv b a :=
  ⟨h.2, h.1⟩

theorem trans {a b c : Expr} (hab : Eqv a b) (hbc : Eqv b c) : Eqv a c :=
  ⟨Relation.ReflTransGen.trans hab.1 hbc.1, Relation.ReflTransGen.trans hbc.2 hab.2⟩

theorem add_comm (a b : Expr) : Eqv (.add a b) (.add b a) :=
  ⟨Relation.ReflTransGen.single (Reduces.add_comm a b),
   Relation.ReflTransGen.single (Reduces.add_comm b a)⟩

end Eqv

namespace Valence

theorem append_arity (v₁ v₂ : Valence) :
    (Valence.append v₁ v₂).arity = v₁.arity + v₂.arity := by
  rcases v₁ with ⟨u₁, d₁⟩
  rcases v₂ with ⟨u₂, d₂⟩
  simp [Valence.append, Valence.arity, Nat.add_assoc, Nat.add_left_comm]

end Valence

theorem reduces_preserves_valence_arity {e e' : Expr}
    (h : Reduces e e') : (Expr.valence e).arity = (Expr.valence e').arity := by
  induction h with
  | add_comm a b =>
    simp [Expr.valence, Valence.append_arity, Nat.add_comm]
  | add_assoc a b c =>
    simp [Expr.valence, Valence.append_arity, Nat.add_assoc]
  | mul_assoc a b c =>
    simp [Expr.valence, Valence.append_arity, Nat.add_assoc]
  | add_left h ih =>
    simp [Expr.valence, Valence.append_arity, ih]
  | add_right h ih =>
    simp [Expr.valence, Valence.append_arity, ih]
  | mul_left h ih =>
    simp [Expr.valence, Valence.append_arity, ih]
  | mul_right h ih =>
    simp [Expr.valence, Valence.append_arity, ih]

theorem eqv_preserves_valence_arity {e e' : Expr}
    (h : Eqv e e') : (Expr.valence e).arity = (Expr.valence e').arity := by
  exact Relation.ReflTransGen.trans_induction_on h.1
    (fun _ => rfl)
    (fun hstep => reduces_preserves_valence_arity hstep)
    (fun _ _ ih₁ ih₂ => Eq.trans ih₁ ih₂)

end Mettapedia.Languages.MeTTa.TensorDSL
