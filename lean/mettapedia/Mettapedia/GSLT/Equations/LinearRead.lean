import Mettapedia.GSLT.Equations.FactorizedRead

/-! # When the tree message eliminates the open bindings

For a linear pattern, every represented derivation has a consistent
substitution. A repeated variable adds an equality between positions;
dropping that equality can turn failure into success. With an already
bound valuation, local filters check it consistently even for a nonlinear
pattern. These are exact support results, separately from the meaning of
a projected natural-number count.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.LinearRead

open UniversalAlgebra RecipeMatching FactorizedRead

variable {S : Signature} {n : Nat}

def variableLayout : Term S → List Nat
  | .var v => [v]
  | .op _ args => (List.ofFn fun i => variableLayout (args i)).flatten

private theorem products_shape {A B : Type*} (label : A → B) {k : Nat}
    (alternatives : Fin k → List (List A)) (shape : Fin k → List B)
    (localShape : ∀ i ts, ts ∈ alternatives i → ts.map label = shape i)
    (trace : List A) (mem : trace ∈ products (List.ofFn alternatives)) :
    trace.map label = (List.ofFn shape).flatten := by
  induction k generalizing trace with
  | zero => simpa [products] using mem
  | succ k ih =>
    simp only [List.ofFn_succ, products, multiply, List.mem_flatMap, List.mem_map] at mem
    obtain ⟨left, hl, rest, hr, rfl⟩ := mem
    rw [List.ofFn_succ, List.flatten_cons, List.map_append, localShape _ _ hl]
    rw [ih (alternatives ∘ Fin.succ) (shape ∘ Fin.succ)
      (fun i => localShape i.succ) rest hr]
    rfl

theorem derivation_variables (g : Catalogue S (Fin n)) (p : Term S) (c : Fin n)
    (trace : List (Binding n)) (realized : trace ∈ derivations g p c) :
    trace.map Prod.fst = variableLayout p := by
  induction p generalizing c trace with
  | var v => simp [derivations] at realized; subst trace; rfl
  | op f ps ih =>
    simp only [derivations, List.mem_flatMap, Prod.exists] at realized
    obtain ⟨_, children, _, choices⟩ := realized
    exact products_shape Prod.fst _ (fun i => variableLayout (ps i))
      (fun i ts mem => ih i (children i) ts mem) trace choices

def assignment (fallback : Fin n) : List (Binding n) → Nat → Fin n
  | [], _ => fallback
  | (name, value) :: tail, q => if q = name then value else assignment fallback tail q

private theorem assignment_at (fallback : Fin n) (trace : List (Binding n))
    (linear : (trace.map Prod.fst).Nodup) {b : Binding n} (member : b ∈ trace) :
    assignment fallback trace b.1 = b.2 := by
  induction trace with
  | nil => simp at member
  | cons a tail ih =>
    obtain ⟨fresh, latter⟩ := List.nodup_cons.mp linear
    rcases List.mem_cons.mp member with rfl | h
    · rcases b with ⟨name, value⟩
      simp [assignment]
    · have different : b.1 ≠ a.1 := fun same => fresh (List.mem_map.mpr ⟨b, h, same⟩)
      rcases a with ⟨name, value⟩
      simp [assignment, different, ih latter h]

theorem linear_activity (g : Catalogue S (Fin n)) (p : Term S) (c : Fin n)
    (linear : (variableLayout p).Nodup) :
    0 < (messages g (fun _ => (1 : Nat)) p)[c.val] ↔ ∃ ρ, g.Matches ρ p c := by
  rw [message_exact, sumScore_one]
  constructor
  · intro nonempty
    obtain ⟨trace, h⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos nonempty)
    have tags := derivation_variables g p c trace h
    exact ⟨assignment c trace, (match_iff_derivation g _ p c).2
      ⟨trace, h, fun _ hb => assignment_at c trace (tags.symm ▸ linear) hb⟩⟩
  · rintro ⟨ρ, yes⟩
    obtain ⟨trace, h, _⟩ := (match_iff_derivation g ρ p c).1 yes
    exact List.length_pos_of_mem h

private theorem score_valid (P : Binding n → Prop) [DecidablePred P] (trace : List (Binding n)) :
    0 < score (fun b => if P b then (1 : Nat) else 0) trace ↔ ∀ b ∈ trace, P b := by
  induction trace with
  | nil => simp [score]
  | cons b trace ih =>
    change 0 < (if P b then 1 else 0) *
      score (fun b => if P b then (1 : Nat) else 0) trace ↔ _
    by_cases h : P b <;> simp [h, ih]

private theorem positive_valid (P : Binding n → Prop) [DecidablePred P]
    (traces : List (List (Binding n))) :
    0 < sumScore (fun b => if P b then (1 : Nat) else 0) traces ↔
      ∃ trace ∈ traces, ∀ b ∈ trace, P b := by
  induction traces with
  | nil => simp [sumScore]
  | cons trace rest ih =>
    change 0 < score (fun b => if P b then (1 : Nat) else 0) trace +
      sumScore (fun b => if P b then (1 : Nat) else 0) rest ↔ _
    simp only [Nat.add_pos_iff_pos_or_pos, score_valid, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem bound_activity (g : Catalogue S (Fin n)) (ρ : Nat → Fin n) (p : Term S) (c : Fin n) :
    0 < (messages g (fun b => if ρ b.1 = b.2 then (1 : Nat) else 0) p)[c.val] ↔
      g.Matches ρ p c := by
  rw [message_exact, positive_valid, match_iff_derivation]

end Mettapedia.GSLT.Equations.LinearRead
