import Mettapedia.GSLT.Core.GSLT

/-!
# Classical propositional formulas as a GSLT

The logic is not cut-elimination. Cut-elim is a dynamics on proofs
(`PropositionalCut`). Here the language is a GSLT: formulas, Boolean
equations, empty rewrite relation. Inference is the resolution GSLT.
CNF is a translation, not a morphism.

No Foundation. No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalFormula

open Mettapedia.GSLT

inductive Formula where
  | atom : Nat → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
deriving DecidableEq

/-- Negation-normal: `not` only on atoms. -/
def IsNNF : Formula → Prop
  | .atom _ => True
  | .not (.atom _) => True
  | .not _ => False
  | .and A B => IsNNF A ∧ IsNNF B
  | .or A B => IsNNF A ∧ IsNNF B

inductive BoolEq : Formula → Formula → Prop where
  | refl (A : Formula) : BoolEq A A
  | symm {A B} : BoolEq A B → BoolEq B A
  | trans {A B C} : BoolEq A B → BoolEq B C → BoolEq A C
  | not {A B} : BoolEq A B → BoolEq (.not A) (.not B)
  | and {A A' B B'} : BoolEq A A' → BoolEq B B' → BoolEq (.and A B) (.and A' B')
  | or {A A' B B'} : BoolEq A A' → BoolEq B B' → BoolEq (.or A B) (.or A' B')
  | dn (A : Formula) : BoolEq (.not (.not A)) A
  | deMorgan_and (A B : Formula) :
      BoolEq (.not (.and A B)) (.or (.not A) (.not B))
  | deMorgan_or (A B : Formula) :
      BoolEq (.not (.or A B)) (.and (.not A) (.not B))
  | and_comm (A B : Formula) : BoolEq (.and A B) (.and B A)
  | or_comm (A B : Formula) : BoolEq (.or A B) (.or B A)
  | and_assoc (A B C : Formula) :
      BoolEq (.and (.and A B) C) (.and A (.and B C))
  | or_assoc (A B C : Formula) :
      BoolEq (.or (.or A B) C) (.or A (.or B C))

def propositionalEqGSLT : GSLT where
  Term := Formula
  equations := ⟨BoolEq, ⟨BoolEq.refl, BoolEq.symm, BoolEq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

theorem eqGSLT_no_step (A B : Formula) :
    ¬ propositionalEqGSLT.Step A B :=
  fun h => h

/-! ## NNF as a function, identified by `BoolEq` -/

def negNNF : Formula → Formula
  | .atom n => .not (.atom n)
  | .not A => A
  | .and A B => .or (negNNF A) (negNNF B)
  | .or A B => .and (negNNF A) (negNNF B)

def toNNF : Formula → Formula
  | .atom n => .atom n
  | .not A => negNNF (toNNF A)
  | .and A B => .and (toNNF A) (toNNF B)
  | .or A B => .or (toNNF A) (toNNF B)

theorem isNNF_negNNF {A : Formula} (h : IsNNF A) : IsNNF (negNNF A) := by
  induction A with
  | atom n => trivial
  | not A ih =>
      cases A with
      | atom n => trivial
      | not _ => cases h
      | and _ _ => cases h
      | or _ _ => cases h
  | and A B ihA ihB =>
      rcases h with ⟨hA, hB⟩
      exact ⟨ihA hA, ihB hB⟩
  | or A B ihA ihB =>
      rcases h with ⟨hA, hB⟩
      exact ⟨ihA hA, ihB hB⟩

theorem isNNF_toNNF (A : Formula) : IsNNF (toNNF A) := by
  induction A with
  | atom n => trivial
  | not A ih => exact isNNF_negNNF ih
  | and A B ihA ihB => exact ⟨ihA, ihB⟩
  | or A B ihA ihB => exact ⟨ihA, ihB⟩

theorem boolEq_not_negNNF {A : Formula} (h : IsNNF A) :
    BoolEq (.not A) (negNNF A) := by
  induction A with
  | atom n => exact BoolEq.refl _
  | not A ih =>
      cases A with
      | atom n => exact BoolEq.dn _
      | not _ => cases h
      | and _ _ => cases h
      | or _ _ => cases h
  | and A B ihA ihB =>
      rcases h with ⟨hA, hB⟩
      exact (BoolEq.deMorgan_and A B).trans (BoolEq.or (ihA hA) (ihB hB))
  | or A B ihA ihB =>
      rcases h with ⟨hA, hB⟩
      exact (BoolEq.deMorgan_or A B).trans (BoolEq.and (ihA hA) (ihB hB))

theorem boolEq_toNNF (A : Formula) : BoolEq A (toNNF A) := by
  induction A with
  | atom n => exact BoolEq.refl _
  | not A ih =>
      exact (BoolEq.not ih).trans (boolEq_not_negNNF (isNNF_toNNF A))
  | and A B ihA ihB => exact BoolEq.and ihA ihB
  | or A B ihA ihB => exact BoolEq.or ihA ihB

/-! ## Valuations (Boolean, so double-negation is computational) -/

def Formula.sat (v : Nat → Bool) : Formula → Bool
  | .atom n => v n
  | .not A => ! Formula.sat v A
  | .and A B => Formula.sat v A && Formula.sat v B
  | .or A B => Formula.sat v A || Formula.sat v B

theorem sat_of_boolEq {v : Nat → Bool} {A B : Formula} (h : BoolEq A B) :
    Formula.sat v A = Formula.sat v B := by
  induction h with
  | refl A => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihAB ihBC => exact ihAB.trans ihBC
  | not _ ih => simp [Formula.sat, ih]
  | and _ _ ihA ihB => simp [Formula.sat, ihA, ihB]
  | or _ _ ihA ihB => simp [Formula.sat, ihA, ihB]
  | dn A => simp [Formula.sat]
  | deMorgan_and A B => simp [Formula.sat]
  | deMorgan_or A B => simp [Formula.sat]
  | and_comm A B => simp [Formula.sat, Bool.and_comm]
  | or_comm A B => simp [Formula.sat, Bool.or_comm]
  | and_assoc A B C => simp [Formula.sat, Bool.and_assoc]
  | or_assoc A B C => simp [Formula.sat, Bool.or_assoc]

theorem sat_toNNF (v : Nat → Bool) (A : Formula) :
    Formula.sat v A = Formula.sat v (toNNF A) :=
  sat_of_boolEq (boolEq_toNNF A)

/-! ## Clauses (carrier of resolution) -/

inductive Literal where
  | pos : Nat → Literal
  | neg : Nat → Literal
deriving DecidableEq

def Literal.complement : Literal → Literal
  | .pos n => .neg n
  | .neg n => .pos n

theorem complement_involutive (l : Literal) :
    l.complement.complement = l := by
  cases l <;> rfl

def Literal.sat (v : Nat → Bool) : Literal → Bool
  | .pos n => v n
  | .neg n => ! v n

abbrev Clause := List Literal
abbrev CNF := List Clause

def Clause.sat (v : Nat → Bool) (c : Clause) : Bool :=
  c.any (Literal.sat v)

def CNF.sat (v : Nat → Bool) (Γ : CNF) : Bool :=
  Γ.all (Clause.sat v)

theorem empty_clause_unsat (v : Nat → Bool) : Clause.sat v [] = false :=
  rfl

theorem empty_cnf_sat (v : Nat → Bool) : CNF.sat v [] = true :=
  rfl

theorem sat_clause_append (v : Nat → Bool) (c d : Clause) :
    Clause.sat v (c ++ d) = (Clause.sat v c || Clause.sat v d) := by
  simp [Clause.sat, List.any_append]

theorem sat_cnf_append (v : Nat → Bool) (Γ Δ : CNF) :
    CNF.sat v (Γ ++ Δ) = (CNF.sat v Γ && CNF.sat v Δ) := by
  simp [CNF.sat, List.all_append]

theorem sat_cnf_cons (v : Nat → Bool) (c : Clause) (Γ : CNF) :
    CNF.sat v (c :: Γ) = (Clause.sat v c && CNF.sat v Γ) :=
  rfl

def distOr (cs ds : CNF) : CNF :=
  match cs with
  | [] => []
  | c :: cs => ds.map (fun d => c ++ d) ++ distOr cs ds

theorem sat_map_append (v : Nat → Bool) (c : Clause) (ds : CNF) :
    CNF.sat v (ds.map (fun d => c ++ d)) =
      (Clause.sat v c || CNF.sat v ds) := by
  induction ds with
  | nil => simp [CNF.sat]
  | cons d ds ih =>
      change (Clause.sat v (c ++ d) && CNF.sat v (ds.map (fun d => c ++ d))) =
        (Clause.sat v c || (Clause.sat v d && CNF.sat v ds))
      rw [sat_clause_append, ih]
      cases Clause.sat v c <;> cases Clause.sat v d <;> rfl

theorem sat_distOr (v : Nat → Bool) (cs ds : CNF) :
    CNF.sat v (distOr cs ds) = (CNF.sat v cs || CNF.sat v ds) := by
  induction cs with
  | nil => simp [distOr, CNF.sat]
  | cons c cs ih =>
      simp [distOr, sat_cnf_append, sat_map_append, ih, sat_cnf_cons,
        Bool.or_and_distrib_right]

/-! ## CNF of an NNF formula -/

def clausesOfNNF : (A : Formula) → IsNNF A → CNF
  | .atom n, _ => [[.pos n]]
  | .not A, h =>
      match A with
      | .atom n => [[.neg n]]
      | .not _ => False.elim h
      | .and _ _ => False.elim h
      | .or _ _ => False.elim h
  | .and A B, h => clausesOfNNF A h.1 ++ clausesOfNNF B h.2
  | .or A B, h => distOr (clausesOfNNF A h.1) (clausesOfNNF B h.2)

def toCNF (A : Formula) : CNF :=
  clausesOfNNF (toNNF A) (isNNF_toNNF A)

theorem sat_clausesOfNNF (v : Nat → Bool) :
    (A : Formula) → (h : IsNNF A) →
      CNF.sat v (clausesOfNNF A h) = Formula.sat v A
  | .atom n, _ => by
      simp [clausesOfNNF, CNF.sat, Clause.sat, Formula.sat, Literal.sat]
  | .not A, h =>
      match A with
      | .atom n => by
          simp [clausesOfNNF, CNF.sat, Clause.sat, Formula.sat, Literal.sat]
      | .not _ => False.elim h
      | .and _ _ => False.elim h
      | .or _ _ => False.elim h
  | .and A B, h => by
      simp [clausesOfNNF, sat_cnf_append, Formula.sat,
        sat_clausesOfNNF v A h.1, sat_clausesOfNNF v B h.2]
  | .or A B, h => by
      simp [clausesOfNNF, sat_distOr, Formula.sat,
        sat_clausesOfNNF v A h.1, sat_clausesOfNNF v B h.2]

theorem sat_toCNF (v : Nat → Bool) (A : Formula) :
    CNF.sat v (toCNF A) = Formula.sat v A := by
  rw [toCNF, sat_clausesOfNNF, ← sat_toNNF]

#print axioms eqGSLT_no_step
#print axioms isNNF_toNNF
#print axioms boolEq_toNNF
#print axioms sat_toCNF
#print axioms complement_involutive

end Mettapedia.GSLT.Logic.PropositionalFormula
