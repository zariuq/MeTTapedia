import Mathlib.Data.Finset.Card
import Mettapedia.GSLT.Logic.PropositionalResolution

/-!
# Refutation completeness of propositional resolution

Davis–Putnam induction on the atom set. A restriction `Γ[n↦⊤]` drops
clauses containing `n` and erases `¬n`. A refutation of both restrictions
lifts to a refutation of `Γ`.

No Foundation. No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalResolution

open Mettapedia.GSLT.Logic.PropositionalFormula

def litAtom : Literal → Nat
  | .pos n => n
  | .neg n => n

def withoutNeg (n : Nat) (c : Clause) : Clause :=
  c.filter (fun l => l ≠ Literal.neg n)

def withoutPos (n : Nat) (c : Clause) : Clause :=
  c.filter (fun l => l ≠ Literal.pos n)

def restrictTrue (n : Nat) (Γ : CNF) : CNF :=
  (Γ.filter (fun c => Literal.pos n ∉ c)).map (withoutNeg n)

def restrictFalse (n : Nat) (Γ : CNF) : CNF :=
  (Γ.filter (fun c => Literal.neg n ∉ c)).map (withoutPos n)

def clauseAtoms : Clause → Finset Nat
  | [] => ∅
  | l :: c => insert (litAtom l) (clauseAtoms c)

def cnfAtoms : CNF → Finset Nat
  | [] => ∅
  | c :: Γ => clauseAtoms c ∪ cnfAtoms Γ

theorem mem_clauseAtoms {n : Nat} : (c : Clause) →
    n ∈ clauseAtoms c ↔ ∃ l ∈ c, litAtom l = n
  | [] => by simp [clauseAtoms]
  | l :: c => by
      constructor
      · intro h
        simp [clauseAtoms] at h
        cases h with
        | inl he => exact ⟨l, List.mem_cons_self, he.symm⟩
        | inr htail =>
            obtain ⟨l', hl', he⟩ := (mem_clauseAtoms (c := c)).mp htail
            exact ⟨l', List.mem_cons_of_mem _ hl', he⟩
      · rintro ⟨l', hl', he⟩
        simp [clauseAtoms]
        simp [List.mem_cons] at hl'
        cases hl' with
        | inl h =>
            subst h
            exact Or.inl he.symm
        | inr h =>
            exact Or.inr ((mem_clauseAtoms (c := c)).mpr ⟨l', h, he⟩)

theorem mem_cnfAtoms {n : Nat} : (Γ : CNF) →
    n ∈ cnfAtoms Γ ↔ ∃ c ∈ Γ, n ∈ clauseAtoms c
  | [] => by simp [cnfAtoms]
  | c :: Γ => by
      constructor
      · intro h
        simp [cnfAtoms] at h
        cases h with
        | inl hc => exact ⟨c, List.mem_cons_self, hc⟩
        | inr htail =>
            obtain ⟨c', hc', hn⟩ := (mem_cnfAtoms (Γ := Γ)).mp htail
            exact ⟨c', List.mem_cons_of_mem _ hc', hn⟩
      · rintro ⟨c', hc', hn⟩
        simp [cnfAtoms]
        simp [List.mem_cons] at hc'
        cases hc' with
        | inl h =>
            subst h
            exact Or.inl hn
        | inr h =>
            exact Or.inr ((mem_cnfAtoms (Γ := Γ)).mpr ⟨c', h, hn⟩)

theorem clause_eq_nil_of_atoms {c : Clause} (h : clauseAtoms c = ∅) : c = [] := by
  cases c with
  | nil => rfl
  | cons l c =>
      simp [clauseAtoms] at h

theorem mem_withoutNeg {n : Nat} {c : Clause} {l : Literal} :
    l ∈ withoutNeg n c ↔ l ∈ c ∧ l ≠ Literal.neg n := by
  simp [withoutNeg, List.mem_filter]

theorem mem_withoutPos {n : Nat} {c : Clause} {l : Literal} :
    l ∈ withoutPos n c ↔ l ∈ c ∧ l ≠ Literal.pos n := by
  simp [withoutPos, List.mem_filter]

theorem mem_restrictTrue {n : Nat} {Γ : CNF} {c' : Clause} :
    c' ∈ restrictTrue n Γ ↔
      ∃ c ∈ Γ, Literal.pos n ∉ c ∧ withoutNeg n c = c' := by
  simp [restrictTrue, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, hp⟩, rfl⟩
    exact ⟨c, hc, hp, rfl⟩
  · rintro ⟨c, hc, hp, rfl⟩
    exact ⟨c, ⟨hc, hp⟩, rfl⟩

theorem mem_restrictFalse {n : Nat} {Γ : CNF} {c' : Clause} :
    c' ∈ restrictFalse n Γ ↔
      ∃ c ∈ Γ, Literal.neg n ∉ c ∧ withoutPos n c = c' := by
  simp [restrictFalse, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, hn⟩, rfl⟩
    exact ⟨c, hc, hn, rfl⟩
  · rintro ⟨c, hc, hn, rfl⟩
    exact ⟨c, ⟨hc, hn⟩, rfl⟩

theorem n_not_mem_restrictTrue_atoms (n : Nat) (Γ : CNF) :
    n ∉ cnfAtoms (restrictTrue n Γ) := by
  intro hn
  obtain ⟨c', hc', ha⟩ := (mem_cnfAtoms (Γ := restrictTrue n Γ)).mp hn
  obtain ⟨c, hc, hnpos, rfl⟩ := mem_restrictTrue.mp hc'
  obtain ⟨l, hl, he⟩ := (mem_clauseAtoms (c := withoutNeg n c)).mp ha
  have hl' := mem_withoutNeg.mp hl
  cases l with
  | pos m =>
      have : m = n := he
      subst this
      exact hnpos hl'.1
  | neg m =>
      have : m = n := he
      subst this
      exact hl'.2 rfl

theorem n_not_mem_restrictFalse_atoms (n : Nat) (Γ : CNF) :
    n ∉ cnfAtoms (restrictFalse n Γ) := by
  intro hn
  obtain ⟨c', hc', ha⟩ := (mem_cnfAtoms (Γ := restrictFalse n Γ)).mp hn
  obtain ⟨c, hc, hnneg, rfl⟩ := mem_restrictFalse.mp hc'
  obtain ⟨l, hl, he⟩ := (mem_clauseAtoms (c := withoutPos n c)).mp ha
  have hl' := mem_withoutPos.mp hl
  cases l with
  | pos m =>
      have : m = n := he
      subst this
      exact hl'.2 rfl
  | neg m =>
      have : m = n := he
      subst this
      exact hnneg hl'.1

theorem restrictTrue_atoms_subset (n : Nat) (Γ : CNF) :
    cnfAtoms (restrictTrue n Γ) ⊆ cnfAtoms Γ := by
  intro m hm
  obtain ⟨c', hc', ha⟩ := (mem_cnfAtoms (Γ := restrictTrue n Γ)).mp hm
  obtain ⟨c, hc, _, rfl⟩ := mem_restrictTrue.mp hc'
  obtain ⟨l, hl, he⟩ := (mem_clauseAtoms (c := withoutNeg n c)).mp ha
  have hl' := (mem_withoutNeg.mp hl).1
  exact (mem_cnfAtoms (Γ := Γ)).mpr ⟨c, hc, (mem_clauseAtoms (c := c)).mpr ⟨l, hl', he⟩⟩

theorem restrictFalse_atoms_subset (n : Nat) (Γ : CNF) :
    cnfAtoms (restrictFalse n Γ) ⊆ cnfAtoms Γ := by
  intro m hm
  obtain ⟨c', hc', ha⟩ := (mem_cnfAtoms (Γ := restrictFalse n Γ)).mp hm
  obtain ⟨c, hc, _, rfl⟩ := mem_restrictFalse.mp hc'
  obtain ⟨l, hl, he⟩ := (mem_clauseAtoms (c := withoutPos n c)).mp ha
  have hl' := (mem_withoutPos.mp hl).1
  exact (mem_cnfAtoms (Γ := Γ)).mpr ⟨c, hc, (mem_clauseAtoms (c := c)).mpr ⟨l, hl', he⟩⟩

theorem restrictTrue_card_lt {n : Nat} {Γ : CNF} (hn : n ∈ cnfAtoms Γ) :
    (cnfAtoms (restrictTrue n Γ)).card < (cnfAtoms Γ).card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨restrictTrue_atoms_subset n Γ, by
      intro h
      have := n_not_mem_restrictTrue_atoms n Γ
      exact this (h.symm ▸ hn)⟩

theorem restrictFalse_card_lt {n : Nat} {Γ : CNF} (hn : n ∈ cnfAtoms Γ) :
    (cnfAtoms (restrictFalse n Γ)).card < (cnfAtoms Γ).card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨restrictFalse_atoms_subset n Γ, by
      intro h
      have := n_not_mem_restrictFalse_atoms n Γ
      exact this (h.symm ▸ hn)⟩

theorem sat_update_true (v : Nat → Bool) (n : Nat) (A : Nat) :
    (fun m => if m = n then true else v m) A =
      if A = n then true else v A :=
  rfl

theorem unsat_restrictTrue {n : Nat} {Γ : CNF} (h : Unsat Γ) :
    Unsat (restrictTrue n Γ) := by
  intro v
  cases hv : CNF.sat v (restrictTrue n Γ) with
  | false => rfl
  | true =>
      let v' : Nat → Bool := fun m => if m = n then true else v m
      have hsatΓ : CNF.sat v' Γ = true := by
        apply List.all_eq_true.mpr
        intro c hc
        by_cases hp : Literal.pos n ∈ c
        · refine List.any_eq_true.mpr ⟨.pos n, hp, ?_⟩
          simp [Literal.sat, v']
        · have hc' : withoutNeg n c ∈ restrictTrue n Γ :=
            mem_restrictTrue.mpr ⟨c, hc, hp, rfl⟩
          have hsat : Clause.sat v (withoutNeg n c) = true :=
            List.all_eq_true.mp hv _ hc'
          obtain ⟨l, hl, hsv⟩ := List.any_eq_true.mp hsat
          have hl' := mem_withoutNeg.mp hl
          refine List.any_eq_true.mpr ⟨l, hl'.1, ?_⟩
          cases l with
          | pos m =>
              simp [Literal.sat, v'] at hsv ⊢
              exact Or.inr hsv
          | neg m =>
              have hne : m ≠ n := by
                intro he
                exact hl'.2 (he ▸ rfl)
              simp [Literal.sat, v', hne] at hsv ⊢
              exact hsv
      have hun := h v'
      simp [hsatΓ] at hun

theorem unsat_restrictFalse {n : Nat} {Γ : CNF} (h : Unsat Γ) :
    Unsat (restrictFalse n Γ) := by
  intro v
  cases hv : CNF.sat v (restrictFalse n Γ) with
  | false => rfl
  | true =>
      let v' : Nat → Bool := fun m => if m = n then false else v m
      have hsatΓ : CNF.sat v' Γ = true := by
        apply List.all_eq_true.mpr
        intro c hc
        by_cases hnneg : Literal.neg n ∈ c
        · refine List.any_eq_true.mpr ⟨.neg n, hnneg, ?_⟩
          simp [Literal.sat, v']
        · have hc' : withoutPos n c ∈ restrictFalse n Γ :=
            mem_restrictFalse.mpr ⟨c, hc, hnneg, rfl⟩
          have hsat : Clause.sat v (withoutPos n c) = true :=
            List.all_eq_true.mp hv _ hc'
          obtain ⟨l, hl, hsv⟩ := List.any_eq_true.mp hsat
          have hl' := mem_withoutPos.mp hl
          refine List.any_eq_true.mpr ⟨l, hl'.1, ?_⟩
          cases l with
          | pos m =>
              have hne : m ≠ n := by
                intro he
                exact hl'.2 (he ▸ rfl)
              simp [Literal.sat, v', hne] at hsv ⊢
              exact hsv
          | neg m =>
              simp [Literal.sat, v'] at hsv ⊢
              exact Or.inr hsv
      have hun := h v'
      simp [hsatΓ] at hun

theorem filter_filter_comm (c : Clause) (p q : Literal → Bool) :
    (c.filter fun l => p l).filter (fun l => q l) =
      (c.filter fun l => q l).filter (fun l => p l) := by
  simp [List.filter_filter, Bool.and_comm]

theorem withoutNeg_resolvent (n m : Nat) (c d : Clause) :
    withoutNeg n (resolvent m c d) =
      resolvent m (withoutNeg n c) (withoutNeg n d) := by
  simp [withoutNeg, resolvent, List.filter_append, List.filter_filter,
    Bool.and_comm]

theorem withoutPos_resolvent (n m : Nat) (c d : Clause) :
    withoutPos n (resolvent m c d) =
      resolvent m (withoutPos n c) (withoutPos n d) := by
  simp [withoutPos, resolvent, List.filter_append, List.filter_filter,
    Bool.and_comm]

theorem lift_restrictTrue {n : Nat} {Γ : CNF} {c' : Clause}
    (h : ClauseDerives (restrictTrue n Γ) c') :
    ∃ c, ClauseDerives Γ c ∧ withoutNeg n c = c' ∧ Literal.pos n ∉ c := by
  induction h with
  | ax hmem =>
      obtain ⟨c, hc, hnpos, rfl⟩ := mem_restrictTrue.mp hmem
      exact ⟨c, .ax hc, rfl, hnpos⟩
  | resolve m hc hd hp hn ihc ihd =>
      obtain ⟨c, dc, heqc, hpc⟩ := ihc
      obtain ⟨d, dd, heqd, hpd⟩ := ihd
      subst heqc
      subst heqd
      have hmc : Literal.pos m ∈ c := (mem_withoutNeg.mp hp).1
      have hmd : Literal.neg m ∈ d := (mem_withoutNeg.mp hn).1
      have hm_ne : m ≠ n := by
        intro he
        subst he
        exact hpc (mem_withoutNeg.mp hp).1
      refine ⟨resolvent m c d, .resolve m dc dd hmc hmd, ?_, ?_⟩
      · exact withoutNeg_resolvent n m c d
      · intro hin
        simp only [resolvent] at hin
        cases (List.mem_append.mp hin) with
        | inl h => exact hpc (List.mem_of_mem_filter h)
        | inr h => exact hpd (List.mem_of_mem_filter h)

theorem lift_restrictFalse {n : Nat} {Γ : CNF} {c' : Clause}
    (h : ClauseDerives (restrictFalse n Γ) c') :
    ∃ c, ClauseDerives Γ c ∧ withoutPos n c = c' ∧ Literal.neg n ∉ c := by
  induction h with
  | ax hmem =>
      obtain ⟨c, hc, hnneg, rfl⟩ := mem_restrictFalse.mp hmem
      exact ⟨c, .ax hc, rfl, hnneg⟩
  | resolve m hc hd hp hn ihc ihd =>
      obtain ⟨c, dc, heqc, hnc⟩ := ihc
      obtain ⟨d, dd, heqd, hnd⟩ := ihd
      subst heqc
      subst heqd
      have hmc : Literal.pos m ∈ c := (mem_withoutPos.mp hp).1
      have hmd : Literal.neg m ∈ d := (mem_withoutPos.mp hn).1
      refine ⟨resolvent m c d, .resolve m dc dd hmc hmd, ?_, ?_⟩
      · exact withoutPos_resolvent n m c d
      · intro hin
        simp only [resolvent] at hin
        cases (List.mem_append.mp hin) with
        | inl h => exact hnc (List.mem_of_mem_filter h)
        | inr h => exact hnd (List.mem_of_mem_filter h)

theorem onlyNeg_of_withoutNeg_nil {n : Nat} {c : Clause}
    (h : withoutNeg n c = []) : ∀ l ∈ c, l = Literal.neg n := by
  intro l hl
  by_contra hne
  have : l ∈ withoutNeg n c := mem_withoutNeg.mpr ⟨hl, hne⟩
  simp [h] at this

theorem onlyPos_of_withoutPos_nil {n : Nat} {c : Clause}
    (h : withoutPos n c = []) : ∀ l ∈ c, l = Literal.pos n := by
  intro l hl
  by_contra hne
  have : l ∈ withoutPos n c := mem_withoutPos.mpr ⟨hl, hne⟩
  simp [h] at this

theorem resolve_only_pos_neg {n : Nat} {c d : Clause}
    (hc : ∀ l ∈ c, l = Literal.pos n) (hd : ∀ l ∈ d, l = Literal.neg n)
    (_hpc : Literal.pos n ∈ c) (_hnd : Literal.neg n ∈ d) :
    resolvent n c d = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro l hl
  simp [resolvent, List.mem_append, List.mem_filter] at hl
  cases hl with
  | inl h =>
      have := hc l h.1
      exact h.2 this
  | inr h =>
      have := hd l h.1
      exact h.2 this

theorem hasEmpty_of_unsat_no_atoms {Γ : CNF}
    (hA : cnfAtoms Γ = ∅) (hU : Unsat Γ) : [] ∈ Γ := by
  cases Γ with
  | nil => exact (not_unsat_nil hU).elim
  | cons c Γ =>
      have hcA : clauseAtoms c = ∅ := by
        simp [cnfAtoms, Finset.union_eq_empty] at hA
        exact hA.1
      have hc : c = [] := clause_eq_nil_of_atoms hcA
      subst hc
      exact List.mem_cons_self

theorem exists_mem_of_ne_nil {c : Clause} (h : c ≠ []) :
    ∃ l, l ∈ c := by
  cases c with
  | nil => exact (h rfl).elim
  | cons l _ => exact ⟨l, List.mem_cons_self⟩

theorem complete_of_card (k : Nat) :
    ∀ (Γ : CNF), (cnfAtoms Γ).card ≤ k → Unsat Γ → ClauseDerives Γ [] := by
  induction k with
  | zero =>
      intro Γ hle hU
      have hA : cnfAtoms Γ = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
      exact .ax (hasEmpty_of_unsat_no_atoms hA hU)
  | succ k ih =>
      intro Γ hle hU
      by_cases hsmall : (cnfAtoms Γ).card ≤ k
      · exact ih Γ hsmall hU
      · have hcard : (cnfAtoms Γ).card = k + 1 := by omega
        have hpos : 0 < (cnfAtoms Γ).card := by
          rw [hcard]
          exact Nat.succ_pos _
        obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
        have hT : Unsat (restrictTrue n Γ) := unsat_restrictTrue hU
        have hF : Unsat (restrictFalse n Γ) := unsat_restrictFalse hU
        have dT : ClauseDerives (restrictTrue n Γ) [] :=
          ih _ (Nat.lt_succ_iff.mp
            (Nat.lt_of_lt_of_eq (restrictTrue_card_lt hn) hcard)) hT
        have dF : ClauseDerives (restrictFalse n Γ) [] :=
          ih _ (Nat.lt_succ_iff.mp
            (Nat.lt_of_lt_of_eq (restrictFalse_card_lt hn) hcard)) hF
        obtain ⟨cT, dcT, hcT, _⟩ := lift_restrictTrue dT
        obtain ⟨cF, dcF, hcF, _⟩ := lift_restrictFalse dF
        by_cases hTnil : cT = []
        · subst hTnil
          exact dcT
        · by_cases hFnil : cF = []
          · subst hFnil
            exact dcF
          · obtain ⟨lT, hlT⟩ := exists_mem_of_ne_nil hTnil
            obtain ⟨lF, hlF⟩ := exists_mem_of_ne_nil hFnil
            have hnegT : Literal.neg n ∈ cT := by
              simpa [onlyNeg_of_withoutNeg_nil hcT lT hlT] using hlT
            have hposF : Literal.pos n ∈ cF := by
              simpa [onlyPos_of_withoutPos_nil hcF lF hlF] using hlF
            have hres : resolvent n cF cT = [] :=
              resolve_only_pos_neg
                (onlyPos_of_withoutPos_nil hcF)
                (onlyNeg_of_withoutNeg_nil hcT)
                hposF hnegT
            have d := ClauseDerives.resolve n dcF dcT hposF hnegT
            simpa [hres] using d

/-- Unsatisfiable CNFs derive the empty clause. -/
theorem complete (Γ : CNF) (h : Unsat Γ) : ClauseDerives Γ [] :=
  complete_of_card (cnfAtoms Γ).card Γ le_rfl h

theorem complete_multistep (Γ : CNF) (h : Unsat Γ) :
    ∃ Δ : CNF, resolutionGSLT.MultiStep Γ Δ ∧ ([] : Clause) ∈ Δ :=
  derives_multistep (complete Γ h)

#print axioms complete
#print axioms complete_multistep
#print axioms derives_empty_unsat

end Mettapedia.GSLT.Logic.PropositionalResolution
