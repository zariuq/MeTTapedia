import Mettapedia.GSLT.Logic.PropositionalFormula

/-!
# Propositional resolution as a GSLT

Terms are clause sets. One rewrite adds a resolvent. Equations are `Eq`
(clause order is part of the carrier). Empty clause is unsatisfiable.
Resolution preserves Boolean satisfaction. Clause-level derivability is
the inference calculus; refutation completeness is in
`PropositionalResolutionComplete`.

No Foundation. No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalResolution

open Mettapedia.GSLT
open Mettapedia.GSLT.Logic.PropositionalFormula

def resolvent (n : Nat) (c d : Clause) : Clause :=
  c.filter (fun l => l ≠ Literal.pos n) ++
    d.filter (fun l => l ≠ Literal.neg n)

inductive Resolve : CNF → CNF → Prop where
  | mk (n : Nat) (c d : Clause) (Γ : CNF)
      (hc : c ∈ Γ) (hd : d ∈ Γ)
      (hp : Literal.pos n ∈ c) (hn : Literal.neg n ∈ d) :
      Resolve Γ (resolvent n c d :: Γ)

def resolutionGSLT : GSLT where
  Term := CNF
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Resolve
  rewrites_resp_left := by
    intro t t' u htt step
    exact ⟨u, htt ▸ step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step huu
    exact huu ▸ step

theorem step_iff_resolve (Γ Δ : CNF) :
    resolutionGSLT.Step Γ Δ ↔ Resolve Γ Δ :=
  Iff.rfl

theorem empty_clause_cnf_unsat {Γ : CNF} (h : [] ∈ Γ) (v : Nat → Bool) :
    CNF.sat v Γ = false := by
  rw [CNF.sat, Bool.eq_false_iff]
  intro htrue
  have hnil : Clause.sat v [] = true := List.all_eq_true.mp htrue [] h
  simp [Clause.sat] at hnil

theorem sat_filter_of_false {v : Nat → Bool} {c : Clause} {l : Literal}
    (hsat : Clause.sat v c = true) (hfalse : Literal.sat v l = false) :
    Clause.sat v (c.filter (fun l' => l' ≠ l)) = true := by
  have ⟨x, hx, hv⟩ := List.any_eq_true.mp hsat
  have : x ≠ l := by
    intro h
    subst h
    simp [hfalse] at hv
  refine List.any_eq_true.mpr ⟨x, ?_, hv⟩
  exact List.mem_filter.mpr ⟨hx, by simp [this]⟩

theorem sat_resolvent (v : Nat → Bool) (n : Nat) (c d : Clause)
    (hc : Clause.sat v c = true) (hd : Clause.sat v d = true)
    (_hp : Literal.pos n ∈ c) (_hn : Literal.neg n ∈ d) :
    Clause.sat v (resolvent n c d) = true := by
  rw [resolvent, sat_clause_append]
  cases hv : v n with
  | true =>
      have hneg : Literal.sat v (.neg n) = false := by simp [Literal.sat, hv]
      rw [sat_filter_of_false (l := .neg n) hd hneg]
      simp
  | false =>
      have hpos : Literal.sat v (.pos n) = false := by simp [Literal.sat, hv]
      rw [sat_filter_of_false (l := .pos n) hc hpos]
      simp

theorem resolve_preserves_sat {Γ Δ : CNF} (h : Resolve Γ Δ) (v : Nat → Bool)
    (hsat : CNF.sat v Γ = true) : CNF.sat v Δ = true := by
  cases h with
  | mk n c d Γ hc hd hp hn =>
      have hΓ : ∀ e ∈ Γ, Clause.sat v e = true := List.all_eq_true.mp hsat
      simp [sat_cnf_cons, hsat, sat_resolvent v n c d (hΓ c hc) (hΓ d hd) hp hn]

/-- Complementary units resolve to the empty clause. -/
def clash : CNF := [[.pos 0], [.neg 0]]

theorem clash_resolves_empty :
    Resolve clash ([] :: clash) :=
  Resolve.mk 0 [.pos 0] [.neg 0] clash
    (by simp [clash]) (by simp [clash]) (by simp) (by simp)

theorem clash_step :
    resolutionGSLT.Step clash ([] :: clash) :=
  clash_resolves_empty

theorem clash_unsat_after (v : Nat → Bool) :
    CNF.sat v ([] :: clash) = false :=
  empty_clause_cnf_unsat (by simp) v

/-- Formula `p ∧ ¬p` translates to the unit clash. -/
theorem contradiction_cnf :
    toCNF (.and (.atom 0) (.not (.atom 0))) = clash :=
  rfl

/-! ## Unsatisfiability and clause-level derivability -/

def Unsat (Γ : CNF) : Prop := ∀ v : Nat → Bool, CNF.sat v Γ = false

def Satisfiable (Γ : CNF) : Prop := ∃ v : Nat → Bool, CNF.sat v Γ = true

theorem not_unsat_nil : ¬ Unsat [] := by
  intro h
  have := h (fun _ => false)
  simp [CNF.sat] at this

theorem unsat_iff_not_satisfiable (Γ : CNF) :
    Unsat Γ ↔ ¬ Satisfiable Γ := by
  constructor
  · intro h ⟨v, hv⟩
    have := h v
    simp [this] at hv
  · intro h v
    cases hv : CNF.sat v Γ with
    | false => rfl
    | true => exact (h ⟨v, hv⟩).elim

inductive ClauseDerives (Γ : CNF) : Clause → Prop where
  | ax {c : Clause} (h : c ∈ Γ) : ClauseDerives Γ c
  | resolve (n : Nat) {c d : Clause} :
      ClauseDerives Γ c → ClauseDerives Γ d →
      Literal.pos n ∈ c → Literal.neg n ∈ d →
      ClauseDerives Γ (resolvent n c d)

theorem derives_weak {Γ Δ : CNF} (hkeep : ∀ x ∈ Γ, x ∈ Δ) {c : Clause}
    (h : ClauseDerives Γ c) : ClauseDerives Δ c := by
  induction h with
  | ax hx => exact .ax (hkeep _ hx)
  | resolve n _ _ hp hn ihc ihd => exact .resolve n ihc ihd hp hn

theorem derives_sat {Γ : CNF} {c : Clause} (h : ClauseDerives Γ c)
    (v : Nat → Bool) (hsat : CNF.sat v Γ = true) :
    Clause.sat v c = true := by
  induction h with
  | ax hx => exact List.all_eq_true.mp hsat _ hx
  | resolve n hc hd hp hn ihc ihd =>
      exact sat_resolvent v n _ _ ihc ihd hp hn

theorem derives_empty_unsat {Γ : CNF} (h : ClauseDerives Γ []) : Unsat Γ := by
  intro v
  cases hv : CNF.sat v Γ with
  | false => rfl
  | true =>
      have := derives_sat h v hv
      simp [Clause.sat] at this

theorem resolve_keeps {n : Nat} {c d : Clause} {Γ : CNF} {x : Clause}
    (hx : x ∈ Γ) : x ∈ resolvent n c d :: Γ :=
  List.mem_cons_of_mem _ hx

theorem multiStep_trans {Γ Δ Θ : CNF} :
    resolutionGSLT.MultiStep Γ Δ →
    resolutionGSLT.MultiStep Δ Θ →
    resolutionGSLT.MultiStep Γ Θ
  | .refl _, h2 => h2
  | .step s rest, h2 =>
      GSLT.MultiStep.step (S := resolutionGSLT) s (multiStep_trans rest h2)

theorem realize_from {c : Clause} (Γ : CNF) (h : ClauseDerives Γ c)
    (Δ₀ : CNF) (hkeep : ∀ x : Clause, x ∈ Γ → x ∈ Δ₀) :
    ∃ Δ : CNF, resolutionGSLT.MultiStep Δ₀ Δ ∧ c ∈ Δ ∧
      ∀ x : Clause, x ∈ Δ₀ → x ∈ Δ := by
  induction h generalizing Δ₀ with
  | ax hx =>
      exact ⟨Δ₀, GSLT.MultiStep.refl (S := resolutionGSLT) Δ₀, hkeep _ hx,
        fun x hx => hx⟩
  | @resolve n c d hc hd hp hn ihc ihd =>
      obtain ⟨Δc, pc, mc, keepc⟩ := ihc Δ₀ hkeep
      obtain ⟨Δd, pd, md, keepd⟩ :=
        ihd Δc (fun x hx => keepc x (hkeep x hx))
      refine ⟨resolvent n c d :: Δd,
        multiStep_trans pc (multiStep_trans pd
          (GSLT.MultiStep.step (S := resolutionGSLT)
            (Resolve.mk n c d Δd (keepd c mc) md hp hn)
            (GSLT.MultiStep.refl (S := resolutionGSLT)
              (resolvent n c d :: Δd)))),
        List.mem_cons_self, ?_⟩
      intro x hx
      exact List.mem_cons_of_mem _ (keepd x (keepc x hx))

theorem derives_multistep {Γ : CNF} {c : Clause} (h : ClauseDerives Γ c) :
    ∃ Δ : CNF, resolutionGSLT.MultiStep Γ Δ ∧ c ∈ Δ := by
  obtain ⟨Δ, p, m, _⟩ := realize_from Γ h Γ (fun _ hx => hx)
  exact ⟨Δ, p, m⟩

theorem clash_derives_empty : ClauseDerives clash [] :=
  ClauseDerives.resolve 0
    (ClauseDerives.ax (List.mem_cons_self))
    (ClauseDerives.ax (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_self) (List.mem_cons_self)

#print axioms step_iff_resolve
#print axioms resolve_preserves_sat
#print axioms clash_resolves_empty
#print axioms contradiction_cnf
#print axioms derives_empty_unsat
#print axioms clash_derives_empty

end Mettapedia.GSLT.Logic.PropositionalResolution
