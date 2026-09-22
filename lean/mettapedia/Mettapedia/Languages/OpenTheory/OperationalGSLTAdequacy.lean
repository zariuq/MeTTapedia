import Mettapedia.Languages.OpenTheory.OperationalGSLT
import Mettapedia.GSLT.Core.MultiRewrite

/-!
# Adequacy of the OpenTheory theorem-list GSLT

A theorem is in the least policy-qualified closure if and only if it appears
on some `MultiStep` of `openTheoryGSLT` from the empty list.  That is the
native kernel reading: the GSLT does not invent theorems, and every derived
theorem is reachable by expanding the list.

`Expand` is persistent: every previously derived theorem remains in the
state.  As a multi-rewrite, the authored window is the whole theorem list
(`[Γ] → [out :: Γ]`).  Interior document windows of that theory are a larger
relation and are not the OpenTheory kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.OperationalGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.MultiRewrite
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.TheoryClosureCanary
open Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.Logic

section
variable (policy : AxiomPolicy)

theorem expand_persists {Γ Δ : List Theorem} (h : Expand policy Γ Δ) :
    ∀ t : Theorem, t ∈ Γ → t ∈ Δ := by
  intro t ht
  cases h with
  | cons _request _out _Γ0 _hmem _hpol _hstep =>
      exact List.mem_cons_of_mem _ ht

theorem expand_cons_eq {Γ Δ : List Theorem} (h : Expand policy Γ Δ) :
    ∃ result : Theorem, Δ = result :: Γ := by
  cases h with
  | cons _request result _Γ0 _ _ _ => exact ⟨result, rfl⟩

/-- Membership in the source list is enough to replay the same primitive
on a larger list: persistence of premises. -/
theorem expand_weaken {Γ Δ : List Theorem} {result : Theorem}
    (h : Expand policy Γ (result :: Γ))
    (hsub : ∀ t : Theorem, t ∈ Γ → t ∈ Δ) :
    Expand policy Δ (result :: Δ) := by
  obtain ⟨request, out, hEq, hmem, hrule⟩ := (expand_iff_rule policy).mp h
  injection hEq with hout _hΓ
  subst hout
  obtain ⟨request', hprem, hpol, hstep⟩ := hrule
  refine Expand.cons request' result Δ ?_ hpol hstep
  intro t ht
  exact hsub t (hmem t (hprem ▸ ht))

theorem derives_closed_under_expand {Γ Δ : List Theorem}
    (h : Expand policy Γ Δ)
    (hΓ : ∀ t : Theorem, t ∈ Γ → Derives (PolicyPrimitiveRule policy) t) :
    ∀ t : Theorem, t ∈ Δ → Derives (PolicyPrimitiveRule policy) t := by
  intro t ht
  obtain ⟨request, out, hEq, hmem, hrule⟩ := (expand_iff_rule policy).mp h
  have ht' : t ∈ out :: Γ := hEq ▸ ht
  rcases List.mem_cons.mp ht' with hto | hΓt
  · exact hto ▸ Derives.node request.premises out hrule
      (fun p hp => hΓ p (hmem p hp))
  · exact hΓ t hΓt

theorem multistep_trans {A B C : List Theorem} :
    (openTheoryGSLT policy).MultiStep A B →
      (openTheoryGSLT policy).MultiStep B C →
        (openTheoryGSLT policy).MultiStep A C
  | .refl _, hBC => hBC
  | .step hs rest, hBC =>
      GSLT.MultiStep.step (S := openTheoryGSLT policy) hs
        (multistep_trans rest hBC)

theorem derives_of_multistep {Δ Γ : List Theorem} :
    (openTheoryGSLT policy).MultiStep Δ Γ →
      (∀ t : Theorem, t ∈ Δ → Derives (PolicyPrimitiveRule policy) t) →
        ∀ t : Theorem, t ∈ Γ → Derives (PolicyPrimitiveRule policy) t
  | .refl _, hΔ => hΔ
  | .step hs rest, hΔ =>
      derives_of_multistep rest (derives_closed_under_expand policy hs hΔ)

theorem derives_of_reachable {Γ : List Theorem}
    (h : (openTheoryGSLT policy).MultiStep [] Γ)
    {t : Theorem} (ht : t ∈ Γ) :
    Derives (PolicyPrimitiveRule policy) t :=
  derives_of_multistep policy h (fun _ ht => nomatch ht) t ht

theorem mem_cons_of_subset {α : Type*} {x : α} {xs ys : List α}
    (h : ∀ t : α, t ∈ xs → t ∈ ys) :
    ∀ t : α, t ∈ x :: xs → t ∈ x :: ys := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | hxs
  · exact List.mem_cons.mpr (Or.inl rfl)
  · exact List.mem_cons_of_mem _ (h t hxs)

theorem multistep_weaken {Δ Γ Δ' : List Theorem} :
    (openTheoryGSLT policy).MultiStep Δ Γ →
      (∀ t : Theorem, t ∈ Δ → t ∈ Δ') →
        ∃ Γ' : List Theorem,
          (openTheoryGSLT policy).MultiStep Δ' Γ' ∧
            (∀ t : Theorem, t ∈ Γ → t ∈ Γ') ∧
              (∀ t : Theorem, t ∈ Δ' → t ∈ Γ')
  | .refl _, hsub =>
      ⟨Δ', GSLT.MultiStep.refl (S := openTheoryGSLT policy) Δ',
        hsub, fun t ht => ht⟩
  | .step hs rest, hsub => by
      obtain ⟨result, hEq⟩ := expand_cons_eq policy hs
      have hstep' : Expand policy Δ' (result :: Δ') :=
        expand_weaken policy (hEq ▸ hs) hsub
      obtain ⟨Γ', hpath, hΓ, hKeep⟩ :=
        multistep_weaken rest
          (fun t ht => mem_cons_of_subset hsub t (hEq ▸ ht))
      exact ⟨Γ',
        GSLT.MultiStep.step (S := openTheoryGSLT policy) hstep' hpath, hΓ,
        fun t ht => hKeep t (List.mem_cons_of_mem _ ht)⟩

theorem premises_reachable :
    ∀ (premises : List Theorem),
      (∀ p : Theorem, p ∈ premises →
        ∃ Γ : List Theorem,
          (openTheoryGSLT policy).MultiStep [] Γ ∧ p ∈ Γ) →
      ∃ Γ : List Theorem,
        (openTheoryGSLT policy).MultiStep [] Γ ∧
          ∀ p : Theorem, p ∈ premises → p ∈ Γ
  | [], _ =>
      ⟨[], GSLT.MultiStep.refl (S := openTheoryGSLT policy) [],
        fun p hp => nomatch hp⟩
  | p :: ps, ih => by
      obtain ⟨Γp, hpPath, hpMem⟩ :=
        ih p (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨Γs, hsPath, hsMem⟩ :=
        premises_reachable ps
          (fun q hq => ih q (List.mem_cons.mpr (Or.inr hq)))
      obtain ⟨Γ', hfrom, hΓs, hΓp⟩ :=
        multistep_weaken policy (Δ' := Γp) hsPath
          (fun _ ht => nomatch ht)
      refine ⟨Γ', multistep_trans policy hpPath hfrom, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hps
      · exact hΓp q hpMem
      · exact hΓs q (hsMem q hps)

theorem reachable_of_derives {t : Theorem}
    (h : Derives (PolicyPrimitiveRule policy) t) :
    ∃ Γ : List Theorem,
      (openTheoryGSLT policy).MultiStep [] Γ ∧ t ∈ Γ := by
  refine Derives.least
    (fun t => ∃ Γ : List Theorem,
      (openTheoryGSLT policy).MultiStep [] Γ ∧ t ∈ Γ) ?_ h
  intro premises conclusion rule ih
  obtain ⟨Γ, hpath, hmem⟩ := premises_reachable policy premises ih
  obtain ⟨request, hprem, hpol, hstep⟩ := rule
  have hexpand : Expand policy Γ (conclusion :: Γ) :=
    Expand.cons request conclusion Γ
      (fun p hp => hmem p (hprem ▸ hp)) hpol hstep
  exact ⟨conclusion :: Γ,
    multistep_trans policy hpath
      (GSLT.MultiStep.step (S := openTheoryGSLT policy) hexpand
        (GSLT.MultiStep.refl (S := openTheoryGSLT policy)
          (conclusion :: Γ))),
    List.mem_cons.mpr (Or.inl rfl)⟩

theorem derives_iff_reachable (t : Theorem) :
    Derives (PolicyPrimitiveRule policy) t ↔
      ∃ Γ : List Theorem,
        (openTheoryGSLT policy).MultiStep [] Γ ∧ t ∈ Γ :=
  ⟨reachable_of_derives policy, fun ⟨_, hpath, ht⟩ =>
    derives_of_reachable policy hpath ht⟩

/-- Persistent multi-rewrite whose authored window is the whole list. -/
def persistentTheory : MultiRewriteTheory where
  Term := Theorem
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Expand policy
  rewrites_resp_left := by
    intro sources sources' targets equiv step
    have hs : sources' = sources := (Pointwise.eq_of_eq equiv).symm
    subst hs
    exact ⟨targets, step, Pointwise.refl (fun _ => rfl) targets⟩
  rewrites_resp_right := by
    intro sources targets targets' step equiv
    have ht : targets' = targets := (Pointwise.eq_of_eq equiv).symm
    subst ht
    exact step

def expand_as_whole_window {Γ Δ : List Theorem}
    (h : Expand policy Γ Δ) :
    MultiRewriteTheory.WindowWitness (persistentTheory policy) Γ Δ :=
  MultiRewriteTheory.wholeWindow (persistentTheory policy) h <| by
    obtain ⟨result, hEq⟩ := expand_cons_eq policy h
    subst hEq
    exact Or.inr (List.cons_ne_nil _ _)

theorem expand_is_persistent_step {Γ : List Theorem} {result : Theorem}
    (h : Expand policy Γ (result :: Γ)) :
    GSLT.Step (MultiRewriteTheory.toGSLT (persistentTheory policy))
      Γ (result :: Γ) :=
  MultiRewriteTheory.step_of_whole (persistentTheory policy) h
    (Or.inr (List.cons_ne_nil _ _))

end

theorem onlyP_axiomP_reachable :
    ∃ Γ : List Theorem,
      (openTheoryGSLT onlyP).MultiStep [] Γ ∧ axiomP ∈ Γ :=
  reachable_of_derives onlyP onlyP_derives_axiomP

theorem onlyP_axiomQ_not_reachable :
    ¬ ∃ Γ : List Theorem,
      (openTheoryGSLT onlyP).MultiStep [] Γ ∧ axiomQ ∈ Γ := by
  intro ⟨Γ, hpath, ht⟩
  exact onlyP_does_not_derive_axiomQ
    (derives_of_reachable onlyP hpath ht)

#print axioms derives_iff_reachable
#print axioms onlyP_axiomP_reachable
#print axioms onlyP_axiomQ_not_reachable
#print axioms expand_persists
#print axioms expand_is_persistent_step

end Mettapedia.Languages.OpenTheory.OperationalGSLT
