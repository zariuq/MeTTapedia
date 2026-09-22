import Mettapedia.Logic.Derivation
import Mettapedia.GSLT.Logic.PropositionalResolution
import Mettapedia.GSLT.Logic.PropositionalResolutionComplete

/-!
# Native resolution kernel for NIK

Maximal-native for this domain: propositional resolution is a finitary
two-premise clause calculus. The kernel is least closure under those
rules, with Boolean consequence as meaning and finite derivation trees
as replay certificates. Unsatisfiability *is* derivability of the empty
clause (`empty_iff_unsat`). That is the strongest native statement; it
is not a DTT or HOTG wrapping.

No Foundation. No LanguageDef.
-/

set_option autoImplicit false

open Mettapedia.Logic

namespace Mettapedia.GSLT.Logic.PropositionalResolution

open Mettapedia.GSLT.Logic.PropositionalFormula

inductive ResRule (Γ : CNF) : List Clause → Clause → Prop where
  | hyp (c : Clause) (h : c ∈ Γ) : ResRule Γ [] c
  | resolve (n : Nat) (c d : Clause)
      (hp : Literal.pos n ∈ c) (hn : Literal.neg n ∈ d) :
      ResRule Γ [c, d] (resolvent n c d)

inductive ResWitness where
  | hyp (c : Clause)
  | resolve (n : Nat) (c d : Clause)
deriving DecidableEq

def checkRes (Γ : CNF) :
    ResWitness → List Clause → Clause → Bool
  | .hyp c, [], concl => decide (c ∈ Γ) && decide (c = concl)
  | .resolve n c d, [c', d'], concl =>
      decide (c = c') && decide (d = d') &&
        decide (Literal.pos n ∈ c) && decide (Literal.neg n ∈ d) &&
        decide (resolvent n c d = concl)
  | _, _, _ => false

theorem checkRes_sound (Γ : CNF)
    (w : ResWitness) (premises : List Clause) (conclusion : Clause)
    (accepted : checkRes Γ w premises conclusion = true) :
    ResRule Γ premises conclusion := by
  cases w with
  | hyp c =>
      cases premises with
      | nil =>
          simp [checkRes, Bool.and_eq_true, decide_eq_true_eq] at accepted
          rcases accepted with ⟨hmem, rfl⟩
          exact .hyp c hmem
      | cons _ _ => simp [checkRes] at accepted
  | resolve n c d =>
      match premises with
      | [c', d'] =>
          simp [checkRes, Bool.and_eq_true, decide_eq_true_eq] at accepted
          rcases accepted with ⟨⟨⟨⟨rfl, rfl⟩, hp⟩, hn⟩, rfl⟩
          exact .resolve n c d hp hn
      | [] => simp [checkRes] at accepted
      | [_] => simp [checkRes] at accepted
      | _ :: _ :: _ :: _ => simp [checkRes] at accepted

theorem checkRes_complete (Γ : CNF)
    (premises : List Clause) (conclusion : Clause)
    (rule : ResRule Γ premises conclusion) :
    ∃ w, checkRes Γ w premises conclusion = true := by
  cases rule with
  | hyp =>
      exact ⟨.hyp conclusion, by simp [checkRes]; assumption⟩
  | resolve n c d hp hn =>
      exact ⟨.resolve n c d, by simp [checkRes, hp, hn]⟩

def resWitness (Γ : CNF) : RuleWitness (ResRule Γ) where
  W := ResWitness
  isInstance := checkRes Γ
  sound := checkRes_sound Γ
  complete := checkRes_complete Γ

theorem derives_of_clauseDerives {Γ : CNF} {c : Clause} :
    ClauseDerives Γ c → Derives (ResRule Γ) c := by
  intro h
  induction h with
  | ax hx =>
      exact Derives.node [] _ (.hyp _ hx) (fun _ hp => nomatch hp)
  | @resolve n c d hc hd hp hn ihc ihd =>
      refine Derives.node [c, d] _ (.resolve n c d hp hn) ?_
      intro premise hmem
      have : premise = c ∨ premise = d := by
        simpa [List.mem_cons] using hmem
      cases this with
      | inl h => exact h ▸ ihc
      | inr h => exact h ▸ ihd

theorem clauseDerives_of_derives {Γ : CNF} {c : Clause} :
    Derives (ResRule Γ) c → ClauseDerives Γ c := by
  intro h
  refine Derives.least (ClauseDerives Γ) ?_ h
  intro premises conclusion rule sub
  cases rule with
  | hyp => exact .ax (by assumption)
  | resolve n c d hp hn =>
      have hc : ClauseDerives Γ c := sub c (by simp)
      have hd : ClauseDerives Γ d := sub d (by simp)
      exact .resolve n hc hd hp hn

theorem clauseDerives_iff_derives {Γ : CNF} {c : Clause} :
    ClauseDerives Γ c ↔ Derives (ResRule Γ) c :=
  ⟨derives_of_clauseDerives, clauseDerives_of_derives⟩

def Consequence (Γ : CNF) (c : Clause) : Prop :=
  ∀ v : Nat → Bool, CNF.sat v Γ = true → Clause.sat v c = true

theorem resRule_sound {Γ : CNF} {premises : List Clause} {conclusion : Clause}
    (rule : ResRule Γ premises conclusion)
    (premisesOk : ∀ p ∈ premises, Consequence Γ p) :
    Consequence Γ conclusion := by
  cases rule with
  | hyp =>
      intro v hv
      exact List.all_eq_true.mp hv conclusion (by assumption)
  | resolve n c d hp hn =>
      intro v hv
      exact sat_resolvent v n c d
        (premisesOk c (by simp) v hv)
        (premisesOk d (by simp) v hv) hp hn

/-- Native completeness: NIK scope of the empty clause is unsatisfiability. -/
theorem empty_iff_unsat (Γ : CNF) :
    Derives (ResRule Γ) [] ↔ Unsat Γ := by
  constructor
  · intro h
    exact derives_empty_unsat (clauseDerives_of_derives h)
  · intro h
    exact derives_of_clauseDerives (complete Γ h)

theorem replay_empty_of_unsat (Γ : CNF) (h : Unsat Γ) :
    ∃ certificate : Derivation Clause (resWitness Γ).W,
      certificate.valid (resWitness Γ) = true ∧ certificate.concl = [] :=
  Derives.exists_derivation (resWitness Γ) ((empty_iff_unsat Γ).mpr h)

theorem accepted_empty_unsat (Γ : CNF)
    (certificate : Derivation Clause (resWitness Γ).W)
    (accepted : certificate.valid (resWitness Γ) = true)
    (concludes : certificate.concl = []) :
    Unsat Γ := by
  have : Derives (ResRule Γ) [] :=
    concludes ▸ Derivation.valid_sound (resWitness Γ) certificate accepted
  exact (empty_iff_unsat Γ).mp this

#print axioms empty_iff_unsat
#print axioms resWitness
#print axioms replay_empty_of_unsat
#print axioms accepted_empty_unsat

end Mettapedia.GSLT.Logic.PropositionalResolution
