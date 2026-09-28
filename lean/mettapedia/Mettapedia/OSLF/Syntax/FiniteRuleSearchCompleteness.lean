import Mettapedia.OSLF.Syntax.FiniteRuleSearch

/-! Bounded completeness relative to the actual selected rule instances and
the recursive depth of a derivation. This is not a syntax-height bound and
does not assert that candidate generation covers every derivation. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleSearch

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

universe u v

theorem premises_established {J : Type u} {D : J → Type v}
    (solve : (j : J) → Verdict (D j)) (js : List J)
    (positive : ∀ j ∈ js, (solve j).isEstablished = true) :
    (premises solve js).isEstablished = true := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      have first := positive j (List.mem_cons_self ..)
      have rest := ih (fun k member => positive k (List.mem_cons_of_mem j member))
      cases a : solve j <;> cases b : premises solve js <;>
        simp_all [premises, Verdict.isEstablished]

theorem alternatives_established {A : Type u} {E : A → Type v}
    (solve : (a : A) → Verdict (E a)) (choices : List A)
    (a : A) (member : a ∈ choices) (positive : (solve a).isEstablished = true) :
    (alternatives solve choices).isEstablished = true := by
  induction choices with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst a
        cases firstResult : solve first <;>
          simp_all [alternatives, Verdict.isEstablished]
      · have success := ih member
        cases firstResult : solve first <;> cases restResult : alternatives solve rest <;>
          simp_all [alternatives, Verdict.isEstablished]

variable {J : Type u} (F : FinitePresentation.{0,u,v} Unit (fun _ => J))
  (candidates : (j : J) → Candidates F j)

/-- Every rule node is selected at its own goal, and the fuel covers every
recursive branch. Different derivations of one judgment can satisfy this at
different depths and with different selections. -/
def Covered : Nat → {j : J} → F.Derivation () j → Prop
  | 0, _, _ => False
  | fuel + 1, _, .roll shape children =>
      shape ∈ (candidates _).rules ∧ ∀ p, Covered fuel (children p)

/-- A covered derivation guarantees that the deterministic producer succeeds.
The chosen proof need not be the supplied proof: the earlier successful rule
may have a different legitimate history. -/
theorem search_complete_for_covered (fuel : Nat) {j : J} (tree : F.Derivation () j)
    (covered : Covered F candidates fuel tree) :
    (search F candidates fuel j).isEstablished = true := by
  induction fuel generalizing j with
  | zero => exact False.elim covered
  | succ fuel ih =>
      match tree with
      | .roll shape children =>
          have branchSuccess : (premises (search F candidates fuel)
              (F.premises () j shape)).isEstablished = true := by
            apply premises_established
            intro premise member
            rcases List.mem_iff_get.mp member with ⟨position, equal⟩
            subst premise
            exact ih (children position) (covered.2 position)
          have succeeds := alternatives_established
            (fun rule : F.Shape () j =>
              premises (search F candidates fuel) (F.premises () j rule))
            (candidates j).rules shape covered.1 branchSuccess
          cases result : alternatives (fun rule : F.Shape () j =>
              premises (search F candidates fuel) (F.premises () j rule))
              (candidates j).rules with
          | established selected => simp only [search, result, Verdict.isEstablished]
          | refuted impossible => simp only [result, Verdict.isEstablished] at succeeds; cases succeeds
          | incomplete => simp only [result, Verdict.isEstablished] at succeeds; cases succeeds

end Mettapedia.OSLF.Binding.FiniteRuleSearch
