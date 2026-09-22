import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.BinderOps
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# the two-sort experiment: Explicit two-sort Fragment

Shared definition of the two-sort term fragment embedded in ambient `Pattern`,
plus the basic closure and inversion lemmas needed by typing, confluence,
and subject reduction.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.BinderOps

/-- two-sort the two-sort experiment term fragment embedded in ambient `Pattern`.
    This excludes ambient host constructors and non-kernel `.apply` heads. -/
inductive TwoSortTermPattern : Pattern → Prop where
  | bvar (n : Nat) : TwoSortTermPattern (.bvar n)
  | fvar (x : String) : TwoSortTermPattern (.fvar x)
  | u0 : TwoSortTermPattern u0
  | u1 : TwoSortTermPattern u1
  | pi {A B : Pattern} : TwoSortTermPattern A → TwoSortTermPattern B → TwoSortTermPattern (mkPi A B)
  | sigma {A B : Pattern} : TwoSortTermPattern A → TwoSortTermPattern B → TwoSortTermPattern (mkSigma A B)
  | id {A a b : Pattern} : TwoSortTermPattern A → TwoSortTermPattern a → TwoSortTermPattern b → TwoSortTermPattern (mkId A a b)
  | lam {body : Pattern} : TwoSortTermPattern body → TwoSortTermPattern (mkLam body)
  | app {f a : Pattern} : TwoSortTermPattern f → TwoSortTermPattern a → TwoSortTermPattern (mkApp f a)
  | pair {a b : Pattern} : TwoSortTermPattern a → TwoSortTermPattern b → TwoSortTermPattern (mkPair a b)
  | fst {p : Pattern} : TwoSortTermPattern p → TwoSortTermPattern (mkFst p)
  | snd {p : Pattern} : TwoSortTermPattern p → TwoSortTermPattern (mkSnd p)
  | refl {a : Pattern} : TwoSortTermPattern a → TwoSortTermPattern (mkRefl a)

/-- Opening a two-sort term with an fvar remains in the two-sort fragment. -/
theorem twoSortTm_openBVar_fvar (x : String) {k : Nat} {p : Pattern}
    (hp : TwoSortTermPattern p) : TwoSortTermPattern (openBVar k (.fvar x) p) := by
  induction hp generalizing k with
  | bvar n =>
    simp [openBVar]
    split
    · exact .fvar x
    · exact .bvar n
  | fvar y =>
    simpa [openBVar] using (TwoSortTermPattern.fvar y)
  | u0 =>
    simpa [u0, openBVar] using TwoSortTermPattern.u0
  | u1 =>
    simpa [u1, openBVar] using TwoSortTermPattern.u1
  | pi hA hB ihA ihB =>
    simpa [openBVar_mkPi] using TwoSortTermPattern.pi (ihA (k := k)) (ihB (k := k + 1))
  | sigma hA hB ihA ihB =>
    simpa [openBVar_mkSigma] using TwoSortTermPattern.sigma (ihA (k := k)) (ihB (k := k + 1))
  | id hA ha hb ihA iha ihb =>
    simpa [openBVar_mkId] using TwoSortTermPattern.id (ihA (k := k)) (iha (k := k)) (ihb (k := k))
  | lam hBody ihBody =>
    simpa [openBVar_mkLam] using TwoSortTermPattern.lam (ihBody (k := k + 1))
  | app hf ha ihf iha =>
    simpa [openBVar_mkApp] using TwoSortTermPattern.app (ihf (k := k)) (iha (k := k))
  | pair ha hb iha ihb =>
    simpa [openBVar_mkPair] using TwoSortTermPattern.pair (iha (k := k)) (ihb (k := k))
  | fst hp ihp =>
    simpa [openBVar_mkFst] using TwoSortTermPattern.fst (ihp (k := k))
  | snd hp ihp =>
    simpa [openBVar_mkSnd] using TwoSortTermPattern.snd (ihp (k := k))
  | refl ha iha =>
    simpa [openBVar_mkRefl] using TwoSortTermPattern.refl (iha (k := k))

/-- Opening a two-sort term with a two-sort substituent stays in the two-sort fragment. -/
theorem twoSortTm_openBVar {u : Pattern} (hu : TwoSortTermPattern u) {k : Nat} {p : Pattern}
    (hp : TwoSortTermPattern p) : TwoSortTermPattern (openBVar k u p) := by
  induction hp generalizing k with
  | bvar n =>
    simp [openBVar]
    split
    · exact hu
    · exact .bvar n
  | fvar y =>
    simpa [openBVar] using (TwoSortTermPattern.fvar y)
  | u0 =>
    simpa [u0, openBVar] using TwoSortTermPattern.u0
  | u1 =>
    simpa [u1, openBVar] using TwoSortTermPattern.u1
  | pi hA hB ihA ihB =>
    simpa [openBVar_mkPi] using TwoSortTermPattern.pi (ihA (k := k)) (ihB (k := k + 1))
  | sigma hA hB ihA ihB =>
    simpa [openBVar_mkSigma] using TwoSortTermPattern.sigma (ihA (k := k)) (ihB (k := k + 1))
  | id hA ha hb ihA iha ihb =>
    simpa [openBVar_mkId] using TwoSortTermPattern.id (ihA (k := k)) (iha (k := k)) (ihb (k := k))
  | lam hBody ihBody =>
    simpa [openBVar_mkLam] using TwoSortTermPattern.lam (ihBody (k := k + 1))
  | app hf ha ihf iha =>
    simpa [openBVar_mkApp] using TwoSortTermPattern.app (ihf (k := k)) (iha (k := k))
  | pair ha hb iha ihb =>
    simpa [openBVar_mkPair] using TwoSortTermPattern.pair (iha (k := k)) (ihb (k := k))
  | fst hp ihp =>
    simpa [openBVar_mkFst] using TwoSortTermPattern.fst (ihp (k := k))
  | snd hp ihp =>
    simpa [openBVar_mkSnd] using TwoSortTermPattern.snd (ihp (k := k))
  | refl ha iha =>
    simpa [openBVar_mkRefl] using TwoSortTermPattern.refl (iha (k := k))

/-- Closing a two-sort term by abstracting an fvar stays in the two-sort fragment. -/
theorem twoSortTm_closeBVar (x : String) {k : Nat} {p : Pattern}
    (hp : TwoSortTermPattern p) : TwoSortTermPattern (closeBVar k x p) := by
  induction hp generalizing k with
  | bvar n =>
    simpa [closeBVar, closeFVar] using (TwoSortTermPattern.bvar n)
  | fvar y =>
    by_cases h : y = x
    · subst h
      simpa [closeBVar, closeFVar] using (TwoSortTermPattern.bvar k)
    · simp [closeBVar, closeFVar, h]
      exact TwoSortTermPattern.fvar y
  | u0 =>
    simpa [u0, closeBVar, closeFVar] using TwoSortTermPattern.u0
  | u1 =>
    simpa [u1, closeBVar, closeFVar] using TwoSortTermPattern.u1
  | pi hA hB ihA ihB =>
    simpa [mkPi, closeBVar, closeFVar] using TwoSortTermPattern.pi (ihA (k := k)) (ihB (k := k + 1))
  | sigma hA hB ihA ihB =>
    simpa [mkSigma, closeBVar, closeFVar] using TwoSortTermPattern.sigma (ihA (k := k)) (ihB (k := k + 1))
  | id hA ha hb ihA iha ihb =>
    simpa [mkId, closeBVar, closeFVar] using TwoSortTermPattern.id (ihA (k := k)) (iha (k := k)) (ihb (k := k))
  | lam hBody ihBody =>
    simpa [mkLam, closeBVar, closeFVar] using TwoSortTermPattern.lam (ihBody (k := k + 1))
  | app hf ha ihf iha =>
    simpa [mkApp, closeBVar, closeFVar] using TwoSortTermPattern.app (ihf (k := k)) (iha (k := k))
  | pair ha hb iha ihb =>
    simpa [mkPair, closeBVar, closeFVar] using TwoSortTermPattern.pair (iha (k := k)) (ihb (k := k))
  | fst hp ihp =>
    simpa [mkFst, closeBVar, closeFVar] using TwoSortTermPattern.fst (ihp (k := k))
  | snd hp ihp =>
    simpa [mkSnd, closeBVar, closeFVar] using TwoSortTermPattern.snd (ihp (k := k))
  | refl ha iha =>
    simpa [mkRefl, closeBVar, closeFVar] using TwoSortTermPattern.refl (iha (k := k))

/-- Recover purity of `p` from purity of an opened form, when the opening var is fresh. -/
theorem twoSortTm_of_openBVar_fresh (x : String) {p : Pattern}
    (hopen : TwoSortTermPattern (openBVar 0 (.fvar x) p))
    (hfresh : isFresh x p = true) : TwoSortTermPattern p := by
  have hclose : TwoSortTermPattern (closeBVar 0 x (openBVar 0 (.fvar x) p)) :=
    twoSortTm_closeBVar x (k := 0) hopen
  simpa [closeBVar_openBVar_cancel hfresh] using hclose

theorem twoSort_pi_inv {A B : Pattern}
    (h : TwoSortTermPattern (mkPi A B)) : TwoSortTermPattern A ∧ TwoSortTermPattern B := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkPi A B → TwoSortTermPattern A ∧ TwoSortTermPattern B := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case pi hA hB =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨hA, hB⟩
  exact h' _ h rfl

theorem twoSort_sigma_inv {A B : Pattern}
    (h : TwoSortTermPattern (mkSigma A B)) : TwoSortTermPattern A ∧ TwoSortTermPattern B := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkSigma A B → TwoSortTermPattern A ∧ TwoSortTermPattern B := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case sigma hA hB =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨hA, hB⟩
  exact h' _ h rfl

theorem twoSort_lam_inv {body : Pattern}
    (h : TwoSortTermPattern (mkLam body)) : TwoSortTermPattern body := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkLam body → TwoSortTermPattern body := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case lam hBody =>
      subst hEq
      exact hBody
  exact h' _ h rfl

theorem twoSort_app_inv {f a : Pattern}
    (h : TwoSortTermPattern (mkApp f a)) : TwoSortTermPattern f ∧ TwoSortTermPattern a := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkApp f a → TwoSortTermPattern f ∧ TwoSortTermPattern a := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case app hf ha =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨hf, ha⟩
  exact h' _ h rfl

theorem twoSort_pair_inv {a b : Pattern}
    (h : TwoSortTermPattern (mkPair a b)) : TwoSortTermPattern a ∧ TwoSortTermPattern b := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkPair a b → TwoSortTermPattern a ∧ TwoSortTermPattern b := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case pair ha hb =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨ha, hb⟩
  exact h' _ h rfl

theorem twoSort_fst_inv {p : Pattern}
    (h : TwoSortTermPattern (mkFst p)) : TwoSortTermPattern p := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkFst p → TwoSortTermPattern p := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case fst hp =>
      subst hEq
      exact hp
  exact h' _ h rfl

theorem twoSort_snd_inv {p : Pattern}
    (h : TwoSortTermPattern (mkSnd p)) : TwoSortTermPattern p := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkSnd p → TwoSortTermPattern p := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case snd hp =>
      subst hEq
      exact hp
  exact h' _ h rfl

theorem twoSort_id_inv {A a b : Pattern}
    (h : TwoSortTermPattern (mkId A a b)) : TwoSortTermPattern A ∧ TwoSortTermPattern a ∧ TwoSortTermPattern b := by
  have h' :
      ∀ t : Pattern, TwoSortTermPattern t → t = mkId A a b → TwoSortTermPattern A ∧ TwoSortTermPattern a ∧ TwoSortTermPattern b := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case id hA ha hb =>
      rcases hEq with ⟨rfl, rfl, rfl⟩
      exact ⟨hA, ha, hb⟩
  exact h' _ h rfl

theorem twoSort_refl_inv {a : Pattern}
    (h : TwoSortTermPattern (mkRefl a)) : TwoSortTermPattern a := by
  have h' : ∀ t : Pattern, TwoSortTermPattern t → t = mkRefl a → TwoSortTermPattern a := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case refl ha =>
      subst hEq
      exact ha
  exact h' _ h rfl

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment
