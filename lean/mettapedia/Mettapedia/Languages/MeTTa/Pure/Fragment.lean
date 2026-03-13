import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.Languages.MeTTa.Pure.BinderOps
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# MeTTa-Pure: Explicit Pure Fragment

Shared definition of the pure term fragment embedded in ambient `Pattern`,
plus the basic closure and inversion lemmas needed by typing, confluence,
and subject reduction.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Fragment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps

/-- Pure MeTTa-Pure term fragment embedded in ambient `Pattern`.
    This excludes ambient host constructors and non-kernel `.apply` heads. -/
inductive PureTmPattern : Pattern → Prop where
  | bvar (n : Nat) : PureTmPattern (.bvar n)
  | fvar (x : String) : PureTmPattern (.fvar x)
  | u0 : PureTmPattern u0
  | u1 : PureTmPattern u1
  | pi {A B : Pattern} : PureTmPattern A → PureTmPattern B → PureTmPattern (mkPi A B)
  | sigma {A B : Pattern} : PureTmPattern A → PureTmPattern B → PureTmPattern (mkSigma A B)
  | id {A a b : Pattern} : PureTmPattern A → PureTmPattern a → PureTmPattern b → PureTmPattern (mkId A a b)
  | lam {body : Pattern} : PureTmPattern body → PureTmPattern (mkLam body)
  | app {f a : Pattern} : PureTmPattern f → PureTmPattern a → PureTmPattern (mkApp f a)
  | pair {a b : Pattern} : PureTmPattern a → PureTmPattern b → PureTmPattern (mkPair a b)
  | fst {p : Pattern} : PureTmPattern p → PureTmPattern (mkFst p)
  | snd {p : Pattern} : PureTmPattern p → PureTmPattern (mkSnd p)
  | refl {a : Pattern} : PureTmPattern a → PureTmPattern (mkRefl a)

/-- Opening a pure term with an fvar remains in the pure fragment. -/
theorem pureTm_openBVar_fvar (x : String) {k : Nat} {p : Pattern}
    (hp : PureTmPattern p) : PureTmPattern (openBVar k (.fvar x) p) := by
  induction hp generalizing k with
  | bvar n =>
    simp [openBVar]
    split
    · exact .fvar x
    · exact .bvar n
  | fvar y =>
    simpa [openBVar] using (PureTmPattern.fvar y)
  | u0 =>
    simpa [u0, openBVar] using PureTmPattern.u0
  | u1 =>
    simpa [u1, openBVar] using PureTmPattern.u1
  | pi hA hB ihA ihB =>
    simpa [openBVar_mkPi] using PureTmPattern.pi (ihA (k := k)) (ihB (k := k + 1))
  | sigma hA hB ihA ihB =>
    simpa [openBVar_mkSigma] using PureTmPattern.sigma (ihA (k := k)) (ihB (k := k + 1))
  | id hA ha hb ihA iha ihb =>
    simpa [openBVar_mkId] using PureTmPattern.id (ihA (k := k)) (iha (k := k)) (ihb (k := k))
  | lam hBody ihBody =>
    simpa [openBVar_mkLam] using PureTmPattern.lam (ihBody (k := k + 1))
  | app hf ha ihf iha =>
    simpa [openBVar_mkApp] using PureTmPattern.app (ihf (k := k)) (iha (k := k))
  | pair ha hb iha ihb =>
    simpa [openBVar_mkPair] using PureTmPattern.pair (iha (k := k)) (ihb (k := k))
  | fst hp ihp =>
    simpa [openBVar_mkFst] using PureTmPattern.fst (ihp (k := k))
  | snd hp ihp =>
    simpa [openBVar_mkSnd] using PureTmPattern.snd (ihp (k := k))
  | refl ha iha =>
    simpa [openBVar_mkRefl] using PureTmPattern.refl (iha (k := k))

/-- Opening a pure term with a pure substituent stays in the pure fragment. -/
theorem pureTm_openBVar {u : Pattern} (hu : PureTmPattern u) {k : Nat} {p : Pattern}
    (hp : PureTmPattern p) : PureTmPattern (openBVar k u p) := by
  induction hp generalizing k with
  | bvar n =>
    simp [openBVar]
    split
    · exact hu
    · exact .bvar n
  | fvar y =>
    simpa [openBVar] using (PureTmPattern.fvar y)
  | u0 =>
    simpa [u0, openBVar] using PureTmPattern.u0
  | u1 =>
    simpa [u1, openBVar] using PureTmPattern.u1
  | pi hA hB ihA ihB =>
    simpa [openBVar_mkPi] using PureTmPattern.pi (ihA (k := k)) (ihB (k := k + 1))
  | sigma hA hB ihA ihB =>
    simpa [openBVar_mkSigma] using PureTmPattern.sigma (ihA (k := k)) (ihB (k := k + 1))
  | id hA ha hb ihA iha ihb =>
    simpa [openBVar_mkId] using PureTmPattern.id (ihA (k := k)) (iha (k := k)) (ihb (k := k))
  | lam hBody ihBody =>
    simpa [openBVar_mkLam] using PureTmPattern.lam (ihBody (k := k + 1))
  | app hf ha ihf iha =>
    simpa [openBVar_mkApp] using PureTmPattern.app (ihf (k := k)) (iha (k := k))
  | pair ha hb iha ihb =>
    simpa [openBVar_mkPair] using PureTmPattern.pair (iha (k := k)) (ihb (k := k))
  | fst hp ihp =>
    simpa [openBVar_mkFst] using PureTmPattern.fst (ihp (k := k))
  | snd hp ihp =>
    simpa [openBVar_mkSnd] using PureTmPattern.snd (ihp (k := k))
  | refl ha iha =>
    simpa [openBVar_mkRefl] using PureTmPattern.refl (iha (k := k))

/-- Closing a pure term by abstracting an fvar stays in the pure fragment. -/
theorem pureTm_closeBVar (x : String) {k : Nat} {p : Pattern}
    (hp : PureTmPattern p) : PureTmPattern (closeBVar k x p) := by
  induction hp generalizing k with
  | bvar n =>
    simpa [closeBVar, closeFVar] using (PureTmPattern.bvar n)
  | fvar y =>
    by_cases h : y = x
    · subst h
      simpa [closeBVar, closeFVar] using (PureTmPattern.bvar k)
    · simp [closeBVar, closeFVar, h]
      exact PureTmPattern.fvar y
  | u0 =>
    simpa [u0, closeBVar, closeFVar] using PureTmPattern.u0
  | u1 =>
    simpa [u1, closeBVar, closeFVar] using PureTmPattern.u1
  | pi hA hB ihA ihB =>
    simpa [mkPi, closeBVar, closeFVar] using PureTmPattern.pi (ihA (k := k)) (ihB (k := k + 1))
  | sigma hA hB ihA ihB =>
    simpa [mkSigma, closeBVar, closeFVar] using PureTmPattern.sigma (ihA (k := k)) (ihB (k := k + 1))
  | id hA ha hb ihA iha ihb =>
    simpa [mkId, closeBVar, closeFVar] using PureTmPattern.id (ihA (k := k)) (iha (k := k)) (ihb (k := k))
  | lam hBody ihBody =>
    simpa [mkLam, closeBVar, closeFVar] using PureTmPattern.lam (ihBody (k := k + 1))
  | app hf ha ihf iha =>
    simpa [mkApp, closeBVar, closeFVar] using PureTmPattern.app (ihf (k := k)) (iha (k := k))
  | pair ha hb iha ihb =>
    simpa [mkPair, closeBVar, closeFVar] using PureTmPattern.pair (iha (k := k)) (ihb (k := k))
  | fst hp ihp =>
    simpa [mkFst, closeBVar, closeFVar] using PureTmPattern.fst (ihp (k := k))
  | snd hp ihp =>
    simpa [mkSnd, closeBVar, closeFVar] using PureTmPattern.snd (ihp (k := k))
  | refl ha iha =>
    simpa [mkRefl, closeBVar, closeFVar] using PureTmPattern.refl (iha (k := k))

/-- Recover purity of `p` from purity of an opened form, when the opening var is fresh. -/
theorem pureTm_of_openBVar_fresh (x : String) {p : Pattern}
    (hopen : PureTmPattern (openBVar 0 (.fvar x) p))
    (hfresh : isFresh x p = true) : PureTmPattern p := by
  have hclose : PureTmPattern (closeBVar 0 x (openBVar 0 (.fvar x) p)) :=
    pureTm_closeBVar x (k := 0) hopen
  simpa [closeBVar_openBVar_cancel hfresh] using hclose

theorem pure_pi_inv {A B : Pattern}
    (h : PureTmPattern (mkPi A B)) : PureTmPattern A ∧ PureTmPattern B := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkPi A B → PureTmPattern A ∧ PureTmPattern B := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case pi hA hB =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨hA, hB⟩
  exact h' _ h rfl

theorem pure_sigma_inv {A B : Pattern}
    (h : PureTmPattern (mkSigma A B)) : PureTmPattern A ∧ PureTmPattern B := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkSigma A B → PureTmPattern A ∧ PureTmPattern B := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case sigma hA hB =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨hA, hB⟩
  exact h' _ h rfl

theorem pure_lam_inv {body : Pattern}
    (h : PureTmPattern (mkLam body)) : PureTmPattern body := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkLam body → PureTmPattern body := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case lam hBody =>
      subst hEq
      exact hBody
  exact h' _ h rfl

theorem pure_app_inv {f a : Pattern}
    (h : PureTmPattern (mkApp f a)) : PureTmPattern f ∧ PureTmPattern a := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkApp f a → PureTmPattern f ∧ PureTmPattern a := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case app hf ha =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨hf, ha⟩
  exact h' _ h rfl

theorem pure_pair_inv {a b : Pattern}
    (h : PureTmPattern (mkPair a b)) : PureTmPattern a ∧ PureTmPattern b := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkPair a b → PureTmPattern a ∧ PureTmPattern b := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case pair ha hb =>
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨ha, hb⟩
  exact h' _ h rfl

theorem pure_fst_inv {p : Pattern}
    (h : PureTmPattern (mkFst p)) : PureTmPattern p := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkFst p → PureTmPattern p := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case fst hp =>
      subst hEq
      exact hp
  exact h' _ h rfl

theorem pure_snd_inv {p : Pattern}
    (h : PureTmPattern (mkSnd p)) : PureTmPattern p := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkSnd p → PureTmPattern p := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case snd hp =>
      subst hEq
      exact hp
  exact h' _ h rfl

theorem pure_id_inv {A a b : Pattern}
    (h : PureTmPattern (mkId A a b)) : PureTmPattern A ∧ PureTmPattern a ∧ PureTmPattern b := by
  have h' :
      ∀ t : Pattern, PureTmPattern t → t = mkId A a b → PureTmPattern A ∧ PureTmPattern a ∧ PureTmPattern b := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case id hA ha hb =>
      rcases hEq with ⟨rfl, rfl, rfl⟩
      exact ⟨hA, ha, hb⟩
  exact h' _ h rfl

theorem pure_refl_inv {a : Pattern}
    (h : PureTmPattern (mkRefl a)) : PureTmPattern a := by
  have h' : ∀ t : Pattern, PureTmPattern t → t = mkRefl a → PureTmPattern a := by
    intro t ht
    cases ht <;> intro hEq <;>
      simp [u0, u1, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at hEq
    case refl ha =>
      subst hEq
      exact ha
  exact h' _ h rfl

end Mettapedia.Languages.MeTTa.Pure.Fragment
