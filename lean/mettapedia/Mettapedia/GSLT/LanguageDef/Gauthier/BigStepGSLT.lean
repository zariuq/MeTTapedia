/-
# Gauthier programs as a coarse big-step GSLT

This file earns the coarse-grained Meredith/GSLT layer for the E1 Gauthier tables.
The rewrite relation is intentionally flat: at a fixed fuel, register configuration, and
store, a program rewrites in one big step to the integer value returned by the evaluator.
Operational cache choices are below this abstraction layer; the denotation is the evaluator
result itself.
-/

import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.LanguageDef.Gauthier.E1

namespace Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT

open Mettapedia.GSLT.LanguageDef.GauthierE1

/-- Coarse result terms: either a table-indexed program or a completed integer result. -/
inductive BigStepTerm where
  | prog : Prog -> BigStepTerm
  | done : Int -> BigStepTerm
  deriving Repr

/-- Equations for the big-step presentation: extensional equality on programs, equality on results. -/
def BigStepEquiv (sig : Signature Prim) : BigStepTerm -> BigStepTerm -> Prop
  | .prog p, .prog q => Extensional sig p q
  | .done v, .done w => v = w
  | _, _ => False

/-- The equation component `E` for the coarse Gauthier GSLT. -/
def bigStepSetoid (sig : Signature Prim) : Setoid BigStepTerm where
  r := BigStepEquiv sig
  iseqv :=
    ⟨ by
        intro t
        cases t with
        | prog p => exact Extensional.refl sig p
        | done _ => rfl
    , by
        intro t u h
        cases t <;> cases u <;> simp [BigStepEquiv] at h ⊢
        · exact Extensional.symm h
        · exact h.symm
    , by
        intro t u v htu huv
        cases t <;> cases u <;> cases v <;> simp [BigStepEquiv] at htu huv ⊢
        · exact Extensional.trans htu huv
        · exact htu.trans huv
    ⟩

/--
The flat one-step relation `R`: running a program under fixed resources emits a completed value.
The final store is existential because this coarse layer observes the emitted integer.
-/
def BigStepRewrite (sig : Signature Prim) (fuel : Nat) (cfg : Config) (st : Store) :
    BigStepTerm -> BigStepTerm -> Prop
  | .prog p, .done v => ∃ st', eval fuel sig p cfg st = some (v, st')
  | _, _ => False

/-- The big-step relation respects the Gauthier equations on the source side. -/
theorem bigStepRewrite_resp_left (sig : Signature Prim) (fuel : Nat) (cfg : Config) (st : Store) :
    ∀ {t t' u}, (bigStepSetoid sig).r t t' ->
      BigStepRewrite sig fuel cfg st t u ->
      ∃ u', BigStepRewrite sig fuel cfg st t' u' ∧ (bigStepSetoid sig).r u u' := by
  intro t t' u heq hstep
  cases t with
  | done _ =>
      cases u <;> simp [BigStepRewrite] at hstep
  | prog p =>
      cases u with
      | prog _ =>
          simp [BigStepRewrite] at hstep
      | done v =>
          cases t' with
          | done w =>
              change BigStepEquiv sig (.prog p) (.done w) at heq
              exact False.elim heq
          | prog q =>
              change Extensional sig p q at heq
              rcases hstep with ⟨st', hp⟩
              refine ⟨.done v, ⟨?_, rfl⟩⟩
              exact ⟨st', by rwa [← heq fuel cfg st]⟩

/-- The big-step relation respects the Gauthier equations on the target side. -/
theorem bigStepRewrite_resp_right (sig : Signature Prim) (fuel : Nat) (cfg : Config) (st : Store) :
    ∀ {t u u'}, BigStepRewrite sig fuel cfg st t u ->
      (bigStepSetoid sig).r u u' ->
      BigStepRewrite sig fuel cfg st t u' := by
  intro t u u' hstep heq
  cases t with
  | done _ =>
      cases u <;> simp [BigStepRewrite] at hstep
  | prog p =>
      cases u with
      | prog _ =>
          simp [BigStepRewrite] at hstep
      | done v =>
          cases u' with
          | prog q =>
              change BigStepEquiv sig (.done v) (.prog q) at heq
              exact False.elim heq
          | done w =>
              change v = w at heq
              cases heq
              exact hstep

/--
The Gauthier E1 table as a Meredith `GSLT`.

This is flat by design: the one-step rewrite is the fuel-bounded big-step evaluator relation.
-/
def bigStepGSLT (sig : Signature Prim) (fuel : Nat) (cfg : Config) (st : Store) :
    Mettapedia.GSLT.GSLT where
  Term := BigStepTerm
  equations := bigStepSetoid sig
  rewrites := BigStepRewrite sig fuel cfg st
  rewrites_resp_left := bigStepRewrite_resp_left sig fuel cfg st
  rewrites_resp_right := bigStepRewrite_resp_right sig fuel cfg st

/-- One-step may satisfy a postcondition after a rewrite. -/
def Diamond (S : Mettapedia.GSLT.GSLT) (post : S.Term -> Prop) (t : S.Term) : Prop :=
  ∃ u, S.rewrites t u ∧ post u

/-- Every one-step successor satisfies a postcondition. -/
def Box (S : Mettapedia.GSLT.GSLT) (post : S.Term -> Prop) (t : S.Term) : Prop :=
  ∀ u, S.rewrites t u -> post u

/-- A completed-result predicate for the result modality. -/
def DoneValue (v : Int) : BigStepTerm -> Prop
  | .done w => w = v
  | _ => False

/-- The coarse fuel-bounded layer only rewrites to completed-result terms. -/
def DoneTerm : BigStepTerm -> Prop
  | .done _ => True
  | _ => False

/-- Diamond over the flat big-step GSLT is exactly successful evaluator emission. -/
theorem diamond_done_iff (sig : Signature Prim) (fuel : Nat) (cfg : Config) (st : Store)
    (p : Prog) (v : Int) :
    Diamond (bigStepGSLT sig fuel cfg st) (DoneValue v) (.prog p) ↔
      ∃ st', eval fuel sig p cfg st = some (v, st') := by
  constructor
  · intro h
    rcases h with ⟨u, hrew, hdone⟩
    cases u with
    | prog _ =>
        simp [bigStepGSLT, BigStepRewrite] at hrew
    | done w =>
        simp [bigStepGSLT, BigStepRewrite, DoneValue] at hrew hdone
        rcases hrew with ⟨st', hp⟩
        cases hdone
        exact ⟨st', hp⟩
  · intro h
    refine ⟨.done v, ?_, rfl⟩
    simpa [bigStepGSLT, BigStepRewrite] using h

/-- Box over the flat big-step GSLT gives the fuel-bounded result modality. -/
theorem box_fuel_bounded (sig : Signature Prim) (fuel : Nat) (cfg : Config) (st : Store)
    (p : Prog) :
    Box (bigStepGSLT sig fuel cfg st) DoneTerm (.prog p) := by
  intro u h
  cases u <;> simp [bigStepGSLT, BigStepRewrite, DoneTerm] at h ⊢

/-- A program emits value `v` at OEIS seed `k` under the fixed fuel. -/
def EmitsAt (sig : Signature Prim) (fuel : Nat) (p : Prog) (k v : Int) : Prop :=
  Diamond (bigStepGSLT sig fuel (seed k) Store.zero) (DoneValue v) (.prog p)

/-- A program emits every value in a finite prefix at the corresponding OEIS seed. -/
def EmitsPrefix (sig : Signature Prim) (fuel : Nat) (p : Prog) (pref : List Int) : Prop :=
  ∀ i v, listGet? pref i = some v -> EmitsAt sig fuel p (Int.ofNat i) v

theorem emitsAt_iff (sig : Signature Prim) (fuel : Nat) (p : Prog) (k v : Int) :
    EmitsAt sig fuel p k v ↔
      ∃ st', eval fuel sig p (seed k) Store.zero = some (v, st') := by
  simpa [EmitsAt] using
    diamond_done_iff sig fuel (seed k) Store.zero p v

example : EmitsAt orgE1Signature 20 Org.X 3 3 := by
  rw [emitsAt_iff]
  refine ⟨Store.zero, ?_⟩
  simp [Org.X, orgE1Signature, eval, entryAt, listGet?, entry, seed]

example : ¬ EmitsAt orgE1Signature 0 Org.X 3 3 := by
  rw [emitsAt_iff]
  intro h
  rcases h with ⟨st', hst⟩
  simp [eval] at hst

example : DoneValue 7 (.done 7) := rfl

example : ¬ DoneValue 7 (.done 8) := by
  simp [DoneValue]

example : Box (bigStepGSLT orgE1Signature 20 (seed 3) Store.zero) DoneTerm (.prog Org.X) :=
  box_fuel_bounded orgE1Signature 20 (seed 3) Store.zero Org.X

#eval seqPrefix 20 orgE1Signature Org.X 5

end Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
