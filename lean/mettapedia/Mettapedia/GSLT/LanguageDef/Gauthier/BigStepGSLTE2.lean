/-
# Gauthier E2 memo programs as a coarse big-step GSLT

The live `intlSignature` evaluator returns integer lists.  This presentation
keeps the whole list in the rewrite result and makes the runtime's observable
head projection explicit in `MemoEmitsAt`; no scalar E1 semantics is imported
as a surrogate for memo execution.
-/

import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.LanguageDef.Gauthier.E2

namespace Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT

open Mettapedia.GSLT.LanguageDef.GauthierE2

abbrev Program := Mettapedia.GSLT.LanguageDef.GauthierE1.Prog
abbrev MemoSignature :=
  Mettapedia.GSLT.LanguageDef.GauthierE1.Signature
    Mettapedia.GSLT.LanguageDef.GauthierE2.Prim

/-- Coarse terms retain the complete memo-list result. -/
inductive MemoBigStepTerm where
  | prog : Program → MemoBigStepTerm
  | done : List Int → MemoBigStepTerm
  deriving Repr

/-- Program equations are E2 extensional equality; completed lists use equality. -/
def MemoBigStepEquiv (sig : MemoSignature) : MemoBigStepTerm → MemoBigStepTerm → Prop
  | .prog p, .prog q => Extensional sig p q
  | .done values, .done values' => values = values'
  | _, _ => False

def memoBigStepSetoid (sig : MemoSignature) : Setoid MemoBigStepTerm where
  r := MemoBigStepEquiv sig
  iseqv :=
    ⟨ by
        intro term
        cases term with
        | prog p => exact Extensional.refl sig p
        | done _ => rfl
    , by
        intro left right h
        cases left <;> cases right <;> simp [MemoBigStepEquiv] at h ⊢
        · exact Extensional.symm h
        · exact h.symm
    , by
        intro first second third hfirst hsecond
        cases first <;> cases second <;> cases third <;>
          simp [MemoBigStepEquiv] at hfirst hsecond ⊢
        · exact Extensional.trans hfirst hsecond
        · exact hfirst.trans hsecond
    ⟩

/-- One rewrite is one successful run of the real E2 evaluator. -/
def MemoBigStepRewrite (sig : MemoSignature) (fuel : Nat)
    (x y : List Int) (world : World) : MemoBigStepTerm → MemoBigStepTerm → Prop
  | .prog program, .done values => eval fuel sig program x y world = some values
  | _, _ => False

theorem memoBigStepRewrite_resp_left (sig : MemoSignature) (fuel : Nat)
    (x y : List Int) (world : World) :
    ∀ {term term' result}, (memoBigStepSetoid sig).r term term' →
      MemoBigStepRewrite sig fuel x y world term result →
      ∃ result', MemoBigStepRewrite sig fuel x y world term' result' ∧
        (memoBigStepSetoid sig).r result result' := by
  intro term term' result heq hstep
  cases term with
  | done _ =>
      cases result <;> simp [MemoBigStepRewrite] at hstep
  | prog program =>
      cases result with
      | prog _ => simp [MemoBigStepRewrite] at hstep
      | done values =>
          cases term' with
          | done values' =>
              change MemoBigStepEquiv sig (.prog program) (.done values') at heq
              exact False.elim heq
          | prog program' =>
              change Extensional sig program program' at heq
              refine ⟨.done values, ?_, rfl⟩
              exact (heq fuel x y world).symm.trans hstep

theorem memoBigStepRewrite_resp_right (sig : MemoSignature) (fuel : Nat)
    (x y : List Int) (world : World) :
    ∀ {term result result'}, MemoBigStepRewrite sig fuel x y world term result →
      (memoBigStepSetoid sig).r result result' →
      MemoBigStepRewrite sig fuel x y world term result' := by
  intro term result result' hstep heq
  cases term with
  | done _ =>
      cases result <;> simp [MemoBigStepRewrite] at hstep
  | prog program =>
      cases result with
      | prog _ => simp [MemoBigStepRewrite] at hstep
      | done values =>
          cases result' with
          | prog program' =>
              change MemoBigStepEquiv sig (.done values) (.prog program') at heq
              exact False.elim heq
          | done values' =>
              change values = values' at heq
              cases heq
              exact hstep

def memoBigStepGSLT (sig : MemoSignature) (fuel : Nat)
    (x y : List Int) (world : World) : Mettapedia.GSLT.GSLT where
  Term := MemoBigStepTerm
  equations := memoBigStepSetoid sig
  rewrites := MemoBigStepRewrite sig fuel x y world
  rewrites_resp_left := memoBigStepRewrite_resp_left sig fuel x y world
  rewrites_resp_right := memoBigStepRewrite_resp_right sig fuel x y world

def Diamond (system : Mettapedia.GSLT.GSLT)
    (post : system.Term → Prop) (term : system.Term) : Prop :=
  ∃ result, system.rewrites term result ∧ post result

/-- The observable runtime value is the head of a completed memo list. -/
def DoneHeadValue (value : Int) : MemoBigStepTerm → Prop
  | .done values => head? values = some value
  | _ => False

theorem memoDiamond_done_head_iff (sig : MemoSignature) (fuel : Nat)
    (x y : List Int) (world : World) (program : Program) (value : Int) :
    Diamond (memoBigStepGSLT sig fuel x y world) (DoneHeadValue value) (.prog program) ↔
      ∃ values, eval fuel sig program x y world = some values ∧
        head? values = some value := by
  constructor
  · rintro ⟨result, hstep, hdone⟩
    cases result with
    | prog _ => simp [memoBigStepGSLT, MemoBigStepRewrite] at hstep
    | done values =>
        exact ⟨values, hstep, hdone⟩
  · rintro ⟨values, heval, hhead⟩
    exact ⟨.done values, heval, hhead⟩

/-- E2 observation at the harness seeds `[k]` and `[0]` in the default world. -/
def MemoEmitsAt (sig : MemoSignature) (fuel : Nat)
    (program : Program) (seedValue value : Int) : Prop :=
  Diamond (memoBigStepGSLT sig fuel [seedValue] [0] defaultWorld)
    (DoneHeadValue value) (.prog program)

theorem memoEmitsAt_iff (sig : MemoSignature) (fuel : Nat)
    (program : Program) (seedValue value : Int) :
    MemoEmitsAt sig fuel program seedValue value ↔
      ∃ values, eval fuel sig program [seedValue] [0] defaultWorld = some values ∧
        head? values = some value := by
  simpa [MemoEmitsAt] using
    memoDiamond_done_head_iff sig fuel [seedValue] [0] defaultWorld program value

example : MemoEmitsAt intlSignature 2 (.node 10 []) 3 3 := by
  rw [memoEmitsAt_iff]
  refine ⟨[3], ?_, rfl⟩
  simp [eval, intlSignature, orgSignature, listOps,
    Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
    Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
    Mettapedia.GSLT.LanguageDef.GauthierE1.entry]

example : ¬ MemoEmitsAt intlSignature 0 (.node 10 []) 3 3 := by
  rw [memoEmitsAt_iff]
  rintro ⟨values, heval, _⟩
  simp [eval] at heval

end Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT
