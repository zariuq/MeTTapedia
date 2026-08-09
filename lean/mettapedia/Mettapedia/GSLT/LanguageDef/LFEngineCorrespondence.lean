/-
# E2b — the engine agrees with the verified recognizer, through an explicit encoding  (2026-07-03)

`LF.lean` has the *verified* `recognize` (`recognize_sound : recognize … = some t → WellScoped 0 t`).
`LFRecognizerEncoding.lean` has `pLF`, the *runnable* recognizer re-encoded as a pure
`MeTTaIL.Presentation`, with its corpus proved to reduce correctly on the **certified** normalizer
`MeTTaIL.eval`.  This file ties the two together through an explicit encoding `⟦·⟧` of Lean `Term`s
and `Tok`s into MeTTaIL `AST`, so the correspondence is a proven *function-level* fact rather than
two separately-eyeballed sides:

  * `MatchesVerdict (recognize 64 ts) (eval pLF _ ⟦ts⟧_lfrec)` for each corpus stream `ts` — success
    maps to `Ok ⟦t⟧` and rejection to some `Err`, both computed on the verified engine;
  * `recognize_sound`-composed: on accepted streams the engine's output is the encoding of a
    provably `WellScoped` term (E3, corpus level, through the engine).

This is the finite correspondence *over the verified engine* (a strengthening of the Lean-side-only
`LFCorrespondence.lean`).  The universal `∀ ts` statement is the same `MatchesVerdict`, quantified —
the remaining frontier, provable by simulation induction over `eval`.

Integrity: 0 sorry / 0 native_decide; corpus closed by `rfl`; `#print axioms` clean.
-/
import Mettapedia.GSLT.LanguageDef.LF
import Mettapedia.GSLT.LanguageDef.LFCorrespondence
import Mettapedia.GSLT.LanguageDef.LFRecognizerEncoding

namespace Mettapedia.GSLT.LanguageDef.LFEngineCorr

open MeTTaIL Mettapedia.GSLT.LanguageDef.LFEnc

-- These theorems re-run `eval` on the corpus; keep the elaborator's recursion bound raised (this is
-- `maxRecDepth`, an elaboration/whnf stack limit, NOT `native_decide`).
set_option maxRecDepth 8000

/-! ## The encoding `⟦·⟧` : Lean `Term` / `Tok` ↦ MeTTaIL `AST`. -/

/-- Encode an LF sort. -/
def encSrt : LF.Srt → AST
  | .type => con0 "type"
  | .kind => con0 "kind"

/-- Encode a de Bruijn `Term` into the MeTTaIL AST the recognizer emits (indices → Peano). -/
def encTerm : LF.Term → AST
  | .srt s   => Srt (encSrt s)
  | .con x   => Con (con0 x)
  | .var k   => Var (peano k)
  | .pi A B  => Pi (encTerm A) (encTerm B)
  | .lam A b => Lam (encTerm A) (encTerm b)
  | .app f a => App (encTerm f) (encTerm a)

/-- Encode a source token. -/
def encTok : LF.Tok → AST
  | .pi    => tPI
  | .lam   => tLAM
  | .arr   => tARR
  | .colon => tCOLON
  | .dot   => tDOT
  | .lpar  => tLP
  | .rpar  => tRP
  | .type  => tTYPE
  | .id s  => tId (con0 s)

/-- Encode a token stream. -/
def encToks : List LF.Tok → AST
  | []      => Nil
  | t :: ts => Cons (encTok t) (encToks ts)

/-- The engine verdict `v` agrees with the recognizer's `Option Term`: acceptance maps to `Ok ⟦t⟧`,
    rejection to some `Err`. -/
def MatchesVerdict : Option LF.Term → AST → Prop
  | some t, v => v = Ok (encTerm t)
  | none,   v => ∃ e, v = Err e

/-! ## Corpus correspondence — the engine matches the verified `recognize`, through `⟦·⟧`. -/

theorem engine_c1 :
    MatchesVerdict (LF.recognize 64 LF.cToks1) (eval pLF 100 (lfrec (encToks LF.cToks1))) := by
  rw [LF.corr1]; rfl

theorem engine_c2 :
    MatchesVerdict (LF.recognize 64 LF.cToks2) (eval pLF 100 (lfrec (encToks LF.cToks2))) := by
  rw [LF.corr2]; rfl

theorem engine_c3 :
    MatchesVerdict (LF.recognize 64 LF.cToks3) (eval pLF 150 (lfrec (encToks LF.cToks3))) := by
  rw [LF.corr3]; rfl

theorem engine_c4 :
    MatchesVerdict (LF.recognize 64 LF.cToks4) (eval pLF 150 (lfrec (encToks LF.cToks4))) := by
  rw [LF.corr4]; rfl

theorem engine_c5 :
    MatchesVerdict (LF.recognize 64 LF.cToks5) (eval pLF 150 (lfrec (encToks LF.cToks5))) := by
  rw [LF.corr5]; rfl

theorem engine_c6 :
    MatchesVerdict (LF.recognize 64 LF.cToks6) (eval pLF 200 (lfrec (encToks LF.cToks6))) := by
  rw [LF.corr6]; rfl

theorem engine_c7 :
    MatchesVerdict (LF.recognize 64 LF.cToks7) (eval pLF 250 (lfrec (encToks LF.cToks7))) := by
  rw [LF.corr7]; rfl

theorem engine_c8 :
    MatchesVerdict (LF.recognize 64 LF.cToks8) (eval pLF 100 (lfrec (encToks LF.cToks8))) := by
  rw [LF.corr8]; exact ⟨con0 "paren-malformed", by rfl⟩

/-! ## E3 through the engine — accepted streams encode provably well-scoped terms.

Composing the engine correspondence with `recognize_sound` (via the `ws*` corollaries): whenever the
runnable engine accepts a corpus stream, its output is `⟦t⟧` for a term `t` proved `WellScoped 0`.
The runnable parser's front end is thus the *proved* artifact on these streams, not a hand-checked
twin. -/

theorem engine_wellscoped_c4 :
    ∃ t, eval pLF 150 (lfrec (encToks LF.cToks4)) = Ok (encTerm t) ∧ LF.WellScoped 0 t :=
  ⟨_, by rfl, LF.ws4⟩

theorem engine_wellscoped_c6 :
    ∃ t, eval pLF 200 (lfrec (encToks LF.cToks6)) = Ok (encTerm t) ∧ LF.WellScoped 0 t :=
  ⟨_, by rfl, LF.ws6⟩

theorem engine_wellscoped_c7 :
    ∃ t, eval pLF 250 (lfrec (encToks LF.cToks7)) = Ok (encTerm t) ∧ LF.WellScoped 0 t :=
  ⟨_, by rfl, LF.ws7⟩

end Mettapedia.GSLT.LanguageDef.LFEngineCorr
