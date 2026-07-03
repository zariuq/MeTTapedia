/-
# LF recognizer correspondence — the finite corpus, proven on the Lean side  (E2a)

The runnable `.metta` twin (`MettaKernel/kernel/lf_recognizer_v0.metta`) and the verified Lean
`recognize` (`LF.lean`) are corresponded at the corpus by having **both sides equal the same
concrete de Bruijn AST** on each token stream:

  * the `.metta` side is witnessed on *both* CeTTa (the runnable home) and the Lean-verified
    LeaTTa engine — E1, 8/8, pure-rewriting scope where those engines agree;
  * the Lean side is *proven here* by `decide` — `recognize 64 tsᵢ = some astᵢ` for each corpus
    case (and `= none` for the malformed one).

So for every corpus input the two artifacts provably compute the *same* AST: a finite, honest
correspondence with the math side carrying the proof and the engine side carrying the run. The
universal correspondence `∀ ts, ⟦lf-recognize⟧ ts = recognize ts` is the separate frontier.

Integrity: 0 sorry / 0 native_decide; `#print axioms` clean.
-/
import Mettapedia.GSLT.LanguageDef.LF

namespace Mettapedia.GSLT.LanguageDef.LF

/-! ## The 8 corpus token streams (matching the `tk-*` streams in `lf_recognizer_v0.metta`) -/

/-- `rfl z` -/
def cToks1 : List Tok := [.id "rfl", .id "z"]
/-- `eqn z z` -/
def cToks2 : List Tok := [.id "eqn", .id "z", .id "z"]
/-- `eqn z (s z)` -/
def cToks3 : List Tok := [.id "eqn", .id "z", .lpar, .id "s", .id "z", .rpar]
/-- `λ x : nat . x` -/
def cToks4 : List Tok := [.lam, .id "x", .colon, .id "nat", .dot, .id "x"]
/-- `nat → nat` -/
def cToks5 : List Tok := [.id "nat", .arr, .id "nat"]
/-- `( λ x : nat . x ) z` -/
def cToks6 : List Tok := [.lpar, .lam, .id "x", .colon, .id "nat", .dot, .id "x", .rpar, .id "z"]
/-- `Π A : Type . ( A → A )` -/
def cToks7 : List Tok := [.pi, .id "A", .colon, .type, .dot, .lpar, .id "A", .arr, .id "A", .rpar]
/-- malformed: `( .` -/
def cToks8 : List Tok := [.lpar, .dot]

/-! ## Corpus correspondence — the Lean `recognize` computes exactly the twin's AST (fuel 64,
matching the twin). Each is closed by `decide`: the same concrete AST both sides produce. -/

theorem corr1 : recognize 64 cToks1 = some (.app (.con "rfl") (.con "z")) := by decide
theorem corr2 : recognize 64 cToks2 = some (.app (.app (.con "eqn") (.con "z")) (.con "z")) := by decide
theorem corr3 : recognize 64 cToks3
    = some (.app (.app (.con "eqn") (.con "z")) (.app (.con "s") (.con "z"))) := by decide
theorem corr4 : recognize 64 cToks4 = some (.lam (.con "nat") (.var 0)) := by decide
theorem corr5 : recognize 64 cToks5 = some (.pi (.con "nat") (.con "nat")) := by decide
theorem corr6 : recognize 64 cToks6 = some (.app (.lam (.con "nat") (.var 0)) (.con "z")) := by decide
theorem corr7 : recognize 64 cToks7 = some (.pi (.srt .type) (.pi (.var 0) (.var 1))) := by decide
/-- the malformed stream is rejected by the Lean recognizer too (the twin returns `Err`). -/
theorem corr8 : recognize 64 cToks8 = none := by decide

/-! ## E3 (finite): every corpus output the twin emits is well-scoped — `recognize_sound` applied
to the corpus correspondences. The runnable parser's corpus outputs are proved well-formed. -/

theorem ws1 : WellScoped 0 (.app (.con "rfl") (.con "z")) := recognize_sound corr1
theorem ws2 : WellScoped 0 (.app (.app (.con "eqn") (.con "z")) (.con "z")) := recognize_sound corr2
theorem ws3 : WellScoped 0 (.app (.app (.con "eqn") (.con "z")) (.app (.con "s") (.con "z"))) :=
  recognize_sound corr3
theorem ws4 : WellScoped 0 (.lam (.con "nat") (.var 0)) := recognize_sound corr4
theorem ws5 : WellScoped 0 (.pi (.con "nat") (.con "nat")) := recognize_sound corr5
theorem ws6 : WellScoped 0 (.app (.lam (.con "nat") (.var 0)) (.con "z")) := recognize_sound corr6
theorem ws7 : WellScoped 0 (.pi (.srt .type) (.pi (.var 0) (.var 1))) := recognize_sound corr7

end Mettapedia.GSLT.LanguageDef.LF
