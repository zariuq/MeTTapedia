import Mettapedia.GSLT.LanguageDef.AffineExpressionGSLT
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native OSLF observations for the affine expression GSLT

Use the existing OSLF construction on the source's reachability closure.
Terminal integer predicates pull back exactly through accepted compilation.
This is an observation-level theorem: the fused implementation does not
preserve the number or identity of primitive rewrites.
-/

namespace Mettapedia.GSLT.AffineExpression

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def terminalPredicate (P : Int → Prop) : Expr n → Prop
  | .lit v => P v
  | _ => False

theorem closure_literal_iff (env : Fin n → Int) (state : Int) (e : Expr n) (v : Int) :
    (theory env state).closure.Step e (.lit v) ↔ e.eval env state = v := by
  change (∃ reached, (theory env state).MultiStep e reached ∧ reached = .lit v) ↔ _
  constructor
  · rintro ⟨reached, path, eq⟩
    cases eq
    exact (reaches_literal_iff env state e v).mp path
  · intro h
    exact ⟨.lit v, (reaches_literal_iff env state e v).mpr h, rfl⟩

/-- The standard generated diamond, not a separate DSL-specific modality. -/
theorem oslf_terminal_exact (env : Fin n → Int) (state : Int)
    (e : Expr n) (f : Form n) (admitted : compile e = some f) (P : Int → Prop) :
    gsltDiamond (theory env state).closure (terminalPredicate P) e ↔
      P (f.apply env state) := by
  erw [gsltDiamond_spec]
  constructor
  · rintro ⟨target, reached, hp⟩
    cases target with
    | lit v =>
        have hv := (closure_literal_iff env state e v).mp reached
        have hf := compile_sound e f admitted env state
        change P v at hp
        simpa [hf, hv] using hp
    | input | acc | bin => exact False.elim hp
  · intro hp
    refine ⟨.lit (f.apply env state), ?_, hp⟩
    rw [closure_literal_iff]
    exact (compile_sound e f admitted env state).symm

end Mettapedia.GSLT.AffineExpression
