import Mettapedia.GSLT.Logic.PropositionalFormula
import Mettapedia.GSLT.Logic.PropositionalResolution
import Mettapedia.GSLT.Logic.PropositionalCut
import Mettapedia.GSLT.Logic.PropositionalMLL
import Mettapedia.GSLT.Logic.MLLSession
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# The propositional fragment as several GSLTs

Foundation is not imported. These are kernel instances:

* `propositionalEqGSLT` — classical formulas, Boolean equations, *no*
  rewrites. Diamond is empty. This is the language.
* `resolutionGSLT` — clause sets, resolve. Diamond is a resolvent.
  This is the inference calculus.
* `propositionalGSLT` — ND proof terms, `CutStep`. Diamond is cut-elim.
  This is a dynamics on proofs, not the logic.
* `mllEqGSLT` / `mllCutGSLT` — multiplicative linear fragment: duality
  equations, then principal cut-elim on untyped proofs. One-sided
  `Derives` is the logic; typed `hauptsatz` is cut-admissibility, not a
  `CutStep` rewrite. Not `SoundCut`. Session erasure of names is a
  translation, not a cover (`MLLSession`).

No FOL, no additives, no exponentials, no Hauptsatz-as-rewrite.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.PropositionalFragment

open Mettapedia.GSLT
open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.GSLT.Logic.PropositionalResolution
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

theorem eq_diamond_empty (P : Formula → Prop) (A : Formula) :
    gsltDiamond propositionalEqGSLT P A ↔ False := by
  constructor
  · intro h
    rcases (gsltDiamond_spec propositionalEqGSLT P A).mp h with ⟨_, step, _⟩
    exact step.elim
  · intro h
    exact h.elim

theorem resolution_diamond_iff (P : CNF → Prop) (Γ : CNF) :
    gsltDiamond resolutionGSLT P Γ ↔ ∃ Δ, Resolve Γ Δ ∧ P Δ :=
  gsltDiamond_spec resolutionGSLT P Γ

theorem cut_diamond_iff
    (P : Mettapedia.GSLT.Logic.PropositionalCut.Proof → Prop)
    (p : Mettapedia.GSLT.Logic.PropositionalCut.Proof) :
    gsltDiamond Mettapedia.GSLT.Logic.PropositionalCut.propositionalGSLT P p ↔
      ∃ q, Mettapedia.GSLT.Logic.PropositionalCut.CutStep p q ∧ P q :=
  gsltDiamond_spec Mettapedia.GSLT.Logic.PropositionalCut.propositionalGSLT P p

theorem mll_cut_diamond_iff
    (P : Mettapedia.GSLT.Logic.PropositionalMLL.Proof → Prop)
    (p : Mettapedia.GSLT.Logic.PropositionalMLL.Proof) :
    gsltDiamond Mettapedia.GSLT.Logic.PropositionalMLL.mllCutGSLT P p ↔
      ∃ q, Mettapedia.GSLT.Logic.PropositionalMLL.CutStep p q ∧ P q :=
  gsltDiamond_spec Mettapedia.GSLT.Logic.PropositionalMLL.mllCutGSLT P p

theorem mll_eq_diamond_empty
    (P : Mettapedia.GSLT.Logic.PropositionalMLL.Formula → Prop)
    (A : Mettapedia.GSLT.Logic.PropositionalMLL.Formula) :
    gsltDiamond Mettapedia.GSLT.Logic.PropositionalMLL.mllEqGSLT P A ↔ False := by
  constructor
  · intro h
    rcases (gsltDiamond_spec
        Mettapedia.GSLT.Logic.PropositionalMLL.mllEqGSLT P A).mp h
      with ⟨_, step, _⟩
    exact step.elim
  · intro h
    exact h.elim

theorem eq_induces_galois :
    GaloisConnection (gsltDiamond propositionalEqGSLT)
      (gsltBox propositionalEqGSLT) :=
  gsltGalois propositionalEqGSLT

theorem resolution_induces_galois :
    GaloisConnection (gsltDiamond resolutionGSLT) (gsltBox resolutionGSLT) :=
  gsltGalois resolutionGSLT

theorem mll_cut_induces_galois :
    GaloisConnection
      (gsltDiamond Mettapedia.GSLT.Logic.PropositionalMLL.mllCutGSLT)
      (gsltBox Mettapedia.GSLT.Logic.PropositionalMLL.mllCutGSLT) :=
  gsltGalois Mettapedia.GSLT.Logic.PropositionalMLL.mllCutGSLT

/-- The clausal image of `p ∧ ¬p` is a resolution redex to the empty clause. -/
theorem contradiction_is_resolution_redex :
    Resolve (toCNF (.and (.atom 0) (.not (.atom 0))))
      ([] :: toCNF (.and (.atom 0) (.not (.atom 0)))) := by
  simpa [contradiction_cnf] using clash_resolves_empty

#print axioms eq_diamond_empty
#print axioms resolution_diamond_iff
#print axioms cut_diamond_iff
#print axioms mll_cut_diamond_iff
#print axioms contradiction_is_resolution_redex

end Mettapedia.Logic.Bridges.PropositionalFragment
