import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthPiecesControls

/-!
# A gap in the spine decomposition: a binder of a local's type behind a redex, and its repair

Over `A : U0, F : A → A`, at `Π (h : Π (G : U0 → U1). G A) (y : A). U0`, the equation
**`λ h y. h (λ x. x → U0) y ≐ λ h y. h (λ x. x → U0) (F y)`** (`argStore`) is in the dynamic pattern fragment
(`arg_in_fragment`) and solvable by `F := λ y. y` (`arg_solvable`). Its sides are spines of the local `h`, of one
skeleton, at the rigid base `U0`. The type of `h` at its first argument is `(λ x. x → U0) A`, a redex whose normal form
`A → U0` is a Π type. R99's decomposition between spines of one local reads the binders of the local's type literally
after each instantiation, so it reads no pieces, at any budget (`arg_parts_none`: it takes no budget), and the skeleton
family is stuck in its first round (`arg_skeleton_stuck`). The same reading blocks a refutation: on
`λ h y z. h (λ x. x → U0) y ≐ λ h y z. h (λ x. x → U0) z`, whose last arguments are distinct locals, the skeleton
family is stuck too (`distinct_skeleton_stuck`).

**The repair.** The reading along the reducer's reducts of the instantiated types reads the pieces (`arg_reads`), and
the piece family, which uses it, commits on the first store (`arg_piece_committed`) and refutes the second with a
certified refutation (`distinct_piece_refuted`), so that store is unsolvable (`distinct_unsolvable`). A pattern
against the same spine is solved (`pattern_piece_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.ArgControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth.Controls

def u0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)
def u1 {n : Nat} : Tower.Tm n := .head (.sort (.succ Tower.zero))

/-- `A → A` over `A`. -/
def endo : TypeOver ctxA := formIn ctxA (.pi (.var 0) (.var 1)) (by decide +kernel)

/-- `A : U0, F : A → A`. -/
abbrev ctxAF := extend ctxA endo

/-- `Π (h : Π (G : U0 → U1). G A) (y : A). U0`. -/
def higher : TypeOver ctxAF := formIn ctxAF
  (.pi (.pi (.pi u0 u1) (.app (.var 0) (.var 2))) (.pi (.var 2) u0)) (by decide +kernel)

/-- `λ x. x → U0`. -/
def arrow {n : Nat} : Tower.Tm n := .lam (.pi (.var 0) u0)

/-- `λ h y. h (λ x. x → U0) y ≐ λ h y. h (λ x. x → U0) (F y)`. -/
def argEquation : Equation (TotalTerm ctxAF) :=
  (termIn ctxAF higher (.lam (.lam (.app (.app (.var 1) arrow) (.var 0)))) (by decide +kernel),
    termIn ctxAF higher (.lam (.lam (.app (.app (.var 1) arrow) (.app (.var 2) (.var 0))))) (by decide +kernel))
def argStore : EquationStore (TotalTerm ctxAF) := [argEquation]

theorem arg_in_fragment : InFragmentStore argStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl argEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `F := λ y. y`. -/
def answer : ctxA ⟶ ctxAF :=
  Elimination.instantiate ctxA (termIn ctxA endo (.lam (.var 0)) (by decide +kernel)).2

theorem arg_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution argEquation.1.2.code) (subst answer.substitution argEquation.2.2.code)
      (subst answer.substitution argEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `F := λ y. y`. -/
theorem arg_solvable : (frames setting.levels).Solvable argStore := by
  refine ⟨ctxA, answer, (models_iff setting.levels answer argStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(higher.reindex answer).isType.refl, ?_⟩
  have check := arg_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution argEquation.1.2.code) (subst answer.substitution argEquation.2.2.code)
      (subst answer.substitution argEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ctxA.formed (argEquation.1.2.reindex answer).typed (argEquation.2.2.reindex answer).typed

/-- **The decomposition between spines of one local reads no pieces** on the equation, at any budget. -/
theorem arg_parts_none : ContextualDependentSpinesMany.dependentUnder [] argEquation.1.1.code argEquation.1.2.code
    argEquation.2.2.code = none := by decide +kernel

/-- **The skeleton family is stuck in its first round** on the store, at budget 16. -/
theorem arg_skeleton_stuck : isStuck (run (skeletonTower.solver 16) argStore 1) = true := by decide +kernel

/-- **The reading along the reducts of the instantiated types reads the pieces.** -/
theorem arg_reads : (dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    argEquation.1.1.code argEquation.1.2.code argEquation.2.2.code).isSome = true := by decide +kernel

/-- **The piece family commits on the store.** -/
theorem arg_piece_committed : (run (pieceTower.solver 16) argStore 8).readout = .commit := by decide +kernel

/-! ## The same reading blocks a refutation -/

/-- `Π (h : Π (G : U0 → U1). G A) (y z : A). U0` over `A`. -/
def higherYZ : TypeOver ctxA := formIn ctxA
  (.pi (.pi (.pi u0 u1) (.app (.var 0) (.var 1))) (.pi (.var 1) (.pi (.var 2) u0))) (by decide +kernel)

/-- `λ h y z. h (λ x. x → U0) y ≐ λ h y z. h (λ x. x → U0) z`: distinct locals as last arguments. -/
def distinctStore : EquationStore (TotalTerm ctxA) :=
  [(termIn ctxA higherYZ (.lam (.lam (.lam (.app (.app (.var 2) arrow) (.var 1))))) (by decide +kernel),
    termIn ctxA higherYZ (.lam (.lam (.lam (.app (.app (.var 2) arrow) (.var 0))))) (by decide +kernel))]

/-- **The skeleton family is stuck in its first round on the distinct store too**, at budget 16. -/
theorem distinct_skeleton_stuck : isStuck (run (skeletonTower.solver 16) distinctStore 1) = true := by
  decide +kernel

/-- **The piece family refutes the distinct store**, with a certified refutation. -/
theorem distinct_piece_refuted : (run (pieceTower.solver 16) distinctStore 8).readout = .refuted := by
  decide +kernel

theorem distinct_unsolvable : ¬ (frames setting.levels).Solvable distinctStore :=
  Outcome.readout_eq_refuted distinct_piece_refuted

/-- **A pattern against the same spine is solved**: `λ h y. F h y ≐ λ h y. h (λ x. x → U0) y` over
`A, F : Π (h : Π (G : U0 → U1). G A) (y : A). U0` commits; the gap is in the decomposition between spines only. -/
abbrev ctxAH := extend ctxA (formIn ctxA (.pi (.pi (.pi u0 u1) (.app (.var 0) (.var 1))) (.pi (.var 1) u0))
  (by decide +kernel))

def higherH : TypeOver ctxAH := formIn ctxAH
  (.pi (.pi (.pi u0 u1) (.app (.var 0) (.var 2))) (.pi (.var 2) u0)) (by decide +kernel)

def patternStore : EquationStore (TotalTerm ctxAH) :=
  [(termIn ctxAH higherH (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxAH higherH (.lam (.lam (.app (.app (.var 1) arrow) (.var 0)))) (by decide +kernel))]

theorem pattern_piece_committed : (run (pieceTower.solver 16) patternStore 8).readout = .commit := by
  decide +kernel

end ContextualDependentEtaDepth.ArgControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
