import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DomainRaising
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilyControls

/-!
# Controls for domain raising, in the tree's tower

* **A store of the cross shape that one rule decides** (`raiseView`, `raise_principal`, `raise_unread`): over
  `X : U0 → U1` and `Y : U1 → U0`, the equation `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U1` has its two unknowns
  declared over different domains, like the cross store; the families solver does not read it. Here `Y` fits `X`
  (it takes `U1` and returns `U0`), and domain raising answers `X := λ x. Y x`, with a principal answer.
* **On the cross store neither unknown fits the other** (`cross_no_fit`, `cross_no_fit_swapped`): `X : U0 → U0` and
  `Y : U1 → U1`. In the first orientation `Y`'s codomain `U1` does not lie below `X`'s `U0`; in the second, `X` does
  not take `Y`'s arguments of `U1`. That is where the store has no principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-! ## A store of the cross shape decided by domain raising -/

/-- `U0 → U1`. -/
def familyUp : TypeOver (empty setting.R) := formIn (empty setting.R) (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `X : U0 → U1`. -/
abbrev ctxUp := extend (empty setting.R) familyUp

/-- `U1 → U0`, over `X`. -/
def familyDown : TypeOver ctxUp := formIn ctxUp (.pi (.head U1) (.head U0)) (by decide +kernel)

/-- `X : U0 → U1, Y : U1 → U0`. -/
abbrev ctxUpDown := extend ctxUp familyDown

/-- `Π (x : U0). U1`, over `X Y`. -/
def upType : TypeOver ctxUpDown := formIn ctxUpDown (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U1`. -/
def raiseEquation : Equation (TotalTerm ctxUpDown) :=
  (termIn ctxUpDown upType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxUpDown upType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def raiseStore : EquationStore (TotalTerm ctxUpDown) := [raiseEquation]

/-- **`Y` fits `X`**: `X := λ x. Y x`. -/
def raiseView : FitsView (S := setting) raiseEquation where
  p := U0
  q := U1
  G := 1
  F := 0
  pG := U0
  cG := U1
  pF := U1
  cF := U0
  distinct := by decide
  annotation_left := by decide +kernel
  annotation_right := by decide +kernel
  side_left := by decide +kernel
  side_right := by decide +kernel
  declared_G := by decide +kernel
  declared_F := by decide +kernel
  universe_p := by decide
  universe_q := by decide
  universe_pG := by decide
  universe_cG := by decide
  universe_pF := by decide
  universe_cF := by decide
  domain_G := by decide
  domain_F := by decide
  codomain_F := by decide
  codomain_G := by decide

/-- The answer of domain raising on the store. -/
def raiseAnswer : Update setting.levels raiseStore :=
  raiseUpdate TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete raiseView
    (allFamilies_of_B (by decide +kernel)) []

/-- **The store has a principal answer**, `X := λ x. Y x`. -/
theorem raise_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUpDown), (frames setting.levels).Principal raiseStore answer :=
  ⟨_, _, raiseAnswer.completed rfl⟩

/-- **The families solver does not read it**: the two unknowns are declared over different domains. -/
theorem raise_unread : (readFlexData (S := setting) raiseEquation).isNone = true := by decide +kernel

/-! ## On the cross store neither unknown fits the other -/

theorem crossLeft_code : crossEquation.1.2.code = etaExp 1 (.var (1 : Fin ctxCross.arity)) := by decide +kernel
theorem crossRight_code : crossEquation.2.2.code = etaExp 1 (.var (0 : Fin ctxCross.arity)) := by decide +kernel
theorem crossX_declared : Ctx.lookup ctxCross.raw 1 = famCode [U0] U0 := by decide +kernel
theorem crossY_declared : Ctx.lookup ctxCross.raw 0 = famCode [U1] U1 := by decide +kernel

/-- **`Y` does not fit `X`**: its codomain `U1` does not lie below `X`'s `U0`. -/
theorem cross_no_fit : ¬ Nonempty (FitsView (S := setting) crossEquation) := by
  rintro ⟨v⟩
  have hG : v.G = 1 := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans crossLeft_code))
  have hF : v.F = 0 := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans crossRight_code))
  have dG := v.declared_G
  have dF := v.declared_F
  rw [hG, crossX_declared] at dG
  rw [hF, crossY_declared] at dF
  obtain ⟨_, cG⟩ := famCode_inj dG
  obtain ⟨_, cF⟩ := famCode_inj dF
  have codomain := v.codomain_F
  rw [← cG, ← cF] at codomain
  exact absurd codomain (by decide)

/-- **`X` does not fit `Y`**: it does not take `Y`'s arguments of `U1`. -/
theorem cross_no_fit_swapped :
    ¬ Nonempty (FitsView (S := setting) ((crossEquation.2, crossEquation.1) : Equation (TotalTerm ctxCross))) := by
  rintro ⟨v⟩
  have hG : v.G = 0 := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans crossRight_code))
  have hF : v.F = 1 := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans crossLeft_code))
  have dG := v.declared_G
  have dF := v.declared_F
  rw [hG, crossY_declared] at dG
  rw [hF, crossX_declared] at dF
  obtain ⟨pG, _⟩ := famCode_inj dG
  obtain ⟨pF, _⟩ := famCode_inj dF
  have domain := v.domain_F
  have pG' : v.pG = U1 := (List.cons.inj pG).1.symm
  have pF' : v.pF = U0 := (List.cons.inj pF).1.symm
  rw [pG', pF'] at domain
  exact absurd domain (by decide)

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
