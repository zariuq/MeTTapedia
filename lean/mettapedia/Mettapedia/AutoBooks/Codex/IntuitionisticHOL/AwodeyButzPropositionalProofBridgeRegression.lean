import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalProofBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalFragmentRegression
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzPropositionalProofBridgeRegression

open Mettapedia.Logic.HOL
open AwodeyButzPropositionalFragmentRegression

abbrev DBase := AwodeyButzGenericPredicatesRegression.DemoBase
abbrev DConst := AwodeyButzGenericPredicatesRegression.DemoConst

local notation "atomTy" => (SimpleTy.base AwodeyButzGenericPredicatesRegression.DemoBase.atom)

def topConjTopFormula : SimplePropFormula DBase DConst [] :=
  .conj .top .top

def propAtomReflFormula : SimplePropFormula DBase DConst [.prop, atomTy] :=
  .impl propAtomFormula propAtomFormula

theorem toFormula_propAtomFormula :
    SimplePropFormula.toFormula propAtomFormula =
      (.var Var.vz : Formula DConst (SimpleTy.toCtx [.prop, atomTy])) :=
by
  simp [propAtomFormula, AwodeyButzSimpleTermsRegression.propVarTerm, SimpleTerm.toTerm]
  rfl

theorem toFormula_subst_conjFormula :
    SimplePropFormula.toFormula (SimplePropFormula.subst propAtomSynSubst conjFormula) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst (SimpleSubst.toSubst propAtomSynSubst)
        (SimplePropFormula.toFormula conjFormula) := by
  exact SimplePropFormula.toFormula_subst (σs := propAtomSynSubst) (φ := conjFormula)

theorem toFormula_subst_implFormula :
    SimplePropFormula.toFormula (SimplePropFormula.subst propAtomSynSubst implFormula) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst (SimpleSubst.toSubst propAtomSynSubst)
        (SimplePropFormula.toFormula implFormula) := by
  exact SimplePropFormula.toFormula_subst (σs := propAtomSynSubst) (φ := implFormula)

theorem topConjTop_ne_truthFormula :
    SimplePropFormula.toFormula topConjTopFormula ≠
      SimplePropFormula.toFormula truthFormula := by
  intro h
  simp [topConjTopFormula, truthFormula,
    AwodeyButzSimpleTermsRegression.truthConstTerm, SimpleTerm.toTerm] at h

theorem derivable_topConjTop :
    PropositionalDerivable DConst
      ([] : List (Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase)))))
      (SimplePropFormula.toFormula topConjTopFormula) := by
  simpa [topConjTopFormula, SimplePropFormula.toFormula] using
    (PropositionalDerivable.andR
      (Const := DConst)
      (Δ := ([] : List (Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase))))))
      (φ := (.top : Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase)))))
      (ψ := (.top : Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase)))))
      (PropositionalDerivable.topR (Const := DConst)
        (Δ := ([] : List (Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase)))))))
      (PropositionalDerivable.topR (Const := DConst)
        (Δ := ([] : List (Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase))))))))

theorem derivable_propAtom_refl :
    PropositionalDerivable DConst
      ([] : List (Formula DConst (SimpleTy.toCtx [.prop, atomTy])))
      (SimplePropFormula.toFormula propAtomReflFormula) := by
  simpa [propAtomReflFormula, SimplePropFormula.toFormula] using
    (PropositionalDerivable.impR
      (Const := DConst)
      (Δ := ([] : List (Formula DConst (SimpleTy.toCtx [.prop, atomTy]))))
      (φ := SimplePropFormula.toFormula propAtomFormula)
      (ψ := SimplePropFormula.toFormula propAtomFormula)
      (PropositionalDerivable.ax
        (Const := DConst)
        (Δ := [SimplePropFormula.toFormula propAtomFormula])
        (φ := SimplePropFormula.toFormula propAtomFormula)
        (List.mem_singleton_self _)))

theorem derivable_propAtom_assumption :
    PropositionalDerivable DConst
      [SimplePropFormula.toFormula propAtomFormula]
      (SimplePropFormula.toFormula propAtomFormula) := by
  exact .ax (List.mem_singleton_self _)

theorem boundedValid_topConjTop
    (M : SemilocalModel DBase DConst) (u : M.Omega) :
    SemilocalModel.BoundedValidSequent M u
      ([] : List (Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase)))))
      (SimplePropFormula.toFormula topConjTopFormula) := by
  exact SemilocalModel.propositional_bounded_soundness
    (M := M) derivable_topConjTop u

theorem valid_topConjTop
    (M : SemilocalModel DBase DConst) :
    SemilocalModel.ValidSequent M
      ([] : List (Formula DConst (SimpleTy.toCtx ([] : List (SimpleTy DBase)))))
      (SimplePropFormula.toFormula topConjTopFormula) := by
  exact SemilocalModel.propositional_soundness
    (M := M) derivable_topConjTop

theorem boundedValid_propAtom_refl
    (M : SemilocalModel DBase DConst) (u : M.Omega) :
    SemilocalModel.BoundedValidSequent M u
      ([] : List (Formula DConst (SimpleTy.toCtx [.prop, atomTy])))
      (SimplePropFormula.toFormula propAtomReflFormula) := by
  exact SemilocalModel.propositional_bounded_soundness
    (M := M) derivable_propAtom_refl u

theorem valid_propAtom_refl
    (M : SemilocalModel DBase DConst) :
    SemilocalModel.ValidSequent M
      ([] : List (Formula DConst (SimpleTy.toCtx [.prop, atomTy])))
      (SimplePropFormula.toFormula propAtomReflFormula) := by
  exact SemilocalModel.propositional_soundness
    (M := M) derivable_propAtom_refl

end AwodeyButzPropositionalProofBridgeRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
