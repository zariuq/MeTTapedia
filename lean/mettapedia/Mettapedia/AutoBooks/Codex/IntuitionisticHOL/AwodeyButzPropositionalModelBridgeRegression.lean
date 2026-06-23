import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalModelBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.LowerBoundExtensionRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

namespace AwodeyButzPropositionalModelBridgeRegression

open LowerBoundExtensionRegression

local notation "atomSimpleTy" => (SimpleTy.base BaseSort.atom)

def topConjTop : SimplePropFormula BaseSort Const [] :=
  .conj .top .top

def propSelfFormula : SimplePropFormula BaseSort Const [.prop] :=
  .atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop))

def propSelfImp : SimplePropFormula BaseSort Const [.prop] :=
  .impl propSelfFormula propSelfFormula

def propTailSubst : SimpleSubst BaseSort Const [.prop] [atomSimpleTy, .prop] :=
  SimpleSubst.cons
    (.var (SimpleVar.vs (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop)))
    (SimpleSubst.empty BaseSort Const [atomSimpleTy, .prop])

def emptyEnv : SemilocalModel.Env model (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))
  | _, v => nomatch v

def propEnv (p : Prop) :
    SemilocalModel.Env model (SimpleTy.toCtx ([.prop] : List (SimpleTy BaseSort)))
  | _, .vz => p
  | _, .vs v => nomatch v

def atomPropEnv (a : Carrier atomTy) (p : Prop) :
    SemilocalModel.Env model (SimpleTy.toCtx ([atomSimpleTy, .prop] : List (SimpleTy BaseSort)))
  | _, .vz => a
  | _, .vs .vz => p
  | _, .vs (.vs v) => nomatch v

theorem emptyEnv_good :
    GoodEnv emptyEnv := by
  intro τ v
  nomatch v

theorem propEnv_good (p : Prop) :
    GoodEnv (propEnv p) := by
  intro τ v
  cases v with
  | vz => trivial
  | vs v => nomatch v

theorem emptyEnv_isGlobal :
    SemilocalModel.IsGlobalEnv model emptyEnv := by
  exact
    (SemilocalModel.isGlobalEnv_iff_hasExtentLowerBound_top model emptyEnv).2
      (hasExtentLowerBound_top_of_goodEnv emptyEnv_good)

theorem propEnv_isGlobal (p : Prop) :
    SemilocalModel.IsGlobalEnv model (propEnv p) := by
  exact
    (SemilocalModel.isGlobalEnv_iff_hasExtentLowerBound_top model (propEnv p)).2
      (hasExtentLowerBound_top_of_goodEnv (propEnv_good p))

theorem derivable_topConjTop :
    PropositionalDerivable Const
      ([] : List (Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))))
      (SimplePropFormula.toFormula topConjTop) := by
  simpa [topConjTop, SimplePropFormula.toFormula] using
    (PropositionalDerivable.andR
      (Const := Const)
      (Δ := ([] : List (Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort))))))
      (φ := (.top : Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))))
      (ψ := (.top : Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))))
      (PropositionalDerivable.topR
        (Const := Const)
        (Δ := ([] : List (Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))))))
      (PropositionalDerivable.topR
        (Const := Const)
        (Δ := ([] : List (Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort))))))))

theorem derivable_propSelfImp :
    PropositionalDerivable Const
      ([] : List (Formula Const (SimpleTy.toCtx ([.prop] : List (SimpleTy BaseSort)))))
      (SimplePropFormula.toFormula propSelfImp) := by
  simpa [propSelfImp, SimplePropFormula.toFormula] using
    (PropositionalDerivable.impR
      (Const := Const)
      (Δ := ([] : List (Formula Const (SimpleTy.toCtx ([.prop] : List (SimpleTy BaseSort))))))
      (φ := SimplePropFormula.toFormula propSelfFormula)
      (ψ := SimplePropFormula.toFormula propSelfFormula)
      (PropositionalDerivable.ax
        (Const := Const)
        (Δ := [SimplePropFormula.toFormula propSelfFormula])
        (φ := SimplePropFormula.toFormula propSelfFormula)
        (List.mem_singleton_self _)))

theorem semilocalTruth_toFormula_topConjTop :
    SimplePropFormula.semilocalTruth model emptyEnv topConjTop =
      SemilocalModel.formulaTruth model emptyEnv (SimplePropFormula.toFormula topConjTop) := by
  exact SimplePropFormula.semilocalTruth_toFormula
    (M := model) (ρ := emptyEnv) (φ := topConjTop)

theorem semilocalTruth_topConjTop :
    SimplePropFormula.semilocalTruth model emptyEnv topConjTop = ⊤ := by
  simp [topConjTop]

theorem semilocalTruth_topConjTop_of_derivable :
    SimplePropFormula.semilocalTruth model emptyEnv topConjTop = ⊤ := by
  exact SimplePropFormula.semilocalTruth_of_closed_derivable
    (M := model) (φ := topConjTop) derivable_topConjTop emptyEnv emptyEnv_isGlobal

theorem semilocalTruth_propSelfImp (p : Prop) :
    SimplePropFormula.semilocalTruth model (propEnv p) propSelfImp = (p → p) := by
  simp [propSelfImp, propSelfFormula, propEnv,
    SemilocalModel.formulaTruth, SemilocalModel.eval, model]

theorem semilocalTruth_propSelfImp_top (p : Prop) :
    SimplePropFormula.semilocalTruth model (propEnv p) propSelfImp = ⊤ := by
  have htop :
      (⊤ : model.Omega) ≤
        SimplePropFormula.semilocalTruth model (propEnv p) propSelfImp := by
    simpa [SemilocalModel.antecedentTruth] using
      (SimplePropFormula.semilocalTruth_sound_of_translated
        (M := model) (Δ := []) (φ := propSelfImp)
        derivable_propSelfImp (propEnv p) (propEnv_isGlobal p))
  exact le_antisymm le_top htop

theorem semilocalTruth_subst_propTail (a : Carrier atomTy) (p : Prop) :
    SimplePropFormula.semilocalTruth model (atomPropEnv a p)
        (SimplePropFormula.subst propTailSubst propSelfFormula) = p := by
  apply propext
  simp [propTailSubst, propSelfFormula,
    SemilocalModel.formulaTruth, model]
  change p ↔ p
  rfl

theorem semilocalTruth_bot_false :
    ¬ SimplePropFormula.semilocalTruth model emptyEnv
        (.bot : SimplePropFormula BaseSort Const []) := by
  simp [SimplePropFormula.semilocalTruth]
  intro h
  exact h

end AwodeyButzPropositionalModelBridgeRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
