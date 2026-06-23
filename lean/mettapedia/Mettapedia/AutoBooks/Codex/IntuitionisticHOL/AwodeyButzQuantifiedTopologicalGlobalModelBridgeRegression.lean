import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzQuantifiedTopologicalGlobalModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open SimpleQuantifiedTopologicalGlobalModelBridge

namespace AwodeyButzQuantifiedTopologicalGlobalModelBridgeRegression

inductive BaseSort where
  | atom
  deriving DecidableEq, Repr

abbrev Const : Ty BaseSort → Type := fun _ => Empty

def propVar0 : SimpleQuantifiedFormula BaseSort Const [.prop] :=
  .atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop))

def forallPropSelfImp : SimpleQuantifiedFormula BaseSort Const [] :=
  .all .prop
    (.impl
      (.atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop)))
      (.atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop))))

def forallPropVar : SimpleQuantifiedFormula BaseSort Const [] :=
  .all .prop
    (.atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop)))

theorem derivable_propVar0 :
    Derivable (Base := BaseSort) (Const := Const)
      [SimpleQuantifiedFormula.toFormula propVar0]
      (SimpleQuantifiedFormula.toFormula propVar0) := by
  exact Derivable.ax (List.mem_singleton_self _)

theorem derivable_forallPropSelfImp :
    Derivable (Base := BaseSort) (Const := Const) []
      (SimpleQuantifiedFormula.toFormula forallPropSelfImp) := by
  apply Derivable.allR
  apply Derivable.impR
  exact Derivable.ax List.mem_cons_self

theorem truthValid_propVar0 (M : GlobalModel BaseSort Const) :
    simpleInterp.SimpleQuantifiedFormula.TruthValidSequent M [propVar0] propVar0 := by
  exact
    simpleInterp.SimpleQuantifiedFormula.truthValidSequent_of_translated
      (M := M) (Δ := [propVar0]) (φ := propVar0) derivable_propVar0

theorem truthValid_forallPropSelfImp (M : GlobalModel BaseSort Const) :
    simpleInterp.SimpleQuantifiedFormula.TruthValidSequent M [] forallPropSelfImp := by
  exact
    simpleInterp.SimpleQuantifiedFormula.truthValidSequent_of_closed_derivable
      (M := M) (φ := forallPropSelfImp) derivable_forallPropSelfImp

/-- Small global model with honest quantification over propositions. -/
def Carrier : Ty BaseSort → Type
  | .prop => Prop
  | .base _ => PUnit
  | .arr σ τ => Carrier σ → Carrier τ

def model : GlobalModel BaseSort Const where
  toApplicativeStructure :=
    { Carrier := Carrier
      const := by
        intro τ c
        cases c
      app := fun f x => f x
      lam := fun f => f
      beta := by
        intro σ τ f x
        rfl
      eta := by
        intro σ τ f
        rfl }
  Omega := Prop
  frame := inferInstance
  truth := fun p => p
  extent := fun {_} _ => True
  topP := True
  botP := False
  andP := And
  orP := Or
  impP := fun p q => p → q
  eqP := fun x y => x = y
  allP := fun f => ∀ x, f x
  exP := fun f => ∃ x, f x
  truth_top := rfl
  truth_bot := rfl
  truth_and := by
    intro p q
    rfl
  truth_or := by
    intro p q
    rfl
  truth_imp := by
    intro p q
    rfl
  truth_all := by
    intro σ f
    apply propext
    simp
  truth_ex := by
    intro σ f
    apply propext
    simp
  global := by
    intro τ x
    rfl

theorem truthEval_forallPropSelfImp_top :
    simpleInterp.SimpleQuantifiedFormula.truthEval model forallPropSelfImp () = ⊤ := by
  simpa [simpleInterp.SimpleQuantifiedFormula.truthEval] using
    (simpleInterp.SimpleQuantifiedFormula.truth_eval_of_closed_derivable
      (M := model) (φ := forallPropSelfImp) derivable_forallPropSelfImp)

theorem truthEval_forallPropVar_ne_top :
    simpleInterp.SimpleQuantifiedFormula.truthEval model forallPropVar () ≠ ⊤ := by
  intro htop
  rw [simpleInterp.SimpleQuantifiedFormula.truthEval_eq_formulaTruth
      (M := model) forallPropVar ()] at htop
  have hiff := by
    simpa [forallPropVar, SimpleQuantifiedFormula.toFormula,
      SemilocalModel.formulaTruth, SemilocalModel.eval, model] using htop
  have hfalse :=
    (hiff.mpr trivial) False
  simp [ApplicativeStructure.Env.extend, Carrier, SimpleTy.toTy] at hfalse

theorem not_derivable_forallPropVar :
    ¬ Derivable (Base := BaseSort) (Const := Const) []
      (SimpleQuantifiedFormula.toFormula forallPropVar) := by
  intro hder
  have hvalid :
      simpleInterp.SimpleQuantifiedFormula.TruthValidSequent model [] forallPropVar :=
    simpleInterp.SimpleQuantifiedFormula.truthValidSequent_of_closed_derivable
      (M := model) (φ := forallPropVar) hder
  have htop_le :
      (⊤ : model.Omega) ≤ simpleInterp.SimpleQuantifiedFormula.truthEval model forallPropVar () := by
    simpa [simpleInterp.SimpleQuantifiedFormula.truthAntecedent] using hvalid ()
  have htop :
      simpleInterp.SimpleQuantifiedFormula.truthEval model forallPropVar () = ⊤ :=
    le_antisymm le_top htop_le
  exact truthEval_forallPropVar_ne_top htop

end AwodeyButzQuantifiedTopologicalGlobalModelBridgeRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
