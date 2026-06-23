import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzQuantifiedFragment
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.LowerBoundExtensionRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

namespace AwodeyButzQuantifiedFragmentRegression

open LowerBoundExtensionRegression

local notation "atomSimpleTy" => (SimpleTy.base BaseSort.atom)

def forallPropSelfImp : SimpleQuantifiedFormula BaseSort Const [] :=
  .all .prop
    (.impl
      (.atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop)))
      (.atom (.var (SimpleVar.vz : SimpleVar BaseSort [.prop] .prop))))

def existsAtomBot : SimpleQuantifiedFormula BaseSort Const [] :=
  .ex atomSimpleTy .bot

def emptyEnv : SemilocalModel.Env model (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))
  | _, v => nomatch v

theorem derivable_forallPropSelfImp :
    Derivable (Base := BaseSort) (Const := Const)
      ([] : List (Formula Const (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))))
      (SimpleQuantifiedFormula.toFormula forallPropSelfImp) := by
  simp [forallPropSelfImp, SimpleQuantifiedFormula.toFormula]
  apply Derivable.allR
  apply Derivable.impR
  exact Derivable.ax (List.mem_singleton_self _)

theorem semilocalTruth_forallPropSelfImp_model :
    SimpleQuantifiedFormula.semilocalTruth model emptyEnv forallPropSelfImp = ⊤ := by
  rw [SimpleQuantifiedFormula.semilocalTruth_toFormula]
  simp [forallPropSelfImp, SimpleQuantifiedFormula.toFormula, model]
  trivial

theorem globalTruth_forallPropSelfImp
    (M : GlobalModel BaseSort Const)
    (ρ : SemilocalModel.Env M.toSemilocalModel
      (SimpleTy.toCtx ([] : List (SimpleTy BaseSort)))) :
    SimpleQuantifiedFormula.semilocalTruth M.toSemilocalModel ρ forallPropSelfImp = ⊤ := by
  exact SimpleQuantifiedFormula.globalTruth_of_closed_derivable
    (M := M) (φ := forallPropSelfImp) derivable_forallPropSelfImp ρ

theorem semilocalTruth_existsAtomBot_false :
    ¬ SimpleQuantifiedFormula.semilocalTruth model emptyEnv existsAtomBot := by
  rw [SimpleQuantifiedFormula.semilocalTruth_toFormula]
  simp [existsAtomBot, SimpleQuantifiedFormula.toFormula, model]

theorem existsAtomBot_ne_forallPropSelfImp :
    existsAtomBot ≠ forallPropSelfImp := by
  intro h
  cases h

end AwodeyButzQuantifiedFragmentRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
