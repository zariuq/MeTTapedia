import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedBooleans
import Mettapedia.Languages.HOLLight.ExactFormulaReadback

/-! # Typed operational body for the loaded solution predicate

The target term is written independently using typed variables and the
source Boolean symbols. Exact source readback must match it against the
actual cached defining equation before its semantic meaning is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLModelsBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open StandardTheoryInterpretation.Interpretation

abbrev objectType : HOL.Ty AtomicTy := (Ty.var (Name.global "A")).toHOL
abbrev termType : HOL.Ty AtomicTy := (Ty.var (Name.global "T")).toHOL
abbrev mapType : HOL.Ty AtomicTy := (Ty.var (Name.global "H")).toHOL
abbrev homType : HOL.Ty AtomicTy := .arr objectType (.arr objectType (.arr mapType .prop))
abbrev equalType : HOL.Ty AtomicTy := .arr objectType (.arr termType (.arr termType .prop))
abbrev actionType : HOL.Ty AtomicTy := .arr mapType (.arr termType termType)
abbrev storeType : HOL.Ty AtomicTy := .arr termType (.arr termType .prop)
abbrev modelsType : HOL.Ty AtomicTy :=
  .arr homType (.arr equalType (.arr actionType (.arr objectType (.arr objectType (.arr mapType (.arr storeType .prop))))))

abbrev arguments : HOL.Ctx AtomicTy := [storeType, mapType, objectType, objectType, actionType, equalType, homType]

def homApplication : HOL.Term Symbol arguments .prop :=
  .app (.app (.app (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    (.var (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz))

def storeApplication : HOL.Term Symbol (termType :: termType :: arguments) .prop :=
  .app (.app (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz)

def equalityApplication : HOL.Term Symbol (termType :: termType :: arguments) .prop :=
  .app (.app (.app (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
      (.var (.vs (.vs (.vs (.vs .vz))))))
    (.app (.app (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
      (.var (.vs (.vs (.vs .vz))))) (.var (.vs .vz))))
    (.app (.app (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
      (.var (.vs (.vs (.vs .vz))))) (.var .vz))

def allEquations : HOL.Term Symbol arguments .prop :=
  .app (.const (Symbols.universal termType))
    (.lam (.app (.const (Symbols.universal termType))
      (.lam (.app (.app (.const Symbols.implication) storeApplication) equalityApplication))))

def body : HOL.ClosedTerm Symbol modelsType :=
  .lam (.lam (.lam (.lam (.lam (.lam (.lam
    (.app (.app (.const Symbols.conjunction) homApplication) allEquations)))))))

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (hom : HOL.Ty.denote model.Carrier homType) (equal : HOL.Ty.denote model.Carrier equalType)
    (act : HOL.Ty.denote model.Carrier actionType)
    (a b : HOL.Ty.denote model.Carrier objectType) (map : HOL.Ty.denote model.Carrier mapType)
    (store : HOL.Ty.denote model.Carrier storeType) :
    model.denote body (fun index => nomatch index) hom equal act a b map store =
      ULift.up ((hom a b map).down ∧ ∀ x y, (store x y).down → (equal b (act map x) (act map y)).down) := by
  have all : model.constDen (Symbols.universal termType) =
      (fun predicate => ULift.up (∀ value, model.adm termType value → (predicate value).down)) :=
    funext (booleans.universal termType)
  change model.constDen Symbols.conjunction (hom a b map)
    (model.constDen (Symbols.universal termType) (fun x =>
      model.constDen (Symbols.universal termType) (fun y =>
        model.constDen Symbols.implication (store x y) (equal b (act map x) (act map y))))) = _
  rw [booleans.conjunction, all]
  simp only [booleans.implication]
  apply ULift.ext
  apply propext
  constructor
  · rintro ⟨validMap, satisfies⟩
    exact ⟨validMap, fun x y => satisfies x (full _ _) y (full _ _)⟩
  · rintro ⟨validMap, satisfies⟩
    exact ⟨validMap, fun x _ y _ => satisfies x y⟩

#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLModelsBody
