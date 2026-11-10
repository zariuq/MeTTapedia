import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLBodySyntax

/-! # Independent typed body of the store operation

The expected syntax is authored independently and typed by the existing
named elaborator. The loaded definition is compared with this body in its
separate receiver module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

abbrev termsType : HOL.Ty AtomicTy := .arr objectType (.arr termType .prop)
abbrev predicateType : HOL.Ty AtomicTy := .arr termsType (.arr objectType (.arr storeType .prop))

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("terms", termsType), ("a", objectType), ("store", storeType)]
    (all "x" termType (all "y" termType
      (implication (apps (varTerm "store") [varTerm "x", varTerm "y"])
        (conjunction (apps (varTerm "terms") [varTerm "a", varTerm "x"])
          (apps (varTerm "terms") [varTerm "a", varTerm "y"])))))

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (terms : HOL.Ty.denote model.Carrier termsType) (a : HOL.Ty.denote model.Carrier objectType)
    (store : HOL.Ty.denote model.Carrier storeType) :
    model.denote body (fun index => nomatch index) terms a store =
      ULift.up (∀ x y, (store x y).down → (terms a x).down ∧ (terms a y).down) := by
  simp [body, checkClosed, sourceBody, lambdas, all, implication, conjunction, apps, constant, varTerm,
    signature, HOL.NamedElaboration.check, HOL.NamedElaboration.infer,
    HOL.NamedElaboration.expectType]
  have allTerms : model.constDen (Symbols.universal termType) =
      (fun predicate => ULift.up (∀ value, model.adm termType value → (predicate value).down)) :=
    funext (booleans.universal termType)
  change model.constDen (Symbols.universal termType) (fun x =>
    model.constDen (Symbols.universal termType) (fun y =>
      model.constDen Symbols.implication (store x y)
        (model.constDen Symbols.conjunction (terms a x) (terms a y)))) = _
  rw [allTerms]
  simp only [booleans.implication, booleans.conjunction]
  apply ULift.ext
  apply propext
  constructor
  · intro holds x y
    exact holds x (full _ _) y (full _ _)
  · intro holds x _ y _
    exact holds x y

#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreBody
