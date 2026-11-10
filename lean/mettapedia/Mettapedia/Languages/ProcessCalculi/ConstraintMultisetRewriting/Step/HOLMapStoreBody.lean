import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLBodySyntax

/-! # Independent typed body of the mapstore operation

The expected syntax is authored independently and typed by the existing
named elaborator. The loaded definition is compared with this body in its
separate receiver module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLMapStoreBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

abbrev predicateType : HOL.Ty AtomicTy :=
  .arr actionType (.arr mapType (.arr storeType (.arr termType (.arr termType .prop))))

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("act", actionType), ("e", mapType), ("store", storeType), ("u", termType), ("v", termType)]
    (existsTerm "x" termType (existsTerm "y" termType
      (conjunction (apps (varTerm "store") [varTerm "x", varTerm "y"])
        (conjunction (.equal (varTerm "u") (apps (varTerm "act") [varTerm "e", varTerm "x"]))
          (.equal (varTerm "v") (apps (varTerm "act") [varTerm "e", varTerm "y"]))))))

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (act : HOL.Ty.denote model.Carrier actionType) (map : HOL.Ty.denote model.Carrier mapType)
    (store : HOL.Ty.denote model.Carrier storeType) (left right : HOL.Ty.denote model.Carrier termType) :
    model.denote body (fun index => nomatch index) act map store left right =
      ULift.up (∃ x y, (store x y).down ∧ left = act map x ∧ right = act map y) := by
  simp [body, checkClosed, sourceBody, lambdas, existsTerm, conjunction, apps, constant, varTerm,
    signature, HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  have existsTerms : model.constDen (Symbols.existential termType) =
      (fun predicate => ULift.up (∃ value, model.adm termType value ∧ (predicate value).down)) :=
    funext (booleans.existential termType)
  change model.constDen (Symbols.existential termType) (fun x =>
    model.constDen (Symbols.existential termType) (fun y =>
      model.constDen Symbols.conjunction (store x y)
        (model.constDen Symbols.conjunction (ULift.up (model.Eqv termType left (act map x)))
          (ULift.up (model.Eqv termType right (act map y)))))) = _
  rw [existsTerms]
  simp only [booleans.conjunction]
  apply ULift.ext
  apply propext
  constructor
  · rintro ⟨x, _, y, _, member, first, second⟩
    exact ⟨x, y, member, (model.eqv_iff_eq_of_fullDomains full _ _).mp first,
      (model.eqv_iff_eq_of_fullDomains full _ _).mp second⟩
  · rintro ⟨x, y, member, first, second⟩
    exact ⟨x, full _ _, y, full _ _, member, (model.eqv_iff_eq_of_fullDomains full _ _).mpr first,
      (model.eqv_iff_eq_of_fullDomains full _ _).mpr second⟩

#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLMapStoreBody
