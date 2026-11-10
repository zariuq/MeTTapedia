import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedModels

/-! # Independent typed body of optional knowledge exactness

The reverse solution implication quantifies over all valid future morphisms.
It is separate from refinement, consistency and the occurrence update.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLExactBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

abbrev predicateType : HOL.Ty AtomicTy := .arr homType (.arr equalType (.arr actionType
  (.arr HOLFramesBody.compositionType (.arr objectType (.arr objectType
    (.arr mapType (.arr storeType (.arr storeType .prop))))))))

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("hom", homType), ("eq", equalType), ("act", actionType),
    ("comp", HOLFramesBody.compositionType), ("m", objectType), ("b", objectType),
    ("settle", mapType), ("information", storeType), ("next", storeType)]
    (all "c" objectType (all "sigma" mapType
      (implication
        (conjunction (HOLFramesBody.call "hom" ["b", "c", "sigma"])
          (apps (constant HOLLoadedModels.symbol)
            [varTerm "hom", varTerm "eq", varTerm "act", varTerm "m", varTerm "c",
              HOLFramesBody.call "comp" ["sigma", "settle"], varTerm "information"]))
        (apps (constant HOLLoadedModels.symbol)
          [varTerm "hom", varTerm "eq", varTerm "act", varTerm "b", varTerm "c",
            varTerm "sigma", varTerm "next"]))))

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType)
    (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier HOLFramesBody.compositionType)
    (m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType) :
    model.denote body (fun index => nomatch index) hom equal act comp m b settle information next =
      ULift.up (∀ c sigma, (hom b c sigma).down ∧
        (model.constDen HOLLoadedModels.symbol hom equal act m c (comp sigma settle) information).down →
        (model.constDen HOLLoadedModels.symbol hom equal act b c sigma next).down) := by
  simp (config := { maxSteps := 1000000 }) [body, checkClosed, sourceBody, HOLFramesBody.call,
    lambdas, all, implication, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote,
    HOL.PreModel.denote, HOL.PreModel.extend]
  have allObjects : model.constDen (Symbols.universal objectType) =
      (fun predicate => ULift.up (∀ value, model.adm objectType value → (predicate value).down)) :=
    funext (booleans.universal objectType)
  have allMaps : model.constDen (Symbols.universal mapType) =
      (fun predicate => ULift.up (∀ value, model.adm mapType value → (predicate value).down)) :=
    funext (booleans.universal mapType)
  rw [allObjects, allMaps]
  simp only [booleans.conjunction, booleans.implication]
  apply ULift.ext
  apply propext
  constructor
  · intro holds c sigma valid solves
    exact holds c (full _ _) sigma (full _ _) ⟨valid, solves⟩
  · intro holds c _ sigma _ valid
    exact holds c sigma valid.1 valid.2

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLExactBody
