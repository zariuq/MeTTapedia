import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedFire
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedModels

/-! # Independent typed body of semantic effects

Both knowledge clauses are solution implications. Neither literal store
transport, exactness nor a guard-admission condition is inserted into this
body. The read selection remains a separate supplied component.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticEffectBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLBodySyntax HOLOccurrenceCoding
open StandardTheoryInterpretation.Interpretation

def parameters : List (String × HOL.Ty AtomicTy) :=
  [("terms", HOLStoreBody.termsType), ("hom", homType), ("eq", equalType), ("act", actionType),
   ("comp", HOLFramesBody.compositionType), ("a", objectType), ("m", objectType), ("b", objectType),
   ("extension", mapType), ("settle", mapType), ("old", storeType), ("information", storeType), ("next", storeType),
   ("present", setType), ("taken", setType), ("read", setType), ("made", setType), ("after", setType)]

abbrev predicateType : HOL.Ty AtomicTy :=
  .arr HOLStoreBody.termsType (.arr homType (.arr equalType (.arr actionType (.arr HOLFramesBody.compositionType (.arr objectType (.arr objectType (.arr objectType (.arr mapType (.arr mapType (.arr storeType (.arr storeType (.arr storeType (.arr setType (.arr setType (.arr setType (.arr setType (.arr setType (.prop))))))))))))))))))

def modelsCall (source target : String) (map : HOLBodySyntax.Syntax) (store : String) : HOLBodySyntax.Syntax :=
  apps (constant HOLLoadedModels.symbol)
    [varTerm "hom", varTerm "eq", varTerm "act", varTerm source, varTerm target, map, varTerm store]

def storeCall (frame store : String) : HOLBodySyntax.Syntax :=
  apps (constant HOLLoadedStore.symbol) [varTerm "terms", varTerm frame, varTerm store]

def sourceBody : HOLBodySyntax.Syntax := lambdas parameters (HOLFramesBody.conjunctions [
  storeCall "a" "old", storeCall "m" "information", storeCall "b" "next",
  HOLFramesBody.call "hom" ["a", "m", "extension"], HOLFramesBody.call "hom" ["m", "b", "settle"],
  all "c" objectType (all "sigma" mapType
    (implication (modelsCall "m" "c" (varTerm "sigma") "information")
      (modelsCall "a" "c" (HOLFramesBody.call "comp" ["sigma", "extension"]) "old"))),
  all "c" objectType (all "sigma" mapType
    (implication (modelsCall "b" "c" (varTerm "sigma") "next")
      (modelsCall "m" "c" (HOLFramesBody.call "comp" ["sigma", "settle"]) "information"))),
  all "occ" occurrenceType (.equal (HOLFramesBody.call "after" ["occ"])
    (apps (constant HOLLoadedFire.symbol) [varTerm "present", varTerm "taken", varTerm "made", varTerm "occ"]))])

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

def Contract (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier HOLFramesBody.compositionType)
    (a m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (extension settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (old information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType)
    (present taken made after : HOL.Ty.denote.{0,w+1} model.Carrier setType) : Prop :=
  (model.constDen HOLLoadedStore.symbol terms a old).down ∧
  (model.constDen HOLLoadedStore.symbol terms m information).down ∧
  (model.constDen HOLLoadedStore.symbol terms b next).down ∧
  (hom a m extension).down ∧ (hom m b settle).down ∧
  (∀ c sigma, (model.constDen HOLLoadedModels.symbol hom equal act m c sigma information).down →
    (model.constDen HOLLoadedModels.symbol hom equal act a c (comp sigma extension) old).down) ∧
  (∀ c sigma, (model.constDen HOLLoadedModels.symbol hom equal act b c sigma next).down →
    (model.constDen HOLLoadedModels.symbol hom equal act m c (comp sigma settle) information).down) ∧
  (∀ occ, (after occ).down ↔ (model.constDen HOLLoadedFire.symbol present taken made occ).down)

theorem denote_body (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier HOLFramesBody.compositionType)
    (a m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (extension settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (old information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType)
    (present taken read made after : HOL.Ty.denote.{0,w+1} model.Carrier setType) :
    model.denote body (fun index => nomatch index) terms hom equal act comp a m b extension settle
      old information next present taken read made after =
      ULift.up (Contract model terms hom equal act comp a m b extension settle old information next present taken made after) := by
  simp (config := { maxSteps := 2000000 }) [body, checkClosed, sourceBody, parameters, modelsCall, storeCall,
    HOLFramesBody.conjunctions, HOLFramesBody.call, lambdas, all, implication, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  have allObjects : model.constDen (Symbols.universal objectType) =
      (fun predicate => ULift.up (∀ value, model.adm objectType value → (predicate value).down)) :=
    funext (booleans.universal objectType)
  have allMaps : model.constDen (Symbols.universal mapType) =
      (fun predicate => ULift.up (∀ value, model.adm mapType value → (predicate value).down)) :=
    funext (booleans.universal mapType)
  have allOccurrences : model.constDen (Symbols.universal occurrenceType) =
      (fun predicate => ULift.up (∀ value, model.adm occurrenceType value → (predicate value).down)) :=
    funext (booleans.universal occurrenceType)
  have objectsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier objectType) : model.adm objectType value := full _ _
  have mapsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier mapType) : model.adm mapType value := full _ _
  have occurrencesAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier occurrenceType) : model.adm occurrenceType value := full _ _
  have propositionsEqual (p q : HOL.Ty.denote.{0,w+1} model.Carrier .prop) : model.Eqv .prop p q ↔ (p.down ↔ q.down) := Iff.rfl
  simp only [allObjects, allMaps, allOccurrences, booleans.conjunction, booleans.implication,
    objectsAdmitted, mapsAdmitted, occurrencesAdmitted, propositionsEqual, forall_true_left]
  rfl

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticEffectBody
