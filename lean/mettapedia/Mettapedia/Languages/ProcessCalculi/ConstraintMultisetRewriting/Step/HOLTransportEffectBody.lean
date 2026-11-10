import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticEffectBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedMapStore

/-! # The stronger transported-equation profile

The historical tc_prepared_effect definition requires inclusion of transported
source equations and equality with the settled equation predicate. Predicate
equality forgets duplicate list entries; it is not equality of the original
Lean lists. This profile is kept separate from general semantic refinement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTransportEffectBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLBodySyntax HOLOccurrenceCoding
open StandardTheoryInterpretation.Interpretation

def parameters : List (String × HOL.Ty AtomicTy) :=
  [("terms", HOLStoreBody.termsType), ("hom", homType), ("act", actionType),
   ("a", objectType), ("m", objectType), ("b", objectType), ("extension", mapType), ("settle", mapType),
   ("old", storeType), ("information", storeType), ("next", storeType),
   ("present", setType), ("taken", setType), ("read", setType), ("made", setType), ("after", setType)]

abbrev predicateType : HOL.Ty AtomicTy :=
  .arr HOLStoreBody.termsType (.arr homType (.arr actionType
    (.arr objectType (.arr objectType (.arr objectType (.arr mapType (.arr mapType
      (.arr storeType (.arr storeType (.arr storeType
        (.arr setType (.arr setType (.arr setType (.arr setType (.arr setType .prop)))))))))))))))

def sourceBody : HOLBodySyntax.Syntax := lambdas parameters (HOLFramesBody.conjunctions [
  HOLSemanticEffectBody.storeCall "a" "old", HOLSemanticEffectBody.storeCall "m" "information",
  HOLFramesBody.call "hom" ["a", "m", "extension"], HOLFramesBody.call "hom" ["m", "b", "settle"],
  all "x" termType (all "y" termType
    (implication (HOLFramesBody.call "old" ["x", "y"])
      (apps (varTerm "information") [HOLFramesBody.call "act" ["extension", "x"],
        HOLFramesBody.call "act" ["extension", "y"]]))),
  all "x" termType (all "y" termType
    (.equal (HOLFramesBody.call "next" ["x", "y"])
      (apps (constant HOLLoadedMapStore.symbol)
        [varTerm "act", varTerm "settle", varTerm "information", varTerm "x", varTerm "y"]))),
  all "occ" occurrenceType (.equal (HOLFramesBody.call "after" ["occ"])
    (apps (constant HOLLoadedFire.symbol) [varTerm "present", varTerm "taken", varTerm "made", varTerm "occ"]))])

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

def Contract (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (a m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (extension settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (old information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType)
    (present taken made after : HOL.Ty.denote.{0,w+1} model.Carrier setType) : Prop :=
  (model.constDen HOLLoadedStore.symbol terms a old).down ∧
  (model.constDen HOLLoadedStore.symbol terms m information).down ∧
  (hom a m extension).down ∧ (hom m b settle).down ∧
  (∀ x y, (old x y).down → (information (act extension x) (act extension y)).down) ∧
  (∀ x y, (next x y).down ↔ (model.constDen HOLLoadedMapStore.symbol act settle information x y).down) ∧
  (∀ occ, (after occ).down ↔ (model.constDen HOLLoadedFire.symbol present taken made occ).down)

theorem denote_body (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (a m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (extension settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (old information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType)
    (present taken read made after : HOL.Ty.denote.{0,w+1} model.Carrier setType) :
    model.denote body (fun index => nomatch index) terms hom act a m b extension settle
      old information next present taken read made after =
      ULift.up (Contract model terms hom act a m b extension settle old information next present taken made after) := by
  simp (config := { maxSteps := 2000000 }) [body, checkClosed, sourceBody, parameters, HOLSemanticEffectBody.storeCall,
    HOLFramesBody.conjunctions, HOLFramesBody.call, lambdas, all, implication, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  have allTerms : model.constDen (Symbols.universal termType) =
      (fun predicate => ULift.up (∀ value, model.adm termType value → (predicate value).down)) :=
    funext (booleans.universal termType)
  have allOccurrences : model.constDen (Symbols.universal occurrenceType) =
      (fun predicate => ULift.up (∀ value, model.adm occurrenceType value → (predicate value).down)) :=
    funext (booleans.universal occurrenceType)
  have termsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier termType) : model.adm termType value := full _ _
  have occurrencesAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier occurrenceType) : model.adm occurrenceType value := full _ _
  have propositionsEqual (p q : HOL.Ty.denote.{0,w+1} model.Carrier .prop) : model.Eqv .prop p q ↔ (p.down ↔ q.down) := Iff.rfl
  simp only [allTerms, allOccurrences, booleans.conjunction, booleans.implication,
    termsAdmitted, occurrencesAdmitted, propositionsEqual, forall_true_left]
  rfl

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTransportEffectBody
