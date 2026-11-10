import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLStoreBody

/-! # Independent typed body of the indexed frame laws

The eleven clauses retain validity guards and action-level composition.
No identity or associativity equation is imposed on raw morphism values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

abbrev objectsType : HOL.Ty AtomicTy := .arr objectType .prop
abbrev identityType : HOL.Ty AtomicTy := .arr objectType mapType
abbrev compositionType : HOL.Ty AtomicTy := .arr mapType (.arr mapType mapType)
abbrev predicateType : HOL.Ty AtomicTy := .arr objectsType (.arr HOLStoreBody.termsType
  (.arr homType (.arr equalType (.arr actionType (.arr identityType (.arr compositionType .prop))))))

def call (name : String) (arguments : List String) : HOLBodySyntax.Syntax :=
  apps (varTerm name) (arguments.map varTerm)

def conjunctions : List HOLBodySyntax.Syntax → HOLBodySyntax.Syntax
  | [] => constant Symbols.truth
  | [term] => term
  | term :: rest => conjunction term (conjunctions rest)

def allMany (binders : List (String × HOL.Ty AtomicTy)) (term : HOLBodySyntax.Syntax) : HOLBodySyntax.Syntax :=
  binders.foldr (fun binder term => all binder.1 binder.2 term) term

def clauses : List HOLBodySyntax.Syntax := [
  allMany [("a", objectType), ("t", termType)]
    (implication (call "terms" ["a", "t"]) (call "objects" ["a"])),
  allMany [("a", objectType), ("b", objectType), ("f", mapType)]
    (implication (call "hom" ["a", "b", "f"])
      (conjunction (call "objects" ["a"]) (call "objects" ["b"]))),
  all "a" objectType (implication (call "objects" ["a"])
    (apps (varTerm "hom") [varTerm "a", varTerm "a", call "identity" ["a"]])),
  allMany [("a", objectType), ("b", objectType), ("c", objectType), ("f", mapType), ("g", mapType)]
    (implication (conjunction (call "hom" ["a", "b", "f"]) (call "hom" ["b", "c", "g"]))
      (apps (varTerm "hom") [varTerm "a", varTerm "c", call "comp" ["g", "f"]])),
  allMany [("a", objectType), ("b", objectType), ("f", mapType), ("t", termType)]
    (implication (conjunction (call "hom" ["a", "b", "f"]) (call "terms" ["a", "t"]))
      (apps (varTerm "terms") [varTerm "b", call "act" ["f", "t"]])),
  allMany [("a", objectType), ("t", termType)]
    (implication (call "terms" ["a", "t"])
      (.equal (apps (varTerm "act") [call "identity" ["a"], varTerm "t"]) (varTerm "t"))),
  allMany [("a", objectType), ("b", objectType), ("c", objectType), ("f", mapType), ("g", mapType), ("t", termType)]
    (implication (conjunctions [call "hom" ["a", "b", "f"], call "hom" ["b", "c", "g"], call "terms" ["a", "t"]])
      (.equal (apps (varTerm "act") [call "comp" ["g", "f"], varTerm "t"])
        (apps (varTerm "act") [varTerm "g", call "act" ["f", "t"]]))),
  allMany [("a", objectType), ("t", termType)]
    (implication (call "terms" ["a", "t"]) (call "eq" ["a", "t", "t"])),
  allMany [("a", objectType), ("x", termType), ("y", termType)]
    (implication (conjunctions [call "terms" ["a", "x"], call "terms" ["a", "y"], call "eq" ["a", "x", "y"]])
      (call "eq" ["a", "y", "x"])),
  allMany [("a", objectType), ("x", termType), ("y", termType), ("z", termType)]
    (implication (conjunctions [call "terms" ["a", "x"], call "terms" ["a", "y"], call "terms" ["a", "z"],
      call "eq" ["a", "x", "y"], call "eq" ["a", "y", "z"]]) (call "eq" ["a", "x", "z"])),
  allMany [("a", objectType), ("b", objectType), ("f", mapType), ("x", termType), ("y", termType)]
    (implication (conjunctions [call "hom" ["a", "b", "f"], call "terms" ["a", "x"],
      call "terms" ["a", "y"], call "eq" ["a", "x", "y"]])
      (apps (varTerm "eq") [varTerm "b", call "act" ["f", "x"], call "act" ["f", "y"]]))]

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("objects", objectsType), ("terms", HOLStoreBody.termsType), ("hom", homType),
    ("eq", equalType), ("act", actionType), ("identity", identityType), ("comp", compositionType)]
    (conjunctions clauses)

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

def Laws (objects : HOL.Ty.denote.{0,w+1} model.Carrier objectsType)
    (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType) (identity : HOL.Ty.denote.{0,w+1} model.Carrier identityType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier compositionType) : Prop :=
  (∀ a t, (terms a t).down → (objects a).down) ∧
  (∀ a b f, (hom a b f).down → (objects a).down ∧ (objects b).down) ∧
  (∀ a, (objects a).down → (hom a a (identity a)).down) ∧
  (∀ a b c f g, (hom a b f).down ∧ (hom b c g).down → (hom a c (comp g f)).down) ∧
  (∀ a b f t, (hom a b f).down ∧ (terms a t).down → (terms b (act f t)).down) ∧
  (∀ a t, (terms a t).down → act (identity a) t = t) ∧
  (∀ a b c f g t, (hom a b f).down ∧ (hom b c g).down ∧ (terms a t).down →
    act (comp g f) t = act g (act f t)) ∧
  (∀ a t, (terms a t).down → (equal a t t).down) ∧
  (∀ a x y, (terms a x).down ∧ (terms a y).down ∧ (equal a x y).down → (equal a y x).down) ∧
  (∀ a x y z, (terms a x).down ∧ (terms a y).down ∧ (terms a z).down ∧
    (equal a x y).down ∧ (equal a y z).down → (equal a x z).down) ∧
  (∀ a b f x y, (hom a b f).down ∧ (terms a x).down ∧ (terms a y).down ∧ (equal a x y).down →
    (equal b (act f x) (act f y)).down)

theorem denote_body (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (objects : HOL.Ty.denote.{0,w+1} model.Carrier objectsType)
    (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType) (identity : HOL.Ty.denote.{0,w+1} model.Carrier identityType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier compositionType) :
    model.denote body (fun index => nomatch index) objects terms hom equal act identity comp =
      ULift.up (Laws model objects terms hom equal act identity comp) := by
  simp (config := { maxSteps := 1000000 }) [body, checkClosed, sourceBody, clauses, call, allMany, conjunctions, lambdas, all,
    implication, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote,
    HOL.PreModel.denote, HOL.PreModel.extend]
  have allObjects : model.constDen (Symbols.universal objectType) =
      (fun predicate => ULift.up (∀ value, model.adm objectType value → (predicate value).down)) :=
    funext (booleans.universal objectType)
  have allTerms : model.constDen (Symbols.universal termType) =
      (fun predicate => ULift.up (∀ value, model.adm termType value → (predicate value).down)) :=
    funext (booleans.universal termType)
  have allMaps : model.constDen (Symbols.universal mapType) =
      (fun predicate => ULift.up (∀ value, model.adm mapType value → (predicate value).down)) :=
    funext (booleans.universal mapType)
  have objectsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier objectType) : model.adm objectType value := full _ _
  have termsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier termType) : model.adm termType value := full _ _
  have mapsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier mapType) : model.adm mapType value := full _ _
  have termsEqual (left right : HOL.Ty.denote.{0,w+1} model.Carrier termType) :
      model.Eqv termType left right ↔ left = right := model.eqv_iff_eq_of_fullDomains full _ _
  simp only [allObjects, allTerms, allMaps, booleans.conjunction, booleans.implication,
    objectsAdmitted, termsAdmitted, mapsAdmitted, termsEqual, forall_true_left]
  rfl

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesBody
