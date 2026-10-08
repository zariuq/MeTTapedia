import Mettapedia.SetTheory.Profiles.CommonCoreLogicalCompilation
import Mettapedia.SetTheory.Profiles.CommonCoreClassicalCollection

/-!
# Typed schema requests for native common-set logical compilation

Each request contains an authored first-order body at its actual variable
bound. Bounded Separation has a separate bounded syntax; neither Collection
schema is substituted for it. The closed compiled sentences are validated in
the concrete well-founded and hyperset models. Strong Collection retains the
host choice dependency of those ordinary-existence models. These results do
not assert a C parser or proof-checker correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreNativeSchemas

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open ContextualMaterialSetTheory
open GraphBoundedFormulaRealization (BoundedFormula toFormula)
open GraphRealizedSetTheory (subsetCollectionAxiom)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (WireTerm)
open CommonCoreLogicalCompilation

universe u

inductive Kind where
  | boundedSeparation
  | strongCollection
  | subsetCollection
deriving DecidableEq, Repr

def Kind.spelling : Kind → String
  | .boundedSeparation => "boundedSeparation"
  | .strongCollection => "strongCollection"
  | .subsetCollection => "subsetCollection"

/-- The parameter count excludes the schema's distinguished variables. -/
inductive Request (parameters : Nat) where
  | boundedSeparation (body : BoundedFormula (parameters+1))
  | strongCollection (body : Formula (parameters+2))
  | subsetCollection (body : Formula (parameters+3))

def Request.kind {parameters : Nat} : Request parameters → Kind
  | .boundedSeparation _ => .boundedSeparation
  | .strongCollection _ => .strongCollection
  | .subsetCollection _ => .subsetCollection

def Request.variableCount {parameters : Nat} (request : Request parameters) : Nat :=
  match request.kind with
  | .boundedSeparation => parameters+1
  | .strongCollection => parameters+2
  | .subsetCollection => parameters+3

/-- The body is serialized before the schema binders and universal closure
are introduced. Bounded and unbounded quantifiers have different tags. -/
def Request.source {parameters : Nat} : Request parameters → WireTerm
  | .boundedSeparation body => CommonCoreSyntax.encodeBounded body
  | .strongCollection body => CommonCoreSyntax.encodeFormula body
  | .subsetCollection body => CommonCoreSyntax.encodeFormula body

def Request.formula {parameters : Nat} : Request parameters → Formula parameters
  | .boundedSeparation body => separationAxiom (toFormula body)
  | .strongCollection body => strongCollectionAxiom body
  | .subsetCollection body => subsetCollectionAxiom body

def Request.sentence {parameters : Nat} (request : Request parameters) : Formula 0 :=
  close parameters request.formula

def Request.native {parameters : Nat} (request : Request parameters) : WireTerm :=
  encodeSentence request.sentence

/-- The schema-kind distinction is retained in the independent adoption
calculus; Collection is an extension of its weaker core. -/
def Request.adopted {parameters : Nat} (request : Request parameters) :
    CommonCore.Extension request.formula :=
  match request with
  | .boundedSeparation body => .core (.boundedSeparation body)
  | .strongCollection body => .strongCollection body
  | .subsetCollection body => .subsetCollection body

def boundedSeparationCore {parameters : Nat}
    (body : BoundedFormula (parameters+1)) :
    CommonCore.Axiom (Request.formula (.boundedSeparation body)) :=
  .boundedSeparation body

theorem wellFounded_strongCollection_compiled {parameters : Nat}
    (body : Formula (parameters+2)) :
    evaluate (fun child parent : ZFSet.{u} => child ∈ parent)
      (compile (close parameters (strongCollectionAxiom body)) 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr
    (close_valid _ _ _ (CommonCoreClassicalCollection.wellFounded_strongCollection_valid body)
      Fin.elim0)

theorem hyperset_strongCollection_compiled {parameters : Nat}
    (body : Formula (parameters+2)) :
    evaluate (fun child parent : HSet.{u} => child ∈ parent)
      (compile (close parameters (strongCollectionAxiom body)) 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr
    (close_valid _ _ _ (CommonCoreClassicalCollection.hyperset_strongCollection_valid body)
      Fin.elim0)

theorem wellFounded_subsetCollection_compiled {parameters : Nat}
    (body : Formula (parameters+3)) :
    evaluate (fun child parent : ZFSet.{u} => child ∈ parent)
      (compile (close parameters (subsetCollectionAxiom body)) 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr
    (close_valid _ _ _ (CommonCoreClassicalCollection.wellFounded_subsetCollection_valid body)
      Fin.elim0)

theorem hyperset_subsetCollection_compiled {parameters : Nat}
    (body : Formula (parameters+3)) :
    evaluate (fun child parent : HSet.{u} => child ∈ parent)
      (compile (close parameters (subsetCollectionAxiom body)) 0) Fin.elim0 Fin.elim0 :=
  (evaluate_compile _ _ _ _ _).mpr
    (close_valid _ _ _ (CommonCoreClassicalCollection.hyperset_subsetCollection_valid body)
      Fin.elim0)

theorem wellFounded_request_compiled {parameters : Nat} (request : Request parameters) :
    evaluate (fun child parent : ZFSet.{u} => child ∈ parent)
      (compile request.sentence 0) Fin.elim0 Fin.elim0 :=
  match request with
  | .boundedSeparation body => wellFounded_compiled (.boundedSeparation body)
  | .strongCollection body => wellFounded_strongCollection_compiled body
  | .subsetCollection body => wellFounded_subsetCollection_compiled body

theorem hyperset_request_compiled {parameters : Nat} (request : Request parameters) :
    evaluate (fun child parent : HSet.{u} => child ∈ parent)
      (compile request.sentence 0) Fin.elim0 Fin.elim0 :=
  match request with
  | .boundedSeparation body => hyperset_compiled (.boundedSeparation body)
  | .strongCollection body => hyperset_strongCollection_compiled body
  | .subsetCollection body => hyperset_subsetCollection_compiled body

end Mettapedia.SetTheory.Profiles.CommonCoreNativeSchemas
