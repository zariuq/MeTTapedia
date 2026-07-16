import Mettapedia.Languages.Metamath.MMLean4Bridge

/-!
# Canonical semantic views of `mm-lean4` source databases

This module contains only the order-independent semantic projection shared by
source-admission clients.  Concrete syntax order, source spans, and proof
payloads remain the responsibility of the grammar-derived source ledger.
-/

namespace Mettapedia.Languages.Metamath.MMLean4SemanticView

/-- A decidable, order-independent view of one `mm-lean4` database object. -/
inductive RuntimeObjectView where
  | constant (name : String)
  | variable (name : String)
  | hypothesis (essential : Bool) (formula : List Metamath.Verify.Sym)
      (label : String)
  | assertion (formula : List Metamath.Verify.Sym)
      (distinctVariables : List (String × String))
      (hypotheses : List String) (label : String)
deriving Repr, DecidableEq

def runtimeObjectView : Metamath.Verify.Object → RuntimeObjectView
  | .const name => .constant name
  | .var name => .variable name
  | .hyp essential formula label =>
      .hypothesis essential formula.toList label
  | .assert formula frame label =>
      .assertion formula.toList
        (frame.dj.toList.map fun pair => (pair.1, pair.2))
        frame.hyps.toList label

def sortedRuntimeObjects (database : Metamath.Verify.DB) :
    List (String × RuntimeObjectView) :=
  (database.objects.toList.mergeSort fun left right => left.1 < right.1).map
    fun entry => (entry.1, runtimeObjectView entry.2)

structure SemanticDatabaseView where
  finalDistinctVariables : List (String × String)
  finalHypotheses : List String
  objects : List (String × RuntimeObjectView)
deriving Repr, DecidableEq

def semanticDatabaseView
    (database : Metamath.Verify.DB) : SemanticDatabaseView :=
  { finalDistinctVariables :=
      database.frame.dj.toList.map fun pair => (pair.1, pair.2)
    finalHypotheses := database.frame.hyps.toList
    objects := sortedRuntimeObjects database }

def readerAccepted (database : Metamath.Verify.DB) : Bool :=
  database.error?.isNone && database.scopes.isEmpty

def semanticDatabasesAgree
    (left right : Metamath.Verify.DB) : Bool :=
  semanticDatabaseView left == semanticDatabaseView right

def ReaderAgreement (database : Metamath.Verify.DB) : Prop :=
  database.error?.isNone = true ∧ database.scopes.isEmpty = true

theorem readerAccepted_sound {database : Metamath.Verify.DB}
    (hAccepted : readerAccepted database = true) :
    ReaderAgreement database := by
  simpa [readerAccepted, ReaderAgreement, Bool.and_eq_true] using hAccepted

theorem semanticDatabasesAgree_sound
    {left right : Metamath.Verify.DB}
    (hAgreement : semanticDatabasesAgree left right = true) :
    semanticDatabaseView left = semanticDatabaseView right := by
  simpa [semanticDatabasesAgree] using hAgreement

end Mettapedia.Languages.Metamath.MMLean4SemanticView
