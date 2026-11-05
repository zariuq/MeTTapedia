import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion

/-!
# Actual Atom extraction for a closed first-witness region

Relation names are data, not optimizer switches. The extractor recognizes
the source control operations and literal two-integer row pattern, retaining
the exact source Atom in its certificate. The source matcher's special cons
view is excluded. Other shapes remain ordinary source execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Dynamics ObservationQualified
open ClosedOnceQueryExecution

structure Description where
  relation : String
  formula : Int
  node : Int
  ordinary : relation ≠ "cons"

def Description.source (description : Description) : Atom :=
  expression description.relation description.formula description.node

def parse : Atom → Option Description
  | .expression [.symbol "once", .expression [.symbol "match", .symbol "&self",
      .expression [.symbol relation, .grounded (.int formula), .grounded (.int node)], .grounded (.bool true)]] =>
      if ordinary : relation ≠ "cons" then some ⟨relation, formula, node, ordinary⟩ else none
  | _ => none

theorem parse_exact (source : Atom) (description : Description) (parsed : parse source = some description) :
    description.source = source := by
  unfold parse at parsed
  split at parsed
  next relation formula node =>
    split at parsed
    · cases Option.some.inj parsed
      rfl
    · cases parsed
  next => cases parsed

structure Extracted (source : Atom) where
  description : Description
  exact : description.source = source

def extract (source : Atom) : Option (Extracted source) :=
  match parsed : parse source with
  | none => none
  | some description => some ⟨description, parse_exact source description parsed⟩

def Extracted.region {source : Atom} (compiled : Extracted source) {Regime : Type}
    (regime : Regime) (program : SpaceSemantics.Program) (probeBudget : Nat) :
    CertifiedRegion (ClosedOnceQueryRegion.sourceBoundary program source) Regime := by
  rw [← compiled.exact]
  exact ClosedOnceQueryRegion.region regime program compiled.description.relation compiled.description.formula
    compiled.description.node compiled.description.ordinary probeBudget

def classify {Regime : Type} (regime : Regime) (observation : PureCallExtraction.Observation)
    (program : SpaceSemantics.Program) (source : Atom) (probeBudget : Nat) :
    Option (CertifiedRegion (ClosedOnceQueryRegion.sourceBoundary program source) Regime) :=
  match observation with
  | .exactPage => none
  | .completedResult => (extract source).map fun compiled => compiled.region regime program probeBudget

theorem exact_page_refuses {Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (source : Atom) (probeBudget : Nat) : classify regime .exactPage program source probeBudget = none := rfl

theorem unsupported_refuses {Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (source : Atom) (probeBudget : Nat) (unsupported : parse source = none) :
    classify regime .completedResult program source probeBudget = none := by
  have absent : extract source = none := by
    unfold extract
    split
    · rfl
    · rename_i description found
      rw [unsupported] at found
      cases found
  change (extract source).map (fun compiled => compiled.region regime program probeBudget) = none
  rw [absent]
  rfl

theorem execute_preserves_actual_source {source : Atom} (compiled : Extracted source) {Regime : Type}
    (regime : Regime) (program : SpaceSemantics.Program) (probeBudget : Nat) (input : ClosedOnceQueryRegion.Input) :
    (compiled.region regime program probeBudget).execute input =
      (ClosedOnceQueryRegion.sourceBoundary program source).reference input :=
  congrFun (CertifiedRegion.execute_eq_reference _) input

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExtraction
