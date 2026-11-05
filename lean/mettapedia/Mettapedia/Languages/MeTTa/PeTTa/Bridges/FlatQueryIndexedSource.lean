import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQuerySourceExecution
import Mettapedia.GSLT.Dynamics.ConjunctiveBindingObservation

/-!
# Indexed counting from actual flat PeTTa conjunctions

Preparation decodes patterns and one captured snapshot, constructs the value
domain from inputs, checks variable coverage, and builds reusable indexes.
It does not enumerate source answers. Execution counts binding keys with
their occurrence weights; the occurrence Cartesian product is not built.

The certificate reaches the existing PeTTa evaluator's nested match/collapse/
size expression. It is parameterized by a represented caller and remains
valid only for the captured snapshot. Exact evaluator pages, open stored
terms and unsupported scalar values are outside this route. Index preparation
and validation costs remain separate from the completed-result theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryIndexedSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveBindingDomain ConjunctiveBindingEnumeration PreparedJoinRegions
open FlatQueryRowCodec FlatQueryConjunctionCompilation FlatQuerySourceExecution
open Eval SpaceSemantics
open ObservationQualified

variable {Value : Type} [LinearOrder Value]

structure Prepared (codec : Codec Value) (names : Inventory String) (rows patterns : List Atom)
    (environment : DenseEnvironment names Value) where
  legs : List (Leg codec names rows)
  accepted : compile codec names rows patterns = some legs
  covered : Covered environment (factors legs)
  indices : List (StoredFactor names.keys.length Value Nat)
  originals : sources indices = factors legs
  domain : Domain (inputDomain environment (factors legs))

def prepare (codec : Codec Value) (names : Inventory String) (rows patterns : List Atom)
    (environment : DenseEnvironment names Value) (outside : Value) :
    Option (Prepared codec names rows patterns environment) := do
  match accepted : compile codec names rows patterns with
  | none => none
  | some legs =>
      if covered : coveredCheck environment (factors legs) then
        some ⟨legs, accepted, (coveredCheck_iff _ _).mp covered, prepareFactors (factors legs),
          sources_prepare _, prepareDomain outside (inputDomain environment (factors legs))⟩
      else none

def Prepared.count {codec : Codec Value} {names : Inventory String} {rows patterns : List Atom}
    {environment : DenseEnvironment names Value} (prepared : Prepared codec names rows patterns environment)
    (outside : Value) : Nat := weightedCount prepared.domain prepared.indices outside environment

theorem Prepared.count_exact {codec : Codec Value} {names : Inventory String} {rows patterns : List Atom}
    {environment : DenseEnvironment names Value} (prepared : Prepared codec names rows patterns environment)
    (outside : Value) :
    prepared.count outside = (ConjunctiveBindingJoin.run environment (factors prepared.legs)).length := by
  unfold Prepared.count
  rw [weighted_count_eq_source prepared.domain prepared.indices outside environment
    (inputDomain_captures _ _) (by rw [prepared.originals]; exact inputDomain_rows _ _)
    (by rw [prepared.originals]; exact prepared.covered), prepared.originals]

theorem Prepared.returns {codec : Codec Value} {names : Inventory String} {rows patterns : List Atom}
    {environment : DenseEnvironment names Value} (prepared : Prepared codec names rows patterns environment)
    (outside : Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (program : Program) (state : Effects.State) (spaceName : String)
    (snapshot : (Effects.readHandle (.symbol spaceName) >>= state.read) = some rows) :
    Eval.PureReturns program bindings state (countSyntax spaceName patterns) state
      (.grounded (.int (prepared.count outside))) := by
  rw [prepared.count_exact]
  exact compiled_count_returns codec names rows patterns prepared.legs prepared.accepted environment bindings
    represented program state spaceName snapshot

theorem Prepared.bag_exact {codec : Codec Value} {names : Inventory String} {rows patterns : List Atom}
    {environment : DenseEnvironment names Value} (prepared : Prepared codec names rows patterns environment)
    (outside : Value) (bindings : Subst) (represented : Represents codec names environment bindings) :
    (IndexedJoinDelivery.deliver prepared.domain prepared.indices outside (List.finRange names.keys.length) environment :
        Multiset (DenseEnvironment names Value × List Nat)) =
      ((sourceRun rows bindings patterns).map (resultReadback codec names) :
        Multiset (DenseEnvironment names Value × List Nat)) := by
  rw [ConjunctiveBindingObservation.indexed_bag_eq_source prepared.domain prepared.indices outside environment
    (inputDomain_captures _ _) (by rw [prepared.originals]; exact inputDomain_rows _ _)
    (by rw [prepared.originals]; exact prepared.covered), prepared.originals,
    compiled_query_exact codec names rows patterns prepared.legs prepared.accepted environment bindings represented]

def Prepared.certificate {codec : Codec Value} {names : Inventory String} {rows patterns : List Atom}
    {environment : DenseEnvironment names Value} (prepared : Prepared codec names rows patterns environment)
    (outside : Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (program : Program) (spaceName : String) :
    ReadOnlyQuerySource.Certified program bindings (countSyntax spaceName patterns) where
  reads := [(.symbol spaceName, rows)]
  values := [.grounded (.int (prepared.count outside))]
  returns state valid := prepared.returns outside bindings represented program state spaceName
    ((ReadOnlyQuerySource.valid_singleton _ _ _).mp valid)

/-- Classification captures actual input bindings and a complete snapshot;
unsupported capture, missing spaces and non-ground compilation all refuse. -/
def classify (observation : PureCallExtraction.Observation) (codec : Codec Value) (names : Inventory String)
    (program : Program) (bindings : Subst) (state : Effects.State) (spaceName : String)
    (patterns : List Atom) (outside : Value) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program bindings (countSyntax spaceName patterns)) Nat) :=
  match observation with
  | .exactPage => none
  | .completedResult =>
      match capture codec names bindings with
      | none => none
      | some captured => match Effects.readHandle (.symbol spaceName) >>= state.read with
        | none => none
        | some rows => (prepare codec names rows patterns captured.1 outside).map
            (fun prepared => (prepared.certificate outside bindings captured.2 program spaceName).region)

theorem exact_page_refuses (codec : Codec Value) (names : Inventory String)
    (program : Program) (bindings : Subst) (state : Effects.State) (spaceName : String)
    (patterns : List Atom) (outside : Value) :
    classify .exactPage codec names program bindings state spaceName patterns outside = none := rfl

theorem unsupported_capture_refuses_classification (codec : Codec Value) (names : Inventory String)
    (program : Program) (bindings : Subst) (state : Effects.State) (spaceName : String)
    (patterns : List Atom) (outside : Value) (unsupported : capture codec names bindings = none) :
    classify .completedResult codec names program bindings state spaceName patterns outside = none := by
  simp [classify, unsupported]

theorem missing_snapshot_refuses (codec : Codec Value) (names : Inventory String)
    (program : Program) (bindings : Subst) (state : Effects.State) (spaceName : String)
    (patterns : List Atom) (outside : Value)
    (missing : (Effects.readHandle (.symbol spaceName) >>= state.read) = none) :
    classify .completedResult codec names program bindings state spaceName patterns outside = none := by
  unfold classify
  rw [missing]
  cases capture codec names bindings <;> rfl

theorem stale_snapshot_declines {codec : Codec Value} {names : Inventory String} {rows patterns : List Atom}
    {environment : DenseEnvironment names Value} (prepared : Prepared codec names rows patterns environment)
    (outside : Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (program : Program) (state : Effects.State) (spaceName : String)
    (stale : (Effects.readHandle (.symbol spaceName) >>= state.read) ≠ some rows) :
    (prepared.certificate outside bindings represented program spaceName).region.attempt state = .declined state := by
  apply ReadOnlyQuerySource.stale_read_declines
  simpa only [Prepared.certificate, ReadOnlyQuerySource.valid_singleton] using stale

theorem unsupported_compilation_refuses (codec : Codec Value) (names : Inventory String)
    (rows patterns : List Atom) (environment : DenseEnvironment names Value) (outside : Value)
    (unsupported : compile codec names rows patterns = none) :
    prepare codec names rows patterns environment outside = none := by
  unfold prepare
  split
  next failed => rfl
  next legs accepted => simp [unsupported] at accepted

theorem uncovered_variable_refuses (codec : Codec Value) (names : Inventory String)
    (rows patterns : List Atom) (environment : DenseEnvironment names Value) (outside : Value)
    (legs : List (Leg codec names rows)) (accepted : compile codec names rows patterns = some legs)
    (uncovered : ¬ Covered environment (factors legs)) :
    prepare codec names rows patterns environment outside = none := by
  have rejected : coveredCheck environment (factors legs) = false :=
    Bool.eq_false_iff.mpr (fun checked => uncovered ((coveredCheck_iff _ _).mp checked))
  unfold prepare
  split
  next failed => simp [accepted] at failed
  next result compiled =>
    have same : result = legs := Option.some.inj (compiled.symm.trans accepted)
    subst result
    simp [rejected]

namespace Controls

open FlatQueryConjunctionCompilation.Controls

def noNames : Inventory String := ⟨[], by decide⟩
def comma : Atom := .expression [.symbol ","]

theorem active_empty_conjunction_refuses :
    prepare integers noNames [] [comma] (fun _ => none) 0 = none := by decide +kernel

theorem active_variable_conjunction_refuses :
    prepare integers names rows [.expression [.symbol ",", .var "x", .var "y"]] (fun _ => none) 0 = none := by
  decide +kernel

theorem active_conjunction_has_no_compiled_region :
    (classify .completedResult integers noNames {equations := [], declarations := []} []
      (NamedSpaces.Store.new [] []) "&self" [comma] 0).isNone = true := by decide +kernel

def emptyPrepared : Prepared integers noNames [] [] (fun _ => none) :=
  (prepare integers noNames [] [] (fun _ => none) 0).get (by decide +kernel)

theorem empty_ir_conjunction_still_has_one_witness : emptyPrepared.count 0 = 1 := by
  rw [emptyPrepared.count_exact]
  rfl

def prepared : Prepared integers names rows patterns (fun _ => none) :=
  (prepare integers names rows patterns (fun _ => none) 0).get (by decide +kernel)

theorem indexed_count_keeps_duplicates : prepared.count 0 = 4 := by
  rw [prepared.count_exact]
  decide +kernel

theorem unused_inventory_slot_refuses :
    prepare integers names [] [] (fun _ => none) 0 = none := by decide +kernel

theorem open_fact_refuses :
    prepare integers names [.expression [.symbol "r", .var "open", .grounded (.int 1)]]
      [patterns[0]!] (fun _ => none) 0 = none := by decide +kernel

theorem actual_source_count :
    Eval.PureReturns {equations := [], declarations := []} [] FlatQuerySourceExecution.Controls.state
      (countSyntax "&self" patterns) FlatQuerySourceExecution.Controls.state (.grounded (.int 4)) := by
  have returned := prepared.returns 0 [] (by intro slot; rfl)
    {equations := [], declarations := []} FlatQuerySourceExecution.Controls.state "&self" rfl
  simpa [indexed_count_keeps_duplicates] using returned

def triangleRows : List Atom := [
  .expression [.symbol "edge", .grounded (.int 0), .grounded (.int 1)],
  .expression [.symbol "edge", .grounded (.int 0), .grounded (.int 1)],
  .expression [.symbol "edge", .grounded (.int 1), .grounded (.int 2)],
  .expression [.symbol "edge", .grounded (.int 2), .grounded (.int 0)]]

def trianglePatterns : List Atom := [
  .expression [.symbol "edge", .var "x", .var "y"],
  .expression [.symbol "edge", .var "y", .var "z"],
  .expression [.symbol "edge", .var "z", .var "x"]]

def trianglePrepared : Prepared integers names triangleRows trianglePatterns (fun _ => none) :=
  (prepare integers names triangleRows trianglePatterns (fun _ => none) 0).get (by decide +kernel)

theorem cyclic_count_keeps_rotations_and_occurrences : trianglePrepared.count 0 = 6 := by
  rw [trianglePrepared.count_exact]
  decide +kernel

theorem actual_cyclic_source_count :
    Eval.PureReturns {equations := [], declarations := []} [] (NamedSpaces.Store.new triangleRows [])
      (countSyntax "&self" trianglePatterns) (NamedSpaces.Store.new triangleRows []) (.grounded (.int 6)) := by
  have returned := trianglePrepared.returns 0 [] (by intro slot; rfl)
    {equations := [], declarations := []} (NamedSpaces.Store.new triangleRows []) "&self" rfl
  simpa [cyclic_count_keeps_rotations_and_occurrences] using returned

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryIndexedSource
