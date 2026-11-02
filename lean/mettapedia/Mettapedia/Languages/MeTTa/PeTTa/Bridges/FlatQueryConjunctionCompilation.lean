import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRelationCompilation
import Mettapedia.GSLT.Dynamics.ConjunctiveBindingJoin

/-!
# Composing compiled query legs over one captured snapshot

Each leg is compiled from an actual source pattern and the same source rows.
The source traversal threads the real PeTTa substitutions. The compiled
traversal threads only the declared dense query slots. Their ordered results
agree after readback, including every occurrence witness. A successful source
leg proves that its next frame is still represented before the following leg
uses it.

This is the matching-composition bridge. Evaluation of surrounding source
consumers and finite-domain reconstruction for variable-at-a-time delivery
are separate edges, not assumptions hidden in the row compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryConjunctionCompilation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance ConjunctiveRowMatching
open FlatQueryRowCodec FlatQueryPatternExtraction FlatQueryRelationCompilation

variable {Value : Type} [DecidableEq Value]

structure Leg (codec : Codec Value) (names : Inventory String) (rows : List Atom) where
  source : Atom
  pattern : Compiled codec names source
  relation : Relation pattern 0 rows

def compileLeg (codec : Codec Value) (names : Inventory String) (rows : List Atom) (source : Atom) :
    Option (Leg codec names rows) := do
  let pattern ← compilePattern codec names source
  let relation ← FlatQueryRelationCompilation.compile pattern 0 rows
  return ⟨source, pattern, relation⟩

def compile (codec : Codec Value) (names : Inventory String) (rows sources : List Atom) :
    Option (List (Leg codec names rows)) := sources.mapM (compileLeg codec names rows)

theorem compileLeg_source (codec : Codec Value) (names : Inventory String) (rows : List Atom)
    (source : Atom) (leg : Leg codec names rows) (compiled : compileLeg codec names rows source = some leg) :
    leg.source = source := by
  unfold compileLeg at compiled
  obtain ⟨pattern, _, remaining⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨relation, _, same⟩ := Option.bind_eq_some_iff.mp remaining
  cases Option.some.inj same
  rfl

theorem compile_sources (codec : Codec Value) (names : Inventory String) (rows sources : List Atom)
    (legs : List (Leg codec names rows)) (compiled : compile codec names rows sources = some legs) :
    legs.map Leg.source = sources := by
  induction sources generalizing legs with
  | nil => cases compiled; rfl
  | cons source sources ih =>
      simp only [compile, List.mapM_cons, Option.bind_eq_bind] at compiled
      obtain ⟨leg, first, remaining⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨later, rest, same⟩ := Option.bind_eq_some_iff.mp remaining
      cases Option.some.inj same
      simp only [List.map_cons, compileLeg_source codec names rows source leg first, ih later rest]

def sourceRun (rows : List Atom) (bindings : Subst) : List Atom → List (Subst × List Nat)
  | [] => [(bindings, [])]
  | pattern :: patterns => (sourceScan bindings pattern 0 rows).flatMap fun first =>
      (sourceRun rows first.2 patterns).map fun later => (later.1, first.1 :: later.2)

def factors {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (legs : List (Leg codec names rows)) : List (Factor names.Slot Value Nat) :=
  legs.map (fun leg => leg.relation.factor)

def resultReadback (codec : Codec Value) (names : Inventory String) (answer : Subst × List Nat) :
    DenseEnvironment names Value × List Nat := (readback codec names answer.1, answer.2)

theorem conjunctive_readback_exact {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (legs : List (Leg codec names rows)) (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) :
    ConjunctiveBindingJoin.run environment (factors legs) =
      (sourceRun rows bindings (legs.map Leg.source)).map (resultReadback codec names) := by
  induction legs generalizing environment bindings with
  | nil => simp [factors, ConjunctiveBindingJoin.run, sourceRun, resultReadback, readback_exact _ _ _ _ represented]
  | cons leg legs ih =>
      have one := factorScan_source_exact leg.relation environment bindings represented
      have expanded := congrArg
        (List.flatMap (fun first : Nat × DenseEnvironment names Value =>
          (ConjunctiveBindingJoin.run first.2 (factors legs)).map fun later => (later.1, first.1 :: later.2))) one
      simp only [List.flatMap_assoc, Option.toList_map, List.flatMap_map,
        project] at expanded
      change ConjunctiveBindingJoin.run environment (leg.relation.factor :: factors legs) = _
      rw [ConjunctiveBindingJoin.run, expanded]
      simp only [List.map_cons, sourceRun, List.map_flatMap, List.map_map]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro first member
      have next := leg.relation.preserves environment bindings represented first member
      rw [ih (readback codec names first.2) first.2 next]
      simp only [List.map_map, Function.comp_def, resultReadback]

theorem compiled_query_exact (codec : Codec Value) (names : Inventory String) (rows sources : List Atom)
    (legs : List (Leg codec names rows)) (accepted : compile codec names rows sources = some legs)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings) :
    ConjunctiveBindingJoin.run environment (factors legs) =
      (sourceRun rows bindings sources).map (resultReadback codec names) := by
  rw [conjunctive_readback_exact legs environment bindings represented, compile_sources codec names rows sources legs accepted]

theorem compiled_count_exact (codec : Codec Value) (names : Inventory String) (rows sources : List Atom)
    (legs : List (Leg codec names rows)) (accepted : compile codec names rows sources = some legs)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings) :
    (ConjunctiveBindingJoin.run environment (factors legs)).length = (sourceRun rows bindings sources).length := by
  rw [compiled_query_exact codec names rows sources legs accepted environment bindings represented, List.length_map]

namespace Controls

def names : Inventory String := ⟨["x", "y", "z"], by decide⟩
def rows : List Atom := [
  .expression [.symbol "r", .grounded (.int 0), .grounded (.int 1)],
  .expression [.symbol "r", .grounded (.int 0), .grounded (.int 1)],
  .expression [.symbol "s", .grounded (.int 1), .grounded (.int 2)],
  .expression [.symbol "s", .grounded (.int 1), .grounded (.int 0)]]
def patterns : List Atom := [.expression [.symbol "r", .var "x", .var "y"],
  .expression [.symbol "s", .var "y", .var "z"]]

def legs : List (Leg integers names rows) := (compile integers names rows patterns).get (by decide +kernel)

theorem four_ordered_source_witnesses :
    (sourceRun rows [] patterns).map Prod.snd = [[0, 2], [0, 3], [1, 2], [1, 3]] := by decide +kernel

theorem compiled_join_keeps_all_four :
    (ConjunctiveBindingJoin.run (fun _ => none) (factors legs)).map Prod.snd =
      [[0, 2], [0, 3], [1, 2], [1, 3]] := by decide +kernel

theorem incompatible_capture_cannot_be_rebound_by_later_leg :
    sourceRun rows [("y", .grounded (.int 9))] patterns = [] := by decide +kernel

theorem same_row_can_be_read_twice :
    (sourceRun rows [] [patterns[0]!, patterns[0]!]).map Prod.snd =
      [[0, 0], [0, 1], [1, 0], [1, 1]] := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryConjunctionCompilation
