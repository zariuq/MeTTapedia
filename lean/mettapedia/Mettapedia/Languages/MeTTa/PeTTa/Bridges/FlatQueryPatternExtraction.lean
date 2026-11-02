import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRowCodec
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec

/-!
# Checked extraction of flat query patterns and source rows

Names are resolved through the existing duplicate-free inventory. Literal
decoding carries an exact Atom round trip. Row classification distinguishes
a proved mismatch from an unsupported row: the latter refuses compilation,
never supplies evidence of absence. Open row heads and unsupported values
are not dropped from a candidate relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryPatternExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
open SpaceSemantics FlatQueryRowCodec

variable {Value : Type}

def decodeCell (codec : Codec Value) (names : Inventory String) : Atom → Option (Cell names.Slot Value)
  | .var name => (names.resolve? name).map Cell.variable
  | atom => (codec.decode atom).map Cell.constant

theorem decodeCell_exact (codec : Codec Value) (names : Inventory String) (atom : Atom)
    (cell : Cell names.Slot Value) (decoded : decodeCell codec names atom = some cell) :
    encodeCell codec names cell = atom := by
  cases atom with
  | var name =>
      obtain ⟨slot, selected, equal⟩ := Option.map_eq_some_iff.mp decoded
      cases equal
      exact congrArg Atom.var ((names.resolve?_eq_some_iff name slot).mp selected)
  | symbol name | grounded value | expression items =>
      obtain ⟨value, selected, equal⟩ := Option.map_eq_some_iff.mp decoded
      cases equal
      exact codec.exact _ value selected

def decodeCells (codec : Codec Value) (names : Inventory String) (atoms : List Atom) :
    Option (List (Cell names.Slot Value)) := atoms.mapM (decodeCell codec names)

theorem decodeCells_exact (codec : Codec Value) (names : Inventory String) (atoms : List Atom)
    (cells : List (Cell names.Slot Value)) (decoded : decodeCells codec names atoms = some cells) :
    cells.map (encodeCell codec names) = atoms := by
  induction atoms generalizing cells with
  | nil => cases decoded; rfl
  | cons first rest ih =>
      simp only [decodeCells, List.mapM_cons, Option.bind_eq_bind] at decoded
      obtain ⟨cell, firstDecoded, later⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨tail, tailDecoded, same⟩ := Option.bind_eq_some_iff.mp later
      cases Option.some.inj same
      simp only [List.map_cons, decodeCell_exact codec names first cell firstDecoded, ih tail tailDecoded]

structure Compiled (codec : Codec Value) (names : Inventory String) (source : Atom) where
  head : String
  ordinary : head ≠ "cons"
  cells : List (Cell names.Slot Value)
  exact : pattern codec names head cells = source

def compilePattern (codec : Codec Value) (names : Inventory String) :
    (source : Atom) → Option (Compiled codec names source)
  | .expression (.symbol head :: arguments) =>
      if ordinary : head ≠ "cons" then
        match decoded : decodeCells codec names arguments with
        | none => none
        | some cells => some ⟨head, ordinary, cells, by
            unfold pattern
            rw [decodeCells_exact codec names arguments cells decoded]⟩
      else none
  | _ => none

def decodeValues (codec : Codec Value) (atoms : List Atom) : Option (List Value) := atoms.mapM codec.decode

theorem decodeValues_exact (codec : Codec Value) (atoms : List Atom) (values : List Value)
    (decoded : decodeValues codec atoms = some values) : values.map codec.encode = atoms := by
  induction atoms generalizing values with
  | nil => cases decoded; rfl
  | cons first rest ih =>
      simp only [decodeValues, List.mapM_cons, Option.bind_eq_bind] at decoded
      obtain ⟨value, firstDecoded, later⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨tail, tailDecoded, same⟩ := Option.bind_eq_some_iff.mp later
      cases Option.some.inj same
      simp only [List.map_cons, codec.exact first value firstDecoded, ih tail tailDecoded]

theorem Compiled.expression_match {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (bindings : Subst) (values : List Atom) :
    matchValue bindings source (.expression values) =
      matchValue.matchValues bindings (.symbol compiled.head :: compiled.cells.map (encodeCell codec names)) values := by
  conv_lhs => rw [← compiled.exact]
  apply matchValue_expression_of_not_cons
  intro first rest same
  exact compiled.ordinary (by simpa using (List.cons.inj same).1)

theorem Compiled.head_clash {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (actual : Atom) (tail : List Atom)
    (different : (.symbol compiled.head : Atom) ≠ actual) (bindings : Subst) :
    matchValue bindings source (.expression (actual :: tail)) = none := by
  rw [compiled.expression_match]
  simp only [matchValue.matchValues, matchValue_literal (.symbol compiled.head), if_neg different]
  rfl

theorem Compiled.wrong_arity {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (arguments : List Atom)
    (different : arguments.length ≠ compiled.cells.length) (bindings : Subst) :
    matchValue bindings source (.expression (.symbol compiled.head :: arguments)) = none := by
  cases found : matchValue bindings source (.expression (.symbol compiled.head :: arguments)) with
  | none => rfl
  | some bound =>
      rw [compiled.expression_match] at found
      have equal := Eval.matchValues_length found
      simp only [List.length_cons, List.length_map] at equal
      exact False.elim (different (by omega))

structure KnownRow {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (atom : Atom) where
  values : List Value
  arity : values.length = compiled.cells.length
  exact : row codec compiled.head values = atom

inductive RowResult {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (atom : Atom) where
  | irrelevant (proof : ∀ bindings, matchValue bindings source atom = none)
  | known (row : KnownRow compiled atom)

def classifyRow {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) : (atom : Atom) → Option (RowResult compiled atom)
  | .var _ => none
  | .expression (.var _ :: _) => none
  | .expression [] => some (.irrelevant (fun bindings => by
      rw [compiled.expression_match]
      simp [matchValue.matchValues]))
  | .expression (actual :: arguments) =>
      if same : actual = .symbol compiled.head then
        if arity : arguments.length = compiled.cells.length then
          match decoded : decodeValues codec arguments with
          | none => none
          | some values => some (.known ⟨values, by
              have lengths := congrArg List.length (decodeValues_exact codec arguments values decoded)
              simpa only [List.length_map, arity] using lengths, by
              unfold row
              rw [decodeValues_exact codec arguments values decoded, same]⟩)
        else some (.irrelevant (fun bindings => by
          rw [same]
          exact compiled.wrong_arity arguments arity bindings))
      else some (.irrelevant (fun bindings => compiled.head_clash actual arguments (Ne.symm same) bindings))
  | .symbol name => some (.irrelevant (fun bindings => by
      rw [← compiled.exact]
      unfold pattern matchValue
      split <;> simp_all))
  | .grounded value => some (.irrelevant (fun bindings => by
      rw [← compiled.exact]
      unfold pattern matchValue
      split <;> simp_all))

namespace Controls

open FlatQueryRowCodec.Controls

def query : Atom := .expression [.symbol "r", .var "x", .var "x"]
def compiled : Compiled integers oneName query := (compilePattern integers oneName query).get (by decide +kernel)

theorem repeated_names_resolve_to_one_slot : compiled.cells = [.variable only, .variable only] := by decide +kernel

theorem missing_name_is_not_an_implicit_wildcard :
    decodeCell integers oneName (.var "missing") = none := by decide +kernel

theorem cons_view_is_not_a_plain_relation :
    (compilePattern integers oneName (.expression [.symbol "cons", .var "x", .var "x"])).isNone = true := by decide +kernel

theorem stored_open_value_refuses :
    (classifyRow compiled (.expression [.symbol "r", .var "stored", .grounded (.int 1)])).isNone = true := by decide +kernel

theorem stored_open_head_refuses :
    (classifyRow compiled (.expression [.var "head", .grounded (.int 1), .grounded (.int 1)])).isNone = true := by decide +kernel

theorem unrelated_head_is_certified_irrelevant :
    (classifyRow compiled (.expression [.symbol "s", .var "stored"])).isSome = true := by decide +kernel

theorem ground_source_row_decodes :
    (classifyRow compiled (.expression [.symbol "r", .grounded (.int 1), .grounded (.int 1)])).isSome = true := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryPatternExtraction
