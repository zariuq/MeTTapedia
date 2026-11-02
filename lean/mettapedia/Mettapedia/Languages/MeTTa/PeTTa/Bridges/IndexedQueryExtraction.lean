import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.SourceRegionExtraction

/-!
# Indexed-query leaves for source-region inference

The leaf compiler reads an actual source expression, recovers a nested count
query, derives its variable inventory, captures its space operand and caller,
and prepares indexed factors. Generic source composition then follows authored
wrappers and surrounding consumers. Unsupported bodies remain unsupported;
they are never interpreted as empty queries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Eval SpaceSemantics FlatQueryRowCodec FlatQuerySourceExecution CapturedQuerySource

def decodeNested (space : Atom) : (fuel : Nat) → (source : Atom) →
    Option {patterns : List Atom // source = sourceTerm space patterns (Effects.boolean true)}
  | 0, _ => none
  | fuel + 1, source =>
      if finished : source = Effects.boolean true then some ⟨[], finished⟩
      else match source with
      | .expression [.symbol "match", location, pattern, body] =>
          if same : location = space then
            (decodeNested space fuel body).map fun rest =>
              ⟨pattern :: rest.1, by simp only [sourceTerm, same, rest.2]⟩
          else none
      | _ => none

structure CountShape (source : Atom) where
  space : Atom
  patterns : List Atom
  exact : source = countTerm space patterns

def decodeCount (fuel : Nat) : (source : Atom) → Option (CountShape source)
  | .expression [.symbol "size-atom", .expression [.symbol "collapse",
      .expression [.symbol "match", space, pattern, body]]] =>
      (decodeNested space fuel body).map fun rest =>
        ⟨space, pattern :: rest.1, by simp only [countTerm, sourceTerm, rest.2]⟩
  | _ => none

def inventory (patterns : List Atom) : Inventory String :=
  ⟨(patterns.flatMap atomFreeVars).dedup, List.nodup_dedup _⟩

def leaf {Value : Type} [LinearOrder Value] (codec : Codec Value) (outside : Value)
    (shapeFuel : Nat) : SourceRegionExtraction.LeafCompiler := fun program caller state source => do
  let shape ← decodeCount shapeFuel source
  let names := inventory shape.patterns
  let operand ← prepareOperand caller shape.space
  let captured ← capture codec names caller
  let rows ← Effects.readHandle operand.value >>= state.read
  let prepared ← FlatQueryIndexedSource.prepare codec names rows shape.patterns captured.1 outside
  return shape.exact.symm ▸ CapturedQuerySource.certificate prepared outside caller captured.2 operand program

def prepare {Value : Type} [LinearOrder Value] (codec : Codec Value) (outside : Value)
    (shapeFuel compositionFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) :
    Option (ReadOnlyQuerySource.Certified program caller source) :=
  SourceRegionExtraction.prepare (leaf codec outside shapeFuel) compositionFuel program caller state source

theorem extra_effect_is_not_a_count_body :
    decodeNested (.symbol "&self") 8 (.expression [.symbol "println!", .grounded (.int 7)]) = none := by decide +kernel

theorem different_space_is_not_silently_merged :
    decodeNested (.symbol "&self") 8
      (.expression [.symbol "match", .symbol "&other", .expression [.symbol "edge", .var "x"], Effects.boolean true]) = none := by
  decide +kernel

theorem repeated_variables_have_one_inventory_slot :
    (inventory [.expression [.symbol "r", .var "x", .var "x"]]).keys = ["x"] := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction
