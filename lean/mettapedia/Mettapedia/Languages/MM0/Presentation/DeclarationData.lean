import Mettapedia.Languages.MM0.Presentation.ProofTheory
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ComputationLists

/-! # MM0 sort profiles and declaration environments as data -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration

open Kernel
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

abbrev SortTable := List (Nat × SortInfo)

def sortsOf (table : SortTable) : SortSignature := fun index => table.lookup index

def encodeSort (info : SortInfo) : Term :=
  .list [.sym "MM0:Sort", boolean info.pure, boolean info.strict,
    boolean info.provable, boolean info.free]

def decodeBoolean : Term → Option Bool
  | .sym "True" => some true
  | .sym "False" => some false
  | _ => none

@[simp] theorem decodeBoolean_encode (value : Bool) :
    decodeBoolean (boolean value) = some value := by cases value <;> rfl

def decodeSort : Term → Option SortInfo
  | .list [.sym "MM0:Sort", pure, strict, provable, free] => do
      let pure ← decodeBoolean pure
      let strict ← decodeBoolean strict
      let provable ← decodeBoolean provable
      let free ← decodeBoolean free
      return ⟨pure, strict, provable, free⟩
  | _ => none

@[simp] theorem decodeSort_encode (info : SortInfo) : decodeSort (encodeSort info) = some info := by
  cases info
  simp [decodeSort, encodeSort]

theorem encodeSort_injective : Function.Injective encodeSort := by
  intro first second same
  have decoded := congrArg decodeSort same
  simpa using decoded

def encodeSorts (table : SortTable) : Term := encodeNaturalTable encodeSort table

theorem theory_sorts (theory : Theory) : sortsOf theory.sorts = theory.sortSignature := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration
