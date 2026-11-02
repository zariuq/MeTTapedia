import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProvider

/-! Checked extension of immutable provider rows. Existing receipt positions
remain fixed because new rows are appended. This establishes typing and row
position preservation, not arbitrary premise monotonicity or a native-wire
correspondence. Dynamic services still need their own semantic certificates. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderAppend

open Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def appendRows (provider : ProviderSnapshot) (rows : List ProviderRow) : ProviderSnapshot :=
  {provider with rows := provider.rows ++ rows}

def checkRows (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) (rows : List ProviderRow) : Bool :=
  rows.all fun row => match signature? provider row.relation row.values.length with
    | none => false
    | some signature => checkRow language free [] signature row

def appendChecked? (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) (rows : List ProviderRow) : Option ProviderSnapshot :=
  if checkRows language free provider rows then some (appendRows provider rows) else none

@[simp] theorem signatures_preserved (provider : ProviderSnapshot) (rows : List ProviderRow) :
    (appendRows provider rows).signatures = provider.signatures := rfl

@[simp] theorem dynamic_relations_preserved (provider : ProviderSnapshot) (rows : List ProviderRow) :
    (appendRows provider rows).dynamicRelations = provider.dynamicRelations := rfl

@[simp] theorem signature_preserved (provider : ProviderSnapshot) (rows : List ProviderRow)
    (relation : String) (arity : Nat) :
    signature? (appendRows provider rows) relation arity = signature? provider relation arity := rfl

theorem original_prefix (provider : ProviderSnapshot) (rows : List ProviderRow) :
    (appendRows provider rows).rows.take provider.rows.length = provider.rows := by
  simp [appendRows]

theorem original_row_at (provider : ProviderSnapshot) (rows : List ProviderRow)
    (index : Nat) (inside : index < provider.rows.length) :
    (appendRows provider rows).rows[index]? = provider.rows[index]? := by
  exact List.getElem?_append_left inside

theorem appended_row_at (provider : ProviderSnapshot) (rows : List ProviderRow) (index : Nat) :
    (appendRows provider rows).rows[provider.rows.length + index]? = rows[index]? := by
  change (provider.rows ++ rows)[provider.rows.length + index]? = rows[index]?
  rw [List.getElem?_append_right (by omega)]
  simp

theorem row_membership (provider : ProviderSnapshot) (rows : List ProviderRow) (row : ProviderRow) :
    row ∈ (appendRows provider rows).rows ↔ row ∈ provider.rows ∨ row ∈ rows := by
  simp [appendRows]

theorem check_closed_append (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) (rows : List ProviderRow) :
    checkProviderClosed language free (appendRows provider rows) =
      (checkProviderClosed language free provider && checkRows language free provider rows) := by
  simp [checkProviderClosed, appendRows, checkRows, signature?, List.all_append, Bool.and_assoc]
  rfl

theorem checked_typing (language : LanguageDef) (free : FreeTypeContext)
    (provider result : ProviderSnapshot) (rows : List ProviderRow)
    (old : checkProviderClosed language free provider = true)
    (appended : appendChecked? language free provider rows = some result) :
    checkProviderClosed language free result = true := by
  unfold appendChecked? at appended
  split at appended
  next accepted =>
    cases Option.some.inj appended
    simp [check_closed_append, old, accepted]
  next => contradiction

private def controlProvider : ProviderSnapshot :=
  {signatures := [⟨"old", [], []⟩, ⟨"new", [], []⟩], rows := [⟨"old", []⟩]}

#guard (appendChecked? (LanguageDef.empty "cache") (FreeTypeContext.ofList [])
  controlProvider [⟨"new", []⟩]).map (fun provider => provider.rows) ==
    some [⟨"old", []⟩, ⟨"new", []⟩]
#guard (appendChecked? (LanguageDef.empty "cache") (FreeTypeContext.ofList [])
  controlProvider [⟨"missing", []⟩]).isNone
#guard (appendChecked? (LanguageDef.empty "cache") (FreeTypeContext.ofList [])
  controlProvider [⟨"new", [.fvar "wrong-arity"]⟩]).isNone

#print axioms original_row_at
#print axioms checked_typing

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderAppend
