import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Two MeTTa authoring forms for the existing inductive declaration syntax

A builder returns a `Family` value. A complete `Declarations` block contains
one classification and its matching `data` definition. Both readers produce
the existing `InductiveSyntax.Family`, retaining parameters, indices, field
order, result indices and the sort. They neither execute their input nor
authorize induction. The existing indexed admission supplies that meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData

open InductiveSyntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def termData : Term → Atom
  | .name name => .symbol name
  | .app function argument => .expression [termData function, termData argument]
  | .arrow domain result => .expression [.symbol "->", termData domain, termData result]
  | .pi binder domain result =>
      .expression [.symbol "Pi", .symbol binder, termData domain, termData result]
  | .project owner field record =>
      .expression [.symbol "Projection", .symbol owner, .grounded (.int (.ofNat field)), termData record]

def readTerm : Atom → Option Term
  | .symbol name => some (.name name)
  | .expression [function, argument] => do return .app (← readTerm function) (← readTerm argument)
  | .expression [.symbol "->", domain, result] => do return .arrow (← readTerm domain) (← readTerm result)
  | .expression [.symbol "Pi", .symbol binder, domain, result] =>
      do return .pi binder (← readTerm domain) (← readTerm result)
  | .expression [.symbol "Projection", .symbol owner, .grounded (.int (.ofNat field)), record] =>
      do return .project owner field (← readTerm record)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem readTerm_termData (term : Term) : readTerm (termData term) = some term := by
  induction term with
  | name => simp [readTerm, termData]
  | app function argument hf ha => simp [termData, readTerm, hf, ha]
  | arrow domain result hd hr => simp [termData, readTerm, hd, hr]
  | pi binder domain result hd hr => simp [termData, readTerm, hd, hr]
  | project owner field record ih =>
      simp only [termData]
      rw [readTerm]
      simp [ih]

def binderData (binder : Binder) : Atom :=
  .expression [.symbol ":", .symbol binder.name, termData binder.type]

def readBinder : Atom → Option Binder
  | .expression [.symbol ":", .symbol name, type] => do return ⟨name, ← readTerm type⟩
  | _ => none

@[simp] theorem readBinder_binderData (binder : Binder) : readBinder (binderData binder) = some binder := by
  cases binder
  simp [binderData, readBinder]

def bindersData (binders : List Binder) : Atom := .expression (binders.map binderData)
def readBinders : Atom → Option (List Binder)
  | .expression binders => binders.mapM readBinder
  | _ => none

@[simp] theorem readBinders_bindersData (binders : List Binder) :
    readBinders (bindersData binders) = some binders := by
  change (binders.map binderData).mapM readBinder = some binders
  induction binders with
  | nil => rfl
  | cons first rest ih => simp [ih]

def constructorData (constructor : Constructor) : Atom :=
  .expression [.symbol ":",
    .expression [.symbol constructor.name, .expression [.symbol "fields", bindersData constructor.fields]],
    termData constructor.result]

def readConstructor : Atom → Option Constructor
  | .expression [.symbol ":", .expression [.symbol name, .expression [.symbol "fields", fields]], result] => do
      return ⟨name, ← readBinders fields, ← readTerm result⟩
  | _ => none

@[simp] theorem readConstructor_constructorData (constructor : Constructor) :
    readConstructor (constructorData constructor) = some constructor := by
  cases constructor
  simp [constructorData, readConstructor]

def constructorsData (constructors : List Constructor) : Atom := .expression (constructors.map constructorData)
def readConstructors : Atom → Option (List Constructor)
  | .expression constructors => constructors.mapM readConstructor
  | _ => none

@[simp] theorem readConstructors_constructorsData (constructors : List Constructor) :
    readConstructors (constructorsData constructors) = some constructors := by
  change (constructors.map constructorData).mapM readConstructor = some constructors
  induction constructors with
  | nil => rfl
  | cons first rest ih => simp [ih]

def familyData (family : Family) : Atom :=
  .expression [.symbol "Family", .symbol family.name,
    .expression [.symbol "parameters", bindersData family.parameters],
    .expression [.symbol "indices", bindersData family.indices], termData family.sort,
    .expression [.symbol "constructors", constructorsData family.constructors]]

def readFamily : Atom → Option Family
  | .expression [.symbol "Family", .symbol name,
      .expression [.symbol "parameters", parameters], .expression [.symbol "indices", indices], sort,
      .expression [.symbol "constructors", constructors]] => do
      return ⟨name, ← readBinders parameters, ← readBinders indices,
        ← readTerm sort, ← readConstructors constructors⟩
  | _ => none

@[simp] theorem readFamily_familyData (family : Family) : readFamily (familyData family) = some family := by
  cases family
  simp [familyData, readFamily]

def blockData (family : Family) : Atom :=
  .expression [.symbol "Declarations",
    .expression [.symbol ":", .expression [.symbol "Family", .symbol family.name,
      .expression [.symbol "parameters", bindersData family.parameters],
      .expression [.symbol "indices", bindersData family.indices]], termData family.sort],
    .expression [.symbol "=", .symbol family.name,
      .expression [.symbol "data", constructorsData family.constructors]]]

/-- Completion is explicit: this reader accepts exactly a signature and its
complete matching body. Trailing, missing or malformed rows are refused. -/
def readBlock : Atom → Option Family
  | .expression [.symbol "Declarations",
      .expression [.symbol ":", .expression [.symbol "Family", .symbol declared,
        .expression [.symbol "parameters", parameters], .expression [.symbol "indices", indices]], sort],
      .expression [.symbol "=", .symbol defined, .expression [.symbol "data", constructors]]] => do
      if declared ≠ defined then none else do
        return ⟨declared, ← readBinders parameters, ← readBinders indices,
          ← readTerm sort, ← readConstructors constructors⟩
  | _ => none

@[simp] theorem readBlock_blockData (family : Family) : readBlock (blockData family) = some family := by
  cases family
  simp [blockData, readBlock]

theorem familyData_injective : Function.Injective familyData := by
  intro first second same
  have decoded := congrArg readFamily same
  simpa only [readFamily_familyData, Option.some.injEq] using decoded

theorem blockData_injective : Function.Injective blockData := by
  intro first second same
  have decoded := congrArg readBlock same
  simpa only [readBlock_blockData, Option.some.injEq] using decoded

/-- The two distinct input grammars retain the identical declaration. -/
theorem two_forms_same_family (family : Family) :
    readBlock (blockData family) = readFamily (familyData family) := by simp

noncomputable def admitBuilder (A : Type) (names : IndexedNatVecSource.Names)
    (natural vector : Atom) := do
  let natural ← readFamily natural
  let vector ← readFamily vector
  IndexedNatVecSource.admit A names natural vector

noncomputable def admitBlock (A : Type) (names : IndexedNatVecSource.Names)
    (natural vector : Atom) := do
  let natural ← readBlock natural
  let vector ← readBlock vector
  IndexedNatVecSource.admit A names natural vector

/-- Agreement reaches the existing indexed semantic admission, rather than
stopping at a field inventory. Its Nat/Vec fragment restrictions still apply. -/
theorem two_forms_same_admission (A : Type) (names : IndexedNatVecSource.Names)
    (natural vector : Family) :
    admitBlock A names (blockData natural) (blockData vector) =
      admitBuilder A names (familyData natural) (familyData vector) := by
  simp [admitBlock, admitBuilder]

theorem admitted_block_is_existing_admission (A : Type) (names : IndexedNatVecSource.Names)
    (natural vector : Family) :
    admitBlock A names (blockData natural) (blockData vector) =
      IndexedNatVecSource.admit A names natural vector := by simp [admitBlock]

theorem extra_block_row_refused (signature body extra : Atom) :
    readBlock (.expression [.symbol "Declarations", signature, body, extra]) = none := by simp [readBlock]

theorem signature_without_body_refused (signature : Atom) :
    readBlock (.expression [.symbol "Declarations", signature]) = none := by simp [readBlock]

theorem malformed_unused_binder_refused :
    readBinders (.expression [.expression [.symbol ":", .symbol "unused"]]) = none := rfl

#print axioms readBlock_blockData
#print axioms two_forms_same_admission
#print axioms blockData_injective

end Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData
