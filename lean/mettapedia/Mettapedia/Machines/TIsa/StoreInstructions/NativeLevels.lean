import Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPlan

/-!
# Published levels with separately represented bindings

A level's root word selects a descriptor. The descriptor records
the occurrence bookkeeping and the address of the binding bank,
not the values that an unfinished match will write to that bank.
Thus the descriptor can already exist while the level is private.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeLevels

open Mettapedia.Logic.LP
open Derivation (Match Role)
open Derivation.FirstOrderTerms (Bindings)
open NativeMatchPlan (Bank)
open X86PlacedMemory (Reads footprint)
open NativeBinding (View)
open _root_.X86Registers (Register)

abbrev Native := X86RegisterRefinement.State

structure Uses (V : Type*) where
  taken : List ℕ
  read : List ℕ
  seen : List (Finset ℕ)
  made : List V

def Uses.ofMatch {V B : Type*} (m : Match V B) : Uses V := ⟨m.taken, m.read, m.seen, m.made⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}}

structure Descriptor (σ : LPSignature.{u,u,p,u}) where
  pointer : Word
  bank : Bank σ pointer
  uses : Uses (GroundTerm σ)

def prepare {pointer : Word} (bank : Bank σ pointer) (parent : Match (GroundTerm σ) (Bindings σ))
    (role : Role) (identity : ℕ) : Descriptor σ :=
  ⟨pointer, bank, Uses.ofMatch (parent.select role identity parent.bindings)⟩

def Descriptor.Represents (codes : PackedOccurrences.Codes (GroundTerm σ)) (descriptor : Descriptor σ)
    (state : Native) (level : Match (GroundTerm σ) (Bindings σ)) : Prop :=
  descriptor.uses = Uses.ofMatch level ∧
    ∃ table, BindingSlots.Represents table level.bindings ∧ descriptor.bank.Represents codes table state

theorem prepared_represents (codes : PackedOccurrences.Codes (GroundTerm σ)) {pointer : Word}
    (bank : Bank σ pointer) (parent : Match (GroundTerm σ) (Bindings σ)) (role : Role) (identity : ℕ)
    {native : Native} {table : BindingSlots.Table σ} {result : Bindings σ}
    (semantic : BindingSlots.Represents table result) (stored : bank.Represents codes table native) :
    (prepare bank parent role identity).Represents codes native (parent.select role identity result) := by
  cases role <;> exact ⟨rfl, table, semantic, stored⟩

theorem Descriptor.preserved (codes : PackedOccurrences.Codes (GroundTerm σ)) {d : Descriptor σ}
    {before after : Native} {level : Match (GroundTerm σ) (Bindings σ)}
    {written : Finset ℕ} {registers : Finset Register}
    (represented : d.Represents codes before level)
    (frame : X86StateFrame.Frame registers written before after)
    (separate : Disjoint d.bank.writes written) : d.Represents codes after level := by
  obtain ⟨uses, table, bindings, ready⟩ := represented
  refine ⟨uses, table, bindings, ?_⟩
  intro name member
  obtain ⟨word, value⟩ := ready name member
  have one := separate.mono_left (d.bank.slot_subset member)
  exact ⟨word, value.bit.preserved frame (one.mono_left Finset.subset_union_right),
    value.value.preserved frame (one.mono_left Finset.subset_union_left), value.code⟩

structure Directory (σ : LPSignature.{u,u,p,u}) (n : ℕ) where
  root : Fin n → BitVec 48
  catalog : Array (Descriptor σ)

def Directory.lookup {n : ℕ} (directory : Directory σ n) (handle : Word) : Option (Descriptor σ) :=
  directory.catalog[handle.toNat]?

abbrev Resident (σ : LPSignature.{u,u,p,u}) := Word × Descriptor σ

variable {n : ℕ}

def Directory.Represents (codes : PackedOccurrences.Codes (GroundTerm σ)) (directory : Directory σ n)
    (levels : ℕ → Match (GroundTerm σ) (Bindings σ)) (selected : Fin n → Resident σ) (state : Native) : Prop :=
  ∀ index,
    Reads state (directory.root index) (selected index).1 ∧
      directory.lookup (selected index).1 = some (selected index).2 ∧
      (selected index).2.Represents codes state (levels index.val)

def Directory.protected (directory : Directory σ n) (selected : Fin n → Resident σ)
    (index : Fin n) : Finset ℕ :=
  footprint (directory.root index) ∪ (selected index).2.bank.writes

theorem Directory.preserved (codes : PackedOccurrences.Codes (GroundTerm σ))
    {directory : Directory σ n} {before after : Native}
    {levels : ℕ → Match (GroundTerm σ) (Bindings σ)} {selected : Fin n → Resident σ}
    {written : Finset ℕ} {registers : Finset Register}
    (represented : directory.Represents codes levels selected before)
    (frame : X86StateFrame.Frame registers written before after)
    (safe : ∀ index, Disjoint (directory.protected selected index) written) :
    directory.Represents codes levels selected after := by
  intro index
  obtain ⟨pointer, known, meaning⟩ := represented index
  exact ⟨pointer.preserved frame ((safe index).mono_left Finset.subset_union_left), known,
    Descriptor.preserved codes meaning frame ((safe index).mono_left Finset.subset_union_right)⟩

/-- One root store changes exactly one view. All other published
levels keep both their handle and their binding words. -/
theorem Directory.retarget (codes : PackedOccurrences.Codes (GroundTerm σ))
    {directory : Directory σ n} {before after : Native}
    {levels : ℕ → Match (GroundTerm σ) (Bindings σ)} {selected : Fin n → Resident σ}
    {index : Fin n} {handle : Word} {descriptor : Descriptor σ} {next : Match (GroundTerm σ) (Bindings σ)}
    {registers : Finset Register} (represented : directory.Represents codes levels selected before)
    (frame : X86StateFrame.Frame registers (footprint (directory.root index)) before after)
    (safe : ∀ other, other ≠ index → Disjoint (directory.protected selected other) (footprint (directory.root index)))
    (pointer : Reads after (directory.root index) handle)
    (known : directory.lookup handle = some descriptor) (meaning : descriptor.Represents codes after next) :
    directory.Represents codes (Function.update levels index.val next)
      (Function.update selected index (handle, descriptor)) after := by
  intro other
  by_cases isTarget : other = index
  · subst other
    simpa only [Function.update_self] using And.intro pointer (And.intro known meaning)
  · have distinct : other.val ≠ index.val := fun same => isTarget (Fin.ext same)
    rw [Function.update_of_ne isTarget, Function.update_of_ne distinct]
    obtain ⟨old, encoded, observed⟩ := represented other
    exact ⟨old.preserved frame ((safe other isTarget).mono_left Finset.subset_union_left), encoded,
      Descriptor.preserved codes observed frame ((safe other isTarget).mono_left Finset.subset_union_right)⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeLevels
