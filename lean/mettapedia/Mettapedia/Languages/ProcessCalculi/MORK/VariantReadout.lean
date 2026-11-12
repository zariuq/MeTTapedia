import Mettapedia.Data.List.FirstOccurrence
import Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming
import Std.Data.String.ToNat

/-!
# A canonical observation of finite variable-sharing patterns

Variables receive their first occurrence positions, printed as decimal names.
These are observation labels, not fresh executable identities. A basis retains
the inverse transport when the observed term must be restored to its world.
Symbols, grounded data, expression shape, order and multiplicity stay exact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open AtomRenaming (Variant)

def label (basis : List String) (name : String) : String := Nat.repr (basis.idxOf name)

def restoreLabel (basis : List String) (name : String) : String :=
  match name.toNat? with
  | none => name
  | some index => List.FirstOccurrence.decode basis name index

def normalize (term : Atom) : Atom := AtomRenaming.rename (label (atomFreeVars term)) term

theorem restore_label (basis : List String) (name : String) (present : name ∈ basis) :
    restoreLabel basis (label basis name) = name := by
  simp only [restoreLabel,label,Nat.toNat?_repr]
  exact List.FirstOccurrence.decode_index basis _ name present

theorem label_reflects_equality (basis : List String) (first second : String) (present : first ∈ basis) :
    label basis first = label basis second ↔ first = second := by
  constructor
  · intro same
    exact (List.idxOf_inj present).mp (Nat.repr_injective same)
  · rintro rfl; rfl

theorem restore_normalize (term : Atom) :
    AtomRenaming.rename (restoreLabel (atomFreeVars term)) (normalize term) = term := by
  rw [normalize,AtomRenaming.composition]
  calc
    AtomRenaming.rename (restoreLabel (atomFreeVars term) ∘ label (atomFreeVars term)) term =
        AtomRenaming.rename id term := by
      apply (AtomRenaming.equal_iff_on_variables _ _ term).mpr
      intro name present
      exact restore_label _ name present
    _ = term := AtomRenaming.identity term

theorem variant_normalize (term : Atom) : Variant term (normalize term) :=
  ⟨label (atomFreeVars term),restoreLabel (atomFreeVars term),rfl,restore_normalize term⟩

/-- Only injectivity on the observed support is needed. Other names may be
identified without affecting this finite observation. -/
theorem normalize_rename (term : Atom) (names : String → String)
    (injective : ∀ first ∈ atomFreeVars term, ∀ second ∈ atomFreeVars term,
      names first = names second → first = second) :
    normalize (AtomRenaming.rename names term) = normalize term := by
  simp only [normalize,AtomRenaming.freeVars_rename,AtomRenaming.composition]
  apply (AtomRenaming.equal_iff_on_variables _ _ term).mpr
  intro name present
  exact congrArg Nat.repr (List.FirstOccurrence.index_map names _ name present injective)

theorem normalize_of_variant {first second : Atom} (same : Variant first second) :
    normalize first = normalize second := by
  obtain ⟨forward,backward,changed,recovered⟩ := same
  have retract : AtomRenaming.rename backward (AtomRenaming.rename forward first) = first := by
    rw [changed,recovered]
  have invariant := normalize_rename first forward
    (AtomRenaming.retraction_injective_on_variables first forward backward retract)
  rw [changed] at invariant
  exact invariant.symm

/-- Equality of computed observations preserves and reflects independently
specified bidirectional finite renaming. It does not define that relation. -/
theorem normalize_equal_iff_variant (first second : Atom) :
    normalize first = normalize second ↔ Variant first second := by
  constructor
  · intro same
    have recoverSecond : Variant (normalize first) second := by
      rw [same]
      exact (variant_normalize second).symm
    exact (variant_normalize first).trans recoverSecond
  · exact normalize_of_variant

theorem normalize_idempotent (term : Atom) : normalize (normalize term) = normalize term :=
  (normalize_of_variant (variant_normalize term)).symm

theorem normalize_closed (term : Atom) (closed : atomFreeVars term = []) : normalize term = term := by
  calc
    normalize term = AtomRenaming.rename id term := by
      apply (AtomRenaming.equal_iff_on_variables _ _ term).mpr
      simp [closed]
    _ = term := AtomRenaming.identity term

/-- The inverse basis is retained for transport back to the originating
world. The displayed values alone are an observation of sharing. -/
structure Packet where
  basis : List String
  values : List Atom
  deriving DecidableEq, Repr

def pack (values : List Atom) : Packet :=
  let basis := atomFreeVars (.expression values)
  ⟨basis,AtomRenaming.rename.list (label basis) values⟩

def restore (packet : Packet) : List Atom :=
  AtomRenaming.rename.list (restoreLabel packet.basis) packet.values

theorem pack_as_root (values : List Atom) :
    .expression (pack values).values = normalize (.expression values) := rfl

theorem restore_pack (values : List Atom) : restore (pack values) = values := by
  have recovered := restore_normalize (.expression values)
  change Atom.expression (restore (pack values)) = .expression values at recovered
  exact Atom.expression.inj recovered

theorem pack_length (values : List Atom) : (pack values).values.length = values.length := by
  simp [pack,AtomRenaming.list_eq_map]

def joint (values : List Atom) : List Atom := (pack values).values
def each (values : List Atom) : List Atom := values.map normalize

theorem joint_equal_iff_variant (first second : List Atom) :
    joint first = joint second ↔ Variant (.expression first) (.expression second) := by
  rw [← normalize_equal_iff_variant]
  simp only [normalize,AtomRenaming.rename,joint,pack,Atom.expression.injEq]

theorem each_rename (values : List Atom) (names : String → String)
    (injective : ∀ first ∈ atomFreeVars (.expression values),
      ∀ second ∈ atomFreeVars (.expression values), names first = names second → first = second) :
    each (AtomRenaming.rename.list names values) = each values := by
  simp only [each,AtomRenaming.list_eq_map,List.map_map]
  apply List.map_congr_left
  intro term present
  apply normalize_rename
  intro first firstIn second secondIn same
  exact injective first (AtomRenaming.variables_expression.mpr ⟨term,present,firstIn⟩)
    second (AtomRenaming.variables_expression.mpr ⟨term,present,secondIn⟩) same

/-- A joint observation determines every individual observation. The reverse
would discard possible sharing across answer occurrences. -/
theorem each_of_joint_equal {first second : List Atom} (same : joint first = joint second) :
    each first = each second := by
  obtain ⟨forward,backward,changed,recovered⟩ := (joint_equal_iff_variant first second).mp same
  have retract : AtomRenaming.rename backward (AtomRenaming.rename forward (.expression first)) =
      .expression first := by rw [changed,recovered]
  have invariant := each_rename first forward
    (AtomRenaming.retraction_injective_on_variables (.expression first) forward backward retract)
  have lists : AtomRenaming.rename.list forward first = second := Atom.expression.inj changed
  rw [lists] at invariant
  exact invariant.symm

end Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout
