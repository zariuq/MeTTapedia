import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceIdentification
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Pushout squares for physical selections with aliased read ports

The rule interface consists of read positions, which may select the same
physical occurrence. Take positions remain distinct and cannot meet the
retained context. The universal property is in the category of types and
functions; equation solving and term labels remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadPortPushouts

open CategoryTheory CategoryTheory.Limits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u

/-- A sum of exclusive ports and interface ports is glued to a context.
Only the interface map may identify positions. -/
theorem sum_interface_pushout {I K D G : Type u}
    (consume : I → G) (read : K → G) (included : D → G) (kept : K → D)
    (commutes : ∀ k, included (kept k) = read k)
    (context_injective : Function.Injective included)
    (consume_injective : Function.Injective consume)
    (exclusive : ∀ i d, consume i ≠ included d)
    (covered : ∀ g, (∃ i, consume i = g) ∨ ∃ d, included d = g) :
    IsPushout (↾(Sum.inr : K → I ⊕ K)) (↾kept)
      (↾(Sum.elim consume read)) (↾included) := by
  have pull : IsPullback (↾kept) (↾(Sum.inr : K → I ⊕ K))
      (↾included) (↾(Sum.elim consume read)) := by
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext k
      exact commutes k
    · intro x y same
      exact Sum.inr.inj same.2
    · intro d port same
      cases port with
      | inl i => exact False.elim (exclusive i d same.symm)
      | inr k =>
          refine ⟨k, ?_, rfl⟩
          exact context_injective ((commutes k).trans same.symm)
  have : Mono (↾included) := (mono_iff_injective _).mpr context_injective
  have surjective : Set.range (↾included) ⊔ Set.range (↾(Sum.elim consume read)) = Set.univ := by
    ext g
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    rcases covered g with ⟨i, same⟩ | ⟨d, same⟩
    · exact Or.inr ⟨Sum.inl i, same⟩
    · exact Or.inl ⟨d, same⟩
  have off_interface : ∀ (x y : I ⊕ K),
      x ∉ Set.range (↾(Sum.inr : K → I ⊕ K)) →
      y ∉ Set.range (↾(Sum.inr : K → I ⊕ K)) →
      Sum.elim consume read x = Sum.elim consume read y → x = y := by
    intro x y xOutside yOutside same
    cases x with
    | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (consume_injective same)
        | inr k => exact False.elim (yOutside ⟨k, rfl⟩)
    | inr k => exact False.elim (xOutside ⟨k, rfl⟩)
  exact (Types.isPushout_of_isPullback_of_mono' pull surjective off_interface).flip

variable {O : Type u} [DecidableEq O]

/-- Lifted positions let finite ports and occurrence supplies share a universe. -/
abbrev Port (rows : List O) : Type u := ULift.{u} (Fin rows.length)

abbrev Rows (state : Finset O) : Type u := { occurrence // occurrence ∈ state }

def portValue (rows : List O) (port : Port rows) : O := rows.get port.down

theorem portValue_mem (rows : List O) (port : Port rows) : portValue rows port ∈ rows.toFinset :=
  List.mem_toFinset.mpr (List.get_mem ..)

omit [DecidableEq O] in
theorem portValue_injective {rows : List O} (distinct : rows.Nodup) : Function.Injective (portValue rows) := by
  intro first second same
  apply ULift.ext
  exact List.nodup_iff_injective_get.mp distinct same

def inclusion {first second : Finset O} (subset : first ⊆ second) : Rows first → Rows second :=
  fun occurrence => ⟨occurrence.val, subset occurrence.property⟩

omit [DecidableEq O] in
theorem inclusion_injective {first second : Finset O} (subset : first ⊆ second) :
    Function.Injective (inclusion subset) := by
  intro x y same
  exact Subtype.ext (congrArg (fun (row : Rows second) => row.val) same)

def retained (state : Finset O) (selection : Selection O) : Finset O :=
  state \ selection.taken.toFinset

def leftSupport (selection : Selection O) : Finset O :=
  selection.taken.toFinset ∪ selection.read.toFinset

def readQuotient (selection : Selection O) : Port selection.read → Rows selection.read.toFinset :=
  fun port => ⟨portValue selection.read port, portValue_mem ..⟩

theorem readQuotient_surjective (selection : Selection O) :
    Function.Surjective (readQuotient selection) := by
  intro occurrence
  obtain ⟨index, same⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp occurrence.property)
  exact ⟨⟨index⟩, Subtype.ext same⟩

def supportRead (selection : Selection O) : Rows selection.read.toFinset → Rows (leftSupport selection) :=
  inclusion Finset.subset_union_right

def supportTake (selection : Selection O) : Port selection.taken → Rows (leftSupport selection) :=
  fun port => ⟨portValue selection.taken port, Finset.mem_union_left _ (portValue_mem ..)⟩

def quotientLeft (selection : Selection O) :
    Port selection.taken ⊕ Port selection.read → Rows (leftSupport selection) :=
  Sum.elim (supportTake selection) (supportRead selection ∘ readQuotient selection)

/-- The quotient identifying repeated reads is itself a pushout. No take
position is identified with another position. -/
theorem read_gluing_pushout (selection : Selection O)
    (identification : OccurrenceIdentification.IdentificationCondition selection) :
    IsPushout (↾(Sum.inr : Port selection.read → Port selection.taken ⊕ Port selection.read))
      (↾(readQuotient selection)) (↾(quotientLeft selection)) (↾(supportRead selection)) := by
  obtain ⟨distinct, apart⟩ := (OccurrenceIdentification.identification_iff selection).mp identification
  apply sum_interface_pushout (supportTake selection)
      (supportRead selection ∘ readQuotient selection) (supportRead selection)
      (readQuotient selection) (fun _ => rfl) (inclusion_injective _)
  · intro first second same
    exact portValue_injective distinct (congrArg Subtype.val same)
  · intro port occurrence same
    have equalValues : portValue selection.taken port = occurrence.val := congrArg Subtype.val same
    exact Finset.disjoint_left.mp apart (portValue_mem selection.taken port)
      (equalValues.symm ▸ occurrence.property)
  · intro occurrence
    rcases Finset.mem_union.mp occurrence.property with taken | read
    · obtain ⟨index, same⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp taken)
      exact Or.inl ⟨⟨index⟩, Subtype.ext same⟩
    · exact Or.inr ⟨⟨occurrence.val, read⟩, rfl⟩

theorem quotientLeft_surjective (selection : Selection O) :
    Function.Surjective (quotientLeft selection) := by
  intro occurrence
  rcases Finset.mem_union.mp occurrence.property with taken | read
  · obtain ⟨index, same⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp taken)
    exact ⟨Sum.inl ⟨index⟩, Subtype.ext same⟩
  · obtain ⟨index, same⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp read)
    exact ⟨Sum.inr ⟨index⟩, Subtype.ext same⟩

section Selection

variable {T S : Type*} {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A label rule before)

def consumed : Port selection.taken → Rows before.present :=
  fun port => ⟨portValue selection.taken port, valid.occurrences.taken_subset (portValue_mem ..)⟩

def readContext : Port selection.read → Rows (retained before.present selection) :=
  fun port => ⟨portValue selection.read port, Finset.mem_sdiff.mpr
    ⟨valid.occurrences.kept_subset (portValue_mem ..),
      Finset.disjoint_right.mp valid.occurrences.apart (portValue_mem ..)⟩⟩

def contextBefore : Rows (retained before.present selection) → Rows before.present :=
  inclusion Finset.sdiff_subset

def leftMatch : Port selection.taken ⊕ Port selection.read → Rows before.present :=
  Sum.elim (consumed valid) (contextBefore ∘ readContext valid)

def supportBefore : Rows (leftSupport selection) → Rows before.present :=
  inclusion (Finset.union_subset valid.occurrences.taken_subset valid.occurrences.kept_subset)

theorem supportBefore_injective : Function.Injective (supportBefore valid) :=
  inclusion_injective _

/-- The physical match is the read-gluing quotient followed by an inclusion. -/
theorem leftMatch_factors : leftMatch valid = supportBefore valid ∘ quotientLeft selection := by
  funext port
  cases port <;> rfl

/-- Erasing only the membership witnesses recovers the original ordered
selection map, including every repeated read position. -/
theorem leftMatch_value (port : Port selection.taken ⊕ Port selection.read) :
    (leftMatch valid port).val = OccurrenceIdentification.portMatch selection
      (Sum.map ULift.down ULift.down port) := by
  cases port <;> rfl

/-- The actual physical left square, including repeated read positions. -/
theorem left_pushout :
    IsPushout (↾(Sum.inr : Port selection.read → Port selection.taken ⊕ Port selection.read))
      (↾(readContext valid)) (↾(leftMatch valid)) (↾(contextBefore (selection := selection))) := by
  apply sum_interface_pushout (consumed valid) (contextBefore ∘ readContext valid)
      contextBefore (readContext valid) (fun _ => rfl) (inclusion_injective _)
  · intro first second same
    exact portValue_injective valid.take_distinct (congrArg Subtype.val same)
  · intro port occurrence same
    have membership := (Finset.mem_sdiff.mp occurrence.property).2
    exact membership ((congrArg Subtype.val same) ▸ portValue_mem selection.taken port)
  · intro occurrence
    by_cases taken : occurrence.val ∈ selection.taken.toFinset
    · obtain ⟨index, same⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp taken)
      exact Or.inl ⟨⟨index⟩, Subtype.ext same⟩
    · exact Or.inr ⟨⟨occurrence.val, Finset.mem_sdiff.mpr ⟨occurrence.property, taken⟩⟩, rfl⟩

def produced : Port selection.made → Rows (selection.result label rule before).present :=
  fun port => ⟨portValue selection.made port, Finset.mem_union_right _ (portValue_mem ..)⟩

def contextAfter : Rows (retained before.present selection) →
    Rows (selection.result label rule before).present :=
  inclusion Finset.subset_union_left

def rightMatch : Port selection.made ⊕ Port selection.read →
    Rows (selection.result label rule before).present :=
  Sum.elim produced (contextAfter ∘ readContext valid)

/-- Fresh outputs and the retained context give the actual physical right square. -/
theorem right_pushout :
    IsPushout (↾(Sum.inr : Port selection.read → Port selection.made ⊕ Port selection.read))
      (↾(readContext valid)) (↾(rightMatch valid)) (↾(contextAfter (label := label) (rule := rule))) := by
  apply sum_interface_pushout produced (contextAfter ∘ readContext valid)
      contextAfter (readContext valid) (fun _ => rfl) (inclusion_injective _)
  · intro first second same
    exact portValue_injective valid.output_distinct (congrArg Subtype.val same)
  · intro port occurrence same
    have old := (Finset.mem_sdiff.mp occurrence.property).1
    have fresh := Finset.disjoint_left.mp valid.occurrences.fresh (portValue_mem selection.made port)
    have equalValues : portValue selection.made port = occurrence.val := congrArg Subtype.val same
    exact fresh (equalValues.symm ▸ old)
  · intro occurrence
    rcases Finset.mem_union.mp occurrence.property with kept | made
    · exact Or.inr ⟨⟨occurrence.val, kept⟩, rfl⟩
    · obtain ⟨index, same⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp made)
      exact Or.inl ⟨⟨index⟩, Subtype.ext same⟩

end Selection

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadPortPushouts
