import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationOrders

/-!
# Similar blocks with replication

Two components are **alike** (`AlikeR`) when they use the same variables, are both replications or neither, and
every renaming of them reads canonically alike (`recanon`). Two blocks are **similar** (`SimilarR`) when they have the
same number of restrictions and the components of one, read under some order of the restrictions, are alike to the
components of the other in some order.

The readings of a block are its sorted components with parts read again, under each of its reading orders
(`readingOrders`), one of each replicated component kept (`readingsR`); similar blocks have the same readings (`readingsR_same`), so the
least reading, the canonical form's last step, is the same (`least_reading_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {block : ReplicationBlock}

/-- **Alike components**: the same variables, both replications or neither, every injective renaming read alike,
and, for replications, every injective renaming of their arguments with one canonical form. -/
def AlikeR (block : ReplicationBlock) (first second : Pattern) : Prop :=
  (∀ index, FreeIn index first ↔ FreeIn index second) ∧
    isReplicated block first = isReplicated block second ∧
    (∀ relabel, Function.Injective relabel →
      recanon block (rename relabel first) = recanon block (rename relabel second)) ∧
    (isReplicated block first = true → ∀ relabel, Function.Injective relabel →
      canonicalOf block (rename relabel (argumentOf? first)) =
        canonicalOf block (rename relabel (argumentOf? second)))

theorem AlikeR.refl (component : Pattern) : AlikeR block component component :=
  ⟨fun _ => Iff.rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem AlikeR.symm {first second : Pattern} (alike : AlikeR block first second) : AlikeR block second first :=
  ⟨fun index => (alike.1 index).symm, alike.2.1.symm, fun relabel injective => (alike.2.2.1 relabel injective).symm,
    fun replicated relabel injective => (alike.2.2.2 (alike.2.1.trans replicated) relabel injective).symm⟩

theorem AlikeR.trans {first second third : Pattern} (alike : AlikeR block first second)
    (alike' : AlikeR block second third) : AlikeR block first third :=
  ⟨fun index => (alike.1 index).trans (alike'.1 index), alike.2.1.trans alike'.2.1,
    fun relabel injective => (alike.2.2.1 relabel injective).trans (alike'.2.2.1 relabel injective),
    fun replicated relabel injective => (alike.2.2.2 replicated relabel injective).trans
      (alike'.2.2.2 (alike.2.1.symm.trans replicated) relabel injective)⟩

/-- Renaming commutes with taking the argument of a replication. -/
theorem argumentOf?_rename (relabel : Nat → Nat) (component : Pattern) :
    argumentOf? (rename relabel component) = rename relabel (argumentOf? component) := by
  cases component with
  | apply constructor arguments =>
      rw [rename_apply]
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      · rfl
      · simp [argumentOf?]
      · rw [show argumentOf? (Pattern.apply constructor (first :: second :: rest)) =
          Pattern.apply constructor (first :: second :: rest) from rfl, rename_apply]
        rfl
  | bvar => rfl
  | fvar => rfl
  | lambda => rfl
  | multiLambda => rfl
  | subst => rfl
  | collection => rfl

theorem AlikeR.rename {first second : Pattern} (alike : AlikeR block first second) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) :
    AlikeR block (rename relabel first) (rename relabel second) := by
  refine ⟨fun index => ?_, ?_, fun outer outerInjective => ?_, fun replicated outer outerInjective => ?_⟩
  · rw [freeIn_rename, freeIn_rename]
    exact exists_congr fun original => and_congr_left fun _ => alike.1 original
  · rw [isReplicated_rename, isReplicated_rename]
    exact alike.2.1
  · rw [rename_comp, rename_comp]
    exact alike.2.2.1 (outer ∘ relabel) (outerInjective.comp injective)
  · rw [isReplicated_rename] at replicated
    rw [argumentOf?_rename, argumentOf?_rename, rename_comp, rename_comp]
    exact alike.2.2.2 replicated (outer ∘ relabel) (outerInjective.comp injective)

/-- **Similar blocks**: the same number of restrictions, and the components of one, read under some order of the
restrictions, alike to the components of the other in some order. -/
def SimilarR (block : ReplicationBlock) (first second : Prenex) : Prop :=
  first.count = second.count ∧ ∃ order middle, IsOrder first.count order ∧
    List.Forall₂ (AlikeR block) (first.components.map (rename (Prenex.permute first.count order))) middle ∧
    middle.Perm second.components

/-- **The readings of a block**: its sorted components with parts read again, one of each replicated component,
under each of its reading orders. -/
def readingsR (block : ReplicationBlock) (form : Prenex) : List (List Pattern) :=
  (readingOrders block form).map fun order =>
    dedupReplicated block (sortComponents (form.components.map fun component =>
      recanon block (rename (Prenex.permute form.count order) component)))

theorem readingsR_ne_nil (form : Prenex) : readingsR block form ≠ [] := by
  simpa [readingsR] using readingOrders_ne_nil (block := block) form

theorem recanon_map_forall₂ {first second : List Pattern} {relabel : Nat → Nat}
    (injective : Function.Injective relabel) (related : List.Forall₂ (AlikeR block) first second) :
    first.map (fun component => recanon block (rename relabel component)) =
      second.map (fun component => recanon block (rename relabel component)) := by
  induction related with
  | nil => rfl
  | cons here _ recurse => simp only [List.map_cons, here.2.2.1 relabel injective, recurse]

/-- **Similar blocks have the same readings.** -/
theorem readingsR_same {first second : Prenex} (similar : SimilarR block first second) :
    ∀ reading, reading ∈ readingsR block first ↔ reading ∈ readingsR block second := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  simp only at countEq isOrder related permutation
  subst countEq
  have through : ∀ (outer : List Nat), IsOrder count outer →
      dedupReplicated block (sortComponents (secondComponents.map fun component =>
          recanon block (rename (Prenex.permute count outer) component))) =
        dedupReplicated block (sortComponents (firstComponents.map fun component =>
          recanon block (rename (Prenex.permute count outer ∘ Prenex.permute count order) component))) := by
    intro outer outerOrder
    congr 1
    rw [← sortComponents_perm (permutation.map _), ← recanon_map_forall₂ (permute_injective outerOrder) related,
      List.map_map]
    congr 1
    exact List.map_congr_left fun component _ => by simp only [Function.comp, rename_comp]
  -- the second block's signatures are the first's carried along the order
  have signatures : ∀ index < count, signatureOf block ⟨count, secondComponents⟩ (Prenex.permute count order index) =
      signatureOf block ⟨count, firstComponents⟩ index := by
    intro index inside
    have keeps : List.Forall₂ (fun one other => (∀ index < count, mentions index one = mentions index other) ∧
        isReplicated block one = isReplicated block other)
        (firstComponents.map (rename (Prenex.permute count order))) middle :=
      related.imp fun _ _ alike =>
        ⟨fun index _ => Bool.eq_iff_iff.mpr (by rw [mentions_iff, mentions_iff]; exact alike.1 index), alike.2.1⟩
    rw [signatureOf_congr (first := ⟨count, secondComponents⟩) (second := ⟨count, middle⟩) rfl
        (fun component => permutation.mem_iff.symm),
      ← signatureOf_forall₂ keeps (permute_lt isOrder inside), signatureOf_rename isOrder]
  intro reading
  simp only [readingsR, List.mem_map]
  constructor
  · rintro ⟨outer, outerMember, rfl⟩
    have outerOrder : IsOrder count outer := readingOrders_isOrder outerMember
    have composite := outerOrder.comp (inverse_isOrder isOrder)
    refine ⟨(inverse count order).map (Prenex.permute count outer),
      readingOrders_transport_inverse (first := ⟨count, firstComponents⟩) (second := ⟨count, secondComponents⟩) rfl
        isOrder signatures outerMember, ?_⟩
    rw [through _ composite, ← permute_comp outer (inverse_isOrder isOrder), Function.comp_assoc,
      permute_inverse isOrder]
    rfl
  · rintro ⟨outer, outerMember, rfl⟩
    have outerOrder : IsOrder count outer := readingOrders_isOrder outerMember
    refine ⟨order.map (Prenex.permute count outer),
      readingOrders_transport (first := ⟨count, firstComponents⟩) (second := ⟨count, secondComponents⟩) rfl isOrder
        signatures outerMember, ?_⟩
    rw [through _ outerOrder, permute_comp outer isOrder]

/-- **Similar blocks have one least reading.** -/
theorem least_reading_eq {first second : Prenex} (similar : SimilarR block first second) :
    (⟨first.count, least (readingsR block first)⟩ : Prenex) = ⟨second.count, least (readingsR block second)⟩ := by
  rw [similar.1, least_eq_of_same (readingsR_ne_nil _) (readingsR_ne_nil _) (readingsR_same similar)]

/-- **The canonical form of a block is the least reading of its absorbed block.** -/
theorem normal_eq_reading (form : Prenex) :
    normal block form = ⟨(absorb block (canonicalOf block) form).count,
      least (readingsR block (absorb block (canonicalOf block) form))⟩ := by
  rw [normal_unfold]
  rfl

/-- **The least reading is a reading**, under some order of the restrictions. -/
theorem least_reading_mem (form : Prenex) :
    ∃ order ∈ readingOrders block form, least (readingsR block form) =
      dedupReplicated block (sortComponents (form.components.map fun component =>
        recanon block (rename (Prenex.permute form.count order) component))) := by
  have member := least_mem (readingsR_ne_nil (block := block) form)
  simp only [readingsR, List.mem_map] at member
  obtain ⟨order, inOrders, same⟩ := member
  exact ⟨order, inOrders, same.symm⟩

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
