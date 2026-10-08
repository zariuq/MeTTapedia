import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift

/-!
# Growing families with genuinely different attached material bodies

At every stage a new native receipt appears. The zero receipt carries a
cyclic graph value; every positive receipt carries a terminal value. The
attached construction preserves this exact two-class material kernel,
while retaining all distinct positive receipts and their context action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFamilyBodies ContextualGraphFamilyBodyComparison
open ContextualGraphFamilyControls (unitBase growing parameter stageStep)

def bodies : Diagram Nat where
  nodes := {
    obj stage := Fin (stage+1)
    map {_first _second} arrival := TypeCat.ofHom fun node =>
      ⟨node.val, Nat.lt_of_lt_of_le node.isLt (Nat.succ_le_succ (leOfHom arrival))⟩
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ first second := first.val = 0 ∧ second.val = 0
  edge_transport := fun {_ _} _ {_ _} available => available

def reading : NaturalHom (total growing) (values Nat) where
  app _ receipt := ⟨bodies, receipt.2⟩
  naturality _ _ := rfl

def material (stage : Nat) (index : Fin (stage+1)) : Value Nat stage := ⟨bodies, index⟩

def terminalEquality (stage : Nat) (first second : Fin (stage+1))
    (firstNonzero : first.val ≠ 0) (secondNonzero : second.val ≠ 0) :
    Equal (material stage first) (material stage second) :=
  ContextualGraphRealizers.roll bodies bodies
    (fun _ child => False.elim (firstNonzero child.property.1))
    (fun _ child => False.elim (secondNonzero child.property.1))

theorem matching_preserves_zero (stage : Nat) (first second : Fin (stage+1))
    (matching : Equal (material stage first) (material stage second)) (firstZero : first.val = 0) :
    second.val = 0 := by
  let receipt : Child Nat (material stage first) := ⟨first, firstZero, firstZero⟩
  exact (ContextualGraphRealizers.Realizer.currentForth matching receipt).1.property.1

theorem exact_material_kernel (stage : Nat) (first second : Fin (stage+1)) :
    Nonempty (Equal (material stage first) (material stage second)) ↔
      (first.val = 0 ↔ second.val = 0) := by
  constructor
  · rintro ⟨matching⟩
    exact ⟨matching_preserves_zero stage first second matching,
      matching_preserves_zero stage second first matching.symm⟩
  · intro agree
    by_cases firstZero : first.val = 0
    · have same : first = second := Fin.ext (firstZero.trans (agree.mp firstZero).symm)
      exact ⟨Equal.ofEq (congrArg (material stage) same)⟩
    · exact ⟨terminalEquality stage first second firstZero (fun zero => firstZero (agree.mpr zero))⟩

def retained (stage : Nat) (index : Fin (stage+1)) : (literal growing reading).obj (parameter stage) :=
  encode growing reading (parameter stage) index

def attached (stage : Nat) (index : Fin (stage+1)) : Value Nat stage :=
  childValue Nat (carrier growing reading stage PUnit.unit) (retained stage index)

def body_is_retained (stage : Nat) (index : Fin (stage+1)) :
    Equal (material stage index) (attached stage index) :=
  childComparison growing reading (parameter stage) index

theorem attached_exact_kernel (stage : Nat) (first second : Fin (stage+1)) :
    Nonempty (Equal (attached stage first) (attached stage second)) ↔
      (first.val = 0 ↔ second.val = 0) := by
  constructor
  · rintro ⟨matching⟩
    exact (exact_material_kernel stage first second).mp
      ⟨(body_is_retained stage first).trans (matching.trans (body_is_retained stage second).symm)⟩
  · intro agree
    obtain ⟨matching⟩ := (exact_material_kernel stage first second).mpr agree
    exact ⟨(body_is_retained stage first).symm.trans (matching.trans (body_is_retained stage second))⟩

def cyclic_member : Member (material 1 ⟨0, by decide⟩) (carrier growing reading 1 PUnit.unit) :=
  memberIntro growing reading (parameter 1) _ ⟨0, by decide⟩ (Equal.refl _)

def terminal_member : Member (material 1 ⟨1, by decide⟩) (carrier growing reading 1 PUnit.unit) :=
  memberIntro growing reading (parameter 1) _ ⟨1, by decide⟩ (Equal.refl _)

theorem cyclic_terminal_distinguished :
    ¬ Nonempty (Equal (attached 1 ⟨0, by decide⟩) (attached 1 ⟨1, by decide⟩)) := by
  intro same
  exact (by decide : ¬ (1 : Nat) = 0)
    (((attached_exact_kernel 1 ⟨0, by decide⟩ ⟨1, by decide⟩).mp same).mp rfl)

theorem positive_bodies_match :
    Nonempty (Equal (attached 2 ⟨1, by decide⟩) (attached 2 ⟨2, by decide⟩)) :=
  (attached_exact_kernel 2 ⟨1, by decide⟩ ⟨2, by decide⟩).mpr (by decide)

theorem positive_receipts_distinct : retained 2 ⟨1, by decide⟩ ≠ retained 2 ⟨2, by decide⟩ := by
  intro same
  have decoded := congrArg (decode growing reading (parameter 2)) same
  exact (by decide : ¬ (1 : Nat) = 2) (congrArg Fin.val decoded)

theorem attached_family_grows (stage : Nat) :
    ¬ ∃ earlier : (literal growing reading).obj (parameter stage),
      (literal growing reading).map (stageStep stage) earlier =
        retained (stage+1) ⟨stage+1, Nat.lt_succ_self _⟩ := by
  rintro ⟨earlier, same⟩
  have decoded := (decode_naturality growing reading (stageStep stage) earlier).symm.trans
    (congrArg (decode growing reading (parameter (stage+1))) same)
  exact (Nat.ne_of_lt (decode growing reading (parameter stage) earlier).isLt) (congrArg Fin.val decoded)

def cyclicSection : growing.sections :=
  ⟨fun _point => ⟨0, Nat.succ_pos _⟩, fun {_ _} _ => rfl⟩

def retainedSection : (literal growing reading).sections := (sectionDecoder growing reading).symm cyclicSection

def whole_section_material (point : unitBase.Elements) :
    Equal (material point.1 ⟨0, Nat.succ_pos _⟩)
      ((ContextualGraphReceiptFamilies.sectionReading (parent growing reading) retainedSection).app point.1 point.2) :=
  sectionComparison growing reading retainedSection point

/-- The actual successor raise retains both distinctions and collisions
of this infinite varying family. -/
theorem raised_exact_kernel (stage : Nat) (first second : Fin (stage+1)) :
    Nonempty (Equal
      (ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj stage) (attached stage first))
      (ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj stage) (attached stage second))) ↔
      (first.val = 0 ↔ second.val = 0) :=
  (ContextualGraphUniverseLift.matching_iff (attached stage first) (attached stage second)).trans
    (attached_exact_kernel stage first second)

theorem raised_cyclic_terminal_distinguished :
    ¬ Nonempty (Equal
      (ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj 1) (attached 1 ⟨0, by decide⟩))
      (ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj 1) (attached 1 ⟨1, by decide⟩))) := by
  intro same
  exact cyclic_terminal_distinguished ((ContextualGraphUniverseLift.matching_iff _ _).mp same)

theorem raised_positive_bodies_match :
    Nonempty (Equal
      (ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj 2) (attached 2 ⟨1, by decide⟩))
      (ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj 2) (attached 2 ⟨2, by decide⟩))) :=
  (ContextualGraphUniverseLift.matching_iff _ _).mpr positive_bodies_match

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyControls
