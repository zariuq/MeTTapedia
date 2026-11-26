import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.GuardDependencies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MaximalOneExtension
import Mathlib.Data.List.FinRange

/-!
# Finite admission profiles

At one cut, resource and model compatibility is hereditary and entailment
of an individual member's guard is monotone in the other members. These two
properties characterize the rooted finite families closed under bounded
unions. The two real dependency programs below fit the same positive and
negative observations but cannot both be included in one such profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AdmissionProfiles

variable {ι : Type} [DecidableEq ι]

def BoundedUnionClosed (admits : Finset ι → Prop) : Prop :=
  ∀ {left right cap}, admits left → admits right → admits cap →
    left ⊆ cap → right ⊆ cap → admits (left ∪ right)

/-- The exact finite condition for hereditary compatibility and monotone guards. -/
theorem boundedUnionClosed_iff (admits : Finset ι → Prop) :
    (admits ∅ ∧ BoundedUnionClosed admits) ↔
    ∃ (compatible : Finset ι → Prop) (ask : ι → Finset ι → Prop),
      compatible ∅ ∧
      (∀ ⦃small large⦄, small ⊆ large → compatible large → compatible small) ∧
      (∀ i ⦃small large⦄, small ⊆ large → ask i small → ask i large) ∧
      ∀ group, admits group ↔ compatible group ∧ ∀ i ∈ group, ask i group := by
  constructor
  · rintro ⟨empty, unions⟩
    refine ⟨fun group => ∃ cap, admits cap ∧ group ⊆ cap,
      fun i group => ∃ support, admits support ∧ i ∈ support ∧ support ⊆ group,
      ⟨∅, empty, Finset.Subset.refl _⟩, ?_, ?_, ?_⟩
    · rintro small large included ⟨cap, capAdmits, upper⟩
      exact ⟨cap, capAdmits, included.trans upper⟩
    · rintro i small large included ⟨support, supportAdmits, inside, subset⟩
      exact ⟨support, supportAdmits, inside, subset.trans included⟩
    · intro group
      constructor
      · intro admitted
        exact ⟨⟨group, admitted, Finset.Subset.refl _⟩,
          fun i inside => ⟨group, admitted, inside, Finset.Subset.refl _⟩⟩
      · rintro ⟨⟨cap, capAdmits, upper⟩, every⟩
        have cover : ∀ chosen : Finset ι, chosen ⊆ group →
            ∃ support, admits support ∧ chosen ⊆ support ∧ support ⊆ group := by
          intro chosen
          induction chosen using Finset.induction_on with
          | empty =>
            intro _
            exact ⟨∅, empty, Finset.Subset.refl _, Finset.empty_subset _⟩
          | @insert i remaining outside ih =>
            intro included
            obtain ⟨left, leftAdmits, iLeft, leftInside⟩ :=
              every i (included (Finset.mem_insert_self i remaining))
            obtain ⟨right, rightAdmits, remainingRight, rightInside⟩ :=
              ih ((Finset.subset_insert i remaining).trans included)
            refine ⟨left ∪ right,
              unions leftAdmits rightAdmits capAdmits (leftInside.trans upper)
                (rightInside.trans upper), ?_, Finset.union_subset leftInside rightInside⟩
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | rest
            · exact Finset.mem_union_left _ iLeft
            · exact Finset.mem_union_right _ (remainingRight rest)
        obtain ⟨support, supportAdmits, includes, inside⟩ :=
          cover group (Finset.Subset.refl group)
        have same : support = group := Finset.Subset.antisymm inside includes
        exact same ▸ supportAdmits
  · rintro ⟨compatible, ask, empty, down, up, specification⟩
    refine ⟨(specification _).mpr ⟨empty, by simp⟩, ?_⟩
    intro left right cap leftAdmits rightAdmits capAdmits leftInside rightInside
    refine (specification _).mpr
      ⟨down (Finset.union_subset leftInside rightInside) ((specification _).mp capAdmits).1, ?_⟩
    intro i inside
    rcases Finset.mem_union.mp inside with fromLeft | fromRight
    · exact up i Finset.subset_union_left (((specification _).mp leftAdmits).2 i fromLeft)
    · exact up i Finset.subset_union_right (((specification _).mp rightAdmits).2 i fromRight)

#print axioms boundedUnionClosed_iff



section WitnessPositions

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uOcc uE

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- Select at the actual positions of a fixed witness list, retaining order
and allowing distinct positions to carry equal member values. -/
def atPositions {a : Obj} (cap : Bag O E P a) (positions : Finset (Fin cap.members.length)) :
    Bag O E P a :=
  cap.withMembers ((List.finRange cap.members.length).filter (fun i => decide (i ∈ positions))
    |>.map cap.members.get)

private theorem mem_atPositions {a : Obj} (cap : Bag O E P a)
    (positions : Finset (Fin cap.members.length)) (member : Member O E P cap.ext) :
    member ∈ (atPositions cap positions).members ↔
      ∃ i ∈ positions, cap.members.get i = member := by
  constructor
  · intro chosen
    obtain ⟨i, selected, equal⟩ := List.mem_map.mp chosen
    exact ⟨i, of_decide_eq_true (List.mem_filter.mp selected).2, equal⟩
  · rintro ⟨i, inside, equal⟩
    exact List.mem_map.mpr ⟨i, List.mem_filter.mpr
      ⟨List.mem_finRange _, decide_eq_true inside⟩, equal⟩

/-- A compatible list of real match witnesses admits unions of admitted
subselections by position. The cap need only fit, enable its resources and
have a common model. Its own guards may still be unresolved. -/
theorem admits_positions_union [DecidableEq O] (X : Frames Tm Hom)
    (inhabited : ∀ (rule : Rule Tm) (b : Obj), Nonempty (Hom rule.locals b))
    (s : State Tm O) (cap : Bag O E P s.frame)
    (fit : cap.Fits X s)
    (enabled : Enabled (fun _ : O => ()) s.present (cap.selection.commit (T := Unit)))
    (solved : X.Solvable (cap.information X s))
    (left right : Finset (Fin cap.members.length))
    (leftAdmits : (atPositions cap left).Admits X s)
    (rightAdmits : (atPositions cap right).Admits X s) :
    (atPositions cap (left ∪ right)).Admits X s := by
  refine Bag.admits_of_union_cover inhabited fit enabled solved ?_ ?_ ?_ ?_ leftAdmits rightAdmits
  · have sub := (List.filter_sublist (l := List.finRange cap.members.length)
      (p := fun i => decide (i ∈ left ∪ right))).map cap.members.get
    simpa only [atPositions, Bag.withMembers, List.map_get_finRange] using sub
  · intro m member
    obtain ⟨i, inside, rfl⟩ := (mem_atPositions cap left m).mp member
    exact (mem_atPositions cap _ _).mpr ⟨i, Finset.mem_union_left _ inside, rfl⟩
  · intro m member
    obtain ⟨i, inside, rfl⟩ := (mem_atPositions cap right m).mp member
    exact (mem_atPositions cap _ _).mpr ⟨i, Finset.mem_union_right _ inside, rfl⟩
  · intro m member
    obtain ⟨i, inside, rfl⟩ := (mem_atPositions cap (left ∪ right) m).mp member
    rcases Finset.mem_union.mp inside with before | after
    · exact Or.inl ((mem_atPositions cap _ _).mpr ⟨i, before, rfl⟩)
    · exact Or.inr ((mem_atPositions cap _ _).mpr ⟨i, after, rfl⟩)

end WitnessPositions

#print axioms admits_positions_union

section Pruning

variable (ask : ι → Finset ι → Prop) [∀ i group, Decidable (ask i group)]

/-- Descending entailment pruning under an exact guard test. -/
def prune (group : Finset ι) : Finset ι :=
  let next := group.filter fun i => ask i group
  if _unchanged : next = group then group else prune next
termination_by group.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, _unchanged⟩)

/-- Inside a compatible cap, pruning produces the greatest admitted
subgroup. An admitted subset survives each deletion by monotone entailment. -/
theorem prune_spec (up : ∀ i ⦃a b⦄, a ⊆ b → ask i a → ask i b) (group : Finset ι) :
    (prune ask group) ⊆ group ∧
      (∀ i ∈ prune ask group, ask i (prune ask group)) ∧
      ∀ subset ⊆ group, (∀ i ∈ subset, ask i subset) → subset ⊆ prune ask group := by
  rw [prune]
  split
  · rename_i fixed
    refine ⟨Finset.Subset.refl _, fun i inside => ?_, fun _ included _ => included⟩
    have retained := Finset.mem_filter.mp (fixed.symm ▸ inside)
    exact retained.2
  · obtain ⟨smaller, allAsk, greatest⟩ := prune_spec up (group.filter fun i => ask i group)
    refine ⟨smaller.trans (Finset.filter_subset _ _), allAsk, fun subset inside every => ?_⟩
    refine greatest subset ?_ every
    intro i member
    exact Finset.mem_filter.mpr ⟨inside member, up i inside (every i member)⟩
termination_by group.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by assumption⟩)

end Pruning

#print axioms prune_spec

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.GuardDependencies

def leftDependency (i : Fin 3) : Fin 3 := if i = 1 then 2 else i
def rightDependency (i : Fin 3) : Fin 3 := if i = 0 then 2 else i

def Realizes (dependency : Fin 3 → Fin 3) (population : Finset (Fin 3)) : Prop :=
  ∃ f : Batch dependency, f.AdmitsBeforeTells (X (Fin 3)) world ∧
    support f = population ∧ f.members.length = population.card

theorem left_control :
    Realizes leftDependency Finset.univ ∧
    ¬ Realizes leftDependency {0, 1} ∧ Realizes leftDependency {0} := by
  refine ⟨(populations_iff leftDependency _).mpr (by decide), ?_,
    (populations_iff leftDependency _).mpr (by decide)⟩
  intro admitted
  have needed := (populations_iff leftDependency _).mp admitted 1 (by decide)
  exact (by decide : (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3))) needed

theorem right_control :
    Realizes rightDependency Finset.univ ∧
    ¬ Realizes rightDependency {0, 1} ∧ Realizes rightDependency {1} := by
  refine ⟨(populations_iff rightDependency _).mpr (by decide), ?_,
    (populations_iff rightDependency _).mpr (by decide)⟩
  intro admitted
  have needed := (populations_iff rightDependency _).mp admitted 0 (by decide)
  exact (by decide : (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3))) needed

theorem no_greatest_finite_profile :
    ¬ ∃ admits : Finset (Fin 3) → Prop,
      BoundedUnionClosed admits ∧ admits Finset.univ ∧ ¬ admits {0, 1} ∧
      (∀ population, Realizes leftDependency population → admits population) ∧
      (∀ population, Realizes rightDependency population → admits population) := by
  rintro ⟨admits, unions, full, reject, includesLeft, includesRight⟩
  have left := includesLeft _ left_control.2.2
  have right := includesRight _ right_control.2.2
  have combined := unions left right full (Finset.subset_univ _) (Finset.subset_univ _)
  exact reject (by simpa only [Finset.singleton_union] using combined)

#print axioms left_control
#print axioms right_control
#print axioms no_greatest_finite_profile


open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.GuardDependencies

theorem dependency_preserves_unions (dependency : Fin 3 → Fin 3) :
    BoundedUnionClosed (Realizes dependency) := by
  intro left right _ hLeft hRight _ _ _
  apply (populations_iff dependency _).mpr
  intro i present
  rcases Finset.mem_union.mp present with fromLeft | fromRight
  · exact Finset.mem_union_left _ ((populations_iff dependency _).mp hLeft i fromLeft)
  · exact Finset.mem_union_right _ ((populations_iff dependency _).mp hRight i fromRight)

theorem no_greatest  :
    let admissible : (Finset (Fin 3) → Prop) → Prop :=
      fun A => BoundedUnionClosed A ∧ A Finset.univ ∧ ¬ A {0, 1}
    ¬ ∃ A, admissible A ∧ ∀ B, admissible B → ∀ population, B population → A population := by
  dsimp only
  rintro ⟨A, ⟨unions, full, excluded⟩, greatest⟩
  exact no_greatest_finite_profile ⟨A, unions, full, excluded,
    greatest _ ⟨dependency_preserves_unions _, left_control.1, left_control.2.1⟩,
    greatest _ ⟨dependency_preserves_unions _, right_control.1, right_control.2.1⟩⟩

#print axioms dependency_preserves_unions
#print axioms no_greatest

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AdmissionProfiles

