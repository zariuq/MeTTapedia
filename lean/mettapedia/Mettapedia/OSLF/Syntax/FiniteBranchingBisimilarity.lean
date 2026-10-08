import Mettapedia.OSLF.Syntax.FiniteBranchingBisimulationSpan

/-!
# Actual finite labelled bisimilarity

The union of all independently admitted two-sided relations is itself
admitted. It supplies the greatest relation without a final coalgebra.
Reflexivity, symmetry and composition earn the actual equivalence relation,
and complete action availability follows from both successor directions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Bisimulation

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open IndexedPolynomial

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

def Bisimilar (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Relation left right :=
  fun base sort value other => ∃ relation : Relation left right,
    Admitted left right relation ∧ relation base sort value other

/-- The union retains each supplied relation and is itself a bisimulation. -/
theorem bisimilar_admitted (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Admitted left right (Bisimilar left right) := by
  rintro base sort value other ⟨relation, admitted, held⟩ action
  have matching := admitted base sort value other held action
  constructor
  · intro next member
    obtain ⟨otherNext, present, related⟩ := matching.1 next member
    exact ⟨otherNext, present, relation, admitted, related⟩
  · intro otherNext member
    obtain ⟨next, present, related⟩ := matching.2 otherNext member
    exact ⟨next, present, relation, admitted, related⟩

theorem bisimilar_of_span
    {left right middle : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (first : middle ⟶ left) (second : middle ⟶ right)
    (base : PUnit.{u + 1}) (sort : S.Srt) (point : middle.V base sort) :
    Bisimilar left right base sort
      (first.f base sort point) (second.f base sort point) :=
  ⟨imageRelation first second, image_admitted first second, point, rfl, rfl⟩

/-- Empty successor sets agree at every label, independently of branch count. -/
theorem bisimilar_availability
    {left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (base : PUnit.{u + 1}) (sort : S.Srt)
    {value : left.V base sort} {other : right.V base sort}
    (related : Bisimilar left right base sort value other) (action : Actions sort) :
    left.str base sort value action = ∅ ↔ right.str base sort other action = ∅ := by
  have matching := bisimilar_admitted left right base sort value other related action
  constructor
  · intro empty
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro successor member
    obtain ⟨_, impossible, _⟩ := matching.2 successor member
    rw [empty] at impossible
    exact Finset.notMem_empty _ impossible
  · intro empty
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro successor member
    obtain ⟨_, impossible, _⟩ := matching.1 successor member
    rw [empty] at impossible
    exact Finset.notMem_empty _ impossible

theorem bisimilar_refl (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (value : object.V base sort) :
    Bisimilar object object base sort value value := by
  refine ⟨fun _ _ => Eq, ?_, rfl⟩
  intro base sort first second same action
  subst second
  exact Mettapedia.CategoryTheory.FinitePowerset.related_identity _

theorem bisimilar_symm
    {left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    {base : PUnit.{u + 1}} {sort : S.Srt}
    {value : left.V base sort} {other : right.V base sort}
    (related : Bisimilar left right base sort value other) :
    Bisimilar right left base sort other value := by
  rcases related with ⟨relation, admitted, held⟩
  refine ⟨fun base sort other value => relation base sort value other, ?_, held⟩
  intro base sort other value present action
  have matching := admitted base sort value other present action
  exact ⟨matching.2, matching.1⟩

theorem bisimilar_trans
    {left middle right : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    {base : PUnit.{u + 1}} {sort : S.Srt}
    {value : left.V base sort} {other : middle.V base sort} {result : right.V base sort}
    (earlier : Bisimilar left middle base sort value other)
    (later : Bisimilar middle right base sort other result) :
    Bisimilar left right base sort value result := by
  rcases earlier with ⟨before, firstAdmitted, firstHeld⟩
  rcases later with ⟨after, secondAdmitted, secondHeld⟩
  refine ⟨fun base sort value result => ∃ other,
    before base sort value other ∧ after base sort other result, ?_,
    other, firstHeld, secondHeld⟩
  rintro base sort value result ⟨other, firstHeld, secondHeld⟩ action
  exact Mettapedia.CategoryTheory.FinitePowerset.related_compose
    (firstAdmitted base sort value other firstHeld action)
    (secondAdmitted base sort other result secondHeld action)

def bisimulationSetoid (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) : Setoid (object.V base sort) where
  r := Bisimilar object object base sort
  iseqv := ⟨bisimilar_refl object base sort, bisimilar_symm, bisimilar_trans⟩

end Mettapedia.OSLF.FiniteBranching.Bisimulation
