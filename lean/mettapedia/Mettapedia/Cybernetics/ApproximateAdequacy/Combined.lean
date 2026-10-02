import Mettapedia.Cybernetics.ApproximateAdequacy.DefectLaws

/-!
# A defect bound together with a drift bound

The correspondence defect of a path map and the observation drift of its
object map are independent (`Collapse`, `Fold` and `Drift` in lane A's
`MindWorldApproximation`, and `Fold.drift_zero_defect_one` here).  A
certificate asking for both carries two numbers:
* `δ` bounds every identity and composition defect: the mind's arrow for a
  composite world path is within `δ` of the composite of its arrows for the
  parts;
* `ε` makes the graph of the object map a Girard–Pappas approximate
  bisimulation: along every run, world and mind observations stay within
  `ε`.

**Composition law** (`DefectAndDriftBound.comp`): if `F` has bounds
`(δ_F, ε_F)`, `G` has `(δ_G, ε_G)`, and `G` is `L`-Lipschitz on the arrows `F`
produces, the composite has `(δ_G + L δ_F, ε_F + ε_G)`: defects multiply and
add, drifts add.  Neither component bounds the other.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open CategoryTheory
open Mettapedia.Cybernetics.MindWorldApproximateFunctor
open Mettapedia.Cybernetics.MindWorldApproximation

variable {World : Type*} [Category World] {Mind : Type*} [Category Mind]
  {Mind' : Type*} [Category Mind'] {O D : Type*}

/-- **A defect bound together with a drift bound** for a path correspondence
whose objects are the states of transition systems with observations. -/
structure DefectAndDriftBound [LE D] (F : PathCorrespondence World Mind) (distance : O → O → D)
    (stepWorld : World → World → Prop) (stepMind : Mind → Mind → Prop) (obsWorld : World → O)
    (obsMind : Mind → O) (δ : ℝ) (ε : D) : Prop where
  identity_le : ∀ x, F.identityDefect x ≤ δ
  composition_le : ∀ {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last), F.compositionDefect earlier later ≤ δ
  drift : IsApproxBisimulation distance stepWorld stepMind obsWorld obsMind ε
    fun x y => F.obj x = y

namespace DefectAndDriftBound

variable [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D] {distance : O → O → D}
  {stepWorld : World → World → Prop} {stepMind : Mind → Mind → Prop}
  {stepMind' : Mind' → Mind' → Prop} {obsWorld : World → O} {obsMind : Mind → O}
  {obsMind' : Mind' → O} {F : PathCorrespondence World Mind} {G : PathCorrespondence Mind Mind'}
  {δ δ' L : ℝ} {ε ε' : D}

/-- **Composition: defects multiply and add, drifts add.** -/
theorem comp (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c)
    (first : DefectAndDriftBound F distance stepWorld stepMind obsWorld obsMind δ ε)
    (second : DefectAndDriftBound G distance stepMind stepMind' obsMind obsMind' δ' ε')
    (L_nonneg : 0 ≤ L) (lipschitz : F.LipschitzOnImage G L) :
    DefectAndDriftBound (F.comp G) distance stepWorld stepMind' obsWorld obsMind' (δ' + L * δ)
      (ε + ε') where
  identity_le x := (PathCorrespondence.identityDefect_comp_le lipschitz x).trans
    (add_le_add (second.identity_le _) (mul_le_mul_of_nonneg_left (first.identity_le x) L_nonneg))
  composition_le earlier later :=
    (PathCorrespondence.compositionDefect_comp_le lipschitz earlier later).trans
      (add_le_add (second.composition_le _ _)
        (mul_le_mul_of_nonneg_left (first.composition_le earlier later) L_nonneg))
  drift := by
    have graph : Relation.Comp (fun x y => F.obj x = y) (fun y z => G.obj y = z) =
        fun x z => (F.comp G).obj x = z := by
      funext x z
      refine propext ⟨fun ⟨y, same, same'⟩ => ?_, fun same => ⟨F.obj x, rfl, same⟩⟩
      change F.obj x = y at same
      change G.obj y = z at same'
      change G.obj (F.obj x) = z
      rw [same, same']
    have composite := first.drift.comp triangle second.drift
    rw [graph] at composite
    exact composite

omit [AddCommMonoid D] [IsOrderedAddMonoid D] in
/-- **What the drift component certifies**: along every run of the world,
mind observations along a matching mind run stay within `ε`. -/
theorem run_close (bound : DefectAndDriftBound F distance stepWorld stepMind obsWorld obsMind δ ε)
    (run : ℕ → World) (n : ℕ) (moves : ∀ i < n, stepWorld (run i) (run (i + 1))) :
    ∃ run' : ℕ → Mind, run' 0 = F.obj (run 0) ∧ (∀ i < n, stepMind (run' i) (run' (i + 1))) ∧
      ∀ i ≤ n, distance (obsWorld (run i)) (obsMind (run' i)) ≤ ε :=
  bound.drift.1.run_close run rfl n moves

end DefectAndDriftBound

end Mettapedia.Cybernetics.ApproximateAdequacy
