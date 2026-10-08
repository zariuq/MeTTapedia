import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSPresentation
import Mathlib.Data.Finite.Sigma

/-!
# Complete finite firing receipts and target normalization

Each firing retains its authored clause identifier and separately selected
positive occurrences. Its finite inventory is constructed from the actual
finite successor sets. Mapping variables acts on those complete receipts;
normalization maps each receipt to its whole target tree. The finite image
equals the independently computed rule denotation, while duplicate origins
or identified witnesses may be erased only in that extensional image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.AuthoredPresentation

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Classical

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable (authored : AuthoredPresentation S Actions)

theorem finite_firings {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) : Finite (authored.Firing operator arguments action) := by
  let _ : Finite (authored.Origin sort operator action) := authored.finite sort operator action
  let Inventory := Σ origin : authored.Origin sort operator action,
    {input : Input (authored.rule sort operator action origin).pattern X //
      input ∈ (authored.rule sort operator action origin).pattern.inputs arguments}
  let read : authored.Firing operator arguments action → Inventory := fun firing =>
    ⟨firing.origin, ⟨firing.input, (Pattern.mem_inputs _ _ _).mpr
      ⟨firing.matching.1, firing.matching.2.1⟩⟩⟩
  apply Finite.of_injective read
  intro first second same
  cases first with
  | mk firstOrigin firstInput firstMatching =>
      cases second with
      | mk secondOrigin secondInput secondMatching =>
          have origins : firstOrigin = secondOrigin := congrArg Sigma.fst same
          subst secondOrigin
          have inputs : firstInput = secondInput := by
            exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp same).2)
          subst secondInput
          rfl

def firings {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) : Finset (authored.Firing operator arguments action) :=
  let _ : Fintype (authored.Firing operator arguments action) :=
    @Fintype.ofFinite _ (authored.finite_firings operator arguments action)
  Finset.univ

theorem firing_member {X : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    {arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator}
    {action : Actions sort} (firing : authored.Firing operator arguments action) :
    firing ∈ authored.firings operator arguments action := by
  let _ : Fintype (authored.Firing operator arguments action) :=
    @Fintype.ofFinite _ (authored.finite_firings operator arguments action)
  unfold firings
  exact Finset.mem_univ _

/-- The whole finite denotation is the image of complete addressed firings. -/
theorem targets_eq_firing_image {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) :
    Presentation.targets authored.readout operator arguments action =
      (authored.firings operator arguments action).image (Firing.target authored) := by
  apply Finset.ext
  intro target
  rw [authored.mem_targets_iff_firing, Finset.mem_image]
  constructor
  · rintro ⟨firing, same⟩
    exact ⟨firing, authored.firing_member firing, same⟩
  · rintro ⟨firing, _, same⟩
    exact ⟨firing, same⟩

def Firing.map {X Y : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    {arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator}
    {action : Actions sort} (mapping : X ⟶ Y)
    (firing : authored.Firing operator arguments action) :
    authored.Firing operator (mapArguments mapping arguments) action where
  origin := firing.origin
  input := firing.input.map mapping
  matching := matches_map _ mapping arguments firing.input firing.matching

theorem Firing.map_origin {X Y : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    {arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator}
    {action : Actions sort} (mapping : X ⟶ Y)
    (firing : authored.Firing operator arguments action) :
    (firing.map authored mapping).origin = firing.origin := rfl

theorem Firing.map_derivative {X Y : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    {arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator}
    {action : Actions sort} (mapping : X ⟶ Y)
    (firing : authored.Firing operator arguments action)
    (occurrence : (authored.rule sort operator action firing.origin).pattern.Occurrence) :
    (firing.map authored mapping).input.derivatives occurrence =
      mapping PUnit.unit _ (firing.input.derivatives occurrence) := rfl

theorem Firing.map_target {X Y : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    {arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator}
    {action : Actions sort} (mapping : X ⟶ Y)
    (firing : authored.Firing operator arguments action) :
    (firing.map authored mapping).target = S.rename mapping firing.target :=
  (authored.rule sort operator action firing.origin).output_map mapping firing.input

end Mettapedia.OSLF.FiniteBranching.Premises.AuthoredPresentation
