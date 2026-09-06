import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionParallelSpine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionParallelSubstitution

/-!
# Cofinal List and identity development in the combined native package

The common reducts are built from developments of the actual function and
argument subterms. Duplicated metadata remains related by authored conversion;
it is neither erased nor replaced by an executable coherence oracle. These
lemmas include the original List and identity roots in the same parallel
relation as the relation-indexed List eliminator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionParallel

open Presentation NativeIndexedFamilies NativeRelatorConversionCompletion

variable {n : Nat}

/-- A common parallel successor of all parallel reducts of this source. -/
def Cofinal (source : Tower.Tm n) : Prop :=
  ∃ common, ∀ target, Par source target → Par target common

theorem cofinal_listNil
    {a p z s innerA : Tower.Tm n}
    (ca : AuthoredConv innerA a)
    (function : Cofinal (listPrefix a p z s))
    (argument : Cofinal (Intrinsic.nilApp innerA)) :
    Cofinal (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp innerA)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨da, dp, dz, ds, rfl, _, _, _, _⟩ :=
    listPrefix_inversion (function _ (par_refl _))
  obtain ⟨diA, rfl, _⟩ := nilApp_inversion (argument _ (par_refl _))
  refine ⟨dz, ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨a', p', z', s', rfl, ha, _, _, _⟩ := listPrefix_inversion functionStep
      obtain ⟨iA', rfl, hiA⟩ := nilApp_inversion argumentStep
      obtain ⟨daStep, dpStep, dzStep, dsStep⟩ := listPrefix_to_fixed (function _ functionStep)
      exact .listNil (coherent_transport ca hiA.sound ha.sound) daStep dpStep dzStep dsStep
  | listNil _ ha hp hz hs =>
      exact (listPrefix_to_fixed (function _ (par_listPrefix ha hp hz hs))).2.2.1

theorem cofinal_listCons
    {a p z s innerA h t : Tower.Tm n}
    (ca : AuthoredConv innerA a)
    (function : Cofinal (listPrefix a p z s))
    (argument : Cofinal (Intrinsic.consApp innerA h t)) :
    Cofinal (Intrinsic.eliminateApp a p z s (Intrinsic.consApp innerA h t)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨da, dp, dz, ds, rfl, _, _, _, _⟩ :=
    listPrefix_inversion (function _ (par_refl _))
  obtain ⟨diA, dh, dt, rfl, _, _, _⟩ := consApp_inversion (argument _ (par_refl _))
  refine ⟨.app (.app (.app ds dh) dt) (Intrinsic.eliminateApp da dp dz ds dt), ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨a', p', z', s', rfl, ha, _, _, _⟩ := listPrefix_inversion functionStep
      obtain ⟨iA', h', t', rfl, hiA, _, _⟩ := consApp_inversion argumentStep
      obtain ⟨daStep, dpStep, dzStep, dsStep⟩ := listPrefix_to_fixed (function _ functionStep)
      obtain ⟨_, dhStep, dtStep⟩ := consApp_to_fixed (argument _ argumentStep)
      exact .listCons (coherent_transport ca hiA.sound ha.sound)
        daStep dpStep dzStep dsStep dhStep dtStep
  | listCons _ ha hp hz hs hh ht =>
      obtain ⟨daStep, dpStep, dzStep, dsStep⟩ :=
        listPrefix_to_fixed (function _ (par_listPrefix ha hp hz hs))
      obtain ⟨_, dhStep, dtStep⟩ :=
        consApp_to_fixed (argument _ (par_consApp (par_refl _) hh ht))
      exact .app (.app (.app dsStep dhStep) dtStep)
        (.app (par_listPrefix daStep dpStep dzStep dsStep) dtStep)

theorem cofinal_identity
    {a x p d y witness : Tower.Tm n}
    (cy : AuthoredConv y x) (cw : AuthoredConv witness x)
    (function : Cofinal (identityPrefix a x p d y))
    (argument : Cofinal (.refl witness)) :
    Cofinal (Intrinsic.identityEliminateApp a x p d y (.refl witness)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨da, dx, dp, dd, dy, rfl, _, _, _, _, _⟩ :=
    identityPrefix_inversion (function _ (par_refl _))
  obtain ⟨dw, rfl, _⟩ := refl_inversion (argument _ (par_refl _))
  refine ⟨dd, ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨a', x', p', d', y', rfl, _, hx, _, _, hy⟩ := identityPrefix_inversion functionStep
      obtain ⟨w', rfl, hw⟩ := refl_inversion argumentStep
      obtain ⟨daStep, dxStep, dpStep, ddStep, dyStep⟩ :=
        identityPrefix_to_fixed (function _ functionStep)
      have dwStep := refl_to_fixed (argument _ argumentStep)
      exact .identity (coherent_transport cy hy.sound hx.sound)
        (coherent_transport cw hw.sound hx.sound)
        daStep dxStep dpStep ddStep dyStep dwStep
  | identity _ _ ha hx hp hd hy _ =>
      exact (identityPrefix_to_fixed (function _ (par_identityPrefix ha hx hp hd hy))).2.2.2.1

#print axioms cofinal_listNil
#print axioms cofinal_listCons
#print axioms cofinal_identity

end NativeRelatorConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
