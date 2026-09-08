import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionDevelopment

/-!
# Cofinal development of proof-relevant relational elimination

Both outer list indices and constructor metadata remain related by authored
conversion while their occurrences develop independently. The cons result
retains the exact head evidence, tail evidence and recursive elimination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionParallel

open Presentation NativeIndexedFamilies NativeRelatorConversionCompletion

variable {n : Nat}

theorem cofinal_relNil
    {a b r p z s xs ys innerA innerB innerR : Tower.Tm n}
    (ca : AuthoredConv innerA a) (cb : AuthoredConv innerB b) (cr : AuthoredConv innerR r)
    (cx : AuthoredConv xs (Intrinsic.nilApp a)) (cy : AuthoredConv ys (Intrinsic.nilApp b))
    (function : Cofinal (relPrefix a b r p z s xs ys))
    (argument : Cofinal (IntrinsicRelator.nilRelApp innerA innerB innerR)) :
    Cofinal (IntrinsicRelator.eliminateApp a b r p z s xs ys
      (IntrinsicRelator.nilRelApp innerA innerB innerR)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨da, db, dr, dp, dz, ds, dxs, dys, rfl, _, _, _, _, _, _, _, _⟩ :=
    relPrefix_inversion (function _ (par_refl _))
  obtain ⟨diA, diB, diR, rfl, _, _, _⟩ :=
    nilRelApp_inversion (argument _ (par_refl _))
  refine ⟨dz, ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨a', b', r', p', z', s', xs', ys', rfl, ha, hb, hr, _, _, _, hxs, hys⟩ :=
        relPrefix_inversion functionStep
      obtain ⟨iA', iB', iR', rfl, hia, hib, hir⟩ := nilRelApp_inversion argumentStep
      obtain ⟨daStep, dbStep, drStep, dpStep, dzStep, dsStep, dxsStep, dysStep⟩ :=
        relPrefix_to_fixed (function _ functionStep)
      exact .relNil (coherent_transport ca hia.sound ha.sound)
        (coherent_transport cb hib.sound hb.sound) (coherent_transport cr hir.sound hr.sound)
        (coherent_transport cx hxs.sound (nilApp_congr ha.sound))
        (coherent_transport cy hys.sound (nilApp_congr hb.sound))
        daStep dbStep drStep dpStep dzStep dsStep dxsStep dysStep
  | relNil _ _ _ _ _ ha hb hr hp hz hs hxs hys =>
      exact (relPrefix_to_fixed (function _ (par_relPrefix ha hb hr hp hz hs hxs hys))).2.2.2.2.1

theorem cofinal_relCons
    {a b r p z s xs ys innerA innerB innerR h k t u he te : Tower.Tm n}
    (ca : AuthoredConv innerA a) (cb : AuthoredConv innerB b) (cr : AuthoredConv innerR r)
    (cx : AuthoredConv xs (Intrinsic.consApp a h t))
    (cy : AuthoredConv ys (Intrinsic.consApp b k u))
    (function : Cofinal (relPrefix a b r p z s xs ys))
    (argument : Cofinal (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te)) :
    Cofinal (IntrinsicRelator.eliminateApp a b r p z s xs ys
      (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨da, db, dr, dp, dz, ds, dxs, dys, rfl, _, _, _, _, _, _, _, _⟩ :=
    relPrefix_inversion (function _ (par_refl _))
  obtain ⟨diA, diB, diR, dh, dk, dt, du, dhe, dte, rfl, _, _, _, _, _, _, _, _, _⟩ :=
    consRelApp_inversion (argument _ (par_refl _))
  refine ⟨.app (.app (.app (.app (.app (.app (.app ds dh) dk) dt) du) dhe) dte)
    (IntrinsicRelator.eliminateApp da db dr dp dz ds dt du dte), ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨a', b', r', p', z', s', xs', ys', rfl, ha, hb, hr, _, _, _, hxs, hys⟩ :=
        relPrefix_inversion functionStep
      obtain ⟨iA', iB', iR', h', k', t', u', he', te', rfl,
          hia, hib, hir, hh, hk, ht, hu, _, _⟩ := consRelApp_inversion argumentStep
      obtain ⟨daStep, dbStep, drStep, dpStep, dzStep, dsStep, dxsStep, dysStep⟩ :=
        relPrefix_to_fixed (function _ functionStep)
      obtain ⟨_, _, _, dhStep, dkStep, dtStep, duStep, dheStep, dteStep⟩ :=
        consRelApp_to_fixed (argument _ argumentStep)
      exact .relCons (coherent_transport ca hia.sound ha.sound)
        (coherent_transport cb hib.sound hb.sound) (coherent_transport cr hir.sound hr.sound)
        (coherent_transport cx hxs.sound (consApp_congr ha.sound hh.sound ht.sound))
        (coherent_transport cy hys.sound (consApp_congr hb.sound hk.sound hu.sound))
        daStep dbStep drStep dpStep dzStep dsStep dxsStep dysStep
        dhStep dkStep dtStep duStep dheStep dteStep
  | relCons _ _ _ _ _ ha hb hr hp hz hs hxs hys hh hk ht hu hhe hte =>
      obtain ⟨daStep, dbStep, drStep, dpStep, dzStep, dsStep, _, _⟩ :=
        relPrefix_to_fixed (function _ (par_relPrefix ha hb hr hp hz hs hxs hys))
      obtain ⟨_, _, _, dhStep, dkStep, dtStep, duStep, dheStep, dteStep⟩ :=
        consRelApp_to_fixed
          (argument _ (par_consRelApp (par_refl _) (par_refl _) (par_refl _)
            hh hk ht hu hhe hte))
      exact .app (.app (.app (.app (.app (.app (.app dsStep dhStep) dkStep) dtStep) duStep)
        dheStep) dteStep)
        (.app (par_relPrefix daStep dbStep drStep dpStep dzStep dsStep dtStep duStep) dteStep)

#print axioms cofinal_relNil
#print axioms cofinal_relCons

end NativeRelatorConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
