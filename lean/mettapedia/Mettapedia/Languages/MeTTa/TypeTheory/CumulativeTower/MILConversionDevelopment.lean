import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionParallelSpine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionParallelSubstitution

/-!
# Cofinal development of conversion-coherent native computation

Every term has a common parallel successor of all its parallel reducts. The
construction is existential: coherence of duplicated metadata is used as a
mathematical proposition, not as an executable runtime test. Rigid application
spines recover the actual arguments of both native eliminator branches.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILConversionParallel

open Presentation IntrinsicMILHypothesis MILConversionCompletion

variable {n : Nat}

/-- A common parallel successor of every parallel reduct of the given term. -/
def Cofinal (source : Tower.Tm n) : Prop :=
  ∃ common, ∀ target, Par source target → Par target common

theorem prefix_to_fixed
    {s p m pc cc x y ds dp dm dpc dcc dx dy : Tower.Tm n}
    (parallel : Par (eliminatePrefix s p m pc cc x y)
      (eliminatePrefix ds dp dm dpc dcc dx dy)) :
    Par s ds ∧ Par p dp ∧ Par m dm ∧ Par pc dpc ∧ Par cc dcc ∧ Par x dx ∧ Par y dy := by
  obtain ⟨s', p', m', pc', cc', x', y', shape, hs, hp, hm, hpc, hcc, hx, hy⟩ :=
    eliminatePrefix_inversion parallel
  have fields := spine_injective eliminateName shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨hs, hp, hm, hpc, hcc, hx, hy⟩

theorem primitive_to_fixed
    {s p x y z ds dp dx dy dz : Tower.Tm n}
    (parallel : Par (primitiveApp s p x y z) (primitiveApp ds dp dx dy dz)) :
    Par s ds ∧ Par p dp ∧ Par x dx ∧ Par y dy ∧ Par z dz := by
  obtain ⟨s', p', x', y', z', shape, hs, hp, hx, hy, hz⟩ := primitiveApp_inversion parallel
  have fields := @spine_injective n primitiveName [dz, dy, dx, dp, ds] [z', y', x', p', s'] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨hs, hp, hx, hy, hz⟩

theorem chain_to_fixed
    {s p x m y first second ds dp dx dm dy dfirst dsecond : Tower.Tm n}
    (parallel : Par (chainApp s p x m y first second)
      (chainApp ds dp dx dm dy dfirst dsecond)) :
    Par s ds ∧ Par p dp ∧ Par x dx ∧ Par m dm ∧ Par y dy ∧
      Par first dfirst ∧ Par second dsecond := by
  obtain ⟨s', p', x', m', y', first', second', shape, hs, hp, hx, hm, hy, hf, hl⟩ :=
    chainApp_inversion parallel
  have fields := @spine_injective n chainName [dsecond, dfirst, dy, dm, dx, dp, ds]
    [second', first', y', m', x', p', s'] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨hs, hp, hx, hm, hy, hf, hl⟩

theorem cofinal_primitive
    {s p motive pc cc x y innerS innerP innerX innerY symbol : Tower.Tm n}
    (cs : AuthoredConv innerS s) (cp : AuthoredConv innerP p)
    (cx : AuthoredConv innerX x) (cy : AuthoredConv innerY y)
    (function : Cofinal (eliminatePrefix s p motive pc cc x y))
    (argument : Cofinal (primitiveApp innerS innerP innerX innerY symbol)) :
    Cofinal (eliminateApp s p motive pc cc x y
      (primitiveApp innerS innerP innerX innerY symbol)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨ds, dp, dm, dpc, dcc, dx, dy, rfl, _, _, _, _, _, _, _⟩ :=
    eliminatePrefix_inversion (function _ (par_refl _))
  obtain ⟨diS, diP, diX, diY, dz, rfl, _, _, _, _, _⟩ :=
    primitiveApp_inversion (argument _ (par_refl _))
  refine ⟨.app (.app (.app dpc dx) dy) dz, ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨s', p', m', pc', cc', x', y', rfl, hs, hp, _, _, _, hx, hy⟩ :=
        eliminatePrefix_inversion functionStep
      obtain ⟨iS', iP', iX', iY', z', rfl, his, hip, hix, hiy, _⟩ :=
        primitiveApp_inversion argumentStep
      obtain ⟨dsStep, dpStep, dmStep, dpcStep, dccStep, dxStep, dyStep⟩ :=
        prefix_to_fixed (function _ functionStep)
      obtain ⟨_, _, _, _, dzStep⟩ := primitive_to_fixed (argument _ argumentStep)
      exact .primitive (coherent_transport cs his.sound hs.sound)
        (coherent_transport cp hip.sound hp.sound) (coherent_transport cx hix.sound hx.sound)
        (coherent_transport cy hiy.sound hy.sound)
        dsStep dpStep dmStep dpcStep dccStep dxStep dyStep dzStep
  | primitive _ _ _ _ hs hp hm hpc hcc hx hy hz =>
      obtain ⟨_, _, _, dpcStep, _, dxStep, dyStep⟩ :=
        prefix_to_fixed (function _ (par_eliminatePrefix hs hp hm hpc hcc hx hy))
      obtain ⟨_, _, _, _, dzStep⟩ := primitive_to_fixed
        (argument _ (par_primitiveApp (par_refl _) (par_refl _) (par_refl _) (par_refl _) hz))
      exact .app (.app (.app dpcStep dxStep) dyStep) dzStep

#print axioms prefix_to_fixed
#print axioms primitive_to_fixed
#print axioms chain_to_fixed
#print axioms cofinal_primitive

end MILConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
