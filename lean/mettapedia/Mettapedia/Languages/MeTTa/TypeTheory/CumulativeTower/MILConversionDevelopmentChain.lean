import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionDevelopment

/-!
# Cofinal development of a native chain eliminator

The two recursive eliminator calls retain the developed source hypotheses.
Independently developed copies of the metadata remain coherent in the original
authored conversion relation. No conversion decision procedure is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILConversionParallel

open Presentation IntrinsicMILHypothesis MILConversionCompletion

variable {n : Nat}

/-- The actual chain branch has a common parallel successor once its immediate
function and argument do. Its four guards belong to authored conversion. -/
theorem cofinal_chain
    {s p motive pc cc x middle y innerS innerP innerX innerY earlier later : Tower.Tm n}
    (cs : AuthoredConv innerS s) (cp : AuthoredConv innerP p)
    (cx : AuthoredConv innerX x) (cy : AuthoredConv innerY y)
    (function : Cofinal (eliminatePrefix s p motive pc cc x y))
    (argument : Cofinal (chainApp innerS innerP innerX middle innerY earlier later)) :
    Cofinal (eliminateApp s p motive pc cc x y
      (chainApp innerS innerP innerX middle innerY earlier later)) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argument⟩ := argument
  obtain ⟨ds, dp, dm, dpc, dcc, dx, dy, rfl, _, _, _, _, _, _, _⟩ :=
    eliminatePrefix_inversion (function _ (par_refl _))
  obtain ⟨diS, diP, diX, dk, diY, dearlier, dlater, rfl, _, _, _, _, _, _, _⟩ :=
    chainApp_inversion (argument _ (par_refl _))
  refine ⟨.app
    (.app (.app (.app (.app (.app (.app dcc dx) dk) dy) dearlier) dlater)
      (eliminateApp ds dp dm dpc dcc dx dk dearlier))
    (eliminateApp ds dp dm dpc dcc dk dy dlater), ?_⟩
  intro result parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨s', p', m', pc', cc', x', y', rfl, hs, hp, _, _, _, hx, hy⟩ :=
        eliminatePrefix_inversion functionStep
      obtain ⟨iS', iP', iX', k', iY', earlier', later', rfl,
          his, hip, hix, _, hiy, _, _⟩ := chainApp_inversion argumentStep
      obtain ⟨dsStep, dpStep, dmStep, dpcStep, dccStep, dxStep, dyStep⟩ :=
        prefix_to_fixed (function _ functionStep)
      obtain ⟨_, _, _, dkStep, _, dearlierStep, dlaterStep⟩ :=
        chain_to_fixed (argument _ argumentStep)
      exact .chain (coherent_transport cs his.sound hs.sound)
        (coherent_transport cp hip.sound hp.sound) (coherent_transport cx hix.sound hx.sound)
        (coherent_transport cy hiy.sound hy.sound)
        dsStep dpStep dmStep dpcStep dccStep dxStep dkStep dyStep dearlierStep dlaterStep
  | chain _ _ _ _ hs hp hm hpc hcc hx hk hy hearlier hlater =>
      obtain ⟨dsStep, dpStep, dmStep, dpcStep, dccStep, dxStep, dyStep⟩ :=
        prefix_to_fixed (function _ (par_eliminatePrefix hs hp hm hpc hcc hx hy))
      obtain ⟨_, _, _, dkStep, _, dearlierStep, dlaterStep⟩ := chain_to_fixed
        (argument _ (par_chainApp (par_refl _) (par_refl _) (par_refl _) hk
          (par_refl _) hearlier hlater))
      exact .app
        (.app (.app (.app (.app (.app (.app dccStep dxStep) dkStep) dyStep)
          dearlierStep) dlaterStep)
          (.app (par_eliminatePrefix dsStep dpStep dmStep dpcStep dccStep dxStep dkStep)
            dearlierStep))
        (.app (par_eliminatePrefix dsStep dpStep dmStep dpcStep dccStep dkStep dyStep)
          dlaterStep)

#print axioms cofinal_chain

end MILConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
