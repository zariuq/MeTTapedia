import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModel

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelRegression

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open ClosedTermCanonicalWorldModel
open scoped ENNReal

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)

abbrev TestAtomTy : Ty TestBase := .base TestBase.atom

abbrev TestClosedEnv :
    ClosedTermEq.ClosedEnv TestConst [TestAtomTy] :=
  fun {_} v =>
    match v with
    | .vz => .const TestConst.a

theorem canonicalWorldEvidence_singleton_satisfies_canary
    (W : ClosedTheorySet.World TestConst) (φ : CanonicalQuery TestConst)
    (h : canonicalWorldSatisfies W φ) :
    canonicalWorldEvidence (Base := TestBase) (Const := TestConst)
      ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = ⟨1, 0⟩ :=
  canonicalWorldEvidence_singleton_of_satisfies
    (Base := TestBase) (Const := TestConst) W φ h

theorem canonicalWorldEvidence_singleton_not_satisfies_canary
    (W : ClosedTheorySet.World TestConst) (φ : CanonicalQuery TestConst)
    (h : ¬ canonicalWorldSatisfies W φ) :
    canonicalWorldEvidence (Base := TestBase) (Const := TestConst)
      ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = ⟨0, 1⟩ :=
  canonicalWorldEvidence_singleton_of_not_satisfies
    (Base := TestBase) (Const := TestConst) W φ h

theorem queryStrength_singleton_satisfies_canary
    (W : ClosedTheorySet.World TestConst) (φ : CanonicalQuery TestConst)
    (h : canonicalWorldSatisfies W φ) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World TestConst))
        (Query := CanonicalQuery TestConst)
        ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 1 :=
  queryStrength_singleton_of_satisfies
    (Base := TestBase) (Const := TestConst) W φ h

theorem queryStrength_singleton_not_satisfies_canary
    (W : ClosedTheorySet.World TestConst) (φ : CanonicalQuery TestConst)
    (h : ¬ canonicalWorldSatisfies W φ) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World TestConst))
        (Query := CanonicalQuery TestConst)
        ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 0 :=
  queryStrength_singleton_of_not_satisfies
    (Base := TestBase) (Const := TestConst) W φ h

theorem singleton_adequacy_strength_one_canary
    (W : ClosedTheorySet.World TestConst) (φ : CanonicalQuery TestConst) :
    canonicalWorldSatisfies W φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 1 :=
  singleton_adequacy_strength_one
    (Base := TestBase) (Const := TestConst) W φ

theorem singleton_adequacy_strength_zero_canary
    (W : ClosedTheorySet.World TestConst) (φ : CanonicalQuery TestConst) :
    ¬ canonicalWorldSatisfies W φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 0 :=
  singleton_adequacy_strength_zero
    (Base := TestBase) (Const := TestConst) W φ

theorem propTruth_singleton_strength_one_canary
    (W : ClosedTheorySet.World TestConst) (φ : ClosedFormula TestConst) :
    ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf φ) ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 1 :=
  propTruth_iff_singleton_strength_one
    (Base := TestBase) (Const := TestConst) W φ

theorem not_propTruth_singleton_strength_zero_canary
    (W : ClosedTheorySet.World TestConst) (φ : ClosedFormula TestConst) :
    ¬ ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf φ) ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 0 :=
  not_propTruth_iff_singleton_strength_zero
    (Base := TestBase) (Const := TestConst) W φ

theorem envSatisfies_singleton_strength_one_canary
    (W : ClosedTheorySet.World TestConst)
    (φ : Formula TestConst [TestAtomTy]) :
    ClosedTermEq.envSatisfies W.carrier TestClosedEnv φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst))
          (ClosedTermEq.closeFormula TestClosedEnv φ) = 1 :=
  envSatisfies_iff_singleton_strength_one
    (Base := TestBase) (Const := TestConst) W TestClosedEnv φ

theorem not_envSatisfies_singleton_strength_zero_canary
    (W : ClosedTheorySet.World TestConst)
    (φ : Formula TestConst [TestAtomTy]) :
    ¬ ClosedTermEq.envSatisfies W.carrier TestClosedEnv φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst))
          (ClosedTermEq.closeFormula TestClosedEnv φ) = 0 :=
  not_envSatisfies_iff_singleton_strength_zero
    (Base := TestBase) (Const := TestConst) W TestClosedEnv φ

theorem pointwiseImplies_singletonStrengthLE_canary
    (φ ψ : CanonicalQuery TestConst) :
    (∀ W : ClosedTheorySet.World TestConst,
        canonicalWorldSatisfies W φ → canonicalWorldSatisfies W ψ) ↔
      (∀ W : ClosedTheorySet.World TestConst,
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World TestConst))
            (Query := CanonicalQuery TestConst)
            ({W} : Multiset (ClosedTheorySet.World TestConst)) φ ≤
          BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World TestConst))
            (Query := CanonicalQuery TestConst)
            ({W} : Multiset (ClosedTheorySet.World TestConst)) ψ) :=
  pointwiseImplies_iff_singletonStrengthLE
    (Base := TestBase) (Const := TestConst) φ ψ

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelRegression
