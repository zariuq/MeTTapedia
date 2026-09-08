import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionDevelopmentChain
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionParallelCoherence

/-!
# Complete development for the native conversion-coherent presentation

Cofinal developments are constructed from developments of the immediate
subterms. A root classification separates beta, primitive and chain redexes
from structural applications without asserting that the classification is a
conversion decision procedure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILConversionParallel

open Presentation IntrinsicMILHypothesis MILConversionCompletion

variable {n : Nat}

private theorem lam_to_fixed {body body' : Tower.Tm (n + 1)}
    (parallel : Par (.lam body) (.lam body')) : Par body body' := by
  cases parallel with | lam inner => exact inner

private theorem pair_to_fixed {first second first' second' : Tower.Tm n}
    (parallel : Par (.pair first second) (.pair first' second')) :
    Par first first' ∧ Par second second' := by
  cases parallel with | pair left right => exact ⟨left, right⟩

theorem cofinal_beta {body : Tower.Tm (n + 1)} {argument : Tower.Tm n}
    (function : Cofinal (.lam body)) (argumentDevelop : Cofinal argument) :
    Cofinal (.app (.lam body) argument) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argumentDevelop⟩ := argumentDevelop
  obtain ⟨db, rfl, _⟩ := lam_inversion (function _ (par_refl _))
  refine ⟨inst0 da db, ?_⟩
  intro target parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨body', rfl, _⟩ := lam_inversion functionStep
      exact .betaPi (lam_to_fixed (function _ functionStep)) (argumentDevelop _ argumentStep)
  | betaPi bodyStep argumentStep =>
      exact par_inst0 (argumentDevelop _ argumentStep) (lam_to_fixed (function _ (.lam bodyStep)))

theorem cofinal_pair_fst {first second : Tower.Tm n}
    (pairDevelop : Cofinal (.pair first second)) : Cofinal (.fst (.pair first second)) := by
  obtain ⟨common, pairDevelop⟩ := pairDevelop
  obtain ⟨df, ds, rfl, _, _⟩ := pair_inversion (pairDevelop _ (par_refl _))
  refine ⟨df, ?_⟩
  intro target parallel
  cases parallel with
  | fst pairStep =>
      obtain ⟨first', second', rfl, _, _⟩ := pair_inversion pairStep
      obtain ⟨left, right⟩ := pair_to_fixed (pairDevelop _ pairStep)
      exact .betaSigmaFst left right
  | betaSigmaFst left right =>
      exact (pair_to_fixed (pairDevelop _ (.pair left right))).1

theorem cofinal_pair_snd {first second : Tower.Tm n}
    (pairDevelop : Cofinal (.pair first second)) : Cofinal (.snd (.pair first second)) := by
  obtain ⟨common, pairDevelop⟩ := pairDevelop
  obtain ⟨df, ds, rfl, _, _⟩ := pair_inversion (pairDevelop _ (par_refl _))
  refine ⟨ds, ?_⟩
  intro target parallel
  cases parallel with
  | snd pairStep =>
      obtain ⟨first', second', rfl, _, _⟩ := pair_inversion pairStep
      obtain ⟨left, right⟩ := pair_to_fixed (pairDevelop _ pairStep)
      exact .betaSigmaSnd left right
  | betaSigmaSnd left right =>
      exact (pair_to_fixed (pairDevelop _ (.pair left right))).2

inductive AppRoot : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | beta {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
      AppRoot (.lam body) argument
  | primitive {n : Nat}
      {s p motive pc cc x y innerS innerP innerX innerY symbol : Tower.Tm n} :
      AuthoredConv innerS s → AuthoredConv innerP p →
      AuthoredConv innerX x → AuthoredConv innerY y →
      AppRoot (eliminatePrefix s p motive pc cc x y) (primitiveApp innerS innerP innerX innerY symbol)
  | chain {n : Nat}
      {s p motive pc cc x middle y innerS innerP innerX innerY earlier later : Tower.Tm n} :
      AuthoredConv innerS s → AuthoredConv innerP p →
      AuthoredConv innerX x → AuthoredConv innerY y →
      AppRoot (eliminatePrefix s p motive pc cc x y)
        (chainApp innerS innerP innerX middle innerY earlier later)

theorem cofinal_structural_app {function argument : Tower.Tm n}
    (noRoot : ¬ AppRoot function argument)
    (functionDevelop : Cofinal function) (argumentDevelop : Cofinal argument) :
    Cofinal (.app function argument) := by
  obtain ⟨df, functionDevelop⟩ := functionDevelop
  obtain ⟨da, argumentDevelop⟩ := argumentDevelop
  refine ⟨.app df da, ?_⟩
  intro target parallel
  cases parallel with
  | app functionStep argumentStep => exact .app (functionDevelop _ functionStep) (argumentDevelop _ argumentStep)
  | betaPi _ _ => exact False.elim (noRoot (.beta _ _))
  | primitive cs cp cx cy _ _ _ _ _ _ _ _ => exact False.elim (noRoot (.primitive cs cp cx cy))
  | chain cs cp cx cy _ _ _ _ _ _ _ _ _ _ => exact False.elim (noRoot (.chain cs cp cx cy))

theorem cofinal_app {function argument : Tower.Tm n}
    (functionDevelop : Cofinal function) (argumentDevelop : Cofinal argument) :
    Cofinal (.app function argument) := by
  classical
  by_cases root : AppRoot function argument
  · cases root with
    | beta => exact cofinal_beta functionDevelop argumentDevelop
    | primitive cs cp cx cy => exact cofinal_primitive cs cp cx cy functionDevelop argumentDevelop
    | chain cs cp cx cy => exact cofinal_chain cs cp cx cy functionDevelop argumentDevelop
  · exact cofinal_structural_app root functionDevelop argumentDevelop

/-- Complete development for every open raw term of the actual native
syntax. The proof preserves the original metadata-conversion guards. -/
theorem cofinal (source : Tower.Tm n) : Cofinal source := by
  induction source with
  | var index =>
      refine ⟨.var index, ?_⟩
      intro target parallel
      cases parallel
      exact .var index
  | const name =>
      refine ⟨.const name, ?_⟩
      intro target parallel
      cases parallel
      exact .const name
  | head value =>
      refine ⟨.head value, ?_⟩
      intro target parallel
      cases parallel with
      | head _ => exact .head value
      | headRel equality => exact .headRel (Tower.headEq_symmetric.symm _ _ equality)
  | pi domain codomain first second =>
      obtain ⟨dd, first⟩ := first
      obtain ⟨dc, second⟩ := second
      refine ⟨.pi dd dc, ?_⟩
      intro target parallel
      cases parallel with
      | pi domainStep codomainStep => exact .pi (first _ domainStep) (second _ codomainStep)
  | sigma domain codomain first second =>
      obtain ⟨dd, first⟩ := first
      obtain ⟨dc, second⟩ := second
      refine ⟨.sigma dd dc, ?_⟩
      intro target parallel
      cases parallel with
      | sigma domainStep codomainStep => exact .sigma (first _ domainStep) (second _ codomainStep)
  | id type left right first second third =>
      obtain ⟨dt, first⟩ := first
      obtain ⟨dl, second⟩ := second
      obtain ⟨dr, third⟩ := third
      refine ⟨.id dt dl dr, ?_⟩
      intro target parallel
      cases parallel with
      | id typeStep leftStep rightStep => exact .id (first _ typeStep) (second _ leftStep) (third _ rightStep)
  | lam body inner =>
      obtain ⟨db, inner⟩ := inner
      refine ⟨.lam db, ?_⟩
      intro target parallel
      cases parallel with
      | lam bodyStep => exact .lam (inner _ bodyStep)
  | app function argument first second => exact cofinal_app first second
  | pair first second firstDevelop secondDevelop =>
      obtain ⟨df, firstDevelop⟩ := firstDevelop
      obtain ⟨ds, secondDevelop⟩ := secondDevelop
      refine ⟨.pair df ds, ?_⟩
      intro target parallel
      cases parallel with
      | pair firstStep secondStep => exact .pair (firstDevelop _ firstStep) (secondDevelop _ secondStep)
  | fst pair inner =>
      cases pair with
      | pair first second => exact cofinal_pair_fst inner
      | _ =>
          obtain ⟨dp, inner⟩ := inner
          refine ⟨.fst dp, ?_⟩
          intro target parallel
          cases parallel with
          | fst pairStep => exact .fst (inner _ pairStep)
  | snd pair inner =>
      cases pair with
      | pair first second => exact cofinal_pair_snd inner
      | _ =>
          obtain ⟨dp, inner⟩ := inner
          refine ⟨.snd dp, ?_⟩
          intro target parallel
          cases parallel with
          | snd pairStep => exact .snd (inner _ pairStep)
  | refl term inner =>
      obtain ⟨dt, inner⟩ := inner
      refine ⟨.refl dt, ?_⟩
      intro target parallel
      cases parallel with
      | refl termStep => exact .refl (inner _ termStep)

/-- The diamond is a theorem of the specific completed native relation,
not an assumption about arbitrary nonlinear algebraic rules. -/
theorem diamond : Diamond := by
  intro n source left right first second
  obtain ⟨common, reaches⟩ := cofinal source
  exact ⟨common, reaches _ first, reaches _ second⟩

theorem conversion_join {left right : Tower.Tm n} (conversion : AuthoredConv left right) :
    ∃ common, ParStar left common ∧ ParStar right common :=
  authored_conv_join diamond conversion

def nativePiConversionBoundary : PiConversionBoundary IntrinsicMILHypothesis.rules :=
  piConversionBoundaryOfDiamond diamond

def nativeSigmaConversionBoundary : SigmaConversionBoundary IntrinsicMILHypothesis.rules :=
  sigmaConversionBoundaryOfDiamond diamond

#print axioms cofinal_beta
#print axioms cofinal_pair_fst
#print axioms cofinal_pair_snd
#print axioms cofinal_structural_app
#print axioms cofinal_app
#print axioms cofinal
#print axioms diamond
#print axioms conversion_join
#print axioms nativePiConversionBoundary
#print axioms nativeSigmaConversionBoundary

end MILConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
