import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedConversionDevelopment

/-!
# Decoder developments with native computation in the predicate arguments

The two opaque HOL formula constructors have rigid spines. Their arbitrary
arguments may contain all native computations, including duplicated metadata.
The proof decoder develops those arguments without changing the source rules.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeMixedConversionParallel

open Presentation NativeIndexedFamilies
open FormationSensitiveHOLProofFamily FormationSensitiveHOLUniformList

variable {n : Nat}

theorem rawImp_inversion {p q result : Tower.Tm n}
    (parallel : Par (rawImp p q) result) :
    ∃ p' q', result = rawImp p' q' ∧ Par p p' ∧ Par q q' := by
  obtain ⟨arguments, shape, steps⟩ := spine_inversion `HOLUniformList.implication [q, p]
    (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases steps with | cons hq rest =>
    cases rest with | cons hp rest =>
      cases rest
      exact ⟨_, _, shape, hp, hq⟩

theorem rawImp_to_fixed {p q p' q' : Tower.Tm n}
    (parallel : Par (rawImp p q) (rawImp p' q')) : Par p p' ∧ Par q q' := by
  obtain ⟨p'', q'', shape, hp, hq⟩ := rawImp_inversion parallel
  have fields := @spine_injective n `HOLUniformList.implication [q', p'] [q'', p''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl⟩
  exact ⟨hp, hq⟩

theorem universalProposition_inversion {a f result : Tower.Tm n}
    (parallel : Par (universalProposition a f) result) :
    ∃ a' f', result = universalProposition a' f' ∧ Par a a' ∧ Par f f' := by
  obtain ⟨arguments, shape, steps⟩ := spine_inversion `HOLUniformList.universal [f, a]
    (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases steps with | cons hf rest =>
    cases rest with | cons ha rest =>
      cases rest
      exact ⟨_, _, shape, ha, hf⟩

theorem universalProposition_to_fixed {a f a' f' : Tower.Tm n}
    (parallel : Par (universalProposition a f) (universalProposition a' f')) :
    Par a a' ∧ Par f f' := by
  obtain ⟨a'', f'', shape, ha, hf⟩ := universalProposition_inversion parallel
  have fields := @spine_injective n `HOLUniformList.universal [f', a'] [f'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl⟩
  exact ⟨ha, hf⟩

theorem decoder_implication_inversion {p q result : Tower.Tm n}
    (parallel : Par (proof (rawImp p q)) result) :
    (∃ p' q', result = proof (rawImp p' q') ∧ Par p p' ∧ Par q q') ∨
    (∃ p' q', result = implicationFamily p' q' ∧ Par p p' ∧ Par q q') := by
  generalize sourceEq : proof (rawImp p q) = source at parallel
  cases parallel <;>
    simp [proof, rawImp, universalProposition, Intrinsic.eliminateApp,
      Intrinsic.identityEliminateApp, IntrinsicRelator.eliminateApp,
      Intrinsic.eliminateName, Intrinsic.identityEliminateName,
      IntrinsicRelator.eliminateName, proofName] at sourceEq
  case app function argument =>
    obtain ⟨rfl, rfl⟩ := sourceEq
    cases function
    obtain ⟨p', q', rfl, hp, hq⟩ := rawImp_inversion argument
    exact .inl ⟨p', q', rfl, hp, hq⟩
  case implication hp hq =>
    obtain ⟨rfl, rfl⟩ := sourceEq
    exact .inr ⟨_, _, rfl, hp, hq⟩

theorem decoder_universal_inversion {a f result : Tower.Tm n}
    (parallel : Par (proof (universalProposition a f)) result) :
    (∃ a' f', result = proof (universalProposition a' f') ∧ Par a a' ∧ Par f f') ∨
    (∃ a' f', result = universalFamily a' f' ∧ Par a a' ∧ Par f f') := by
  generalize sourceEq : proof (universalProposition a f) = source at parallel
  cases parallel <;>
    simp [proof, rawImp, universalProposition, Intrinsic.eliminateApp,
      Intrinsic.identityEliminateApp, IntrinsicRelator.eliminateApp,
      Intrinsic.eliminateName, Intrinsic.identityEliminateName,
      IntrinsicRelator.eliminateName, proofName] at sourceEq
  case app function argument =>
    obtain ⟨rfl, rfl⟩ := sourceEq
    cases function
    obtain ⟨a', f', rfl, ha, hf⟩ := universalProposition_inversion argument
    exact .inl ⟨a', f', rfl, ha, hf⟩
  case universal ha hf =>
    obtain ⟨rfl, rfl⟩ := sourceEq
    exact .inr ⟨_, _, rfl, ha, hf⟩

theorem cofinal_implication {p q : Tower.Tm n}
    (argument : Cofinal (rawImp p q)) : Cofinal (proof (rawImp p q)) := by
  obtain ⟨common, argument⟩ := argument
  obtain ⟨dp, dq, rfl, _, _⟩ := rawImp_inversion (argument _ (par_refl _))
  refine ⟨implicationFamily dp dq, ?_⟩
  intro result parallel
  rcases decoder_implication_inversion parallel with structural | decoded
  · obtain ⟨p', q', rfl, hp, hq⟩ := structural
    obtain ⟨hpd, hqd⟩ := rawImp_to_fixed (argument _ (.app (.app (.const _) hp) hq))
    exact .implication hpd hqd
  · obtain ⟨p', q', rfl, hp, hq⟩ := decoded
    obtain ⟨hpd, hqd⟩ := rawImp_to_fixed (argument _ (.app (.app (.const _) hp) hq))
    exact .pi (.app (.const _) hpd) (par_rename wk (.app (.const _) hqd))

theorem cofinal_universal {a f : Tower.Tm n}
    (argument : Cofinal (universalProposition a f)) :
    Cofinal (proof (universalProposition a f)) := by
  obtain ⟨common, argument⟩ := argument
  obtain ⟨da, df, rfl, _, _⟩ := universalProposition_inversion (argument _ (par_refl _))
  refine ⟨universalFamily da df, ?_⟩
  intro result parallel
  rcases decoder_universal_inversion parallel with structural | decoded
  · obtain ⟨a', f', rfl, ha, hf⟩ := structural
    obtain ⟨had, hfd⟩ := universalProposition_to_fixed
      (argument _ (.app (.app (.const _) ha) hf))
    exact .universal had hfd
  · obtain ⟨a', f', rfl, ha, hf⟩ := decoded
    obtain ⟨had, hfd⟩ := universalProposition_to_fixed
      (argument _ (.app (.app (.const _) ha) hf))
    exact .pi had (.app (.const _) (.app (par_rename wk hfd) (.var 0)))

#print axioms rawImp_inversion
#print axioms universalProposition_inversion
#print axioms decoder_implication_inversion
#print axioms decoder_universal_inversion
#print axioms cofinal_implication
#print axioms cofinal_universal

end HOLNativeMixedConversionParallel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

