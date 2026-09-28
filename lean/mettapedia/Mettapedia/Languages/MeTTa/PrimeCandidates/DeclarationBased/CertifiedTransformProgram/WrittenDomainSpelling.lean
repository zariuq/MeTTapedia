import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.WrittenDomains
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.KernelSpelling

/-!
# Written domains in the kernel's spelling

The kernel spells a λ with a written domain `(Lam A b)` and a bare one
`(Lam b)`; its erasure drops the domain. A term with written domains, spelled
and then erased in the kernel's spelling, is the spelling of its erasure in
the calculus. So the runtime's erasure and the calculus's erasure are one
erasure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.WrittenDomainSpelling

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open CertifiedTransformProgram.ArtifactComparison (KTerm)

/-- The kernel spelling of a term with written domains. -/
def spell : {n : Nat} → ATm Tower.Head n → Option KTerm
  | _, .var index => some (.idx index.val)
  | _, .const name => (KTerm.nameText name).map .declConst
  | _, .head (.sort (.const level)) => some (.sortConst level)
  | _, .head _ => none
  | _, .pi domain codomain => do pure (.pi (← spell domain) (← spell codomain))
  | _, .sigma domain codomain => do pure (.sigma (← spell domain) (← spell codomain))
  | _, .id carrier left right =>
      do pure (.ident (← spell carrier) (← spell left) (← spell right))
  | _, .lamBare body => do pure (.lamBare (← spell body))
  | _, .lamTyped domain body => do pure (.lamTyped (← spell domain) (← spell body))
  | _, .app function argument => do pure (.app (← spell function) (← spell argument))
  | _, .pair first second => do pure (.pair (← spell first) (← spell second))
  | _, .fst package => do pure (.fst (← spell package))
  | _, .snd package => do pure (.snd (← spell package))
  | _, .refl term => do pure (.refl (← spell term))

/-- Spelling then erasing in the kernel's spelling is spelling the erasure. -/
theorem erase_spell : ∀ {n : Nat} (term : ATm Tower.Head n) {spelled : KTerm},
    spell term = some spelled →
      KTerm.ofTm (ATm.erase term) = some (IdentityEquality.KernelSpelling.erase spelled)
  | _, .var index, spelled, equal => by
      simp only [spell, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .const name, spelled, equal => by
      simp only [spell, Option.map_eq_some_iff] at equal
      obtain ⟨text, named, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, named, IdentityEquality.KernelSpelling.erase]
  | _, .head (.sort (.const level)), spelled, equal => by
      simp only [spell, Option.some.injEq] at equal
      subst equal
      rfl
  | _, .head (.sort (.param _)), _, equal => by simp [spell] at equal
  | _, .head (.sort (.succ _)), _, equal => by simp [spell] at equal
  | _, .head (.sort (.max _ _)), _, equal => by simp [spell] at equal
  | _, .head .legacyGround, _, equal => by simp [spell] at equal
  | _, .pi domain codomain, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨d, hd, c, hc, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell domain hd, erase_spell codomain hc,
        IdentityEquality.KernelSpelling.erase]
  | _, .sigma domain codomain, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨d, hd, c, hc, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell domain hd, erase_spell codomain hc,
        IdentityEquality.KernelSpelling.erase]
  | _, .id carrier left right, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨c, hc, l, hl, r, hr, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell carrier hc, erase_spell left hl,
        erase_spell right hr, IdentityEquality.KernelSpelling.erase]
  | _, .lamBare body, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨b, hb, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell body hb,
        IdentityEquality.KernelSpelling.erase]
  | _, .lamTyped domain body, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨d, _, b, hb, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell body hb,
        IdentityEquality.KernelSpelling.erase]
  | _, .app function argument, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨f, hf, a, ha, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell function hf, erase_spell argument ha,
        IdentityEquality.KernelSpelling.erase]
  | _, .pair first second, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨f, hf, s, hs, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell first hf, erase_spell second hs,
        IdentityEquality.KernelSpelling.erase]
  | _, .fst package, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨p, hp, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell package hp,
        IdentityEquality.KernelSpelling.erase]
  | _, .snd package, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨p, hp, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell package hp,
        IdentityEquality.KernelSpelling.erase]
  | _, .refl term, spelled, equal => by
      simp only [spell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at equal
      obtain ⟨t, ht, rfl⟩ := equal
      simp [ATm.erase, KTerm.ofTm, erase_spell term ht,
        IdentityEquality.KernelSpelling.erase]

/-! ## Controls -/

/-- The identity at `num` with its domain written, and without it. -/
def typedIdentity : ATm Tower.Head 0 :=
  .lamTyped (.const `num) (.var 0)

def bareIdentity : ATm Tower.Head 0 :=
  .lamBare (.var 0)

theorem typedIdentity_spelled :
    spell typedIdentity = some (.lamTyped (.declConst "num") (.idx 0)) := rfl

/-- The two spellings differ, their erasures coincide. -/
theorem identities_erase_alike :
    spell typedIdentity ≠ spell bareIdentity ∧
      ATm.erase typedIdentity = ATm.erase bareIdentity := by
  refine ⟨?_, rfl⟩
  rw [typedIdentity_spelled]
  simp [spell, bareIdentity]

/-- The runtime erasure of the written identity is the spelling of the bare one. -/
theorem typedIdentity_erases :
    KTerm.ofTm (ATm.erase typedIdentity) =
      some (IdentityEquality.KernelSpelling.erase (.lamTyped (.declConst "num") (.idx 0))) :=
  erase_spell typedIdentity typedIdentity_spelled

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.WrittenDomainSpelling
