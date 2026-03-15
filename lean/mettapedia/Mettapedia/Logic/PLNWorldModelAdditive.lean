import Mathlib.Data.Multiset.Fold
import Mettapedia.Logic.PLNWorldModel

/-!
# Additive World-Model Extensions

This module isolates the generic additive extension theorem behind the
`PLNWorldModel` interface:

- atomic observations contribute evidence query-wise;
- multisets of observations extend that contribution additively;
- the extension is uniquely determined once we require preservation of `0`,
  singletons, and multiset addition.

The zero law matters. Singleton preservation plus additivity alone does not fix
`E 0`, so it does not characterize a unique extension.

## Generic (polymorphic) additive extension

The `Gen*` variants are polymorphic over any `AddCommMonoid Ev`, so they apply
to `Evidence`, `MultiEvidence k`, `NormalGammaEvidence`, or any future conjugate
family. The original `Evidence`-specific names are preserved as abbreviations.
-/

namespace Mettapedia.Logic.PLNWorldModelAdditive

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

/-! ## Generic Additive Extension (polymorphic over evidence type) -/

/-- Generic atomic query-wise evidence contribution. -/
abbrev GenAtomicEvidenceContribution (Obs Query Ev : Type*) := Obs → Query → Ev

section Generic

variable {Obs Query Ev : Type*}

private noncomputable def genFold [AddCommMonoid Ev] (s : Multiset Ev) : Ev :=
  @Multiset.fold Ev (· + ·)
    ⟨fun _ _ => add_comm _ _⟩ ⟨fun _ _ _ => add_assoc _ _ _⟩ 0 s

/-- The canonical additive extension, polymorphic over any `AddCommMonoid`. -/
noncomputable def genAdditiveExtension [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (σ : Multiset Obs) (q : Query) : Ev :=
  genFold (σ.map (fun o => a o q))

@[simp] theorem genAdditiveExtension_zero [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev) (q : Query) :
    genAdditiveExtension a (0 : Multiset Obs) q = 0 := by
  simp [genAdditiveExtension, genFold]

@[simp] theorem genAdditiveExtension_singleton [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev) (o : Obs) (q : Query) :
    genAdditiveExtension a ({o} : Multiset Obs) q = a o q := by
  simp [genAdditiveExtension, genFold, Multiset.map_singleton,
        @Multiset.fold_singleton Ev (· + ·)]

theorem genAdditiveExtension_cons [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (o : Obs) (σ : Multiset Obs) (q : Query) :
    genAdditiveExtension a (o ::ₘ σ) q =
      a o q + genAdditiveExtension a σ q := by
  simp [genAdditiveExtension, genFold]

theorem genAdditiveExtension_add [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    genAdditiveExtension a (σ₁ + σ₂) q =
      genAdditiveExtension a σ₁ q + genAdditiveExtension a σ₂ q := by
  simp only [genAdditiveExtension, genFold, Multiset.map_add]
  simpa [add_assoc, add_comm, add_left_comm] using
    @Multiset.fold_add Ev (· + ·)
      ⟨fun _ _ => add_comm _ _⟩ ⟨fun _ _ _ => add_assoc _ _ _⟩
      (s₁ := σ₁.map (fun o => a o q))
      (s₂ := σ₂.map (fun o => a o q))
      (b₁ := (0 : Ev)) (b₂ := (0 : Ev))

/-- A query-wise map on multisets is a generic additive extension when it
preserves `0`, singletons, and multiset addition. -/
structure GenIsAdditiveExtension [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (E : Multiset Obs → Query → Ev) : Prop where
  zero : ∀ q, E 0 q = 0
  singleton : ∀ o q, E ({o} : Multiset Obs) q = a o q
  add : ∀ σ₁ σ₂ q, E (σ₁ + σ₂) q = E σ₁ q + E σ₂ q

theorem genIsAdditiveExtension_genAdditiveExtension [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev) :
    GenIsAdditiveExtension a (genAdditiveExtension a) where
  zero := genAdditiveExtension_zero a
  singleton := genAdditiveExtension_singleton a
  add := genAdditiveExtension_add a

theorem eq_genAdditiveExtension [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    {E : Multiset Obs → Query → Ev}
    (hE : GenIsAdditiveExtension a E) :
    E = genAdditiveExtension a := by
  funext σ q
  induction σ using Multiset.induction_on with
  | empty => exact hE.zero q
  | @cons o σ ih =>
      calc
        E (o ::ₘ σ) q = E (({o} : Multiset Obs) + σ) q := by simp
        _ = E ({o} : Multiset Obs) q + E σ q := hE.add ({o} : Multiset Obs) σ q
        _ = a o q + genAdditiveExtension a σ q := by rw [hE.singleton, ih]
        _ = genAdditiveExtension a (o ::ₘ σ) q := by
          simp [genAdditiveExtension, genFold]

theorem genExistsUnique_additiveExtension [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev) :
    ∃! E : Multiset Obs → Query → Ev, GenIsAdditiveExtension a E := by
  exact ⟨genAdditiveExtension a, genIsAdditiveExtension_genAdditiveExtension a, fun E hE =>
    eq_genAdditiveExtension a hE⟩

end Generic

/-! ## Evidence-specific specializations (backward-compatible) -/

variable {Obs' Query' : Type*}

local instance : Std.Commutative (fun x y : Evidence => x + y) where
  comm := add_comm

local instance : Std.Associative (fun x y : Evidence => x + y) where
  assoc := add_assoc

/-- Atomic query-wise evidence contribution from one observation. -/
abbrev AtomicEvidenceContribution (Obs Query : Type*) := Obs → Query → Evidence

/-- The canonical additive extension of an atomic evidence contribution from
single observations to multisets of observations. -/
noncomputable def additiveExtension
    (a : AtomicEvidenceContribution Obs' Query')
    (σ : Multiset Obs') (q : Query') : Evidence :=
  genAdditiveExtension a σ q

@[simp] theorem additiveExtension_zero
    (a : AtomicEvidenceContribution Obs' Query') (q : Query') :
    additiveExtension a 0 q = 0 :=
  genAdditiveExtension_zero a q

@[simp] theorem additiveExtension_singleton
    (a : AtomicEvidenceContribution Obs' Query') (o : Obs') (q : Query') :
    additiveExtension a ({o} : Multiset Obs') q = a o q :=
  genAdditiveExtension_singleton a o q

theorem additiveExtension_cons
    (a : AtomicEvidenceContribution Obs' Query')
    (o : Obs') (σ : Multiset Obs') (q : Query') :
    additiveExtension a (o ::ₘ σ) q =
      a o q + additiveExtension a σ q :=
  genAdditiveExtension_cons a o σ q

theorem additiveExtension_add
    (a : AtomicEvidenceContribution Obs' Query')
    (σ₁ σ₂ : Multiset Obs') (q : Query') :
    additiveExtension a (σ₁ + σ₂) q =
      additiveExtension a σ₁ q + additiveExtension a σ₂ q :=
  genAdditiveExtension_add a σ₁ σ₂ q

/-- A query-wise map on multisets is an additive extension when it preserves
`0`, singletons, and multiset addition. -/
abbrev IsAdditiveExtension
    (a : AtomicEvidenceContribution Obs' Query')
    (E : Multiset Obs' → Query' → Evidence) : Prop :=
  GenIsAdditiveExtension a E

theorem isAdditiveExtension_additiveExtension
    (a : AtomicEvidenceContribution Obs' Query') :
    IsAdditiveExtension a (additiveExtension a) :=
  genIsAdditiveExtension_genAdditiveExtension a

/-- The additive extension is uniquely determined by preservation of `0`,
singletons, and multiset addition. -/
theorem eq_additiveExtension_of_isAdditiveExtension
    (a : AtomicEvidenceContribution Obs' Query')
    {E : Multiset Obs' → Query' → Evidence}
    (hE : IsAdditiveExtension a E) :
    E = additiveExtension a :=
  eq_genAdditiveExtension a hE

/-- Free additive extension theorem over multisets of observations. -/
theorem existsUnique_additiveExtension
    (a : AtomicEvidenceContribution Obs' Query') :
    ∃! E : Multiset Obs' → Query' → Evidence, IsAdditiveExtension a E :=
  genExistsUnique_additiveExtension a

/-- Package multiset addition as an `EvidenceType` when using multisets as
posterior states. This is a non-instance helper so existing domain-specific
instances remain free to choose their own import boundaries. -/
def multisetEvidenceType (Obs : Type*) : EvidenceType (Multiset Obs) where

/-- Any atomic evidence contribution induces a multiset-based world model. -/
noncomputable def worldModelOfAtomicEvidence
    (a : AtomicEvidenceContribution Obs' Query') :
    letI : EvidenceType (Multiset Obs') := multisetEvidenceType Obs'
    WorldModel (Multiset Obs') Query' := by
  letI : EvidenceType (Multiset Obs') := multisetEvidenceType Obs'
  exact
    { evidence := additiveExtension a
      evidence_add := additiveExtension_add a
      evidence_zero := additiveExtension_zero a }

/-! ## Profile-Level Bundling

The generic additive extension is an `AddMonoidHom` from observations
into the evidence-profile object `Query → Ev`.  This is the profile
perspective: each observation multiset determines an entire answer
profile, and the map is additive. -/

/-- The generic additive extension bundled as an `AddMonoidHom` into
    the evidence-profile object `Query → Ev`. -/
noncomputable def genAdditiveExtensionProfileHom [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev) :
    AddMonoidHom (Multiset Obs) (Query → Ev) where
  toFun σ q := genAdditiveExtension a σ q
  map_zero' := funext (genAdditiveExtension_zero a)
  map_add' σ₁ σ₂ := funext (genAdditiveExtension_add a σ₁ σ₂)

/-- The `Evidence`-specialized version. -/
noncomputable def additiveExtensionProfileHom
    (a : AtomicEvidenceContribution Obs' Query') :
    AddMonoidHom (Multiset Obs') (Query' → Evidence) :=
  genAdditiveExtensionProfileHom a

end Mettapedia.Logic.PLNWorldModelAdditive
