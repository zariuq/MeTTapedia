import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityPi

/-!
Pi congruence at the source's left-domain context. The target Pi's formation
comes from proved source endpoint regularity. Its reducibility is derived
from semantic comparison, so a right-domain validity hypothesis is not added.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

def sourcePiEquality {Γ : RawContext n} {A A' : Ty n} {B B' : TyAbs n}
    (domain : FormTy Γ A) (domains : TypeEq Γ A A')
    (codomains : TypeEq (Γ.snoc A) B.open B'.open) : TypeEq Γ (Ty.pi A B) (Ty.pi A' B') := by
  have levelsA := domains.level_eq
  have levelsB : B.level = B'.level := by
    simpa only [TyAbs.level_open] using codomains.level_eq
  have equal := TypeEq.atSort (TermEq.piCong domain domains codomains)
  simpa only [Ty.pi, ← levelsA, ← levelsB] using equal

theorem ValidTypeEq.piCong {Γ : RawContext n} {A A' : Ty n} {B B' : TyAbs n}
    (domains : ValidTypeEq Γ A A') (codomains : ValidTypeEq (Γ.snoc A) B.open B'.open) :
    ValidTypeEq Γ (Ty.pi A B) (Ty.pi A' B') := by
  obtain ⟨formedA⟩ := domains.left.source
  obtain ⟨sourceA⟩ := domains.source
  obtain ⟨sourceB⟩ := codomains.source
  have source := sourcePiEquality formedA sourceA sourceB
  apply ValidTypeEq.ofLeft source (domains.left.pi codomains.left)
  intro m Δ σ substitution
  simp only [Ty.pi_subst]
  rw [(domains.left.piRelated codomains.left substitution).annotatedPack_eq]
  let actual := substitution.sourceEvidence formedA.context
  have sourceEqual := source.substitute actual
  have rightFormation := (typeEndpoints source).right.substitute actual
  refine ⟨A'.subst σ, B'.subst σ,
    ⟨.refl (by simpa only [Ty.pi_subst] using rightFormation)⟩,
    ⟨by simpa only [Ty.pi_subst] using sourceEqual⟩, ?_, ?_⟩
  · intro k Θ ρ world
    simpa only [ValidType.piFamily, Ty.rename_subst] using
      domains.equal (substitution.renaming world)
  · intro k Θ ρ world a argument
    have tails := substitution.renaming world
    have leftDomain := domains.left.reducible tails
    have member : (annotatedPack Θ (A.subst (fun i => (σ i).rename ρ))).redTm a := by
      simpa only [ValidType.piFamily, Ty.rename_subst] using argument
    simpa only [ValidType.piFamily, ty_open_pair, ← TyAbs.rename_subst] using
      codomains.equal (tails.pair leftDomain member)

theorem ValidTermEq.piCong {Γ : RawContext n} {A A' : Ty n} {B B' : TyAbs n}
    (domains : ValidTypeEq Γ A A') (codomains : ValidTypeEq (Γ.snoc A) B.open B'.open) :
    ValidTermEq Γ (.pi A B) (.pi A' B') (Ty.universe (max A.level B.level)) := by
  obtain ⟨formedA⟩ := domains.left.source
  obtain ⟨sourceA⟩ := domains.source
  obtain ⟨sourceB⟩ := codomains.source
  have validPi := domains.piCong codomains
  have levelsA := sourceA.level_eq
  have levelsB : B.level = B'.level := by
    simpa only [TyAbs.level_open] using sourceB.level_eq
  apply ValidTermEq.ofLeft (.piCong formedA sourceA sourceB)
    (ValidTerm.pi domains.left codomains.left)
  intro m Δ σ substitution
  obtain ⟨target⟩ := substitution.formed
  simp only [Ty.universe_subst, Term.subst]
  rw [(universeReducible (max A.level B.level + 1) (max A.level B.level)
    (Nat.lt_succ_self _) target).annotatedPack_eq]
  have left := validPi.left.reducible substitution
  have right := validPi.right.reducible substitution
  have equal := validPi.equal substitution
  change LogRel (max A.level B.level) Δ (.el (max A.level B.level) (.pi (A.subst σ) (B.subst σ)))
    (annotatedPack Δ (.el (max A.level B.level) (.pi (A.subst σ) (B.subst σ)))) at left
  change LogRel (max A'.level B'.level) Δ (.el (max A'.level B'.level) (.pi (A'.subst σ) (B'.subst σ)))
    (annotatedPack Δ (.el (max A'.level B'.level) (.pi (A'.subst σ) (B'.subst σ)))) at right
  change (annotatedPack Δ (.el (max A.level B.level) (.pi (A.subst σ) (B.subst σ)))).eqTy
    (.el (max A'.level B'.level) (.pi (A'.subst σ) (B'.subst σ))) at equal
  rw [← levelsA, ← levelsB] at right equal
  exact universeEquality (Nat.lt_succ_self _) left right equal

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
