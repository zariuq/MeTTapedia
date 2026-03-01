import Mettapedia.Logic.PLNIntensionalWorldModel

/-!
# Chapter 12 Intensional-Inheritance Canaries

Executable fixture theorems for Chapter-12 mixed-channel behavior:

1. Positive: extensional-projection mixed policy returns extensional evidence.
2. Positive: ASSOC-projection mixed policy returns ASSOC evidence.
3. Negative: these two projections are not equivalent on a split-evidence fixture.
-/

namespace Mettapedia.Logic.PLNIntensionalCanary

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel
open scoped ENNReal

/-- Toy untyped query family for Chapter-12 inheritance channels. -/
inductive ToyInheritanceQuery where
  | ext : Bool → Bool → ToyInheritanceQuery
  | assoc : Bool → Bool → ToyInheritanceQuery
  | pat : Bool → Bool → ToyInheritanceQuery
  deriving DecidableEq, Repr

/-- Triple-state fixture: extensional / ASSOC / PAT evidence channels. -/
abbrev ToyState := Evidence × Evidence × Evidence

noncomputable instance : EvidenceType ToyState where
  toAddCommMonoid := inferInstance

instance : WorldModel ToyState ToyInheritanceQuery where
  evidence W q :=
    match q with
    | .ext _ _ => W.1
    | .assoc _ _ => W.2.1
    | .pat _ _ => W.2.2
  evidence_add W₁ W₂ q := by
    cases q <;> simp [Prod.fst_add, Prod.snd_add]

def toyExt (a b : Bool) : ToyInheritanceQuery := .ext a b
def toyAssoc (a b : Bool) : ToyInheritanceQuery := .assoc a b
def toyPat (a b : Bool) : ToyInheritanceQuery := .pat a b

/-- Mixed-query policy that projects to the extensional channel. -/
def encMixedExtensional :
    InheritanceQueryBuilder Bool ToyInheritanceQuery :=
  InheritanceQueryBuilder.mixedAsExtensional toyExt toyAssoc toyPat

/-- Mixed-query policy that projects to the ASSOC channel. -/
def encMixedAssoc :
    InheritanceQueryBuilder Bool ToyInheritanceQuery :=
  InheritanceQueryBuilder.mixedAsAssoc toyExt toyAssoc toyPat

/-- Split fixture: extensional and ASSOC channels intentionally disagree. -/
def Wsplit : ToyState := (⟨3, 1⟩, ⟨1, 4⟩, ⟨0, 2⟩)

/-- Positive canary: extensional-projection mixed policy equals extensional evidence. -/
theorem canary_ch12_mixed_extensional_projection :
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedExtensional true false
      =
    InheritanceQueryBuilder.extensionalEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedExtensional true false := by
  rfl

/-- Positive canary: ASSOC-projection mixed policy equals ASSOC evidence. -/
theorem canary_ch12_mixed_assoc_projection :
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedAssoc true false
      =
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedAssoc true false := by
  rfl

/-- Negative canary (non-equivalence):
on `Wsplit`, extensional-projection and ASSOC-projection mixed policies diverge. -/
theorem canary_ch12_mixed_projection_non_equivalent :
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedExtensional true false
      ≠
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedAssoc true false := by
  intro hEq
  have hpos : (3 : ℝ≥0∞) = 1 := by
    exact congrArg Evidence.pos (by simpa [Wsplit, encMixedExtensional, encMixedAssoc,
      InheritanceQueryBuilder.mixedEvidence, InheritanceQueryBuilder.mixedQ,
      InheritanceQueryBuilder.mixedAsExtensional, InheritanceQueryBuilder.mixedAsAssoc,
      toyExt, toyAssoc] using hEq)
  norm_num at hpos

end Mettapedia.Logic.PLNIntensionalCanary
