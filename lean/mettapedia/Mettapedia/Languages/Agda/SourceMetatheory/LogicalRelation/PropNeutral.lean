import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropReflexivity

/-!
Neutral reflection for the concrete relation. This supplies the variable
case of semantic validity and the fresh-variable argument for semantic Pi
component extraction. It is derived for every current-level Pi family; no
source Pi-injectivity or general subject-reduction premise is used.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

structure NeutralReflection (Γ : RawContext n) (A : Ty n) (P : Pack n) : Prop where
  term : ∀ {t}, Neutral t → Typing Γ t A → P.redTm t
  equality : ∀ {t u}, Neutral t → Neutral u → TermEq Γ t u A → P.eqTm t u

def LowerNeutral (bound : Nat) (lower : Nat → Relation) : Prop :=
  ∀ {k : Nat}, k < bound → ∀ {n : Nat} {Γ : RawContext n} {A : Ty n},
    FormTy Γ A → Neutral A.term → lower k Γ A (neutralPack Γ A)

theorem LR.neutralReflection {bound : Nat} {lower : Nat → Relation}
    (lowerNeutral : LowerNeutral bound lower) {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LR bound lower Γ A P) : NeutralReflection Γ A P := by
  induction related with
  | @«universe» n Γ A k less red =>
      obtain ⟨red⟩ := red
      constructor
      · intro t neutral typed
        have atUniverse : Typing Γ t (Ty.universe k) := .conv typed red.equal
        exact ⟨t, ⟨.refl atUniverse⟩, ⟨.neutral neutral⟩, neutralPack Γ (.el k t),
          lowerNeutral less (.ofTyping atUniverse) neutral⟩
      · intro t u left right equal
        have atUniverse : TermEq Γ t u (Ty.universe k) := .conv equal red.equal
        have endpoints := termEndpoints atUniverse
        exact ⟨t, u, ⟨.refl endpoints.left⟩, ⟨.refl endpoints.right⟩,
          ⟨.neutral left⟩, ⟨.neutral right⟩, ⟨atUniverse⟩,
          ⟨neutralPack Γ (.el k u), lowerNeutral less (.ofTyping endpoints.right) right⟩,
          neutralPack Γ (.el k t), lowerNeutral less (.ofTyping endpoints.left) left,
          .el k u, ⟨TypeRed.refl (.ofTyping endpoints.right)⟩, ⟨right⟩,
          ⟨TypeEq.atSort atUniverse⟩⟩
  | neutral red _ =>
      obtain ⟨red⟩ := red
      constructor
      · intro t neutral typed
        exact ⟨t, ⟨.refl (.conv typed red.equal)⟩, ⟨neutral⟩⟩
      · intro t u left right equal
        have atHead := TermEq.conv equal red.equal
        have endpoints := termEndpoints atHead
        exact ⟨t, u, ⟨.refl endpoints.left⟩, ⟨.refl endpoints.right⟩, ⟨left⟩, ⟨right⟩, ⟨atHead⟩⟩
  | @pi n Γ A domain codomain red _ _ family domains _ _ codomainIH =>
      obtain ⟨red⟩ := red
      have member {t : Term n} (neutral : Neutral t) (typed : Typing Γ t (Ty.pi domain codomain)) :
          PiRedTm family t := by
        refine ⟨t, ⟨.refl typed⟩, ⟨.neutral neutral⟩, ?_, ?_⟩
        · intro m Δ ρ w a argument
          obtain ⟨argumentTyped⟩ := (domains w).escape.typing argument
          have headTyped : Typing Δ (t.rename ρ) (Ty.pi (domain.rename ρ) (codomain.rename ρ)) := by
            simpa only [Ty.pi_rename] using w.typing typed
          exact (codomainIH w argument).term (.app (neutral.rename ρ)) (.app headTyped argumentTyped)
        · intro m Δ ρ w a b left _right equal
          obtain ⟨argumentsEqual⟩ := (domains w).escape.termEquality equal
          have headTyped : Typing Δ (t.rename ρ) (Ty.pi (domain.rename ρ) (codomain.rename ρ)) := by
            simpa only [Ty.pi_rename] using w.typing typed
          exact (codomainIH w left).equality (.app (neutral.rename ρ)) (.app (neutral.rename ρ))
            (.appCong (.refl headTyped) argumentsEqual)
      constructor
      · intro t neutral typed
        exact member neutral (.conv typed red.equal)
      · intro t u left right equal
        have atHead : TermEq Γ t u (Ty.pi domain codomain) := .conv equal red.equal
        have endpoints := termEndpoints atHead
        refine ⟨member left endpoints.left, member right endpoints.right,
          t, u, ⟨.refl endpoints.left⟩, ⟨.refl endpoints.right⟩, ⟨atHead⟩, ?_⟩
        intro m Δ ρ w a argument
        obtain ⟨argumentTyped⟩ := (domains w).escape.typing argument
        have headsEqual : TermEq Δ (t.rename ρ) (u.rename ρ)
            (Ty.pi (domain.rename ρ) (codomain.rename ρ)) := by
          simpa only [Ty.pi_rename] using w.termEquality atHead
        exact (codomainIH w argument).equality (.app (left.rename ρ)) (.app (right.rename ρ))
          (.appCong headsEqual (.refl argumentTyped))

theorem LogRel.neutralReflection {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) : NeutralReflection Γ A P := by
  refine LR.neutralReflection ?_ related
  intro k less n Δ B formed neutral
  apply (below_iff less).mpr
  exact LR.neutral ⟨TypeRed.refl formed⟩ ⟨neutral⟩

/-- Every formed neutral type is reducible at every semantic stratum. -/
theorem LogRel.neutralType (bound : Nat) {Γ : RawContext n} {A : Ty n}
    (formed : FormTy Γ A) (neutral : Neutral A.term) :
    LogRel bound Γ A (neutralPack Γ A) :=
  LR.neutral ⟨TypeRed.refl formed⟩ ⟨neutral⟩

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
