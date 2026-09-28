import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayRenaming

/-!
# Scope transport for the replay-assembled set interpretation

Renaming the existing evidence tree and its native annotations commutes with
environment reindexing. Both the set value and the retained product domain
are transported, including beneath nested lambdas. No injectivity or model
soundness assumption is needed for this structural law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (extend extend_rename)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n m : Nat}

def Meaning.reindex (rho : Ren n m) (meaning : Meaning.{u} n) : Meaning.{u} m :=
  ⟨fun env => meaning.value (env ∘ rho),
    meaning.productDomain?.map (fun domain env => domain (env ∘ rho))⟩

/-- This transports an actual assembly result, not a chosen denotation witness.
The associated checker-renaming theorem separately establishes acceptance. -/
theorem assemble_rename
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (code : Code Head ConversionCode n) :
    ∀ (subject type : Tm Head n) (meaning : Meaning.{u} n),
      assemble heads constants code subject type = some meaning →
      ∀ {m : Nat} (rho : Ren n m),
        assemble heads constants (code.rename renameConversion rho)
          (rename rho subject) (rename rho type) = some (meaning.reindex rho) := by
  induction code with
  | headType | var | const _ _ _ | reflIntro _ _ _ =>
      intro subject type meaning assembled m rho
      cases subject <;> simp only [assemble, reduceCtorEq, Option.some.injEq] at assembled
      all_goals subst meaning; rfl
  | piForm u v domain body ihA ihB | sigmaForm u v domain body ihA ihB =>
      intro subject type meaning assembled m rho
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨a, atA, b, atB, rfl⟩ := assembled
      have renamedA := ihA _ _ a atA rho
      have renamedB := ihB _ _ b atB (liftRen rho)
      simp only [rename] at renamedA renamedB
      simp only [Code.rename, rename, assemble,
        renamedA, renamedB,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Meaning.reindex, Meaning.plain, Option.map_some, Option.map_none, extend_rename]
  | lamIntro level formation body ihFormation ihBody =>
      intro subject type meaning assembled m rho
      cases subject <;> cases type <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨formed, atFormation, domain, atDomain, b, atBody, rfl⟩ := assembled
      have renamedFormation := ihFormation _ _ formed atFormation rho
      simp only [rename] at renamedFormation
      simp only [Code.rename, rename, assemble,
        renamedFormation, ihBody _ _ b atBody (liftRen rho),
        Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Meaning.reindex, Meaning.plain, atDomain, Option.map_some, Option.map_none, extend_rename]
  | appElim A B function argument ihF ihA =>
      intro subject type meaning assembled m rho
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨f, atF, a, atA, rfl⟩ := assembled
      have renamedF := ihF _ _ f atF rho
      simp only [rename] at renamedF
      simp only [Code.rename, rename, assemble, renamedF, ihA _ _ a atA rho,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
  | pairIntro level formation first second _ ihX ihY =>
      intro subject type meaning assembled m rho
      cases subject <;> cases type <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨x, atX, y, atY, rfl⟩ := assembled
      simp only [Code.rename, rename, assemble, ← rename_inst0,
        ihX _ _ x atX rho, ihY _ _ y atY rho,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
  | fstElim B pair ihPair | sndElim A B pair ihPair =>
      intro subject type meaning assembled m rho
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨p, atP, rfl⟩ := assembled
      have renamedP := ihPair _ _ p atP rho
      simp only [rename] at renamedP
      simp only [Code.rename, rename, assemble, renamedP,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
  | idForm level formation left right _ ihX ihY =>
      intro subject type meaning assembled m rho
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨x, atX, y, atY, rfl⟩ := assembled
      simp only [Code.rename, rename, assemble, ihX _ _ x atX rho, ihY _ _ y atY rho,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
  | cumul level source ih =>
      intro subject type meaning assembled m rho
      cases type <;> simp only [assemble, reduceCtorEq] at assembled
      simpa only [Code.rename, rename, assemble] using ih subject (.head level) meaning assembled rho
  | convert A level source formation conversion ih _ =>
      intro subject type meaning assembled m rho
      simpa only [Code.rename, assemble] using ih subject A meaning assembled rho

#print axioms assemble_rename

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
