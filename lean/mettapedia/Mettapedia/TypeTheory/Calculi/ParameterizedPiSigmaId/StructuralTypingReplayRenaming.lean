import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplay

/-!
# Reindexing the actual structural evidence tree

Compatible context renaming transports successful replay with the same tree
structure and renamed native annotations. Closed declaration formation stays
closed. Conversion payloads use an explicit renaming action whose checker
preservation is qualified separately. The structural-only profile is recovered
by the empty payload action.
This does not assert Boolean-decision invariance under arbitrary
renaming: identifying two well-formed assumptions can repair a formerly
mismatched type. The final control exhibits that distinction explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type} {n m k : Nat}
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)

def Code.rename
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    {n m : Nat} (rho : Ren n m) : Code Head ConversionCode n → Code Head ConversionCode m
  | .headType => .headType
  | .var => .var
  | .const universeHead formation => .const universeHead formation
  | .piForm u v domain body => .piForm u v (domain.rename renameConversion rho)
      (body.rename renameConversion (liftRen rho))
  | .sigmaForm u v domain body => .sigmaForm u v (domain.rename renameConversion rho)
      (body.rename renameConversion (liftRen rho))
  | .lamIntro u formation body => .lamIntro u (formation.rename renameConversion rho)
      (body.rename renameConversion (liftRen rho))
  | .appElim A B function argument =>
      .appElim (Presentation.rename rho A) (Presentation.rename (liftRen rho) B)
        (function.rename renameConversion rho) (argument.rename renameConversion rho)
  | .pairIntro u formation first second =>
      .pairIntro u (formation.rename renameConversion rho)
        (first.rename renameConversion rho) (second.rename renameConversion rho)
  | .fstElim B pair => .fstElim (Presentation.rename (liftRen rho) B)
      (pair.rename renameConversion rho)
  | .sndElim A B pair =>
      .sndElim (Presentation.rename rho A) (Presentation.rename (liftRen rho) B)
        (pair.rename renameConversion rho)
  | .idForm u formation left right =>
      .idForm u (formation.rename renameConversion rho)
        (left.rename renameConversion rho) (right.rename renameConversion rho)
  | .reflIntro A term => .reflIntro (Presentation.rename rho A) (term.rename renameConversion rho)
  | .cumul u term => .cumul u (term.rename renameConversion rho)
  | .convert A u source formation conversion => .convert (Presentation.rename rho A) u
      (source.rename renameConversion rho) (formation.rename renameConversion rho)
      (renameConversion rho conversion)

theorem Code.rename_ext {rho xi : Ren n m} (equal : ∀ index, rho index = xi index)
    (code : Code Head ConversionCode n) :
    code.rename renameConversion rho = code.rename renameConversion xi := by
  have same : rho = xi := funext equal
  rw [same]

@[simp] theorem Code.rename_id
    (conversionId : ∀ {n} (code : ConversionCode n), renameConversion idRen code = code)
    (code : Code Head ConversionCode n) : code.rename renameConversion idRen = code := by
  induction code <;> simp_all only [Code.rename, liftRen_id, Presentation.rename_id]

private theorem liftRen_comp_eq (rhoTwo : Ren m k) (rhoOne : Ren n m) :
    (fun index => liftRen rhoTwo (liftRen rhoOne index)) =
      liftRen (fun index => rhoTwo (rhoOne index)) :=
  funext (liftRen_comp_apply rhoTwo rhoOne)

@[simp] theorem Code.rename_comp
    (conversionComp : ∀ {n m k} (rhoTwo : Ren m k) (rhoOne : Ren n m) (code : ConversionCode n),
      renameConversion rhoTwo (renameConversion rhoOne code) =
        renameConversion (fun index => rhoTwo (rhoOne index)) code)
    (rhoTwo : Ren m k) (rhoOne : Ren n m) (code : Code Head ConversionCode n) :
    (code.rename renameConversion rhoOne).rename renameConversion rhoTwo =
      code.rename renameConversion (fun index => rhoTwo (rhoOne index)) := by
  induction code generalizing m k rhoTwo <;>
    simp_all only [Code.rename, Presentation.rename_comp, liftRen_comp_eq]

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (conversionRenamePreserves : ∀ {n m} (rho : Ren n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (renameConversion rho code) (rename rho left) (rename rho right) = true)

include conversionRenamePreserves

/-- Actual accepted evidence replays after compatible context renaming.
Injectivity is unnecessary for this forward statement. -/
theorem check_rename (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject type : Tm Head n},
      check R conversionCheck context subject type code = true →
      ∀ {m : Nat} {target : Ctx Head m} {rho : Ren n m}, CtxRen context target rho →
        check R conversionCheck target (rename rho subject) (rename rho type)
          (code.rename renameConversion rho) = true := by
  induction code with
  | headType =>
      intro context subject type accepted m target rho compatible
      cases subject <;> cases type <;>
        simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simpa only [Code.rename, rename, check, decide_eq_true_eq] using accepted
  | var =>
      intro context subject type accepted m target rho compatible
      cases subject <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      subst type
      simp only [Code.rename, rename, check, decide_eq_true_eq]
      exact (compatible _).symm
  | const universeHead formation ih =>
      intro context subject type accepted m target rho compatible
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      rename_i name
      cases known : R.constantType name with
      | none => simp only [known, Bool.false_eq_true] at accepted
      | some declared =>
          simp only [known, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨⟨isUniverse, formed⟩, same⟩ := accepted
          subst type
          simp only [Code.rename, rename, check, known, rename_liftClosed,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨isUniverse, formed⟩, True.intro⟩
  | piForm u v domain body ihDomain ihBody =>
      intro context subject type accepted m target rho compatible
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨isU, isV⟩, joined⟩, ihDomain domainAccepted compatible⟩,
        ihBody bodyAccepted (compatible.snoc _)⟩
  | sigmaForm u v domain body ihDomain ihBody =>
      intro context subject type accepted m target rho compatible
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨isU, isV⟩, joined⟩, ihDomain domainAccepted compatible⟩,
        ihBody bodyAccepted (compatible.snoc _)⟩
  | lamIntro universeHead formation body ihFormation ihBody =>
      intro context subject type accepted m target rho compatible
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨isUniverse, formed⟩, bodyAccepted⟩ := accepted
      simp only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨isUniverse, ihFormation formed compatible⟩,
        ihBody bodyAccepted (compatible.snoc _)⟩
  | appElim A B function argument ihFunction ihArgument =>
      intro context subject type accepted m target rho compatible
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨functionAccepted, argumentAccepted⟩, same⟩ := accepted
      subst type
      simp only [Code.rename, rename, check, rename_inst0, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨ihFunction functionAccepted compatible, ihArgument argumentAccepted compatible⟩, True.intro⟩
  | pairIntro universeHead formation first second ihFormation ihFirst ihSecond =>
      intro context subject type accepted m target rho compatible
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨isUniverse, formed⟩, firstAccepted⟩, secondAccepted⟩ := accepted
      simp only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨isUniverse, ihFormation formed compatible⟩,
        ihFirst firstAccepted compatible⟩, ?_⟩
      simpa only [rename_inst0] using ihSecond secondAccepted compatible
  | fstElim B pair ihPair =>
      intro context subject type accepted m target rho compatible
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simpa only [Code.rename, rename, check] using ihPair accepted compatible
  | sndElim A B pair ihPair =>
      intro context subject type accepted m target rho compatible
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨pairAccepted, same⟩ := accepted
      subst type
      simp only [Code.rename, rename, check, rename_inst0, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ihPair pairAccepted compatible, True.intro⟩
  | idForm universeHead formation left right ihFormation ihLeft ihRight =>
      intro context subject type accepted m target rho compatible
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isUniverse, formed⟩, leftAccepted⟩, rightAccepted⟩, same⟩ := accepted
      simp only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨isUniverse, ihFormation formed compatible⟩,
        ihLeft leftAccepted compatible⟩, ihRight rightAccepted compatible⟩, same⟩
  | reflIntro A term ihTerm =>
      intro context subject type accepted m target rho compatible
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨termAccepted, same⟩ := accepted
      subst type
      simp only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ihTerm termAccepted compatible, True.intro⟩
  | cumul universeHead term ihTerm =>
      intro context subject type accepted m target rho compatible
      cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simpa only [Code.rename, rename, check, Bool.and_eq_true, decide_eq_true_eq] using
        And.intro (ihTerm accepted.1 compatible) accepted.2
  | convert A u source formation conversion ihSource ihFormation =>
      intro context subject type accepted m target rho compatible
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨⟨isUniverse, sourceAccepted⟩, formed⟩, converted⟩ := accepted
      simp only [Code.rename, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨isUniverse, ihSource sourceAccepted compatible⟩,
        ihFormation formed compatible⟩, conversionRenamePreserves rho conversion converted⟩

omit conversionRenamePreserves

def noConversionRename {n m : Nat} (_rho : Ren n m) (code : NoConversion n) : NoConversion m :=
  nomatch code

#print axioms check_rename
#print axioms Code.rename_id
#print axioms Code.rename_comp

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
