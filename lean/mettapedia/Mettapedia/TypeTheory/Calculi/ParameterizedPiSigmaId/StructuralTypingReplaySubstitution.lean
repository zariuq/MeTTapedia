import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayRenaming

/-!
# Executable instantiation of retained typing evidence

Each substituted variable supplies its own finite typing certificate. Binder
lifting introduces the new variable certificate and weakens the supplied
ones. All other nodes retain the input typing-rule tree, transforming its
annotations and conversion payloads. Closed declaration formation is reused
unchanged. Successful replay is preserved by this executable transformation.

The transformation also accepts malformed inputs, returning a variable code
at a mismatched structural node. Its contract concerns accepted input replay;
it does not diagnose rejected inputs or search for replacement proofs.
No preservation of rejection is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)

def liftVariableCodes {n m : Nat} (codes : Fin n → Code Head ConversionCode m) :
    Fin (n + 1) → Code Head ConversionCode (m + 1) :=
  Fin.cases .var (fun index => (codes index).rename renameConversion wk)

/-- Transform the supplied finite proof, using the supplied proofs of the
substitution images at variable leaves. Subject and type determine the
premise judgments at nodes whose certificates omit redundant annotations. -/
def Code.substitute
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
    {n m : Nat} (σ : Sub Head n m) (imageCodes : Fin n → Code Head ConversionCode m)
    (subject type : Tm Head n) : Code Head ConversionCode n → Code Head ConversionCode m
  | .headType => .headType
  | .var => match subject with
      | .var index => imageCodes index
      | _ => .var
  | .const u formation => .const u formation
  | .piForm u v domain body => match subject with
      | .pi A B => .piForm u v
          (domain.substitute renameConversion substituteConversion σ imageCodes A (.head u))
          (body.substitute renameConversion substituteConversion (liftSub σ)
            (liftVariableCodes renameConversion imageCodes) B (.head v))
      | _ => .var
  | .sigmaForm u v domain body => match subject with
      | .sigma A B => .sigmaForm u v
          (domain.substitute renameConversion substituteConversion σ imageCodes A (.head u))
          (body.substitute renameConversion substituteConversion (liftSub σ)
            (liftVariableCodes renameConversion imageCodes) B (.head v))
      | _ => .var
  | .lamIntro u formation body => match subject, type with
      | .lam term, .pi A B => .lamIntro u
          (formation.substitute renameConversion substituteConversion σ imageCodes (.pi A B) (.head u))
          (body.substitute renameConversion substituteConversion (liftSub σ)
            (liftVariableCodes renameConversion imageCodes) term B)
      | _, _ => .var
  | .appElim A B function argument => match subject with
      | .app f a => .appElim (subst σ A) (subst (liftSub σ) B)
          (function.substitute renameConversion substituteConversion σ imageCodes f (.pi A B))
          (argument.substitute renameConversion substituteConversion σ imageCodes a A)
      | _ => .var
  | .pairIntro u formation first second => match subject, type with
      | .pair a b, .sigma A B => .pairIntro u
          (formation.substitute renameConversion substituteConversion σ imageCodes (.sigma A B) (.head u))
          (first.substitute renameConversion substituteConversion σ imageCodes a A)
          (second.substitute renameConversion substituteConversion σ imageCodes b (inst0 a B))
      | _, _ => .var
  | .fstElim B pair => match subject with
      | .fst p => .fstElim (subst (liftSub σ) B)
          (pair.substitute renameConversion substituteConversion σ imageCodes p (.sigma type B))
      | _ => .var
  | .sndElim A B pair => match subject with
      | .snd p => .sndElim (subst σ A) (subst (liftSub σ) B)
          (pair.substitute renameConversion substituteConversion σ imageCodes p (.sigma A B))
      | _ => .var
  | .idForm u formation left right => match subject with
      | .id A a b => .idForm u
          (formation.substitute renameConversion substituteConversion σ imageCodes A (.head u))
          (left.substitute renameConversion substituteConversion σ imageCodes a A)
          (right.substitute renameConversion substituteConversion σ imageCodes b A)
      | _ => .var
  | .reflIntro A term => match subject with
      | .refl a => .reflIntro (subst σ A)
          (term.substitute renameConversion substituteConversion σ imageCodes a A)
      | _ => .var
  | .cumul u term => .cumul u
      (term.substitute renameConversion substituteConversion σ imageCodes subject (.head u))
  | .convert A u source formation conversion => .convert (subst σ A) u
      (source.substitute renameConversion substituteConversion σ imageCodes subject A)
      (formation.substitute renameConversion substituteConversion σ imageCodes type (.head u))
      (substituteConversion σ conversion)

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (renamePreserves : ∀ {n m} (ρ : Ren n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (renameConversion ρ code) (Presentation.rename ρ left) (Presentation.rename ρ right) = true)
variable (substitutePreserves : ∀ {n m} (σ : Sub Head n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (substituteConversion σ code) (subst σ left) (subst σ right) = true)

include renamePreserves in
theorem check_liftVariableCodes {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {σ : Sub Head n m} {imageCodes : Fin n → Code Head ConversionCode m}
    (accepted : ∀ index, check R conversionCheck target (σ index)
      (subst σ (Ctx.lookup source index)) (imageCodes index) = true)
    (A : Tm Head n) (index : Fin (n + 1)) :
    check R conversionCheck (.snoc target (subst σ A)) (liftSub σ index)
      (subst (liftSub σ) (Ctx.lookup (.snoc source A) index))
      (liftVariableCodes renameConversion imageCodes index) = true := by
  refine Fin.cases ?_ (fun index => ?_) index
  · simp [liftVariableCodes, liftSub, Ctx.lookup, check, subst_liftSub_wk]
  · simpa only [liftVariableCodes, Fin.cases_succ, liftSub_succ, Ctx.lookup,
      subst_liftSub_wk] using
      check_rename renameConversion R conversionCheck renamePreserves (imageCodes index)
        (accepted index) (rho := wk) (target := .snoc target (subst σ A)) (fun _ => rfl)

include renamePreserves substitutePreserves in
/-- Accepted substitution-image certificates and accepted source evidence
produce an accepted transformed certificate at the actual substituted terms.
No completeness theorem or choice of an alternative derivation is used. -/
theorem check_substitute {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {source : Ctx Head n} {subject type : Tm Head n},
      check R conversionCheck source subject type code = true →
      ∀ {m : Nat} {target : Ctx Head m} (σ : Sub Head n m)
        (imageCodes : Fin n → Code Head ConversionCode m),
        (∀ index, check R conversionCheck target (σ index)
          (subst σ (Ctx.lookup source index)) (imageCodes index) = true) →
        check R conversionCheck target (subst σ subject) (subst σ type)
          (code.substitute renameConversion substituteConversion σ imageCodes subject type) = true := by
  induction code with
  | headType =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> cases type <;>
        simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simpa only [Code.substitute, subst, check, decide_eq_true_eq] using accepted
  | var =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      subst type
      exact images _
  | const u formation ih =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      rename_i name
      cases known : R.constantType name with
      | none => simp only [known, Bool.false_eq_true] at accepted
      | some declared =>
          simp only [known, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨⟨isUniverse, formed⟩, same⟩ := accepted
          subst type
          simp only [Code.substitute, subst, check, known, subst_liftClosed,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨isUniverse, formed⟩, True.intro⟩
  | piForm u v domain body ihDomain ihBody =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨isU, isV⟩, joined⟩, ihDomain domainAccepted σ imageCodes images⟩,
        ihBody bodyAccepted (liftSub σ) _
          (check_liftVariableCodes renameConversion R conversionCheck renamePreserves images _)⟩
  | sigmaForm u v domain body ihDomain ihBody =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨isU, isV⟩, joined⟩, ihDomain domainAccepted σ imageCodes images⟩,
        ihBody bodyAccepted (liftSub σ) _
          (check_liftVariableCodes renameConversion R conversionCheck renamePreserves images _)⟩
  | lamIntro u formation body ihFormation ihBody =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨isUniverse, formed⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨isUniverse, ihFormation formed σ imageCodes images⟩,
        ihBody bodyAccepted (liftSub σ) _
          (check_liftVariableCodes renameConversion R conversionCheck renamePreserves images _)⟩
  | appElim A B function argument ihFunction ihArgument =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨functionAccepted, argumentAccepted⟩, same⟩ := accepted
      subst type
      simp only [Code.substitute, subst, check, subst_inst0, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨ihFunction functionAccepted σ imageCodes images,
        ihArgument argumentAccepted σ imageCodes images⟩, True.intro⟩
  | pairIntro u formation first second ihFormation ihFirst ihSecond =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨isUniverse, formed⟩, firstAccepted⟩, secondAccepted⟩ := accepted
      simp only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨isUniverse, ihFormation formed σ imageCodes images⟩,
        ihFirst firstAccepted σ imageCodes images⟩, ?_⟩
      simpa only [subst_inst0] using ihSecond secondAccepted σ imageCodes images
  | fstElim B pair ihPair =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simpa only [Code.substitute, subst, check] using ihPair accepted σ imageCodes images
  | sndElim A B pair ihPair =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨pairAccepted, same⟩ := accepted
      subst type
      simp only [Code.substitute, subst, check, subst_inst0, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ihPair pairAccepted σ imageCodes images, True.intro⟩
  | idForm u formation left right ihFormation ihLeft ihRight =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isUniverse, formed⟩, leftAccepted⟩, rightAccepted⟩, same⟩ := accepted
      simp only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨isUniverse, ihFormation formed σ imageCodes images⟩,
        ihLeft leftAccepted σ imageCodes images⟩, ihRight rightAccepted σ imageCodes images⟩, same⟩
  | reflIntro A term ihTerm =>
      intro source subject type accepted m target σ imageCodes images
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨termAccepted, same⟩ := accepted
      subst type
      simp only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ihTerm termAccepted σ imageCodes images, True.intro⟩
  | cumul u term ihTerm =>
      intro source subject type accepted m target σ imageCodes images
      cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simpa only [Code.substitute, subst, check, Bool.and_eq_true, decide_eq_true_eq] using
        And.intro (ihTerm accepted.1 σ imageCodes images) accepted.2
  | convert A u sourceCode formation conversion ihSource ihFormation =>
      intro source subject type accepted m target σ imageCodes images
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨⟨isUniverse, sourceAccepted⟩, formed⟩, converted⟩ := accepted
      simp only [Code.substitute, check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨isUniverse, ihSource sourceAccepted σ imageCodes images⟩,
        ihFormation formed σ imageCodes images⟩, substitutePreserves σ conversion converted⟩

#print axioms check_liftVariableCodes
#print axioms check_substitute

include renamePreserves substitutePreserves in
/-- The existing dependent telescope checker supplies all variable-image
premises of certificate transport; there is no second argument validator. -/
theorem check_substitute_of_checked_arguments {n m : Nat}
    {source : Ctx Head n} {target : Ctx Head m} {subject type : Tm Head n}
    {code : Code Head ConversionCode n}
    (accepted : check R conversionCheck source subject type code = true)
    (σ : Sub Head n m) (imageCodes : Fin n → Code Head ConversionCode m)
    (images : TelescopeArgumentChecking.checkArguments (check R conversionCheck target)
      source σ imageCodes = true) :
    check R conversionCheck target (subst σ subject) (subst σ type)
      (code.substitute renameConversion substituteConversion σ imageCodes subject type) = true :=
  check_substitute renameConversion substituteConversion R conversionCheck
    renamePreserves substitutePreserves code accepted σ imageCodes
    ((TelescopeArgumentChecking.checkArguments_eq_true_iff _ source σ imageCodes).mp images)

#print axioms check_substitute_of_checked_arguments

/-- Open one checked binder, using the argument's actual certificate at
every occurrence. This also instantiates formation evidence. -/
def Code.instantiate {n : Nat} (subject type : Tm Head (n + 1)) (argument : Tm Head n)
    (bodyCode : Code Head ConversionCode (n + 1)) (argumentCode : Code Head ConversionCode n) :
    Code Head ConversionCode n :=
  bodyCode.substitute renameConversion substituteConversion (consSub argument ids)
    (Fin.cases argumentCode (fun _ => .var)) subject type

include renamePreserves substitutePreserves in
theorem Code.instantiate_checked {n : Nat} {context : Ctx Head n} {A argument : Tm Head n}
    {subject type : Tm Head (n + 1)} {bodyCode : Code Head ConversionCode (n + 1)}
    {argumentCode : Code Head ConversionCode n}
    (bodyAccepted : check R conversionCheck (.snoc context A) subject type bodyCode = true)
    (argumentAccepted : check R conversionCheck context argument A argumentCode = true) :
    check R conversionCheck context (inst0 argument subject) (inst0 argument type)
      (Code.instantiate renameConversion substituteConversion subject type argument bodyCode argumentCode) = true := by
  apply check_substitute renameConversion substituteConversion R conversionCheck
    renamePreserves substitutePreserves bodyCode bodyAccepted (consSub argument ids)
    (Fin.cases argumentCode (fun _ => .var))
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · simpa only [consSub, Fin.cases_zero, Ctx.lookup_snoc_zero, subst_consSub_rename_wk,
      subst_ids] using argumentAccepted
  · simp only [consSub, Fin.cases_succ, ids, Ctx.lookup_snoc_succ,
      subst_consSub_rename_wk, subst_ids, check, decide_true]

#print axioms Code.instantiate_checked

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
