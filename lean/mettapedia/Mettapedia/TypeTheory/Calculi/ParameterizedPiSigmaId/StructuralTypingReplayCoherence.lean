import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution

/-!
# Coherence of retained typing-certificate instantiation

Renaming and simultaneous substitution act on the actual finite evidence
tree. The mixed laws below retain supplied variable-image certificates,
including their binder weakenings; they do not identify different proofs
merely because both replay successfully.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (conversionRenameComp : ∀ {n m k} (ρ : Ren m k) (ξ : Ren n m) (code : ConversionCode n),
  renameConversion ρ (renameConversion ξ code) = renameConversion (fun i => ρ (ξ i)) code)
variable (conversionRenameSubstitute : ∀ {n m k} (ρ : Ren m k) (σ : Sub Head n m)
  (code : ConversionCode n), renameConversion ρ (substituteConversion σ code) =
    substituteConversion (fun i => Presentation.rename ρ (σ i)) code)
variable (conversionSubstituteRename : ∀ {n m k} (σ : Sub Head m k) (ρ : Ren n m)
  (code : ConversionCode n), substituteConversion σ (renameConversion ρ code) =
    substituteConversion (fun i => σ (ρ i)) code)

private theorem rename_liftSub_eq {n m k : Nat} (ρ : Ren m k) (σ : Sub Head n m) :
    (fun i => Presentation.rename (liftRen ρ) (liftSub σ i)) = liftSub (fun i => Presentation.rename ρ (σ i)) :=
  funext (rename_liftSub ρ σ)

private theorem liftSub_liftRen_eq {n m k : Nat} (σ : Sub Head m k) (ρ : Ren n m) :
    (fun i => liftSub σ (liftRen ρ i)) = liftSub (fun i => σ (ρ i)) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

include conversionRenameComp in
theorem liftVariableCodes_rename {n m k : Nat} (ρ : Ren m k)
    (codes : Fin n → Code Head ConversionCode m) :
    (fun i => (liftVariableCodes renameConversion codes i).rename renameConversion (liftRen ρ)) =
      liftVariableCodes renameConversion (fun i => (codes i).rename renameConversion ρ) := by
  funext index
  refine Fin.cases rfl (fun index => ?_) index
  simp only [liftVariableCodes, Fin.cases_succ, Code.rename_comp renameConversion conversionRenameComp]
  rfl

theorem liftVariableCodes_liftRen {n m k : Nat} (ρ : Ren n m)
    (codes : Fin m → Code Head ConversionCode k) :
    (fun i => liftVariableCodes renameConversion codes (liftRen ρ i)) =
      liftVariableCodes renameConversion (fun i => codes (ρ i)) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

include conversionRenameComp conversionRenameSubstitute in
theorem Code.rename_substitute {n m k : Nat} (code : Code Head ConversionCode n)
    (σ : Sub Head n m) (imageCodes : Fin n → Code Head ConversionCode m)
    (subject type : Tm Head n) (ρ : Ren m k) :
    (code.substitute renameConversion substituteConversion σ imageCodes subject type).rename
        renameConversion ρ =
      code.substitute renameConversion substituteConversion (fun i => Presentation.rename ρ (σ i))
        (fun i => (imageCodes i).rename renameConversion ρ) subject type := by
  induction code generalizing m k with
  | headType => rfl
  | var => cases subject <;> rfl
  | const => rfl
  | lamIntro | pairIntro =>
      cases subject <;> cases type <;>
        simp_all only [Code.substitute, Code.rename,
          rename_liftSub_eq, liftVariableCodes_rename renameConversion conversionRenameComp]
  | _ =>
      cases subject <;>
        simp_all only [Code.substitute, Code.rename, rename_subst,
          rename_liftSub_eq, liftVariableCodes_rename renameConversion conversionRenameComp]

include conversionSubstituteRename in
theorem Code.substitute_rename {n m k : Nat} (code : Code Head ConversionCode n)
    (ρ : Ren n m) (σ : Sub Head m k) (imageCodes : Fin m → Code Head ConversionCode k)
    (subject type : Tm Head n) :
    (code.rename renameConversion ρ).substitute renameConversion substituteConversion σ imageCodes
        (Presentation.rename ρ subject) (Presentation.rename ρ type) =
      code.substitute renameConversion substituteConversion (fun i => σ (ρ i))
        (fun i => imageCodes (ρ i)) subject type := by
  induction code generalizing m k with
  | headType => rfl
  | var => cases subject <;> rfl
  | const => rfl
  | piForm u v domain body ihDomain ihBody =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute]
      rename_i A B
      congr 1
      · exact ihDomain ρ σ imageCodes A (.head u)
      · simpa only [liftSub_liftRen_eq, liftVariableCodes_liftRen, Presentation.rename] using
          ihBody (liftRen ρ) (liftSub σ) (liftVariableCodes renameConversion imageCodes) B (.head v)
  | sigmaForm u v domain body ihDomain ihBody =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute]
      rename_i A B
      congr 1
      · exact ihDomain ρ σ imageCodes A (.head u)
      · simpa only [liftSub_liftRen_eq, liftVariableCodes_liftRen, Presentation.rename] using
          ihBody (liftRen ρ) (liftSub σ) (liftVariableCodes renameConversion imageCodes) B (.head v)
  | lamIntro u formation body ihFormation ihBody =>
      cases subject <;> cases type <;>
        simp only [Presentation.rename, Code.rename, Code.substitute]
      rename_i term A B
      congr 1
      · exact ihFormation ρ σ imageCodes (.pi A B) (.head u)
      · simpa only [liftSub_liftRen_eq, liftVariableCodes_liftRen] using
          ihBody (liftRen ρ) (liftSub σ) (liftVariableCodes renameConversion imageCodes) term B
  | appElim A B function argument ihFunction ihArgument =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute, subst_rename,
        liftSub_liftRen_eq]
      rename_i f a
      congr 1
      · exact ihFunction ρ σ imageCodes f (.pi A B)
      · exact ihArgument ρ σ imageCodes a A
  | pairIntro u formation first second ihFormation ihFirst ihSecond =>
      cases subject <;> cases type <;>
        simp only [Presentation.rename, Code.rename, Code.substitute]
      rename_i a b A B
      congr 1
      · exact ihFormation ρ σ imageCodes (.sigma A B) (.head u)
      · exact ihFirst ρ σ imageCodes a A
      · simpa only [rename_inst0] using ihSecond ρ σ imageCodes b (inst0 a B)
  | fstElim B pair ihPair =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute, subst_rename,
        liftSub_liftRen_eq]
      rename_i p
      congr 1
      exact ihPair ρ σ imageCodes p (.sigma type B)
  | sndElim A B pair ihPair =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute, subst_rename,
        liftSub_liftRen_eq]
      rename_i p
      congr 1
      exact ihPair ρ σ imageCodes p (.sigma A B)
  | idForm u formation left right ihFormation ihLeft ihRight =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute]
      rename_i A a b
      congr 1
      · exact ihFormation ρ σ imageCodes A (.head u)
      · exact ihLeft ρ σ imageCodes a A
      · exact ihRight ρ σ imageCodes b A
  | reflIntro A term ihTerm =>
      cases subject <;> simp only [Presentation.rename, Code.rename, Code.substitute, subst_rename]
      rename_i a
      congr 1
      exact ihTerm ρ σ imageCodes a A
  | cumul u term ihTerm =>
      simp only [Code.rename, Code.substitute]
      congr 1
      exact ihTerm ρ σ imageCodes subject (.head u)
  | convert A u source formation conversion ihSource ihFormation =>
      simp only [Code.rename, Code.substitute, subst_rename, conversionSubstituteRename]
      congr 1
      · exact ihSource ρ σ imageCodes subject A
      · exact ihFormation ρ σ imageCodes type (.head u)

#print axioms Code.rename_substitute
#print axioms Code.substitute_rename

/-- Compose the particular image proofs, using each original dependent
lookup type. This is finite certificate substitution, not existential proof
selection from typing completeness. -/
def composeImageCodes {n m k : Nat} (source : Ctx Head n) (σ : Sub Head n m)
    (first : Fin n → Code Head ConversionCode m) (τ : Sub Head m k)
    (second : Fin m → Code Head ConversionCode k) : Fin n → Code Head ConversionCode k :=
  fun i => (first i).substitute renameConversion substituteConversion τ second
    (σ i) (subst σ (Ctx.lookup source i))

include conversionRenameComp conversionRenameSubstitute conversionSubstituteRename in
theorem liftVariableCodes_comp {n m k : Nat} (source : Ctx Head n) (A : Tm Head n)
    (σ : Sub Head n m) (first : Fin n → Code Head ConversionCode m)
    (τ : Sub Head m k) (second : Fin m → Code Head ConversionCode k) :
    composeImageCodes renameConversion substituteConversion (.snoc source A) (liftSub σ)
        (liftVariableCodes renameConversion first) (liftSub τ)
        (liftVariableCodes renameConversion second) =
      liftVariableCodes renameConversion
        (composeImageCodes renameConversion substituteConversion source σ first τ second) := by
  funext index
  refine Fin.cases rfl (fun index => ?_) index
  simp only [composeImageCodes, liftVariableCodes, Fin.cases_succ, liftSub_succ,
    Ctx.lookup, subst_liftSub_wk]
  rw [Code.substitute_rename renameConversion substituteConversion conversionSubstituteRename,
    Code.rename_substitute renameConversion substituteConversion conversionRenameComp
      conversionRenameSubstitute]
  rfl

theorem liftVariableCodes_var {n : Nat} :
    liftVariableCodes renameConversion (fun _ : Fin n => (.var : Code Head ConversionCode n)) =
      (fun _ => .var) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

#print axioms liftVariableCodes_comp

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (conversionSubstituteId : ∀ {n} (code : ConversionCode n), substituteConversion ids code = code)
variable (conversionSubstituteComp : ∀ {n m k} (σ : Sub Head n m) (τ : Sub Head m k)
  (code : ConversionCode n), substituteConversion τ (substituteConversion σ code) =
    substituteConversion (subComp τ σ) code)

include conversionSubstituteId in
/-- Identity substitution with the variable certificates retains the
accepted source certificate itself, not only its admitted judgment. -/
theorem Code.substitute_ids_of_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {source : Ctx Head n} {subject type : Tm Head n},
      check R conversionCheck source subject type code = true →
      code.substitute renameConversion substituteConversion ids (fun _ => .var) subject type = code := by
  induction code with
  | headType => intros; rfl
  | var => intro source subject type accepted; cases subject <;> rfl
  | const => intros; rfl
  | piForm u v domain body ihDomain ihBody =>
      intro source subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨_, _⟩, _⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, liftSub_ids, liftVariableCodes_var,
        ihDomain domainAccepted, ihBody bodyAccepted]
  | sigmaForm u v domain body ihDomain ihBody =>
      intro source subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨_, _⟩, _⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, liftSub_ids, liftVariableCodes_var,
        ihDomain domainAccepted, ihBody bodyAccepted]
  | lamIntro u formation body ihFormation ihBody =>
      intro source subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨_, formed⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, liftSub_ids, liftVariableCodes_var,
        ihFormation formed, ihBody bodyAccepted]
  | pairIntro u formation first second ihFormation ihFirst ihSecond =>
      intro source subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨_, formed⟩, firstAccepted⟩, secondAccepted⟩ := accepted
      simp only [Code.substitute, ihFormation formed, ihFirst firstAccepted, ihSecond secondAccepted]
  | idForm u formation left right ihFormation ihLeft ihRight =>
      intro source subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨_, formed⟩, leftAccepted⟩, rightAccepted⟩, _⟩ := accepted
      simp only [Code.substitute, ihFormation formed, ihLeft leftAccepted, ihRight rightAccepted]
  | appElim A B function argument ihFunction ihArgument =>
      intro source subject type accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨functionAccepted, argumentAccepted⟩, _⟩ := accepted
      simp only [Code.substitute, subst_ids, liftSub_ids,
        ihFunction functionAccepted, ihArgument argumentAccepted]
  | fstElim B pair ihPair =>
      intro source subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst_ids, liftSub_ids, ihPair accepted]
  | sndElim A B pair ihPair =>
      intro source subject type accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst_ids, liftSub_ids, ihPair accepted.1]
  | reflIntro A term ihTerm =>
      intro source subject type accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst_ids, ihTerm accepted.1]
  | cumul u term ihTerm =>
      intro source subject type accepted
      cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simp only [Code.substitute, ihTerm accepted.1]
  | convert A u sourceCode formation conversion ihSource ihFormation =>
      intro source subject type accepted
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨⟨_, sourceAccepted⟩, formed⟩, _⟩ := accepted
      simp only [Code.substitute, subst_ids, conversionSubstituteId,
        ihSource sourceAccepted, ihFormation formed]

include conversionRenameComp conversionRenameSubstitute conversionSubstituteRename conversionSubstituteComp in
/-- Iterated instantiation equals one instantiation with the composed
substitution and the computed composite image proofs. The equality is of
finite certificate trees; no quotient by successful checking is taken. -/
theorem Code.substitute_comp_of_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {source : Ctx Head n} {subject type : Tm Head n},
      check R conversionCheck source subject type code = true →
      ∀ {m k : Nat} (σ : Sub Head n m) (first : Fin n → Code Head ConversionCode m)
        (τ : Sub Head m k) (second : Fin m → Code Head ConversionCode k),
        (code.substitute renameConversion substituteConversion σ first subject type).substitute
            renameConversion substituteConversion τ second (subst σ subject) (subst σ type) =
          code.substitute renameConversion substituteConversion (subComp τ σ)
            (composeImageCodes renameConversion substituteConversion source σ first τ second)
            subject type := by
  induction code with
  | headType => intros; rfl
  | var =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      subst type
      rfl
  | const => intros; rfl
  | piForm u v domain body ihDomain ihBody =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, subst]
      congr 1
      · exact ihDomain domainAccepted σ first τ second
      · simpa only [subst, liftSub_subComp, liftVariableCodes_comp renameConversion substituteConversion
          conversionRenameComp conversionRenameSubstitute conversionSubstituteRename] using
          ihBody bodyAccepted (liftSub σ) (liftVariableCodes renameConversion first)
            (liftSub τ) (liftVariableCodes renameConversion second)
  | sigmaForm u v domain body ihDomain ihBody =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, subst]
      congr 1
      · exact ihDomain domainAccepted σ first τ second
      · simpa only [subst, liftSub_subComp, liftVariableCodes_comp renameConversion substituteConversion
          conversionRenameComp conversionRenameSubstitute conversionSubstituteRename] using
          ihBody bodyAccepted (liftSub σ) (liftVariableCodes renameConversion first)
            (liftSub τ) (liftVariableCodes renameConversion second)
  | lamIntro u formation body ihFormation ihBody =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨isUniverse, formed⟩, bodyAccepted⟩ := accepted
      simp only [Code.substitute, subst]
      congr 1
      · exact ihFormation formed σ first τ second
      · simpa only [liftSub_subComp, liftVariableCodes_comp renameConversion substituteConversion
          conversionRenameComp conversionRenameSubstitute conversionSubstituteRename] using
          ihBody bodyAccepted (liftSub σ) (liftVariableCodes renameConversion first)
            (liftSub τ) (liftVariableCodes renameConversion second)
  | appElim A B function argument ihFunction ihArgument =>
      intro source subject type accepted m k σ first τ second
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨functionAccepted, argumentAccepted⟩, same⟩ := accepted
      simp only [Code.substitute, subst, subst_subComp, liftSub_subComp]
      congr 1
      · exact ihFunction functionAccepted σ first τ second
      · exact ihArgument argumentAccepted σ first τ second
  | pairIntro u formation firstCode secondCode ihFormation ihFirst ihSecond =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨isUniverse, formed⟩, firstAccepted⟩, secondAccepted⟩ := accepted
      simp only [Code.substitute, subst]
      congr 1
      · exact ihFormation formed σ first τ second
      · exact ihFirst firstAccepted σ first τ second
      · simpa only [subst_inst0] using ihSecond secondAccepted σ first τ second
  | fstElim B pair ihPair =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst, subst_subComp, liftSub_subComp]
      congr 1
      exact ihPair accepted σ first τ second
  | sndElim A B pair ihPair =>
      intro source subject type accepted m k σ first τ second
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst, subst_subComp, liftSub_subComp]
      congr 1
      exact ihPair accepted.1 σ first τ second
  | idForm u formation left right ihFormation ihLeft ihRight =>
      intro source subject type accepted m k σ first τ second
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isUniverse, formed⟩, leftAccepted⟩, rightAccepted⟩, same⟩ := accepted
      simp only [Code.substitute, subst]
      congr 1
      · exact ihFormation formed σ first τ second
      · exact ihLeft leftAccepted σ first τ second
      · exact ihRight rightAccepted σ first τ second
  | reflIntro A term ihTerm =>
      intro source subject type accepted m k σ first τ second
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst, subst_subComp]
      congr 1
      exact ihTerm accepted.1 σ first τ second
  | cumul u term ihTerm =>
      intro source subject type accepted m k σ first τ second
      cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      simp only [Code.substitute, subst]
      congr 1
      exact ihTerm accepted.1 σ first τ second
  | convert A u sourceCode formation conversion ihSource ihFormation =>
      intro source subject type accepted m k σ first τ second
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨⟨isUniverse, sourceAccepted⟩, formed⟩, converted⟩ := accepted
      simp only [Code.substitute, subst_subComp, conversionSubstituteComp]
      congr 1
      · exact ihSource sourceAccepted σ first τ second
      · exact ihFormation formed σ first τ second

#print axioms Code.substitute_ids_of_checked
#print axioms Code.substitute_comp_of_checked

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
