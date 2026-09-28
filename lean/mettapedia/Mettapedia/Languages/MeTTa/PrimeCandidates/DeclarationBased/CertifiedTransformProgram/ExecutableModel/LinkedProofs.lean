import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SetReading
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Linking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLReadingCompileModulo

/-!
# Linked proofs are terms of the object package

A `set:` proof whose assumptions are published facts is linked by compiling it
with the realizations of the facts as its hypotheses
(`IdentityEquality.Linking`). Linking was typed in the identity profile, a
formation-sensitive package with untyped conversion. Here the same linked
terms are typed in the selected typed judgment of the object package
`objectRules`, on which strong normalization (`objectRules_sn`) and
consistency (`CodeModel.consistent`) are proved:

* every published fact is realized in `objectRules` (`published_typedO`);
* **retyping** (`linked_typedO`): a proof whose conversion articles stay
  inside the terms the object package reads, compiled against the
  realizations, is a closed term of `objectRules` at the decoding of the code
  of its theorem; it is the term the generic compiler `compileModulo` links
  (`linked_compileModulo`);
* **the checkpoint**: the linked `zero-add` proof is a closed term of
  `objectRules` at `holds ∀k. add zero k = k` (`linkedZeroAdd_typedO`), so it
  is strongly normalizing (`linkedZeroAdd_sn`), and the package does not
  refute its theorem (`zeroAdd_not_refuted`, `zeroAdd_not_refuted_bot`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open SetProfile (SetBase SetConst numTy zeroT sucT addT motive)
open IdentityEquality.Linking (Published zeroAddPublished)
open IdentityEquality.Translation (linkedZeroAdd)
open HOLNativeGenericProofCompiler (Modulo.compileModulo)

namespace CodeModel

/-! ## Published facts -/

/-- Every published fact is read, and its realization is a closed term of the
object package at the decoding of its code: it is a fact of the hosted set
profile, realized as there. -/
theorem published_typedO {fact : HOL.Formula SetConst []} :
    (published : Published fact) →
      ∃ code, setReading.term fact = some code ∧
        Typed objectRules .nil published.realization (programCodes.holdsOf code) :=
  fun published => published.toHosted.typed

/-! ## Retyping linked proofs -/

/-- **Retyping.** A proof from published facts whose conversion articles stay
inside the read terms, compiled against the realizations, is a closed term of
the object package at the decoding of the code of its theorem. -/
theorem linked_typedO {assumptions : List (HOL.Formula SetConst [])}
    {statement : HOL.Formula SetConst []}
    {proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement}
    (articles : setReading.ArticlesRead SetProfile.sourceEquations proof)
    (published : ∀ i : Fin assumptions.length, Published (assumptions.get i)) {term : Tower.Tm 0}
    (compiled : setReading.compile proof Fin.elim0 (fun i => (published i).realization) =
      some term) :
    ∃ code, setReading.term statement = some code ∧
      Typed objectRules .nil term (programCodes.holdsOf code) := by
  obtain ⟨code, hcode, typed⟩ := setReading_laws.compile_typed setReading_realizes articles
    (fun i => Fin.elim0 i)
    (fun i => by
      obtain ⟨c, hc, t⟩ := published_typedO (published i)
      exact ⟨c, hc, by rw [SetProfile.subst_elim0]; exact t⟩)
    compiled
  rw [SetProfile.subst_elim0] at typed
  exact ⟨code, hcode, typed⟩

/-- A linked proof does not prove the false proposition of the consistency
theorem, and the package refutes no linked theorem. -/
theorem linked_not_refuted {assumptions : List (HOL.Formula SetConst [])}
    {statement : HOL.Formula SetConst []}
    {proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement}
    (articles : setReading.ArticlesRead SetProfile.sourceEquations proof)
    (published : ∀ i : Fin assumptions.length, Published (assumptions.get i)) {term : Tower.Tm 0}
    (compiled : setReading.compile proof Fin.elim0 (fun i => (published i).realization) =
      some term)
    {code : Tower.Tm 0} (read : setReading.term statement = some code) (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf code falseCode)) := by
  intro refutation
  obtain ⟨code', read', typed⟩ := linked_typedO articles published compiled
  rw [read] at read'
  cases read'
  exact consistent (.app f term) (setReading_laws.impElim
    (setReading_laws.term_typed read) falseCode_typed refutation typed)

/-! ## The zero-add document -/

open SetProfile (sourceEquations zeroAddStatement zeroAddProof zeroAddCode addZeroEquation
  addSucEquation singleSubst pairSubst singleSubst_core pairSubst_core)

/-- A definitional step between two terms the object package reads. -/
theorem readStep {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase} {s t : HOL.Term SetConst Γ τ}
    (step : HOL.SourceStep sourceEquations s t) (hs : (setReading.term s).isSome = true)
    (ht : (setReading.term t).isSome = true) : setReading.RepConversion sourceEquations s t :=
  .rel _ _ ⟨hs, ht, step⟩

/-- The article of the conclusion: β under the quantifier. -/
theorem conclusionRead :
    setReading.RepConversion sourceEquations (.all (.app motive (.var .vz))) zeroAddStatement :=
  readStep (.all (.beta _ _)) rfl rfl

/-- The article of the base case: β, then `add zero zero = zero`. -/
theorem baseRead :
    setReading.RepConversion sourceEquations (Γ := []) (.eq zeroT zeroT) (.app motive zeroT) :=
  .symm _ _ (.trans _ (.eq (addT zeroT zeroT) zeroT) _ (readStep (.beta _ _) rfl rfl)
    (readStep (.eqLeft _ (.delta addZeroEquation (by simp [sourceEquations])
      (singleSubst zeroT) (singleSubst_core rfl))) rfl rfl))

/-- The article of the induction hypothesis: β. -/
theorem hypothesisRead :
    setReading.RepConversion sourceEquations (Γ := [numTy]) (.app motive (.var .vz))
      (.eq (addT zeroT (.var .vz)) (.var .vz)) :=
  readStep (.beta _ _) rfl rfl

/-- The article of the reflexivity premise: β backwards. -/
theorem reflexivityRead :
    setReading.RepConversion sourceEquations (Γ := [numTy])
      (.eq (sucT (addT zeroT (.var .vz))) (sucT (addT zeroT (.var .vz))))
      (.app SetProfile.congruenceMotive (addT zeroT (.var .vz))) :=
  .symm _ _ (readStep (.beta _ _) rfl rfl)

/-- The article of the step: β on both sides and `add zero (suc k) = suc (add zero k)`. -/
theorem stepRead :
    setReading.RepConversion sourceEquations (Γ := [numTy])
      (.app SetProfile.congruenceMotive (.var .vz)) (.app motive (sucT (.var .vz))) :=
  .trans _ (.eq (sucT (addT zeroT (.var .vz))) (sucT (.var .vz))) _ (readStep (.beta _ _) rfl rfl)
    (.symm _ _ (.trans _ (.eq (addT zeroT (sucT (.var .vz))) (sucT (.var .vz))) _
      (readStep (.beta _ _) rfl rfl)
      (readStep (.eqLeft _ (.delta addSucEquation (by simp [sourceEquations])
        (pairSubst (.var .vz) zeroT) (pairSubst_core rfl rfl))) rfl rfl)))

/-- Every conversion article of the retained `zero-add` proof stays inside the
terms the object package reads. -/
theorem zeroAdd_articles : setReading.ArticlesRead sourceEquations zeroAddProof :=
  .convert conclusionRead
    (.impE (.impE (.allE _ (.hyp _)) (.convert baseRead (.allE _ (.hyp _))))
      (.allI (.impI (.convert stepRead
        (.impE (.impE (.allE _ (.allE _ (.allE _ (.hyp _)))) (.convert hypothesisRead (.hyp _)))
          (.convert reflexivityRead (.allE _ (.hyp _))))))))

/-- The reading compiles the retained proof, against the realizations, to the
linked term. -/
theorem zeroAdd_compiledO :
    setReading.compile zeroAddProof Fin.elim0 (fun i => (zeroAddPublished i).realization) =
      some linkedZeroAdd :=
  rfl

theorem zeroAddStatement_read : setReading.term zeroAddStatement = some zeroAddCode := rfl

/-- **Checkpoint.** The linked `zero-add` proof is a closed term of the object
package at the decoding of `∀k. add zero k = k`. -/
theorem linkedZeroAdd_typedO :
    Typed objectRules .nil linkedZeroAdd (programCodes.holdsOf zeroAddCode) := by
  obtain ⟨code, read, typed⟩ :=
    linked_typedO zeroAdd_articles zeroAddPublished zeroAdd_compiledO
  rw [zeroAddStatement_read] at read
  cases read
  exact typed

/-- **Checkpoint.** The linked `zero-add` proof is strongly normalizing under
the object package's own reduction. -/
theorem linkedZeroAdd_sn : StrongNormalization.SN objectRules linkedZeroAdd :=
  (objectRules_sn .nil linkedZeroAdd_typedO).1

/-- **Consistency coverage.** No closed term of the object package proves
`zero-add ⇒ ∀n. zero = suc n`. -/
theorem zeroAdd_not_refuted (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf zeroAddCode falseCode)) :=
  linked_not_refuted zeroAdd_articles zeroAddPublished zeroAdd_compiledO zeroAddStatement_read f

/-- **Consistency coverage.** No closed term of the object package proves
`zero-add ⇒ ∀p. p`. -/
theorem zeroAdd_not_refuted_bot (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf zeroAddCode botCode)) :=
  fun refutation => consistent_bot (.app f linkedZeroAdd) (setReading_laws.impElim
    (setReading_laws.term_typed zeroAddStatement_read) botCode_typed refutation
    linkedZeroAdd_typedO)

/-! ## The generic compiler links the same terms -/

/-- The set reading reads the set profile's own symbols. -/
theorem setReading_agrees : setReading.Agrees SetProfile.signature where
  implication := rfl
  universal _ := rfl
  equality _ := rfl
  constant c t found := by
    cases c <;> simp only [setReading, setConstant, reduceCtorEq, Option.some.injEq] at found <;>
      subst found <;> rfl

/-- The retyped linked term is the term the generic compiler links. -/
theorem linked_compileModulo {assumptions : List (HOL.Formula SetConst [])}
    {statement : HOL.Formula SetConst []}
    {proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement}
    (published : ∀ i : Fin assumptions.length, Published (assumptions.get i)) {term : Tower.Tm 0}
    (compiled : setReading.compile proof Fin.elim0 (fun i => (published i).realization) =
      some term) :
    Modulo.compileModulo SetProfile.signature proof Fin.elim0
      (fun i => (published i).realization) = some term :=
  setReading_agrees.compile_compileModulo proof Fin.elim0 _ compiled

/-- **Licensing, at the zero-add document**: the generic compiler links the
retained proof to `linkedZeroAdd`, which is a closed term of the object
package at the decoding of the signature's representation of `zero-add`. -/
theorem zeroAdd_compileModulo_typedO :
    Modulo.compileModulo SetProfile.signature zeroAddProof Fin.elim0
        (fun i => (zeroAddPublished i).realization) = some linkedZeroAdd ∧
      ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature zeroAddStatement =
          some code ∧ Typed objectRules .nil linkedZeroAdd (programCodes.holdsOf code) := by
  obtain ⟨linked, code, represented, _, typed⟩ := setReading_laws.compileModulo_typedO
    setReading_realizes setReading_agrees zeroAdd_articles (fun i => Fin.elim0 i)
    (fun i => by
      obtain ⟨c, hc, t⟩ := published_typedO (zeroAddPublished i)
      exact ⟨c, hc, by rw [SetProfile.subst_elim0]; exact t⟩)
    zeroAdd_compiledO
  rw [SetProfile.subst_elim0] at typed
  exact ⟨linked, code, represented, typed⟩

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
