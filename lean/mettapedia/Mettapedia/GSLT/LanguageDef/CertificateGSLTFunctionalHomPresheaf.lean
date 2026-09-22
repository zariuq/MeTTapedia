import Mettapedia.GSLT.LanguageDef.CertificateGSLTExponentialObstruction
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRepresentableProofs

/-!
# The contextual function-hom presheaf need not be representable

For one certificate goal, the assignment sending a premise context to the
actual proofs from that context extended by the goal back to the goal is a
presheaf. Contextual substitution acts by pairing its extension with the
untouched final premise. In a calculus with no closed certificates this
presheaf cannot be a Yoneda representable, even objectwise: the certificate
context category has finite products but lacks the needed self-exponential.

This identifies a precise boundary for any Prime function-type syntax.
Presheaf-valued semantic functions can exist beyond the representables, while
the current authored certificate contexts alone do not supply their codes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Extend a contextual proof substitution by leaving one final context
block intact. Both legs are the existing finite-product projections. -/
def extendContextRight
    {definition : ValidatedCalculusLanguageDef}
    (right : ClassifyingContext definition)
    {source target : ClassifyingContext definition}
    (substitution : source ⟶ target) :
    ClassifyingContext.concat source right ⟶
      ClassifyingContext.concat target right :=
  ClassifyingContext.pair
    (ClassifyingContext.fstProjection source right ≫ substitution)
    (ClassifyingContext.sndProjection source right)

@[simp] theorem extendContextRight_fst
    {definition : ValidatedCalculusLanguageDef}
    (right : ClassifyingContext definition)
    {source target : ClassifyingContext definition}
    (substitution : source ⟶ target) :
    extendContextRight right substitution ≫
        ClassifyingContext.fstProjection target right =
      ClassifyingContext.fstProjection source right ≫ substitution :=
  ClassifyingContext.pair_fst _ _

@[simp] theorem extendContextRight_snd
    {definition : ValidatedCalculusLanguageDef}
    (right : ClassifyingContext definition)
    {source target : ClassifyingContext definition}
    (substitution : source ⟶ target) :
    extendContextRight right substitution ≫
        ClassifyingContext.sndProjection target right =
      ClassifyingContext.sndProjection source right :=
  ClassifyingContext.pair_snd _ _

@[simp] theorem extendContextRight_id
    {definition : ValidatedCalculusLanguageDef}
    (right source : ClassifyingContext definition) :
    extendContextRight right (𝟙 source) =
      𝟙 (ClassifyingContext.concat source right) := by
  simpa [extendContextRight] using
    (ClassifyingContext.pair_eta
      (𝟙 (ClassifyingContext.concat source right)))

@[simp] theorem extendContextRight_comp
    {definition : ValidatedCalculusLanguageDef}
    (right : ClassifyingContext definition)
    {first second third : ClassifyingContext definition}
    (left : first ⟶ second) (next : second ⟶ third) :
    extendContextRight right (left ≫ next) =
      extendContextRight right left ≫ extendContextRight right next := by
  symm
  apply ClassifyingContext.pair_unique
    (ClassifyingContext.fstProjection first right ≫ left ≫ next)
    (ClassifyingContext.sndProjection first right)
  · rw [Category.assoc, extendContextRight_fst,
      ← Category.assoc, extendContextRight_fst]
    simp only [Category.assoc]
  · simp only [Category.assoc, extendContextRight_snd]

/-- For any input and output contexts, the contextual certificate-map type
forms a presheaf: restriction precomposes after extending the substitution
over the input context. -/
def contextualFunctionFace
    (definition : ValidatedCalculusLanguageDef)
    (input output : ClassifyingContext definition) :
    Face (ClassifyingContext definition) where
  obj context :=
    ClassifyingContext.concat context.unop input ⟶ output
  map substitution := TypeCat.ofHom fun proof =>
    extendContextRight input substitution.unop ≫ proof
  map_id context := by
    apply ConcreteCategory.hom_ext
    intro proof
    change extendContextRight input (𝟙 context.unop) ≫ proof = proof
    rw [extendContextRight_id]
    exact Category.id_comp proof
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro proof
    change extendContextRight input (second.unop ≫ first.unop) ≫ proof =
        extendContextRight input second.unop ≫
          (extendContextRight input first.unop ≫ proof)
    rw [extendContextRight_comp]
    simp only [Category.assoc]

/-- The one-judgment self-function face used by the nonrepresentability
canary is an instance of the general contextual certificate-map presheaf. -/
def functionHomFace
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Face (ClassifyingContext definition) :=
  contextualFunctionFace definition ⟨[goal]⟩ ⟨[goal]⟩

/-- The functional-hom presheaf retains two ways of selecting identical
premise labels at separate positions. Its semantic carrier is not a
propositional truth value. -/
theorem functionHomFace_not_subsingleton
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    ¬ Subsingleton ((functionHomFace definition goal).obj
      (Opposite.op (⟨[goal]⟩ : ClassifyingContext definition))) := by
  intro thin
  let one : ClassifyingContext definition := ⟨[goal]⟩
  change Subsingleton (ClassifyingContext.concat one one ⟶ one) at thin
  have equal : ClassifyingContext.fstProjection one one =
      ClassifyingContext.sndProjection one one :=
    @Subsingleton.elim _ thin _ _
  have headEqual := congrArg
    (fun morphism : ClassifyingContext.concat one one ⟶ one =>
      morphism.get (0 : Fin 1)) equal
  change (OpenDerivation.assumption (definition := definition)
    (context := [goal, goal]) (0 : Fin 2)) =
      OpenDerivation.assumption (definition := definition)
        (context := [goal, goal]) (1 : Fin 2) at headEqual
  exact ClassifyingContext.duplicate_assumptions_distinct definition goal
    headEqual

/-- With no closed certificates, the functional-hom presheaf is not even
objectwise equivalent to a representable. This is stronger than failure of
natural representability. -/
theorem functionHomFace_not_representable_of_no_closed
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (noClosed : ∀ candidate : Pattern,
      ¬ Nonempty (OpenDerivation definition [] candidate)) :
    ¬ ∃ exponent : ClassifyingContext definition,
      ∀ context : ClassifyingContext definition,
        Nonempty (((functionHomFace definition goal).obj
          (Opposite.op context)) ≃
          (yoneda.obj exponent).obj (Opposite.op context)) := by
  rintro ⟨exponent, represented⟩
  apply no_self_exponential_of_no_closed definition goal noClosed
  refine ⟨exponent, ?_⟩
  intro context
  exact represented context

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.extendContextRight_comp
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.contextualFunctionFace
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.functionHomFace
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.functionHomFace_not_subsingleton
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.functionHomFace_not_representable_of_no_closed
