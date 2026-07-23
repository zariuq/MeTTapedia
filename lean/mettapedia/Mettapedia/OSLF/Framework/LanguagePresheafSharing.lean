import Mettapedia.GSLT.Meredith.LambdaTheory
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.ToposReduction

/-!
# Sharing a Language Presentation with its Presheaf Lambda Theory

For a `LanguageDef`, the operational OSLF construction and the categorical
presheaf construction start from the same authored presentation.  This module
closes two precise compatibility seams between them:

1. Yoneda embeds the free constructor category fully faithfully, so the
   presheaf completion neither identifies distinct authored constructor paths
   nor invents transformations between representable sorts.
2. The internal OSLF reduction subfunctor supplies the rewrite relation of a
   full Meredith lambda theory.  On constant program terms, this relation is
   equivalent to both internal-subfunctor membership and the original
   `langReducesUsing` judgment.

The second result concerns reduction support.  It deliberately does not claim
to preserve distinct derivation or rule-occurrence identities with the same
source and target.
-/

namespace Mettapedia.OSLF.Framework.LanguagePresheafSharing

open CategoryTheory
open Opposite
open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ToposReduction
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Constructor sharing through Yoneda -/

/-- Authored constructor paths are exactly the natural transformations between
their representable presheaves. -/
noncomputable def languageConstructorYonedaEquiv
    (lang : LanguageDef) (s t : LangSort lang) :
    (ConstructorObj.mk s ⟶ ConstructorObj.mk t) ≃
      (languageSortRepresentableObj lang s ⟶
        languageSortRepresentableObj lang t) :=
  (CategoryTheory.Yoneda.fullyFaithful
    (C := ConstructorObj lang)).homEquiv

/-- The forward direction of `languageConstructorYonedaEquiv` is the ordinary
Yoneda action on a constructor path. -/
@[simp] theorem languageConstructorYonedaEquiv_apply
    (lang : LanguageDef) {s t : LangSort lang}
    (f : ConstructorObj.mk s ⟶ ConstructorObj.mk t) :
    languageConstructorYonedaEquiv lang s t f = CategoryTheory.yoneda.map f :=
  rfl

/-- The presheaf completion does not collapse two distinct authored
constructor paths. -/
theorem languageConstructorYoneda_map_eq_iff
    (lang : LanguageDef) {s t : LangSort lang}
    (f g : ConstructorObj.mk s ⟶ ConstructorObj.mk t) :
    CategoryTheory.yoneda.map f = CategoryTheory.yoneda.map g ↔ f = g := by
  constructor
  · exact (CategoryTheory.Yoneda.fullyFaithful
      (C := ConstructorObj lang)).map_injective
  · intro h
    subst h
    rfl

/-- Every transformation between two representable language sorts comes from
a unique authored constructor path. -/
theorem languageConstructorYoneda_existsUnique_path
    (lang : LanguageDef) {s t : LangSort lang}
    (α : languageSortRepresentableObj lang s ⟶
      languageSortRepresentableObj lang t) :
    ∃! f : ConstructorObj.mk s ⟶ ConstructorObj.mk t,
      CategoryTheory.yoneda.map f = α := by
  let e := languageConstructorYonedaEquiv lang s t
  refine ⟨e.symm α, ?_, ?_⟩
  · exact e.apply_symm_apply α
  · intro g hg
    apply e.injective
    rw [languageConstructorYonedaEquiv_apply, hg]
    exact e.apply_symm_apply α |>.symm

/-! ## The shared internal reduction relation -/

/-- The program object is the constant presheaf of `LanguageDef` patterns.

This is the vertex object already used by `ToposReduction`; the definition is
shared rather than reconstructed for the lambda-theory package. -/
abbrev languageProgramObj (lang : LanguageDef) :
    (languagePresheafLambdaTheory lang).Obj :=
  patternConstPresheaf (C := ConstructorObj lang)

/-- A pair of generalized program terms is related when every component pair
belongs to the existing internal OSLF reduction subfunctor. -/
def languagePointwiseReducesUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    {Γ : (languagePresheafLambdaTheory lang).Obj}
    (p q : Γ ⟶ languageProgramObj lang) : Prop :=
  ∀ (X : Opposite (ConstructorObj lang)) (x : Γ.obj X),
    ((ULift.up ((p.app X x).down, (q.app X x).down)) :
        (pairConstPresheaf (C := ConstructorObj lang)).obj X) ∈
      (reductionSubfunctorUsing
        (C := ConstructorObj lang) relEnv lang).obj X

/-- The canonical full mWC lambda theory generated from a `LanguageDef` and a
premise relation environment.

Its CCC, finite limits, and predicate fibration are the existing canonical
presheaf construction.  Its distinguished program object and rewrite relation
are the existing internal OSLF graph object and reduction subfunctor. -/
noncomputable def languageOperationalLambdaTheoryUsing
    (relEnv : RelationEnv) (lang : LanguageDef) : LambdaTheory where
  toLambdaTheoryWithEquality := languagePresheafLambdaTheory lang
  Pr := languageProgramObj lang
  rewriteRel := languagePointwiseReducesUsing relEnv lang
  rewriteRel_nat := by
    intro Γ Δ σ p q hpq X x
    change
      ((ULift.up
        (((p.app X) (σ.app X x)).down, ((q.app X) (σ.app X x)).down)) :
          (pairConstPresheaf (C := ConstructorObj lang)).obj X) ∈
        (reductionSubfunctorUsing
          (C := ConstructorObj lang) relEnv lang).obj X
    exact hpq X (σ.app X x)

/-- Default-environment full operational lambda theory for a language. -/
noncomputable def languageOperationalLambdaTheory (lang : LanguageDef) : LambdaTheory :=
  languageOperationalLambdaTheoryUsing RelationEnv.empty lang

/-- A constant generalized program term in any presheaf context. -/
def constantPatternTerm
    (lang : LanguageDef)
    (Γ : (languagePresheafLambdaTheory lang).Obj)
    (p : Pattern) : Γ ⟶ languageProgramObj lang where
  app _ := TypeCat.ofHom (fun _ => ULift.up p)
  naturality := by
    intro X Y f
    rfl

/-- A constant program endomorphism.  Using the nonempty program object as its
context lets the reflection theorem recover a component without assuming that
every presheaf context is inhabited. -/
def constantProgramEndomorphism (lang : LanguageDef) (p : Pattern) :
    languageProgramObj lang ⟶ languageProgramObj lang :=
  constantPatternTerm lang (languageProgramObj lang) p

/-- Exact support sharing: on constant program terms, the full lambda-theory
rewrite relation is precisely the original declarative one-step relation.

An explicit sort witness makes the constructor category nonempty, which is
necessary for the reflection direction out of a pointwise presheaf relation. -/
theorem languageOperationalLambdaTheoryUsing_constant_rewrite_iff
    (relEnv : RelationEnv) (lang : LanguageDef) (s : LangSort lang)
    (p q : Pattern) :
    (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel
        (constantProgramEndomorphism lang p)
        (constantProgramEndomorphism lang q) ↔
      langReducesUsing relEnv lang p q := by
  constructor
  · intro h
    have hmem := h
      (Opposite.op (ConstructorObj.mk s))
      (ULift.up p)
    exact (mem_reductionSubfunctorUsing_iff
      (C := ConstructorObj lang) (relEnv := relEnv) (lang := lang)
      (X := Opposite.op (ConstructorObj.mk s)) (p := p) (q := q)).1 hmem
  · intro h X x
    exact (mem_reductionSubfunctorUsing_iff
      (C := ConstructorObj lang) (relEnv := relEnv) (lang := lang)
      (X := X) (p := p) (q := q)).2 h

/-- The same shared support theorem stated directly against the existing
internal reduction subfunctor. -/
theorem languageOperationalLambdaTheoryUsing_constant_rewrite_iff_internal
    (relEnv : RelationEnv) (lang : LanguageDef) (s : LangSort lang)
    (p q : Pattern) :
    (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel
        (constantProgramEndomorphism lang p)
        (constantProgramEndomorphism lang q) ↔
      ((ULift.up (p, q)) :
          (pairConstPresheaf (C := ConstructorObj lang)).obj
            (Opposite.op (ConstructorObj.mk s))) ∈
        (reductionSubfunctorUsing
          (C := ConstructorObj lang) relEnv lang).obj
            (Opposite.op (ConstructorObj.mk s)) := by
  rw [languageOperationalLambdaTheoryUsing_constant_rewrite_iff
    relEnv lang s p q]
  exact (mem_reductionSubfunctorUsing_iff
    (C := ConstructorObj lang) (relEnv := relEnv) (lang := lang)
    (X := Opposite.op (ConstructorObj.mk s)) (p := p) (q := q)).symm

/-- Executable agreement: constant-term rewriting in the full lambda theory is
equivalent to the executable `LanguageDef` engine. -/
theorem languageOperationalLambdaTheoryUsing_constant_rewrite_iff_exec
    (relEnv : RelationEnv) (lang : LanguageDef) (s : LangSort lang)
    (p q : Pattern) :
    (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel
        (constantProgramEndomorphism lang p)
        (constantProgramEndomorphism lang q) ↔
      langReducesExecUsing relEnv lang p q := by
  rw [languageOperationalLambdaTheoryUsing_constant_rewrite_iff
    relEnv lang s p q]
  exact langReducesUsing_iff_execUsing relEnv lang p q

/-- The OSLF possibility modality agrees with existence of a related constant
program term in the full operational lambda theory. -/
theorem langDiamondUsing_iff_exists_operationalLambdaRewrite
    (relEnv : RelationEnv) (lang : LanguageDef) (s : LangSort lang)
    (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing relEnv lang φ p ↔
      ∃ q,
        (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel
          (constantProgramEndomorphism lang p)
          (constantProgramEndomorphism lang q) ∧
        φ q := by
  constructor
  · intro h
    rcases (langDiamondUsing_spec relEnv lang φ p).1 h with ⟨q, hpq, hφ⟩
    exact ⟨q,
      (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
        relEnv lang s p q).2 hpq,
      hφ⟩
  · rintro ⟨q, hpq, hφ⟩
    exact (langDiamondUsing_spec relEnv lang φ p).2
      ⟨q,
        (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
          relEnv lang s p q).1 hpq,
        hφ⟩

/-- The OSLF rely/box modality agrees with universal quantification over
incoming related constant program terms in the full operational lambda theory. -/
theorem langBoxUsing_iff_forall_operationalLambdaIncoming
    (relEnv : RelationEnv) (lang : LanguageDef) (s : LangSort lang)
    (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing relEnv lang φ p ↔
      ∀ q,
        (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel
          (constantProgramEndomorphism lang q)
          (constantProgramEndomorphism lang p) →
        φ q := by
  constructor
  · intro h q hqp
    exact (langBoxUsing_spec relEnv lang φ p).1 h q
      ((languageOperationalLambdaTheoryUsing_constant_rewrite_iff
        relEnv lang s q p).1 hqp)
  · intro h
    exact (langBoxUsing_spec relEnv lang φ p).2 fun q hqp =>
      h q ((languageOperationalLambdaTheoryUsing_constant_rewrite_iff
        relEnv lang s q p).2 hqp)

/-- Default-environment possibility agreement. -/
theorem langDiamond_iff_exists_operationalLambdaRewrite
    (lang : LanguageDef) (s : LangSort lang)
    (φ : Pattern → Prop) (p : Pattern) :
    langDiamond lang φ p ↔
      ∃ q,
        (languageOperationalLambdaTheory lang).rewriteRel
          (constantProgramEndomorphism lang p)
          (constantProgramEndomorphism lang q) ∧
        φ q := by
  simpa [langDiamond, languageOperationalLambdaTheory] using
    (langDiamondUsing_iff_exists_operationalLambdaRewrite
      RelationEnv.empty lang s φ p)

/-- Default-environment rely/box agreement. -/
theorem langBox_iff_forall_operationalLambdaIncoming
    (lang : LanguageDef) (s : LangSort lang)
    (φ : Pattern → Prop) (p : Pattern) :
    langBox lang φ p ↔
      ∀ q,
        (languageOperationalLambdaTheory lang).rewriteRel
          (constantProgramEndomorphism lang q)
          (constantProgramEndomorphism lang p) →
        φ q := by
  simpa [langBox, languageOperationalLambdaTheory] using
    (langBoxUsing_iff_forall_operationalLambdaIncoming
      RelationEnv.empty lang s φ p)

/-- Negative canary: a rejected raw step remains rejected by the full
lambda-theory relation on constant terms. -/
theorem languageOperationalLambdaTheoryUsing_constant_not_rewrite
    (relEnv : RelationEnv) (lang : LanguageDef) (s : LangSort lang)
    (p q : Pattern) (h : ¬ langReducesUsing relEnv lang p q) :
    ¬ (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel
        (constantProgramEndomorphism lang p)
        (constantProgramEndomorphism lang q) := by
  rwa [languageOperationalLambdaTheoryUsing_constant_rewrite_iff
    relEnv lang s p q]

/-! ## Concrete non-collapse canary -/

/-- The rho constructor category's identity path is distinct from quote then
drop. -/
theorem rho_identity_ne_pdropNquote :
    (SortPath.nil : SortPath rhoCalc rhoProc rhoProc) ≠ pdropNquoteMor := by
  intro h
  change
    (SortPath.nil : SortPath rhoCalc rhoProc rhoProc) =
      SortPath.cons (SortPath.cons SortPath.nil nquoteArrow) pdropArrow at h
  cases h

/-- Yoneda preserves the concrete distinction between the rho identity path
and quote-then-drop. -/
theorem rho_yoneda_identity_ne_pdropNquote :
    CategoryTheory.yoneda.map
        (SortPath.nil : SortPath rhoCalc rhoProc rhoProc) ≠
      CategoryTheory.yoneda.map pdropNquoteMor := by
  intro h
  exact rho_identity_ne_pdropNquote
    ((languageConstructorYoneda_map_eq_iff rhoCalc
      (SortPath.nil : SortPath rhoCalc rhoProc rhoProc)
      pdropNquoteMor).1 h)

end Mettapedia.OSLF.Framework.LanguagePresheafSharing
