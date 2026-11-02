import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateApplication
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Dependent product application with a guarded Boolean domain

The identity method has a family that depends on its input and output.
Applying it retains the exact substituted source family. False arguments
fail the domain guard, and a false result fails the specialized family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateApplicationControls

open Mettapedia.Logic
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open HOL.FiniteConstructorEncoding.Controls (Constants model values)

def domain : HOL.ClosedTerm Constants (.arr .prop .prop) := .lam (.var .vz)
def conjunction : HOL.ClosedTerm Constants (.arr .prop (.arr .prop .prop)) :=
  .lam (.lam (.and (.var (.vs .vz)) (.var .vz)))
def identity : HOL.ClosedTerm Constants (.arr .prop .prop) := .lam (.var .vz)
def motive : HOL.ClosedTerm Constants (.arr .prop (.arr .prop (.arr .prop .prop))) :=
  .lam (.lam (.lam (.and (.var (.vs (.vs .vz))) (.and (.var (.vs .vz)) (.var .vz)))))

theorem conjunction_weaken (Γ : HOL.Ctx Empty) : HOL.weakenCtx Γ conjunction =
    (.lam (.lam (.and (.var (.vs .vz)) (.var .vz))) : HOL.Term Constants Γ (.arr .prop (.arr .prop .prop))) := by
  induction Γ with
  | nil => rfl
  | cons type Γ previous =>
    simp only [HOL.weakenCtx_cons, previous, HOL.weaken, HOL.rename, HOL.Rename.lift]

def familyAt {Γ : HOL.Ctx Empty} (argument : HOL.Term Constants Γ .prop) :
    HOL.Term Constants Γ (.arr .prop .prop) :=
  .lam (.app (.app (HOL.weakenCtx (.prop :: Γ) conjunction) (HOL.weaken argument)) (.var .vz))

def family : HOL.Term Constants [.prop] (.arr .prop .prop) := familyAt (.var .vz)

def lex : LexicalReading Nat Empty Constants where
  constCode? _ := none
  headCode?
    | 0 => some ⟨.arr .prop .prop, domain⟩
    | 1 => some ⟨.prop, .top⟩
    | 2 => some ⟨.arr .prop (.arr .prop .prop), conjunction⟩
    | 3 => some ⟨.prop, .bot⟩
    | 4 => some ⟨.arr .prop (.arr .prop (.arr .prop .prop)), motive⟩
    | _ => none

def sourceDomain {n : Nat} : CTm Nat n := .head 0
def sourceFunction : CTm Nat 0 := .lam sourceDomain (.var 0)
def sourceArgument : CTm Nat 0 := .head 1
def sourceFamily : CTm Nat 1 :=
  .lam sourceDomain (.app (.app (.head 2) (.var 1)) (.var 0))

theorem domain_read {Γ : HOL.Ctx Empty} : Reads lex (sourceDomain (n := Γ.length)) (HOL.weakenCtx Γ domain) :=
  .head rfl

theorem function_read : Reads lex (Γ := []) sourceFunction identity :=
  .abstraction domain_read (by
    have index : (HOL.Var.vz : HOL.Var ([.prop] : HOL.Ctx Empty) .prop).toFin = (0 : Fin 1) := Fin.ext (by decide)
    exact index ▸ (Reads.var (lex := lex) (HOL.Var.vz : HOL.Var ([.prop] : HOL.Ctx Empty) .prop)))

theorem argument_read : Reads lex (Γ := []) sourceArgument (.top : HOL.ClosedFormula Constants) := .head rfl

theorem family_read : Reads lex (Γ := [.prop]) sourceFamily family :=
  .abstraction domain_read (.application (.application (.head rfl) (by
    have index : (HOL.Var.vs .vz : HOL.Var ([.prop, .prop] : HOL.Ctx Empty) .prop).toFin = (1 : Fin 2) := Fin.ext (by decide)
    exact index ▸ (Reads.var (lex := lex) (HOL.Var.vs .vz : HOL.Var ([.prop, .prop] : HOL.Ctx Empty) .prop)))) (by
    have index : (HOL.Var.vz : HOL.Var ([.prop, .prop] : HOL.Ctx Empty) .prop).toFin = (0 : Fin 2) := Fin.ext (by decide)
    exact index ▸ (Reads.var (lex := lex) (HOL.Var.vz : HOL.Var ([.prop, .prop] : HOL.Ctx Empty) .prop))))

def conjunctionBeta {Γ : HOL.Ctx Empty} {assumptions : List (HOL.Formula Constants Γ)}
    (argument result : HOL.Term Constants Γ .prop) :
    HOL.ProofSyntax Constants assumptions (.eq
      (.app (.app (HOL.weakenCtx Γ conjunction) argument) result) (.and argument result)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (HOL.CurriedGuardProgramProofs.beta2 (.and (.var (.vs .vz)) (.var .vz)) argument result)
  simp only [HOL.instantiate, HOL.subst, HOL.Subst.single, HOL.Subst.lift, conjunction_weaken]
  have cancel : HOL.subst (HOL.Subst.single result) (HOL.rename HOL.Rename.weaken argument) = argument :=
    HOL.PredicateFixedPoint.subst_single_weaken result argument
  simp only [cancel]

theorem conjunctionBeta_free {Γ : HOL.Ctx Empty} {assumptions : List (HOL.Formula Constants Γ)}
    (argument result : HOL.Term Constants Γ .prop) :
    (conjunctionBeta (assumptions := assumptions) argument result).FunctionExtensionalityFree := by
  unfold conjunctionBeta
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact HOL.CurriedGuardProgramProofs.beta2_free _ _ _

def familyBeta {Γ : HOL.Ctx Empty} {assumptions : List (HOL.Formula Constants Γ)}
    (argument result : HOL.Term Constants Γ .prop) :
    HOL.ProofSyntax Constants assumptions (.eq (.app (familyAt argument) result) (.and argument result)) := by
  have second : HOL.ProofSyntax Constants assumptions (.eq
      (.app (.app (HOL.weakenCtx Γ conjunction) argument) result) (.and argument result)) :=
    conjunctionBeta argument result
  apply HOL.ProofSyntax.eqTrans ?_ second
  apply HOL.ProofSyntax.castIndices rfl ?_
    (HOL.ProofSyntax.beta result
      (.app (.app (HOL.weakenCtx (.prop :: Γ) conjunction) (HOL.weaken argument)) (.var .vz)))
  simp only [HOL.instantiate, HOL.subst, HOL.Subst.single, HOL.subst_weakenCtx,
    HOL.PredicateFixedPoint.subst_single_weaken]
  rfl

theorem familyBeta_free {Γ : HOL.Ctx Empty} {assumptions : List (HOL.Formula Constants Γ)}
    (argument result : HOL.Term Constants Γ .prop) :
    (familyBeta (assumptions := assumptions) argument result).FunctionExtensionalityFree := by
  unfold familyBeta
  constructor
  · apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · exact conjunctionBeta_free _ _

def functionTyped : HOL.ProofSyntax Constants [] (.app (HOL.PredicateProducts.pi domain family) identity) := by
  apply HOL.PredicateProducts.introduce
  let point : HOL.Term Constants [.prop] .prop := .var .vz
  let hypotheses : List (HOL.Formula Constants [.prop]) := [.app (HOL.weaken domain) point]
  have pointTrue : HOL.ProofSyntax Constants hypotheses point :=
    .impE (.eqPropEL (.beta point (.var .vz))) (.hyp 0)
  have resultTrue : HOL.ProofSyntax Constants hypotheses (.app (HOL.weaken identity) point) :=
    .impE (.eqPropER (.beta point (.var .vz))) pointTrue
  exact .impE (.eqPropER (familyBeta point (.app (HOL.weaken identity) point))) (.andI pointTrue resultTrue)

theorem functionTyped_free : functionTyped.FunctionExtensionalityFree := by
  unfold functionTyped
  apply HOL.PredicateProducts.introduce_free
  exact ⟨familyBeta_free _ _, ⟨True.intro, True.intro⟩, ⟨True.intro, True.intro, True.intro⟩⟩

def argumentTyped : HOL.ProofSyntax Constants [] (.app domain (.top : HOL.ClosedFormula Constants)) :=
  .impE (.eqPropER (.beta .top (.var .vz))) .topI

def applied := applyProduct (Reads.product domain_read family_read) domain_read family_read
  function_read argument_read functionTyped argumentTyped

theorem applied_free : applied.val.FunctionExtensionalityFree :=
  applyProduct_free (Reads.product domain_read family_read) domain_read family_read
    function_read argument_read functionTyped argumentTyped functionTyped_free ⟨True.intro, True.intro⟩

def expectedSource : CTm Nat 0 :=
  .lam sourceDomain (.app (.app (.head 2) (.head 1)) (.var 0))

theorem substituted_source : sourceFamily.subst (CTm.subst0 sourceArgument) = expectedSource := rfl

theorem specialized_read : Reads lex (Γ := []) expectedSource (HOL.instantiate (.top : HOL.ClosedFormula Constants) family) :=
  substituted_source ▸ applied.property.2

theorem specialized_infer : Reader.infer? lex [] expectedSource =
    some ⟨.arr .prop .prop, HOL.instantiate (.top : HOL.ClosedFormula Constants) family⟩ :=
  Reader.infer?_complete specialized_read

theorem false_argument_refused : ¬ Nonempty (HOL.ProofSyntax Constants [] (.app domain (.bot : HOL.ClosedFormula Constants))) := by
  rintro ⟨proof⟩
  have impossible := HOL.Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (by intro _ absent; nomatch absent) (by intro _ absent; nomatch absent)
  exact impossible

theorem false_result_refused : ¬ Nonempty (HOL.ProofSyntax Constants []
    (.app (HOL.instantiate (.top : HOL.ClosedFormula Constants) family) .bot)) := by
  rintro ⟨proof⟩
  have impossible := HOL.Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (by intro _ absent; nomatch absent) (by intro _ absent; nomatch absent)
  exact impossible.2

namespace MotiveResult

def sourceFamily : CTm Nat 1 := .app (.app (.head 4) (.var 0)) (.head 1)
def family : HOL.Term Constants [.prop] (.arr .prop .prop) :=
  .app (.app (HOL.weakenCtx [.prop] motive) (.var .vz)) .top

theorem family_read : Reads lex (Γ := [.prop]) sourceFamily family :=
  .application (.application (.head rfl) (by
    have index : (HOL.Var.vz : HOL.Var ([.prop] : HOL.Ctx Empty) .prop).toFin = (0 : Fin 1) := Fin.ext (by decide)
    exact index ▸ (Reads.var (lex := lex) (HOL.Var.vz : HOL.Var ([.prop] : HOL.Ctx Empty) .prop))))
    (by simpa only [HOL.weakenCtx_cons, HOL.weakenCtx_nil, HOL.weaken, HOL.rename] using
      (Reads.head (lex := lex) (Γ := [.prop]) (head := 1) (closed := HOL.Term.top) rfl))

def functionTyped : HOL.ProofSyntax Constants [] (.app (HOL.PredicateProducts.pi domain family) identity) := by
  apply HOL.PredicateProducts.introduce
  let point : HOL.Term Constants [.prop] .prop := .var .vz
  let hypotheses : List (HOL.Formula Constants [.prop]) := [.app (HOL.weaken domain) point]
  have pointTrue : HOL.ProofSyntax Constants hypotheses point :=
    .impE (.eqPropEL (.beta point (.var .vz))) (.hyp 0)
  have resultTrue : HOL.ProofSyntax Constants hypotheses (.app (HOL.weaken identity) point) :=
    .impE (.eqPropER (.beta point (.var .vz))) pointTrue
  exact .impE (.eqPropER (HOL.CurriedGuardProgramProofs.beta3
    (.and (.var (.vs (.vs .vz))) (.and (.var (.vs .vz)) (.var .vz)))
    point .top (.app (HOL.weaken identity) point))) (.andI pointTrue (.andI .topI resultTrue))

theorem functionTyped_free : functionTyped.FunctionExtensionalityFree := by
  unfold functionTyped
  apply HOL.PredicateProducts.introduce_free
  exact ⟨HOL.CurriedGuardProgramProofs.beta3_free _ _ _ _, ⟨True.intro, True.intro⟩,
    True.intro, ⟨True.intro, True.intro, True.intro⟩⟩

def applied := applyProduct (Reads.product domain_read family_read) domain_read family_read
  function_read argument_read functionTyped argumentTyped

theorem applied_free : applied.val.FunctionExtensionalityFree :=
  applyProduct_free (Reads.product domain_read family_read) domain_read family_read
    function_read argument_read functionTyped argumentTyped functionTyped_free ⟨True.intro, True.intro⟩

theorem motive_read : Reads lex (Γ := []) (sourceFamily.subst (CTm.subst0 sourceArgument))
    (.app (.app motive .top) .top) :=
  .application (.application (.head rfl) (.head rfl)) (.head rfl)

def producedWitness := inhabitReadResult motive .top .top (.app identity .top)
  applied.property.2 motive_read applied.val

theorem producedWitness_free : producedWitness.FunctionExtensionalityFree :=
  inhabitReadResult_free motive .top .top (.app identity .top)
    applied.property.2 motive_read applied.val applied_free

end MotiveResult

#print axioms applied_free
#print axioms false_argument_refused
#print axioms false_result_refused
#print axioms MotiveResult.producedWitness_free

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateApplicationControls
