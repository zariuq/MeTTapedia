import Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.OSLF.Syntax.TermClone

/-!
# The authored WM constructors in the intrinsic binding term algebra

The four core operators are taken from the declarations of the structural
`LanguageDef`. Their arguments and results are intrinsically sorted. The
generic binding-term substitution and clone laws therefore apply without a
second WM-specific substitution operation. Erasure compares these terms with
the patterns used by the existing WM operational semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusBindingSignature

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.TypeSynthesis
open _root_.CategoryTheory

abbrev WMSignature := signatureOf wmStructuralLanguageDef
private abbrev State := TypeExpr.base "State"
private abbrev Query := TypeExpr.base "Query"
private abbrev Evidence := TypeExpr.base "BinaryEvidence"

def reviseOperator : WMSignature.Op State :=
  .constructor reviseDecl (by simp [wmStructuralLanguageDef, LanguageDef.ofCore, coreTerms])
    (by simp [UsesBareCollection, reviseDecl])
    (.cons (.simple "first" State) (.cons (.simple "second" State) .nil))

def extractOperator : WMSignature.Op Evidence :=
  .constructor extractDecl (by simp [wmStructuralLanguageDef, LanguageDef.ofCore, coreTerms])
    (by simp [UsesBareCollection, extractDecl])
    (.cons (.simple "world" State) (.cons (.simple "query" Query) .nil))

def combineOperator : WMSignature.Op Evidence :=
  .constructor combineDecl (by simp [wmStructuralLanguageDef, LanguageDef.ofCore, coreTerms])
    (by simp [UsesBareCollection, combineDecl])
    (.cons (.simple "first" Evidence) (.cons (.simple "second" Evidence) .nil))

def zeroOperator : WMSignature.Op Evidence :=
  .constructor evidenceZeroDecl
    (by simp [wmStructuralLanguageDef, LanguageDef.ofCore, coreTerms])
    (by simp [UsesBareCollection, evidenceZeroDecl]) .nil

/-- The four operator arities are computed from the authored parameter rows. -/
theorem core_operator_arities :
    WMSignature.arity reviseOperator = [([], State), ([], State)] ∧
    WMSignature.arity extractOperator = [([], State), ([], Query)] ∧
    WMSignature.arity combineOperator = [([], Evidence), ([], Evidence)] ∧
    WMSignature.arity zeroOperator = [] := ⟨rfl, rfl, rfl, rfl⟩

def revise {Γ : Ctx WMSignature} (first second : Term WMSignature Γ State) :
    Term WMSignature Γ State :=
  .op reviseOperator (.cons first (.cons second .nil))

def extract {Γ : Ctx WMSignature} (world : Term WMSignature Γ State)
    (query : Term WMSignature Γ Query) : Term WMSignature Γ Evidence :=
  .op extractOperator (.cons world (.cons query .nil))

def combine {Γ : Ctx WMSignature} (first second : Term WMSignature Γ Evidence) :
    Term WMSignature Γ Evidence :=
  .op combineOperator (.cons first (.cons second .nil))

def zero {Γ : Ctx WMSignature} : Term WMSignature Γ Evidence :=
  .op zeroOperator .nil

theorem erase_revise {Γ : Ctx WMSignature}
    (first second : Term WMSignature Γ State) :
    erase (revise first second) = pRevise (erase first) (erase second) := rfl

theorem erase_extract {Γ : Ctx WMSignature}
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query) :
    erase (extract world query) = pExtract (erase world) (erase query) := rfl

theorem erase_combine {Γ : Ctx WMSignature}
    (first second : Term WMSignature Γ Evidence) :
    erase (combine first second) = pCombine (erase first) (erase second) := rfl

theorem erase_zero {Γ : Ctx WMSignature} :
    erase (zero (Γ := Γ)) = pEvidenceZero := rfl

theorem bind_revise {Γ Δ : Ctx WMSignature} (sigma : Sub WMSignature Γ Δ)
    (first second : Term WMSignature Γ State) :
    bind sigma (revise first second) = revise (bind sigma first) (bind sigma second) := rfl

theorem bind_extract {Γ Δ : Ctx WMSignature} (sigma : Sub WMSignature Γ Δ)
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query) :
    bind sigma (extract world query) = extract (bind sigma world) (bind sigma query) := rfl

theorem bind_combine {Γ Δ : Ctx WMSignature} (sigma : Sub WMSignature Γ Δ)
    (first second : Term WMSignature Γ Evidence) :
    bind sigma (combine first second) = combine (bind sigma first) (bind sigma second) := rfl

theorem bind_zero {Γ Δ : Ctx WMSignature} (sigma : Sub WMSignature Γ Δ) :
    bind sigma (zero (Γ := Γ)) = zero (Γ := Δ) := rfl

/-- The n-ary clone action for observation is the declaration-derived
simultaneous substitution, not a second substitution semantics. -/
theorem clone_substitute_extract {Γ Δ : Ctx WMSignature}
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query)
    (env : (i : Fin Γ.length) → Term WMSignature Δ (Γ.get i)) :
    (termClone WMSignature).substitute (extract world query) env =
      extract ((termClone WMSignature).substitute world env)
        ((termClone WMSignature).substitute query env) := by
  exact bind_extract (substVar env) world query

/-- Substitution through a two-argument observation composes as the actual
WM term clone's categorical composition, even for shared variables in its
state and query arguments. -/
theorem clone_substitute_assoc_extract {Γ Δ Θ : Ctx WMSignature}
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query)
    (first : (i : Fin Γ.length) → Term WMSignature Δ (Γ.get i))
    (second : (i : Fin Δ.length) → Term WMSignature Θ (Δ.get i)) :
    (termClone WMSignature).substitute
      ((termClone WMSignature).substitute (extract world query) first) second =
    (termClone WMSignature).substitute (extract world query)
      (fun i => (termClone WMSignature).substitute (first i) second) :=
  (termClone WMSignature).substitute_assoc (extract world query) first second

/-- The declaration-derived observation also commutes with raw binder
instantiation under erasure. -/
theorem erase_extract_bind_extend {Γ : Ctx WMSignature}
    {domain : TypeExpr} (replacement : Term WMSignature Γ domain)
    (world : Term WMSignature (domain :: Γ) State)
    (query : Term WMSignature (domain :: Γ) Query) :
    erase (bind (extend replacement) (extract world query)) =
      instantiateBVar (erase replacement)
        (pExtract (erase world) (erase query)) := by
  rw [erase_bind_extend, erase_extract]

/-- The generic intrinsic term model supplies sorted source and target
representatives for the *actual* directed authored extraction step. This
connects n-ary syntax and substitution to the operational WM presentation. -/
theorem intrinsic_extraction_typed_computation {Γ : Ctx WMSignature}
    (first second : Term WMSignature Γ State)
    (query : Term WMSignature Γ Query) :
    HasType wmStructuralLanguageDef FreeTypeContext.empty Γ
      (erase (extract (revise first second) query)) Evidence ∧
    HasType wmStructuralLanguageDef FreeTypeContext.empty Γ
      (erase (combine (extract first query) (extract second query))) Evidence ∧
    langSemanticReduces wmStructuralLanguageDef
      (erase (extract (revise first second) query))
      (erase (combine (extract first query) (extract second query))) := by
  refine ⟨erase_typed _, erase_typed _, ?_⟩
  simpa [erase_extract, erase_revise, erase_combine] using
    evidence_add_computes (erase first) (erase second) (erase query)

/-- A sort-preserving simultaneous substitution preserves the concrete
authored extraction computation. This uses the same source rule after
substitution, not an abstract assertion that every raw authored step is
stable under every untyped pattern substitution. -/
theorem intrinsic_extraction_substitution_stable {Γ Δ : Ctx WMSignature}
    (sigma : Sub WMSignature Γ Δ)
    (first second : Term WMSignature Γ State)
    (query : Term WMSignature Γ Query) :
    langSemanticReduces wmStructuralLanguageDef
      (erase (bind sigma (extract (revise first second) query)))
      (erase (bind sigma
        (combine (extract first query) (extract second query)))) := by
  have step :=
    (intrinsic_extraction_typed_computation
      (bind sigma first) (bind sigma second) (bind sigma query)).2.2
  simpa [bind_extract, bind_revise, bind_combine] using step

/-- One state input is reused twice while the query occupies a distinct
position. Contraction is supplied by the generic clone, not by an extra WM
constructor or a special-purpose variable rule. -/
def repeatedStateObservation : Term WMSignature [State, Query] Evidence :=
  extract (revise (.var .zero) (.var .zero)) (.var (.succ .zero))

theorem repeatedStateObservation_erases :
    erase repeatedStateObservation =
      pExtract (pRevise (.bvar 0) (.bvar 0)) (.bvar 1) := rfl

theorem repeatedStateObservation_computes :
    langSemanticReduces wmStructuralLanguageDef
      (erase repeatedStateObservation)
      (erase (combine
        (extract (.var (S := WMSignature) (Γ := [State, Query]) .zero)
          (.var (.succ .zero)))
        (extract (.var .zero) (.var (.succ .zero))))) := by
  exact (intrinsic_extraction_typed_computation
    (.var .zero) (.var .zero) (.var (.succ .zero))).2.2

/-- A query binder cannot be used in a State input merely because the raw
pattern shape of `Revise` is otherwise correct. -/
theorem raw_cross_sort_revise_rejected :
    ¬ HasType wmStructuralLanguageDef FreeTypeContext.empty [Query]
      (pRevise (.bvar 0) (.bvar 0)) State := by
  intro typed
  have accepted :=
    (checkHasType_eq_true_iff (by decide +kernel)).2 typed
  have rejected :
      checkHasType
        wmStructuralLanguageDef FreeTypeContext.empty [Query]
        (pRevise (.bvar 0) (.bvar 0)) State = false := by
    decide +kernel
  rw [rejected] at accepted
  cases accepted

/-- Erasure changes under genuine context substitution. Thus the intrinsic
context presheaf cannot simply be identified with the existing constant
raw-pattern program presheaf; a comparison must transport substitutions. -/
theorem erasure_not_constant_under_substitution :
    erase (bind
      (extend (Term.var (S := WMSignature) (Γ := [State]) .zero))
      (Term.var (S := WMSignature) (Γ := [State, State]) (.succ .zero))) ≠
    erase (Term.var (S := WMSignature) (Γ := [State, State]) (.succ .zero)) := by
  decide

/-- The actual declaration-derived observation is represented as a morphism
from its full input context to the singleton evidence context. -/
def observationMorphism {Γ : Ctx WMSignature}
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query) :
    (⟨Γ⟩ : Syntactic.Ctxt WMSignature) ⟶ Syntactic.single Evidence :=
  (Syntactic.termsRepresented ⟨Γ⟩ Evidence).symm (extract world query)

theorem observationMorphism_represents {Γ : Ctx WMSignature}
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query) :
    Syntactic.termsRepresented ⟨Γ⟩ Evidence
      (observationMorphism world query) = extract world query := by
  simp [observationMorphism]

/-- Categorical precomposition is exactly intrinsic simultaneous
substitution of both observation arguments. -/
theorem observationMorphism_comp {Γ Δ : Ctx WMSignature}
    (sigma : Sub WMSignature Γ Δ)
    (world : Term WMSignature Γ State) (query : Term WMSignature Γ Query) :
    (sigma : (⟨Δ⟩ : Syntactic.Ctxt WMSignature) ⟶
      (⟨Γ⟩ : Syntactic.Ctxt WMSignature)) ≫
      observationMorphism world query =
    observationMorphism (bind sigma world) (bind sigma query) := by
  funext sort position
  cases position with
  | zero => exact bind_extract sigma world query
  | succ impossible => exact nomatch impossible

#print axioms core_operator_arities
#print axioms clone_substitute_assoc_extract
#print axioms intrinsic_extraction_substitution_stable
#print axioms observationMorphism_comp
#print axioms raw_cross_sort_revise_rejected
#print axioms erasure_not_constant_under_substitution

end Mettapedia.OSLF.Framework.WMCalculusBindingSignature
