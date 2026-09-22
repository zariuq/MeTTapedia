import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution

/-!
# Controls for declaration-derived scoped syntax

The input control reads the actual rho constructor declarations, with both
Name and Proc variables and a binding argument. The multi-abstraction control
keeps two different binder counts in one authored parameter family.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

private def dropRule : GrammarRule := rhoCalc.terms.get ⟨1, by decide⟩
private def parallelRule : GrammarRule := rhoCalc.terms.get ⟨3, by decide⟩
private def inputRule : GrammarRule := rhoCalc.terms.get ⟨5, by decide⟩
private def zeroRule : GrammarRule := rhoCalc.terms.get ⟨0, by decide⟩
private def quoteRule : GrammarRule := rhoCalc.terms.get ⟨2, by decide⟩

private def zero {bound : List TypeExpr} : Term (signatureOf rhoCalc) bound TypeExpr.proc :=
  .op (.constructor zeroRule (List.get_mem _ _) (by
    simp [UsesBareCollection, zeroRule, rhoCalc]) .nil) .nil

private def quotedZero {bound : List TypeExpr} :
    Term (signatureOf rhoCalc) bound TypeExpr.name := by
  apply Term.op (Operator.constructor quoteRule (List.get_mem _ _) (by
    simp [UsesBareCollection, quoteRule, rhoCalc, TypeExpr.proc, TypeExpr.baseType])
    (.cons (.simple "p" TypeExpr.proc) .nil))
  change Args (signatureOf rhoCalc) [([], TypeExpr.proc)] bound
  exact .cons zero .nil

private def drop {bound : List TypeExpr}
    (name : Term (signatureOf rhoCalc) bound TypeExpr.name) :
    Term (signatureOf rhoCalc) bound TypeExpr.proc :=
  .op (.constructor dropRule (List.get_mem _ _) (by
    simp [UsesBareCollection, dropRule, rhoCalc, TypeExpr.name, TypeExpr.baseType])
    (.cons (.simple "n" TypeExpr.name) .nil)) (.cons name .nil)

/-- Both the newly bound name and an enclosing name occur in the body. -/
def inputBody : Term (signatureOf rhoCalc)
    [TypeExpr.name, TypeExpr.name, TypeExpr.proc] TypeExpr.proc :=
  .op (.collectionConstructor parallelRule (List.get_mem _ _) "ps" .hashBag TypeExpr.proc rfl 3)
    (show Args (signatureOf rhoCalc) (List.replicate 3 ([], TypeExpr.proc))
      [TypeExpr.name, TypeExpr.name, TypeExpr.proc] from
    .cons (drop (.var .zero))
      (.cons (drop (.var (.succ .zero)))
        (.cons (.var (.succ (.succ .zero))) .nil)))

def input : Term (signatureOf rhoCalc) [TypeExpr.name, TypeExpr.proc] TypeExpr.proc :=
  .op (.constructor inputRule (List.get_mem _ _) (by
    simp [UsesBareCollection, inputRule, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.funType])
    (.cons (.simple "n" TypeExpr.name)
      (.cons (.abstraction none "p" TypeExpr.name TypeExpr.proc) .nil)))
    (.cons (.var .zero) (.cons inputBody .nil))

theorem input_erases : erase input =
    .apply "PInput" [.bvar 0, .lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],
        .apply "PDrop" [.bvar 1], .bvar 2] none)] := rfl

theorem input_typed : HasType rhoCalc FreeTypeContext.empty
    [TypeExpr.name, TypeExpr.proc] (erase input) TypeExpr.proc := erase_typed input

theorem input_weakened_erases : erase (weaken (t := TypeExpr.proc) input) =
    .apply "PInput" [.bvar 1, .lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],
        .apply "PDrop" [.bvar 2], .bvar 3] none)] := by
  rw [erase_weaken, input_erases]
  rfl

/-- A well-scoped alternative still captures the enclosing Name variable. -/
def captured : Pattern := .apply "PInput" [.bvar 1, .lambda none
  (.collection .hashBag [.apply "PDrop" [.bvar 0],
    .apply "PDrop" [.bvar 0], .bvar 3] none)]

theorem captured_is_wellScoped : captured.isWellScopedAt 3 = true := by decide

theorem weakening_does_not_capture :
    erase (weaken (t := TypeExpr.proc) input) ≠ captured := by
  rw [input_weakened_erases]
  decide

/-- Binder elimination is exercised on the actual collection constructor body,
with both a newly bound Name and an enclosing Name in its ordered context. -/
theorem input_instantiation :
    erase (bind (extend (Term.var (S := signatureOf rhoCalc) (Var.zero
      (Γ := [TypeExpr.proc]) (s := TypeExpr.name)))) inputBody) =
    instantiateBVar (.bvar 0) (erase inputBody) :=
  erase_bind_extend _ inputBody

/-- Replacing the enclosing Name traverses an actual Name-binding argument;
the local Name remains bound and the older Proc shifts down. -/
theorem input_closed_instantiation :
    erase (bind (extend (quotedZero (bound := [TypeExpr.proc]))) input) =
    .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],
        .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]], .bvar 1] none)] := by
  rw [erase_bind_extend, input_erases]
  simp [instantiateBVar, instantiateBVarAt, erase,
    eraseConstructorArguments, ParameterScope.wrap,
    quotedZero, zero, quoteRule, zeroRule, rhoCalc, liftBVars]

private def multiRule : GrammarRule where
  label := "BindMany"
  category := "Proc"
  params := [.multiAbstraction "p" (.arrow (.multiBinder TypeExpr.name) TypeExpr.proc)]
  syntaxPattern := [.nonTerminal "p"]

private def multiLanguage : LanguageDef :=
  LanguageDef.ofCore "ManyBinders" ["Name", "Proc"] [multiRule] [] []

theorem multiLanguage_valid : multiLanguage.validate = [] := by decide +kernel

def threeBinders : Term (signatureOf multiLanguage) [TypeExpr.proc] TypeExpr.proc :=
  .op (.constructor multiRule (by simp [multiLanguage, LanguageDef.ofCore]) (by
    simp [UsesBareCollection, multiRule, TermParam.multiAbstraction])
    (.cons (.multiAbstraction [] "p" TypeExpr.name TypeExpr.proc 3) .nil))
    (.cons (.var (.succ (.succ (.succ .zero)))) .nil)

def zeroBinders : Term (signatureOf multiLanguage) [TypeExpr.proc] TypeExpr.proc :=
  .op (.constructor multiRule (by simp [multiLanguage, LanguageDef.ofCore]) (by
    simp [UsesBareCollection, multiRule, TermParam.multiAbstraction])
    (.cons (.multiAbstraction [] "p" TypeExpr.name TypeExpr.proc 0) .nil))
    (.cons (.var .zero) .nil)

theorem multiple_counts_preserved :
    erase threeBinders = .apply "BindMany" [.multiLambda 3 [] (.bvar 3)] ∧
    erase zeroBinders = .apply "BindMany" [.multiLambda 0 [] (.bvar 0)] := ⟨rfl, rfl⟩

theorem illShaped_abstraction_has_no_scope
    (binder : Option String) (name : String) (kind : CollType) (element : TypeExpr)
    (binders : List TypeExpr) (body : TypeExpr) :
    IsEmpty (ParameterScope (.abstractionNamed binder name (.collection kind element))
      binders body) := ⟨fun scope => nomatch scope⟩

theorem no_dangling_variable (type : TypeExpr) : IsEmpty (Var ([] : List TypeExpr) type) :=
  ⟨fun position => nomatch position⟩

theorem undeclared_constructor_not_available :
    ¬ ({ label := "Invented", category := "Proc", params := [], syntaxPattern := [] } :
      GrammarRule) ∈ rhoCalc.terms := by decide

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Controls
