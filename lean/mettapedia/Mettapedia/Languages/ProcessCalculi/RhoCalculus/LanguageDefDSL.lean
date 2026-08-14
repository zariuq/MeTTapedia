import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Explicit extensions of the canonical rho `LanguageDef`

`Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc` is the sole authored semantic root.
It presents the paper calculus: `Comm` is the only primitive computational
rule, `ParCong` supplies contextual closure, and `QuoteDrop` remains an
equation.  This module contains named deltas for conveniences that are not in
that core.  Every language below is obtained by extending `rhoCalc`; none is a
second definition of rho.

The execution delta is intentionally available only in Lean.  CeTTa's
`--lang rhocalc --profile cost` instantiates the pure calculus and does not use
any value from this module.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- An explicitly additive rho-language extension.  Keeping the delta as data
prevents an extension from silently becoming a second semantic root. -/
structure RhoExtensionDelta where
  typeDecls : List TypeDecl := []
  termDecls : List GrammarRule := []
  equationDecls : List Equation := []
  rewriteDecls : List RewriteRule := []

namespace RhoExtensionDelta

/-- Compose two deltas in declaration order. -/
def compose (first second : RhoExtensionDelta) : RhoExtensionDelta where
  typeDecls := first.typeDecls ++ second.typeDecls
  termDecls := first.termDecls ++ second.termDecls
  equationDecls := first.equationDecls ++ second.equationDecls
  rewriteDecls := first.rewriteDecls ++ second.rewriteDecls

/-- Apply a named delta to an already-authored language. -/
def extend (delta : RhoExtensionDelta) (base : LanguageDef)
    (extendedName : String) : LanguageDef :=
  { base with
      «name» := extendedName
      «types» := base.types ++ delta.typeDecls
      «terms» := base.terms ++ delta.termDecls
      «equations» := base.equations ++ delta.equationDecls
      «rewrites» := base.rewrites ++ delta.rewriteDecls }

@[simp] theorem extend_rewrites (delta : RhoExtensionDelta)
    (base : LanguageDef) (extendedName : String) :
    (delta.extend base extendedName).rewrites =
      base.rewrites ++ delta.rewriteDecls := rfl

@[simp] theorem extend_equations (delta : RhoExtensionDelta)
    (base : LanguageDef) (extendedName : String) :
    (delta.extend base extendedName).equations =
      base.equations ++ delta.equationDecls := rfl

end RhoExtensionDelta

/-! ## Named deltas -/

/-- Direct execution of a free quotation.  This is not a rule of pure rho. -/
def execRewrite : RewriteRule where
  «name» := "Exec"
  typeContext := [("P", TypeExpr.proc)]
  premises := []
  left := .apply "PDrop" [.apply "NQuote" [.fvar "P"]]
  right := .fvar "P"

/-- Minimal execution delta: `*(@P) ~> P`. -/
def execDelta : RhoExtensionDelta where
  rewriteDecls := [execRewrite]

/-- Explicit transport of one reduction through finite-set context. -/
def parSetCongRewrite : RewriteRule where
  «name» := "ParSetCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := .collection .hashSet [.fvar "S"] (some "rest")
  right := .collection .hashSet [.fvar "T"] (some "rest")

/-- Optional finite-set context descent, kept separate from execution and
represented by a rule rather than a collection flag. -/
def setContextDelta : RhoExtensionDelta where
  rewriteDecls := [parSetCongRewrite]

section DeltaDSL

open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- A syntax-only container used to elaborate the bounded reference-encoding
delta.  It is private and is never consumed as a language; only its new
declarations are extracted into `referenceEncodingDelta`. -/
private def referenceEncodingDeltaSource : LanguageDef :=
  languageDef! {
    name : "RhoReferenceEncodingDelta"
    types {
      Proc
      Name
    }
    terms {
      PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns, xs).*map(|n, x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
      PNew . ^[xs].p:[Name* -> Proc]
        |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;
    }
    equations {
      Extrude . xs.*map(|x| x # ...rest)
        |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest}));
    }
    rewrites {
      PolyComm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
        ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
      NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T);
    }
  }

/-- Polyadic input, restriction/extrusion, and their rules as a bounded audit
delta for the Greg/Dylan reference encoding.  It does not redefine the pure
constructors, `QuoteDrop`, or unary `Comm`. -/
def referenceEncodingDelta : RhoExtensionDelta where
  termDecls := referenceEncodingDeltaSource.terms
  equationDecls := referenceEncodingDeltaSource.equations
  rewriteDecls := referenceEncodingDeltaSource.rewrites

/-- A private elaboration container for host-native fold declarations. -/
private def nativeFoldDeltaSource : LanguageDef :=
  languageDef! {
    name : "RhoNativeFoldDelta"
    types {
      Proc
      ![i64] as Int
    }
    terms {
      CastInt . n:Int |- "int" "(" n ")" : Proc ![fold];
      Add . a:Proc, b:Proc |- a "+" b : Proc ![fold];
    }
    equations { }
    rewrites { }
  }

end DeltaDSL

/-- Host-native integer fold declarations, isolated from the reference syntax
delta and from pure rho. -/
def nativeFoldDelta : RhoExtensionDelta where
  typeDecls := nativeFoldDeltaSource.types.drop 1
  termDecls := nativeFoldDeltaSource.terms

/-! ## Derived extension languages -/

/-- Pure rho plus only direct free-drop execution. -/
def rhoCalcExecExt : LanguageDef :=
  execDelta.extend rhoCalc "RhoCalcExecExt"

/-- Pure rho plus optional finite-set congruence descent, but no `Exec`. -/
def rhoCalcSetExt : LanguageDef :=
  setContextDelta.extend rhoCalc "RhoCalcSetExt"

/-- The generic Lean extended-rho bucket: direct execution plus the bounded
reference-encoding syntax delta. -/
def rhoCalcExtended : LanguageDef :=
  (execDelta.compose referenceEncodingDelta).extend rhoCalc "RhoCalcExtended"

/-- `rhoCalcExtended` plus explicitly host-native fold declarations. -/
def rhoCalcExtendedWithNativeFolds : LanguageDef :=
  nativeFoldDelta.extend rhoCalcExtended "RhoCalcExtendedWithNativeFolds"

/-! ## Pure/extension behavioral boundary -/

/-- A free-standing dropped quotation. -/
def freeDropWitness : Pattern :=
  .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]

/-- The result supplied by the non-paper `Exec` rule. -/
def freeDropTarget : Pattern := .apply "PZero" []

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Free drop has no executable one-step successor in the canonical calculus. -/
theorem freeDrop_exec_nil_pure :
    rewriteAt (engineBasePremises RelationEnv.empty) rhoCalc 1
      freeDropWitness = [] := by
  decide +kernel

/-- Declarative form of free-drop inertness in pure rho. -/
theorem freeDrop_no_langReduces_pure (q : Pattern) :
    ¬ langReduces rhoCalc freeDropWitness q := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rewriteRule ruleMember
  change rewriteRule ∈ [rhoCommRewrite, rhoParCongRewrite] at ruleMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
  rcases ruleMember with ruleEq | ruleEq <;> subst rewriteRule <;> decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The minimal execution extension admits exactly the intended witness step. -/
theorem freeDrop_exec_mem_execExt :
    freeDropTarget ∈
      rewriteAt (engineBasePremises RelationEnv.empty) rhoCalcExecExt 1
        freeDropWitness := by
  decide +kernel

/-- Declarative form of the execution-extension witness. -/
theorem freeDrop_langReduces_execExt :
    langReduces rhoCalcExecExt freeDropWitness freeDropTarget := by
  exact exec_to_langReducesUsing
    (relEnv := RelationEnv.empty) (lang := rhoCalcExecExt)
    ⟨1, freeDrop_exec_mem_execExt⟩

/-- The theorem-level boundary: pure rho rejects free execution and the named
execution extension admits it. -/
theorem freeDrop_pure_vs_execExt :
    (∀ q, ¬ langReduces rhoCalc freeDropWitness q) ∧
      langReduces rhoCalcExecExt freeDropWitness freeDropTarget := by
  exact ⟨freeDrop_no_langReduces_pure, freeDrop_langReduces_execExt⟩

/-- The equational `QuoteDrop` cancellation remains in pure rho. -/
theorem quoteDrop_equation_present_pure :
    ∃ equation ∈ rhoCalc.equations, equation.name = "QuoteDrop" := by
  decide +kernel

/-- Pure rho contains `Comm` and contextual `ParCong`, but no `Exec`. -/
theorem rhoCalc_rewrite_names :
    rhoCalc.rewrites.map (·.name) = ["Comm", "ParCong"] := rfl

/-! ## Set-context policy witness, using COMM rather than Exec -/

/-- A pure COMM redex whose continuation ignores the received name. -/
def rhoCommRedex : Pattern :=
  .collection .hashBag
    [ .apply "POutput" [.fvar "x", .apply "PZero" []]
    , .apply "PInput" [.fvar "x", .lambda none (.apply "PZero" [])]
    ] none

/-- The reduct of `rhoCommRedex`. -/
def rhoCommReduct : Pattern :=
  .collection .hashBag [.apply "PZero" []] none

/-- A COMM redex nested under a set context. -/
def rhoSetCommWitness : Pattern :=
  .collection .hashSet [rhoCommRedex] none

/-- The set-context reduct admitted by `rhoCalcSetExt`. -/
def rhoSetCommWitnessNF : Pattern :=
  .collection .hashSet [rhoCommReduct] none

/-- The same COMM redex nested under a vector, used as a negative control. -/
def rhoVecCommWitness : Pattern :=
  .collection .vec [rhoCommRedex] none

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The COMM witness reduces at top level in canonical pure rho. -/
theorem rhoCommRedex_exec_mem_pure :
    rhoCommReduct ∈
      rewriteAt (engineBasePremises RelationEnv.empty) rhoCalc 1 rhoCommRedex := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Canonical bag-only rho blocks reduction below a set context. -/
theorem rhoSetCommWitness_exec_nil_canonical :
    rewriteAt (engineBasePremises RelationEnv.empty) rhoCalc 2
      rhoSetCommWitness = [] := by
  decide +kernel

theorem rhoSetCommWitness_no_langReduces_canonical (q : Pattern) :
    ¬ langReduces rhoCalc rhoSetCommWitness q := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rewriteRule ruleMember
  change rewriteRule ∈ [rhoCommRewrite, rhoParCongRewrite] at ruleMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
  rcases ruleMember with ruleEq | ruleEq <;> subst rewriteRule <;> decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The set-context extension admits the nested COMM step. -/
theorem rhoSetCommWitness_exec_mem_setExt :
    rhoSetCommWitnessNF ∈
      rewriteAt (engineBasePremises RelationEnv.empty) rhoCalcSetExt 2
        rhoSetCommWitness := by
  decide +kernel

theorem rhoSetCommWitness_langReduces_setExt :
    langReduces rhoCalcSetExt rhoSetCommWitness rhoSetCommWitnessNF := by
  exact exec_to_langReducesUsing
    (relEnv := RelationEnv.empty) (lang := rhoCalcSetExt)
    ⟨2, rhoSetCommWitness_exec_mem_setExt⟩

theorem rhoSetCommWitness_exists_langReduces_setExt :
    ∃ q, langReduces rhoCalcSetExt rhoSetCommWitness q :=
  ⟨rhoSetCommWitnessNF, rhoSetCommWitness_langReduces_setExt⟩

theorem rhoSetCommWitness_canonical_vs_setExt :
    (∀ q, ¬ langReduces rhoCalc rhoSetCommWitness q) ∧
      (∃ q, langReduces rhoCalcSetExt rhoSetCommWitness q) := by
  exact ⟨rhoSetCommWitness_no_langReduces_canonical,
    rhoSetCommWitness_exists_langReduces_setExt⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Neither canonical rho nor the set-only extension enables vector descent. -/
theorem rhoVecCommWitness_exec_nil_setExt :
    rewriteAt (engineBasePremises RelationEnv.empty) rhoCalcSetExt 3
      rhoVecCommWitness = [] := by
  decide +kernel

theorem rhoVecCommWitness_no_langReduces_setExt (q : Pattern) :
    ¬ langReduces rhoCalcSetExt rhoVecCommWitness q := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rewriteRule ruleMember
  change rewriteRule ∈ [rhoCommRewrite, rhoParCongRewrite, parSetCongRewrite] at ruleMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
  rcases ruleMember with ruleEq | ruleEq | ruleEq <;>
    subst rewriteRule <;> decide +kernel

theorem rhoCalcSetExt_set_not_vec_context_policy :
    (∃ q, langReduces rhoCalcSetExt rhoSetCommWitness q) ∧
      (∀ q, ¬ langReduces rhoCalcSetExt rhoVecCommWitness q) := by
  exact ⟨rhoSetCommWitness_exists_langReduces_setExt,
    rhoVecCommWitness_no_langReduces_setExt⟩

/-! ## Structural and syntax export checks -/

def exportedPureSyntax : String :=
  renderLanguageWithUserSyntax rhoCalc

def exportedExtendedSyntax : String :=
  renderLanguageWithUserSyntax rhoCalcExtended

def exportedExtendedSyntaxWithFolds : String :=
  renderLanguageWithUserSyntax rhoCalcExtendedWithNativeFolds

theorem rhoCalcExecExt_rewrite_names :
    rhoCalcExecExt.rewrites.map (·.name) = ["Comm", "ParCong", "Exec"] := rfl

theorem rhoCalcExtended_rewrite_names :
    rhoCalcExtended.rewrites.map (·.name) =
      ["Comm", "ParCong", "Exec", "PolyComm", "NewCong"] := rfl

theorem rhoCalcExtended_new_term_names :
    (rhoCalcExtended.terms.drop rhoCalc.terms.length).map (·.label) =
      ["PInputs", "PNew"] := rfl

theorem rhoCalcExtendedWithNativeFolds_new_term_names :
    (rhoCalcExtendedWithNativeFolds.terms.drop rhoCalcExtended.terms.length).map
        (·.label) = ["CastInt", "Add"] := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended
