import Mettapedia.GSLT.LanguageDef.IRPass
import Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.Core.ConservativeExtension
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# The binding-decision language

Binding decision trees are the first intermediate representation of the
generic lowering: constructor tests, child projections, bound-occurrence
tests, captures, and joins.  Here they are a language definition, and their
evaluation is the operational semantics that definition generates.

The machine has three state forms.  `run` executes a decision against a
subject under a continuation; `ret` returns the bindings one decision
produced; `done` is the terminal result.  A join pushes its right operand,
runs the left operand, then merges the two results with the canonical
binding merge, so the nesting of merges is exactly the nesting of the
decision tree.  Projection, bound tests, constructor tests, and merging are
relation premises evaluated by a deterministic catalog; unsupported states
are inert.

The authored language is proved exact against an independent typed
reference machine on every encoded state, so the later adequacy of that
machine to the compiled decision evaluator transfers to the language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.GSLT.Core.ConservativeExtension (encodeNat decodeNat? decodeNat?_encodeNat)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Encodings of the typed data -/

def encodeName (name : String) : Pattern := .apply name []

def decodeName? : Pattern → Option String
  | .apply name [] => some name
  | _ => none

@[simp] theorem decodeName?_encodeName (name : String) :
    decodeName? (encodeName name) = some name := rfl

def encodePath : AccessPath → Pattern
  | .root => .apply "bd-root" []
  | .child parent index => .apply "bd-child" [encodePath parent, encodeNat index]

def decodePath? : Pattern → Option AccessPath
  | .apply "bd-root" [] => some .root
  | .apply "bd-child" [parent, index] => do
      let parentPath ← decodePath? parent
      let childIndex ← decodeNat? index
      some (.child parentPath childIndex)
  | _ => none

@[simp] theorem decodePath?_encodePath : ∀ path : AccessPath,
    decodePath? (encodePath path) = some path
  | .root => rfl
  | .child parent index => by
      simp [encodePath, decodePath?, decodePath?_encodePath parent]

def encodeBindings : Bindings → Pattern
  | [] => .apply "bd-nil" []
  | (name, value) :: rest => .apply "bd-bind" [encodeName name, value, encodeBindings rest]

def decodeBindings? : Pattern → Option Bindings
  | .apply "bd-nil" [] => some []
  | .apply "bd-bind" [name, value, rest] => do
      let boundName ← decodeName? name
      let boundRest ← decodeBindings? rest
      some ((boundName, value) :: boundRest)
  | _ => none

@[simp] theorem decodeBindings?_encodeBindings : ∀ bindings : Bindings,
    decodeBindings? (encodeBindings bindings) = some bindings
  | [] => rfl
  | (name, value) :: rest => by
      simp [encodeBindings, decodeBindings?, decodeBindings?_encodeBindings rest, encodeName,
        decodeName?]

def encodeDecision : Decision → Pattern
  | .succeed => .apply "bd-succeed" []
  | .capture path name => .apply "bd-capture" [encodePath path, encodeName name]
  | .checkBound path expected => .apply "bd-check-bound" [encodePath path, encodeNat expected]
  | .checkConstructor path expected arity children =>
      .apply "bd-check-constructor"
        [encodePath path, encodeName expected, encodeNat arity, encodeDecision children]
  | .join head tail => .apply "bd-join" [encodeDecision head, encodeDecision tail]

/-- Continuation frames: a pending right operand, or a finished left result
waiting to be merged. -/
inductive Frame where
  | joinRight (tail : Decision)
  | joinMerge (bindings : Bindings)

def encodeFrame : Frame → Pattern
  | .joinRight tail => .apply "bd-join-right" [encodeDecision tail]
  | .joinMerge bindings => .apply "bd-join-merge" [encodeBindings bindings]

def encodeKont : List Frame → Pattern
  | [] => .apply "bd-knil" []
  | frame :: rest => .apply "bd-kcons" [encodeFrame frame, encodeKont rest]

/-- States of the typed reference machine. -/
inductive MachineState where
  | run (decision : Decision) (subject : Pattern) (kont : List Frame)
  | ret (bindings : Bindings) (subject : Pattern) (kont : List Frame)
  | done (bindings : Bindings)

def encodeState : MachineState → Pattern
  | .run decision subject kont =>
      .apply "bd-run" [encodeDecision decision, subject, encodeKont kont]
  | .ret bindings subject kont =>
      .apply "bd-ret" [encodeBindings bindings, subject, encodeKont kont]
  | .done bindings => .apply "bd-done" [encodeBindings bindings]

/-! ## The typed reference machine -/

/-- Whether a focused subject is the bound occurrence with the expected index. -/
def isBoundAt (focused : Pattern) (expected : Nat) : Bool :=
  match focused with
  | .bvar actual => expected == actual
  | _ => false

/-- Whether a focused subject is an application with the expected head and arity. -/
def isConstructorOf (focused : Pattern) (expected : String) (arity : Nat) : Bool :=
  match focused with
  | .apply actual arguments => expected == actual && arity == arguments.length
  | _ => false

/-- One deterministic machine step.  A stuck state has no successor. -/
def machineStep? : MachineState → Option MachineState
  | .run .succeed subject kont => some (.ret [] subject kont)
  | .run (.capture path name) subject kont =>
      match path.project? subject with
      | some focused => some (.ret [(name, focused)] subject kont)
      | none => none
  | .run (.checkBound path expected) subject kont =>
      match path.project? subject with
      | some focused => if isBoundAt focused expected then some (.ret [] subject kont) else none
      | none => none
  | .run (.checkConstructor path expected arity children) subject kont =>
      match path.project? subject with
      | some focused =>
          if isConstructorOf focused expected arity then some (.run children subject kont)
          else none
      | none => none
  | .run (.join head tail) subject kont => some (.run head subject (.joinRight tail :: kont))
  | .ret bindings subject (.joinRight tail :: kont) =>
      some (.run tail subject (.joinMerge bindings :: kont))
  | .ret tailBindings subject (.joinMerge headBindings :: kont) =>
      match mergeBindings headBindings tailBindings with
      | some merged => some (.ret merged subject kont)
      | none => none
  | .ret bindings _ [] => some (.done bindings)
  | .done _ => none

/-! ## Authored syntax -/

private def constructor (label category : String)
    (parameters : List (String × TypeExpr)) : GrammarRule :=
  { label
    category
    params := parameters.map fun parameter => .simple parameter.1 parameter.2
    syntaxPattern := [] }

def pathType : TypeDecl := TypeDecl.plain "Path"
def indexType : TypeDecl := TypeDecl.plain "Index"
def nameType : TypeDecl := TypeDecl.plain "Name"
def subjectType : TypeDecl := TypeDecl.plain "Subject"
def decisionType : TypeDecl := TypeDecl.plain "Decision"
def bindingsType : TypeDecl := TypeDecl.plain "Bindings"
def frameType : TypeDecl := TypeDecl.plain "Frame"
def kontType : TypeDecl := TypeDecl.plain "Kont"
def stateType : TypeDecl := TypeDecl.plain "State"

def rootConstructor : GrammarRule := constructor "bd-root" "Path" []
def childConstructor : GrammarRule :=
  constructor "bd-child" "Path" [("parent", .base "Path"), ("index", .base "Index")]
def zeroConstructor : GrammarRule := constructor "zero" "Index" []
def succConstructor : GrammarRule := constructor "succ" "Index" [("pred", .base "Index")]
def succeedConstructor : GrammarRule := constructor "bd-succeed" "Decision" []
def captureConstructor : GrammarRule :=
  constructor "bd-capture" "Decision" [("path", .base "Path"), ("name", .base "Name")]
def checkBoundConstructor : GrammarRule :=
  constructor "bd-check-bound" "Decision" [("path", .base "Path"), ("index", .base "Index")]
def checkConstructorConstructor : GrammarRule :=
  constructor "bd-check-constructor" "Decision"
    [("path", .base "Path"), ("head", .base "Name"), ("arity", .base "Index"),
      ("child", .base "Decision")]
def joinConstructor : GrammarRule :=
  constructor "bd-join" "Decision" [("head", .base "Decision"), ("tail", .base "Decision")]
def nilBindingsConstructor : GrammarRule := constructor "bd-nil" "Bindings" []
def bindConstructor : GrammarRule :=
  constructor "bd-bind" "Bindings"
    [("name", .base "Name"), ("value", .base "Subject"), ("rest", .base "Bindings")]
def joinRightConstructor : GrammarRule :=
  constructor "bd-join-right" "Frame" [("tail", .base "Decision")]
def joinMergeConstructor : GrammarRule :=
  constructor "bd-join-merge" "Frame" [("bindings", .base "Bindings")]
def knilConstructor : GrammarRule := constructor "bd-knil" "Kont" []
def kconsConstructor : GrammarRule :=
  constructor "bd-kcons" "Kont" [("frame", .base "Frame"), ("rest", .base "Kont")]
def runConstructor : GrammarRule :=
  constructor "bd-run" "State"
    [("decision", .base "Decision"), ("subject", .base "Subject"), ("kont", .base "Kont")]
def retConstructor : GrammarRule :=
  constructor "bd-ret" "State"
    [("bindings", .base "Bindings"), ("subject", .base "Subject"), ("kont", .base "Kont")]
def doneConstructor : GrammarRule :=
  constructor "bd-done" "State" [("bindings", .base "Bindings")]

def metavariable (name : String) : Pattern := .fvar name

def runPattern (decision subject kont : Pattern) : Pattern :=
  .apply "bd-run" [decision, subject, kont]
def retPattern (bindings subject kont : Pattern) : Pattern :=
  .apply "bd-ret" [bindings, subject, kont]
def donePattern (bindings : Pattern) : Pattern := .apply "bd-done" [bindings]
def succeedPattern : Pattern := .apply "bd-succeed" []
def capturePattern (path name : Pattern) : Pattern := .apply "bd-capture" [path, name]
def checkBoundPattern (path index : Pattern) : Pattern := .apply "bd-check-bound" [path, index]
def checkConstructorPattern (path head arity child : Pattern) : Pattern :=
  .apply "bd-check-constructor" [path, head, arity, child]
def joinPattern (head tail : Pattern) : Pattern := .apply "bd-join" [head, tail]
def nilBindingsPattern : Pattern := .apply "bd-nil" []
def bindPattern (name value rest : Pattern) : Pattern := .apply "bd-bind" [name, value, rest]
def joinRightPattern (tail : Pattern) : Pattern := .apply "bd-join-right" [tail]
def joinMergePattern (bindings : Pattern) : Pattern := .apply "bd-join-merge" [bindings]
def knilPattern : Pattern := .apply "bd-knil" []
def kconsPattern (frame rest : Pattern) : Pattern := .apply "bd-kcons" [frame, rest]

def projectRelation : String := "bd-project"
def boundRelation : String := "bd-bound"
def constructorRelation : String := "bd-constructor"
def mergeRelation : String := "bd-merge"

/-- Succeed returns no bindings. -/
def succeedRewrite : RewriteRule :=
  { name := "bd-succeed"
    typeContext := [("subject", .base "Subject"), ("kont", .base "Kont")]
    premises := []
    left := runPattern succeedPattern (metavariable "subject") (metavariable "kont")
    right := retPattern nilBindingsPattern (metavariable "subject") (metavariable "kont") }

/-- Capture binds the projected subject to the name. -/
def captureRewrite : RewriteRule :=
  { name := "bd-capture"
    typeContext :=
      [("path", .base "Path"), ("name", .base "Name"), ("subject", .base "Subject"),
        ("kont", .base "Kont"), ("focused", .base "Subject")]
    premises :=
      [.relationQuery projectRelation
        [metavariable "path", metavariable "subject", metavariable "focused"]]
    left := runPattern (capturePattern (metavariable "path") (metavariable "name"))
      (metavariable "subject") (metavariable "kont")
    right := retPattern
      (bindPattern (metavariable "name") (metavariable "focused") nilBindingsPattern)
      (metavariable "subject") (metavariable "kont") }

/-- A bound test passes with no bindings. -/
def checkBoundRewrite : RewriteRule :=
  { name := "bd-check-bound"
    typeContext :=
      [("path", .base "Path"), ("index", .base "Index"), ("subject", .base "Subject"),
        ("kont", .base "Kont"), ("focused", .base "Subject")]
    premises :=
      [.relationQuery projectRelation
        [metavariable "path", metavariable "subject", metavariable "focused"],
       .relationQuery boundRelation [metavariable "focused", metavariable "index"]]
    left := runPattern (checkBoundPattern (metavariable "path") (metavariable "index"))
      (metavariable "subject") (metavariable "kont")
    right := retPattern nilBindingsPattern (metavariable "subject") (metavariable "kont") }

/-- A constructor test continues with the child decision. -/
def checkConstructorRewrite : RewriteRule :=
  { name := "bd-check-constructor"
    typeContext :=
      [("path", .base "Path"), ("head", .base "Name"), ("arity", .base "Index"),
        ("child", .base "Decision"), ("subject", .base "Subject"), ("kont", .base "Kont"),
        ("focused", .base "Subject")]
    premises :=
      [.relationQuery projectRelation
        [metavariable "path", metavariable "subject", metavariable "focused"],
       .relationQuery constructorRelation
        [metavariable "focused", metavariable "head", metavariable "arity"]]
    left := runPattern
      (checkConstructorPattern (metavariable "path") (metavariable "head")
        (metavariable "arity") (metavariable "child"))
      (metavariable "subject") (metavariable "kont")
    right := runPattern (metavariable "child") (metavariable "subject") (metavariable "kont") }

/-- A join runs its left operand with the right operand pending. -/
def joinRewrite : RewriteRule :=
  { name := "bd-join"
    typeContext :=
      [("head", .base "Decision"), ("tail", .base "Decision"), ("subject", .base "Subject"),
        ("kont", .base "Kont")]
    premises := []
    left := runPattern (joinPattern (metavariable "head") (metavariable "tail"))
      (metavariable "subject") (metavariable "kont")
    right := runPattern (metavariable "head") (metavariable "subject")
      (kconsPattern (joinRightPattern (metavariable "tail")) (metavariable "kont")) }

/-- A finished left operand starts the right operand. -/
def joinRightRewrite : RewriteRule :=
  { name := "bd-join-right"
    typeContext :=
      [("bindings", .base "Bindings"), ("tail", .base "Decision"), ("subject", .base "Subject"),
        ("kont", .base "Kont")]
    premises := []
    left := retPattern (metavariable "bindings") (metavariable "subject")
      (kconsPattern (joinRightPattern (metavariable "tail")) (metavariable "kont"))
    right := runPattern (metavariable "tail") (metavariable "subject")
      (kconsPattern (joinMergePattern (metavariable "bindings")) (metavariable "kont")) }

/-- A finished right operand is merged with the left result. -/
def joinMergeRewrite : RewriteRule :=
  { name := "bd-join-merge"
    typeContext :=
      [("tailBindings", .base "Bindings"), ("headBindings", .base "Bindings"),
        ("subject", .base "Subject"), ("kont", .base "Kont"), ("merged", .base "Bindings")]
    premises :=
      [.relationQuery mergeRelation
        [metavariable "headBindings", metavariable "tailBindings", metavariable "merged"]]
    left := retPattern (metavariable "tailBindings") (metavariable "subject")
      (kconsPattern (joinMergePattern (metavariable "headBindings")) (metavariable "kont"))
    right := retPattern (metavariable "merged") (metavariable "subject") (metavariable "kont") }

/-- An empty continuation finishes. -/
def finishRewrite : RewriteRule :=
  { name := "bd-finish"
    typeContext := [("bindings", .base "Bindings"), ("subject", .base "Subject")]
    premises := []
    left := retPattern (metavariable "bindings") (metavariable "subject") knilPattern
    right := donePattern (metavariable "bindings") }

/-- The binding-decision language definition. -/
def language : LanguageDef :=
  { name := "binding-decision"
    types :=
      [pathType, indexType, nameType, subjectType, decisionType, bindingsType, frameType,
        kontType, stateType]
    terms :=
      [rootConstructor, childConstructor, zeroConstructor, succConstructor, succeedConstructor,
        captureConstructor, checkBoundConstructor, checkConstructorConstructor, joinConstructor,
        nilBindingsConstructor, bindConstructor, joinRightConstructor, joinMergeConstructor,
        knilConstructor, kconsConstructor, runConstructor, retConstructor, doneConstructor]
    equations := []
    rewrites :=
      [succeedRewrite, captureRewrite, checkBoundRewrite, checkConstructorRewrite, joinRewrite,
        joinRightRewrite, joinMergeRewrite, finishRewrite] }

private theorem labels_nodup : (language.terms.map (·.label)).Nodup := by
  decide

private theorem succeed_validate : LanguageDef.validateRewrite language succeedRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem capture_validate : LanguageDef.validateRewrite language captureRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem checkBound_validate : LanguageDef.validateRewrite language checkBoundRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem checkConstructor_validate : LanguageDef.validateRewrite language checkConstructorRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem join_validate : LanguageDef.validateRewrite language joinRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem joinRight_validate : LanguageDef.validateRewrite language joinRightRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem joinMerge_validate : LanguageDef.validateRewrite language joinMergeRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem finish_validate : LanguageDef.validateRewrite language finishRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, runPattern, retPattern, donePattern, succeedPattern,
      capturePattern, checkBoundPattern, checkConstructorPattern, joinPattern,
      nilBindingsPattern, bindPattern, joinRightPattern, joinMergePattern, knilPattern,
      kconsPattern, metavariable, projectRelation, boundRelation, constructorRelation,
      mergeRelation, pathType, indexType, nameType, subjectType, decisionType, bindingsType,
      frameType, kontType, stateType, rootConstructor, childConstructor, zeroConstructor,
      succConstructor, succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites, LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite rewriteMember
  change rewrite ∈
    [succeedRewrite, captureRewrite, checkBoundRewrite, checkConstructorRewrite, joinRewrite,
      joinRightRewrite, joinMergeRewrite, finishRewrite] at rewriteMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at rewriteMember
  rcases rewriteMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact succeed_validate
  · exact capture_validate
  · exact checkBound_validate
  · exact checkConstructor_validate
  · exact join_validate
  · exact joinRight_validate
  · exact joinMerge_validate
  · exact finish_validate

/-- The authored definition passes the ordinary structural validator. -/
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact rewrites_validate

def validatedLanguage : ValidatedLanguageDef := ⟨language, language_validate⟩

/-! ## The relation catalog -/

def rowWhen (condition : Bool) (arguments : List Pattern) : List (List Pattern) :=
  if condition then [arguments] else []

/-- The deterministic catalog consulted by the premises. -/
def relationEnv : RelationEnv where
  tuples relation arguments :=
    if relation = projectRelation then
      match arguments with
      | [path, subject, .fvar _] =>
          match decodePath? path with
          | some accessPath =>
              match accessPath.project? subject with
              | some focused => [[path, subject, focused]]
              | none => []
          | none => []
      | _ => []
    else if relation = boundRelation then
      match arguments with
      | [focused, index] =>
          match decodeNat? index with
          | some expected => rowWhen (isBoundAt focused expected) arguments
          | none => []
      | _ => []
    else if relation = constructorRelation then
      match arguments with
      | [focused, head, arity] =>
          match decodeName? head, decodeNat? arity with
          | some expected, some count => rowWhen (isConstructorOf focused expected count) arguments
          | _, _ => []
      | _ => []
    else if relation = mergeRelation then
      match arguments with
      | [left, right, .fvar _] =>
          match decodeBindings? left, decodeBindings? right with
          | some headBindings, some tailBindings =>
              match mergeBindings headBindings tailBindings with
              | some merged => [[left, right, encodeBindings merged]]
              | none => []
          | _, _ => []
      | _ => []
    else
      []

/-- The binding-decision representation. -/
def ir : IRLanguage := ⟨validatedLanguage, relationEnv⟩

private theorem rules_noncontextual :
    ∀ rule, rule ∈ language.rewrites → NoncontextualPremises rule.premises := by
  intro rule ruleMember
  change rule ∈
    [succeedRewrite, captureRewrite, checkBoundRewrite, checkConstructorRewrite, joinRewrite,
      joinRightRewrite, joinMergeRewrite, finishRewrite] at ruleMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ruleMember
  rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact .nil
    | exact .relationQuery .nil
    | exact .relationQuery (.relationQuery .nil)

theorem language_isEquationFree : language.isEquationFree = true := by decide

/-- The representation's step is membership in the generic root executor. -/
theorem step_iff_mem_executor (source target : Pattern) :
    ir.semantics.Step source target ↔
      target ∈ rewriteStepWithPremisesUsing relationEnv language source := by
  change EquationSaturatedStep (engineBasePremises relationEnv) language source target ↔ _
  rw [equationSaturatedStep_iff_step_of_no_generators language_isEquationFree]
  rw [step_iff_rootStep_of_noncontextualRules rules_noncontextual]
  simp [RootStep, rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing]

end Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
