import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecutionBeta
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedOperationalDecomposition
import Mettapedia.OSLF.MeTTaIL.ContextualStepClosedSubsystem

/-!
# Canonical rule data for mixed HOL/native computation

The operation accepts a canonically encoded native term and returns one
canonically encoded reduct. Its contextual rules are precisely the fifteen
term positions of `StepCore`; there is no descent through declaration-name,
variable-index, or universe-expression metadata. The seven declared roots
retain every repeated parameter of the original joint presentation.

Binder-crossing computation calls the existing authored binding language.
The finite rule lists are flattened here, and closed-subsystem invariance
proves that this extension leaves that binding service unchanged.

Head equality is intentionally a separately qualified, two-input service;
this rule inventory does not enumerate equivalent universe spellings.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open DeclarationAwarePatternCodec DeclarationAwareSubstitutionLanguage
open NativeIndexedFamilies

namespace Binding
export DeclarationAwareSubstitutionExecution
  (weaken substitute beta execute language rules intrinsic_weaken_exact intrinsic_beta_exact)
end Binding

def compute (source : Pattern) : Pattern :=
  .apply "prime-tm-computes" [source]

def constant (name : Lean.Name) : Pattern := tmConst (encodeDeclName name)

def apps (function : Pattern) (arguments : List Pattern) : Pattern :=
  arguments.foldl tmApp function

def nil (element : Pattern) : Pattern :=
  apps (constant Intrinsic.nilName) [element]

def cons (element head tail : Pattern) : Pattern :=
  apps (constant Intrinsic.consName) [element, head, tail]

def listEliminate (element motive zeroCase nextCase list : Pattern) : Pattern :=
  apps (constant Intrinsic.eliminateName) [element, motive, zeroCase, nextCase, list]

def identityEliminate (element point motive reflCase endpoint evidence : Pattern) : Pattern :=
  apps (constant Intrinsic.identityEliminateName)
    [element, point, motive, reflCase, endpoint, evidence]

def nilRel (source target relation : Pattern) : Pattern :=
  apps (constant IntrinsicRelator.nilRelName) [source, target, relation]

def consRel (source target relation head₁ head₂ tail₁ tail₂ heads tails : Pattern) : Pattern :=
  apps (constant IntrinsicRelator.consRelName)
    [source, target, relation, head₁, head₂, tail₁, tail₂, heads, tails]

def relEliminate (source target relation motive zeroCase nextCase list₁ list₂
    evidence : Pattern) : Pattern :=
  apps (constant IntrinsicRelator.eliminateName)
    [source, target, relation, motive, zeroCase, nextCase, list₁, list₂, evidence]

def proof (proposition : Pattern) : Pattern :=
  tmApp (constant FormationSensitiveHOLProofFamily.proofName) proposition

def implication (left right : Pattern) : Pattern :=
  apps (constant `HOLUniformList.implication) [left, right]

def universal (domain predicate : Pattern) : Pattern :=
  apps (constant `HOLUniformList.universal) [domain, predicate]

def computationRule (name : String) (source target : Pattern)
    (premises : List Premise := []) : RewriteRule :=
  { name, typeContext := [], premises, left := compute source, right := target }

def betaRule : RewriteRule :=
  computationRule "prime-compute-beta" (tmApp (tmLam (m "body")) (m "argument"))
    (m "output") [.congruence
      (Binding.substitute zero (m "argument") (m "body")) (m "output")]

def firstRule : RewriteRule :=
  computationRule "prime-compute-first" (tmFst (tmPair (m "a") (m "b"))) (m "a")

def secondRule : RewriteRule :=
  computationRule "prime-compute-second" (tmSnd (tmPair (m "a") (m "b"))) (m "b")

def listNilRule : RewriteRule :=
  computationRule "prime-compute-list-nil"
    (listEliminate (m "a") (m "p") (m "z") (m "s") (nil (m "a"))) (m "z")

def listConsRule : RewriteRule :=
  computationRule "prime-compute-list-cons"
    (listEliminate (m "a") (m "p") (m "z") (m "s")
      (cons (m "a") (m "h") (m "t")))
    (apps (m "s") [m "h", m "t",
      listEliminate (m "a") (m "p") (m "z") (m "s") (m "t")])

def identityRule : RewriteRule :=
  computationRule "prime-compute-identity"
    (identityEliminate (m "a") (m "x") (m "p") (m "d") (m "x")
      (tmRefl (m "x"))) (m "d")

def relNilRule : RewriteRule :=
  computationRule "prime-compute-rel-nil"
    (relEliminate (m "a") (m "b") (m "r") (m "p") (m "z") (m "s")
      (nil (m "a")) (nil (m "b")) (nilRel (m "a") (m "b") (m "r")))
    (m "z")

def relConsRule : RewriteRule :=
  computationRule "prime-compute-rel-cons"
    (relEliminate (m "a") (m "b") (m "r") (m "p") (m "z") (m "s")
      (cons (m "a") (m "h") (m "t")) (cons (m "b") (m "k") (m "u"))
      (consRel (m "a") (m "b") (m "r") (m "h") (m "k") (m "t") (m "u")
        (m "he") (m "te")))
    (apps (m "s") [m "h", m "k", m "t", m "u", m "he", m "te",
      relEliminate (m "a") (m "b") (m "r") (m "p") (m "z") (m "s")
        (m "t") (m "u") (m "te")])

def implicationRule : RewriteRule :=
  computationRule "prime-compute-proof-implication"
    (proof (implication (m "p") (m "q")))
    (tmPi (proof (m "p")) (m "lifted"))
    [.congruence (Binding.weaken zero (proof (m "q"))) (m "lifted")]

def universalRule : RewriteRule :=
  computationRule "prime-compute-proof-universal"
    (proof (universal (m "a") (m "f")))
    (tmPi (m "a") (proof (tmApp (m "lifted") (tmVar zero))))
    [.congruence (Binding.weaken zero (m "f")) (m "lifted")]

def rootRules : List RewriteRule :=
  [betaRule, firstRule, secondRule, listNilRule, listConsRule, identityRule,
   relNilRule, relConsRule, implicationRule, universalRule]

def contextRule (name : String) (source subterm target : Pattern) : RewriteRule :=
  computationRule name source target [.congruence (compute subterm) (m "next")]

def contextRules : List RewriteRule :=
  [contextRule "prime-context-pi-domain" (tmPi (m "a") (m "b")) (m "a")
      (tmPi (m "next") (m "b")),
   contextRule "prime-context-pi-body" (tmPi (m "a") (m "b")) (m "b")
      (tmPi (m "a") (m "next")),
   contextRule "prime-context-sigma-domain" (tmSigma (m "a") (m "b")) (m "a")
      (tmSigma (m "next") (m "b")),
   contextRule "prime-context-sigma-body" (tmSigma (m "a") (m "b")) (m "b")
      (tmSigma (m "a") (m "next")),
   contextRule "prime-context-id-type" (tmId (m "a") (m "b") (m "c")) (m "a")
      (tmId (m "next") (m "b") (m "c")),
   contextRule "prime-context-id-left" (tmId (m "a") (m "b") (m "c")) (m "b")
      (tmId (m "a") (m "next") (m "c")),
   contextRule "prime-context-id-right" (tmId (m "a") (m "b") (m "c")) (m "c")
      (tmId (m "a") (m "b") (m "next")),
   contextRule "prime-context-lambda" (tmLam (m "a")) (m "a") (tmLam (m "next")),
   contextRule "prime-context-app-function" (tmApp (m "a") (m "b")) (m "a")
      (tmApp (m "next") (m "b")),
   contextRule "prime-context-app-argument" (tmApp (m "a") (m "b")) (m "b")
      (tmApp (m "a") (m "next")),
   contextRule "prime-context-pair-first" (tmPair (m "a") (m "b")) (m "a")
      (tmPair (m "next") (m "b")),
   contextRule "prime-context-pair-second" (tmPair (m "a") (m "b")) (m "b")
      (tmPair (m "a") (m "next")),
   contextRule "prime-context-first" (tmFst (m "a")) (m "a") (tmFst (m "next")),
   contextRule "prime-context-second" (tmSnd (m "a")) (m "a") (tmSnd (m "next")),
   contextRule "prime-context-refl" (tmRefl (m "a")) (m "a") (tmRefl (m "next"))]

def computationRules : List RewriteRule := rootRules ++ contextRules

def language : LanguageDef :=
  { Binding.language with
    name := "prime-canonical-hol-native-computation-v1"
    terms := Binding.language.terms ++
      [DeclarationAwareDataLanguage.dataConstructor "prime-tm-computes" 1]
    rewrites := Binding.rules ++ computationRules }

def execute (fuel : Nat) (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) language fuel source

def bindingHeads : List String :=
  ["prime-index-lt", "prime-tm-weakens-at", "prime-tm-substitutes-at", "prime-tm-root-beta"]

theorem binding_calls_closed :
    ∀ rule ∈ Binding.rules, CallsWithin bindingHeads rule.premises := by decide

theorem computation_heads :
    ∀ rule ∈ computationRules, HasOperationHead ["prime-tm-computes"] rule.left := by decide

theorem binding_service_unchanged (fuel : Nat) (source : Pattern)
    (head : HasOperationHead bindingHeads source) :
    execute fuel source = Binding.execute fuel source := by
  symm
  apply rewriteAt_closed_extension bindingHeads Binding.language language computationRules
    (engineBasePremises RelationEnv.empty) (engineBasePremises RelationEnv.empty)
    rfl binding_calls_closed ?_ fuel source head
  intro source head rule member
  exact matchPattern_eq_nil_of_disjoint_operationHeads
    (computation_heads rule member) head (by decide)

theorem root_count : rootRules.length = 10 := rfl
theorem context_count : contextRules.length = 15 := rfl
theorem total_count : language.rewrites.length = 55 := rfl

#print axioms binding_service_unchanged

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData
