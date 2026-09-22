import Mettapedia.GSLT.LanguageDef.MultiRewriteExtension
import Mettapedia.GSLT.LanguageDef.MultiRewriteJoin
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Schematic denotation of multi-rewrite declarations

The declaration layer (`MultiRewriteExtension.denotedTheory`) fires on
literal pattern lists.  This module is the join denotation: one
substitution across all sources, then `applyBindings` on the targets.

Ordered matching is `matchArgsWith syntacticEq`.  That function already
calls `mergeBindingsWith` at every source, so the substitution law is
`mergeJoin`.  Bag matching (`joinBag`) is the commutative search; it is
named here and not claimed as rho COMM.

Unary windows use the canonical premise-aware, equation-modulo language
relation under an explicit relation environment. Joins retain their atomic
shared-binding match, saturated under the same endpoint equations. This
saturation is a semantic relation, not an arbitrary equational matcher.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MultiRewriteSchematic

open Mettapedia.GSLT
open Mettapedia.GSLT.MultiRewrite
open Mettapedia.GSLT.LanguageDef.MultiRewriteExtension
open Mettapedia.GSLT.LanguageDef.MultiRewriteJoin
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def matchSources (patterns terms : List Pattern) : List Bindings :=
  matchArgsWith syntacticEq patterns terms

def instantiate (σ : Bindings) (targets : List Pattern) : List Pattern :=
  targets.map (applyBindings σ)

def fires (declaration : MultiRewriteDecl)
    (sources targets : List Pattern) : Prop :=
  ∃ σ ∈ matchSources declaration.sources sources,
    targets = instantiate σ declaration.targets

/-- A retained join certificate: representatives, the common binding, and
its actual membership in executable matching. Equal supports need not have
the same certificate. -/
structure JoinWitness (relEnv : RelationEnv) (language : LanguageDef)
    (declaration : MultiRewriteDecl) (sources targets : List Pattern) where
  matchedSources : List Pattern
  bindings : Bindings
  source_eq : Pointwise (langGSLTUsing relEnv language).Equiv sources matchedSources
  matched : bindings ∈ matchSources declaration.sources matchedSources
  target_eq : Pointwise (langGSLTUsing relEnv language).Equiv
    (instantiate bindings declaration.targets) targets

def firesModulo (relEnv : RelationEnv) (language : LanguageDef)
    (declaration : MultiRewriteDecl) (sources targets : List Pattern) : Prop :=
  Nonempty (JoinWitness relEnv language declaration sources targets)

theorem fires_to_modulo (relEnv : RelationEnv) (language : LanguageDef)
    {declaration : MultiRewriteDecl} {sources targets : List Pattern}
    (firing : fires declaration sources targets) :
    firesModulo relEnv language declaration sources targets := by
  obtain ⟨bindings, matched, rfl⟩ := firing
  exact ⟨⟨sources, bindings,
    Pointwise.refl (langGSLTUsing relEnv language).equations.refl _, matched,
    Pointwise.refl (langGSLTUsing relEnv language).equations.refl _⟩⟩

def schematicTheoryUsing (relEnv : RelationEnv)
    (language : LanguageDef) (library : AdmittedLibrary) :
    MultiRewriteTheory where
  Term := Pattern
  equations := (langGSLTUsing relEnv language).equations
  rewrites := fun sources targets =>
    (ofUnary (langGSLTUsing relEnv language)).rewrites sources targets ∨
      (∃ declaration ∈ library.1,
        firesModulo relEnv language declaration sources targets)
  rewrites_resp_left := by
    intro sources sources' targets equiv firing
    rcases firing with unary | ⟨declaration, member, ⟨join⟩⟩
    · obtain ⟨targets', step, eqv⟩ :=
        (ofUnary (langGSLTUsing relEnv language)).rewrites_resp_left equiv unary
      exact ⟨targets', Or.inl step, eqv⟩
    · refine ⟨targets, Or.inr ⟨declaration, member, ⟨{ join with source_eq := ?_ }⟩⟩,
        Pointwise.refl (langGSLTUsing relEnv language).equations.refl _⟩
      exact Pointwise.trans (r := (langGSLTUsing relEnv language).Equiv)
        (fun first second => (langGSLTUsing relEnv language).equations.trans first second)
        (Pointwise.symm (r := (langGSLTUsing relEnv language).Equiv)
          (fun equal => (langGSLTUsing relEnv language).equations.symm equal) equiv)
        join.source_eq
  rewrites_resp_right := by
    intro sources targets targets' firing equiv
    rcases firing with unary | ⟨declaration, member, ⟨join⟩⟩
    · exact Or.inl
        ((ofUnary (langGSLTUsing relEnv language)).rewrites_resp_right unary equiv)
    · refine Or.inr ⟨declaration, member, ⟨{ join with target_eq := ?_ }⟩⟩
      exact Pointwise.trans (r := (langGSLTUsing relEnv language).Equiv)
        (fun first second => (langGSLTUsing relEnv language).equations.trans first second)
        join.target_eq equiv

def schematicTheory (language : LanguageDef) (library : AdmittedLibrary) :
    MultiRewriteTheory := schematicTheoryUsing RelationEnv.empty language library

def schematicGSLTUsing (relEnv : RelationEnv)
    (language : LanguageDef) (library : AdmittedLibrary) : GSLT :=
  (schematicTheoryUsing relEnv language library).toGSLT

def schematicGSLT (language : LanguageDef) (library : AdmittedLibrary) : GSLT :=
  schematicGSLTUsing RelationEnv.empty language library

/-- The support relation forgets which join declaration and binding fired.
Clients that retain events use this witness instead. The unary branch uses
the canonical kernel relation; it does not reconstruct an engine proof tree. -/
inductive RuleWitness (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (sources targets : List Pattern) : Type where
  | unary : (ofUnary (langGSLTUsing relEnv language)).rewrites sources targets →
      RuleWitness relEnv language library sources targets
  | join (declaration : MultiRewriteDecl) (authored : declaration ∈ library.1)
      (firing : JoinWitness relEnv language declaration sources targets) :
      RuleWitness relEnv language library sources targets

theorem ruleWitness_iff (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (sources targets : List Pattern) :
    Nonempty (RuleWitness relEnv language library sources targets) ↔
      (schematicTheoryUsing relEnv language library).rewrites sources targets := by
  constructor
  · rintro ⟨witness⟩
    cases witness with
    | unary step => exact Or.inl step
    | join declaration member firing => exact Or.inr ⟨declaration, member, ⟨firing⟩⟩
  · rintro (unary | ⟨declaration, member, ⟨join⟩⟩)
    · exact ⟨.unary unary⟩
    · exact ⟨.join declaration member join⟩

/-- Retain the chosen window (hence ordered occurrences), and the particular
join certificate. Its erasure is the existing kernel window, not a second
transition system. -/
structure RetainedEvent (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (source target : List Pattern) where
  window : (schematicTheoryUsing relEnv language library).WindowWitness source target
  rule : RuleWitness relEnv language library window.sources window.targets

theorem retainedEvent_iff_step (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (source target : List Pattern) :
    Nonempty (RetainedEvent relEnv language library source target) ↔
      (schematicGSLTUsing relEnv language library).Step source target := by
  constructor
  · rintro ⟨event⟩
    exact ⟨event.window⟩
  · rintro ⟨window⟩
    obtain ⟨rule⟩ := (ruleWitness_iff _ _ _ _ _).mpr window.rule
    exact ⟨⟨window, rule⟩⟩

def RuleWitness.joinLabel? {relEnv : RelationEnv} {language : LanguageDef}
    {library : AdmittedLibrary} {sources targets : List Pattern} :
    RuleWitness relEnv language library sources targets → Option String
  | .unary _ => none
  | .join declaration _ _ => some declaration.name

/-- Equal endpoint support cannot identify distinct authored join labels. -/
theorem join_witnesses_distinct {relEnv : RelationEnv} {language : LanguageDef}
    {library : AdmittedLibrary} {sources targets : List Pattern}
    (first second : MultiRewriteDecl) (firstMember : first ∈ library.1)
    (secondMember : second ∈ library.1)
    (firstFiring : JoinWitness relEnv language first sources targets)
    (secondFiring : JoinWitness relEnv language second sources targets)
    (different : first.name ≠ second.name) :
    RuleWitness.join first firstMember firstFiring ≠
      RuleWitness.join second secondMember secondFiring := by
  intro same
  exact different (Option.some.inj (congrArg RuleWitness.joinLabel? same))

theorem matchSources_length {patterns source : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchSources patterns source) :
    patterns.length = source.length := by
  induction patterns generalizing source bindings with
  | nil =>
      cases source with
      | nil => rfl
      | cons term rest => simp [matchSources, matchArgsWith] at matched
  | cons pattern patterns ih =>
      cases source with
      | nil => simp [matchSources, matchArgsWith] at matched
      | cons term rest =>
          simp only [matchSources, matchArgsWith] at matched
          obtain ⟨head, _, tailMatch⟩ := List.mem_flatMap.mp matched
          obtain ⟨tail, member, _⟩ := List.mem_filterMap.mp tailMatch
          exact congrArg Nat.succ (ih member)

theorem JoinWitness.arities {relEnv : RelationEnv} {language : LanguageDef}
    {declaration : MultiRewriteDecl} {sources targets : List Pattern}
    (witness : JoinWitness relEnv language declaration sources targets) :
    sources.length = declaration.sources.length ∧
      targets.length = declaration.targets.length := by
  exact ⟨witness.source_eq.length.trans (matchSources_length witness.matched).symm,
    witness.target_eq.length.symm.trans (List.length_map ..)⟩

/-- Authored arity restriction, decidable without testing semantic steps. -/
def NoUnaryDeclarations (library : AdmittedLibrary) : Prop :=
  ∀ declaration ∈ library.1,
    declaration.sources.length ≠ 1 ∨ declaration.targets.length ≠ 1

theorem singleton_rewrite_iff (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (nonUnary : NoUnaryDeclarations library)
    (source target : Pattern) :
    (schematicTheoryUsing relEnv language library).rewrites [source] [target] ↔
      langSemanticReducesUsing relEnv language source target := by
  constructor
  · rintro (unary | ⟨declaration, member, ⟨join⟩⟩)
    · exact ofUnary_step.mp unary
    · obtain ⟨sourceArity, targetArity⟩ := join.arities
      rcases nonUnary declaration member with notSource | notTarget
      · exact (notSource sourceArity.symm).elim
      · exact (notTarget targetArity.symm).elim
  · intro step
    exact Or.inl (ofUnary_step.mpr step)

/-- On equation-free presentations, the unary fragment is precisely the
existing finite-depth executable matcher, including its premise checks. -/
theorem singleton_rewrite_iff_exec (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (nonUnary : NoUnaryDeclarations library)
    (equationFree : language.isEquationFree = true) (source target : Pattern) :
    (schematicTheoryUsing relEnv language library).rewrites [source] [target] ↔
      langReducesExecUsing relEnv language source target :=
  (singleton_rewrite_iff relEnv language library nonUnary source target).trans
    ((langSemanticReducesUsing_iff_langReducesUsing_of_equation_free
      relEnv equationFree source target).trans
        (langReducesUsing_iff_execUsing relEnv language source target))

/-- Window closure introduces no new singleton behavior under the same
arity restriction. Empty and proper subwindows cannot hide an atomic join. -/
theorem singleton_step_iff (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (nonUnary : NoUnaryDeclarations library)
    (source target : Pattern) :
    (schematicGSLTUsing relEnv language library).Step [source] [target] ↔
      langSemanticReducesUsing relEnv language source target := by
  constructor
  · rintro ⟨window⟩
    have sourceLength := window.source_eq.length
    have targetLength := window.target_eq.length
    change 1 = (window.pre ++ window.sources ++ window.suf).length at sourceLength
    change (window.pre ++ window.targets ++ window.suf).length = 1 at targetLength
    simp only [List.length_append] at sourceLength targetLength
    have arities : window.sources.length = 1 ∧ window.targets.length = 1 := by
      rcases window.rule with unary | ⟨declaration, member, ⟨join⟩⟩
      · exact ofUnary_only_singletons unary
      · have joinArities := join.arities
        have nonUnaryJoin := nonUnary declaration member
        have positive : 0 < window.sources.length ∨ 0 < window.targets.length :=
          window.real.imp List.length_pos_iff.mpr List.length_pos_iff.mpr
        omega
    have preEmpty : window.pre = [] := List.length_eq_zero_iff.mp (by omega)
    have sufEmpty : window.suf = [] := List.length_eq_zero_iff.mp (by omega)
    obtain ⟨redex, sourceWindow⟩ := List.length_eq_one_iff.mp arities.1
    obtain ⟨contractum, targetWindow⟩ := List.length_eq_one_iff.mp arities.2
    have sourceEq : (langGSLTUsing relEnv language).Equiv source redex := by
      have same := window.source_eq
      simp only [preEmpty, sufEmpty, sourceWindow, List.nil_append, List.append_nil] at same
      cases same with
      | cons head _ => exact head
    have targetEq : (langGSLTUsing relEnv language).Equiv contractum target := by
      have same := window.target_eq
      simp only [preEmpty, sufEmpty, targetWindow, List.nil_append, List.append_nil] at same
      cases same with
      | cons head _ => exact head
    have primitive : langSemanticReducesUsing relEnv language redex contractum :=
      (singleton_rewrite_iff relEnv language library nonUnary _ _).mp
        (by simpa only [sourceWindow, targetWindow] using window.rule)
    obtain ⟨result, step, equivalent⟩ :=
      (langGSLTUsing relEnv language).rewrites_resp_left
        ((langGSLTUsing relEnv language).equations.symm sourceEq) primitive
    exact (langGSLTUsing relEnv language).rewrites_resp_right step
      ((langGSLTUsing relEnv language).equations.trans
        ((langGSLTUsing relEnv language).equations.symm equivalent) targetEq)
  · intro step
    exact MultiRewriteTheory.step_of_unary _
      ((singleton_rewrite_iff relEnv language library nonUnary _ _).mpr step)

/-- For general equations the execution certificate includes representatives.
This is not an algorithm for finding those representatives. -/
theorem singleton_step_iff_exec_representatives
    (relEnv : RelationEnv) (language : LanguageDef)
    (library : AdmittedLibrary) (nonUnary : NoUnaryDeclarations library)
    (source target : Pattern) :
    (schematicGSLTUsing relEnv language library).Step [source] [target] ↔
      ∃ redex contractum,
        (langGSLTUsing relEnv language).Equiv source redex ∧
        langReducesExecUsing relEnv language redex contractum ∧
        (langGSLTUsing relEnv language).Equiv contractum target := by
  rw [singleton_step_iff relEnv language library nonUnary]
  change StepModuloEquations (engineBasePremises relEnv) language source target ↔ _
  constructor
  · rintro ⟨redex, contractum, sourceEq, step, targetEq⟩
    exact ⟨redex, contractum, sourceEq,
      langReducesUsing_to_exec relEnv language step, targetEq⟩
  · rintro ⟨redex, contractum, sourceEq, step, targetEq⟩
    exact ⟨redex, contractum, sourceEq,
      exec_to_langReducesUsing relEnv language step, targetEq⟩

theorem pointwise_eq_of_equationFree (relEnv : RelationEnv)
    {language : LanguageDef} (equationFree : language.isEquationFree = true)
    {sources targets : List Pattern}
    (equiv : Pointwise (langGSLTUsing relEnv language).Equiv sources targets) :
    sources = targets := by
  induction equiv with
  | nil => rfl
  | cons head tail ih =>
      exact congrArg₂ List.cons
        ((gsltModuloEquations_equiv_iff_eq_of_no_generators equationFree _ _).mp head) ih

theorem firesModulo_iff_of_equationFree (relEnv : RelationEnv)
    {language : LanguageDef} (equationFree : language.isEquationFree = true)
    (declaration : MultiRewriteDecl) (sources targets : List Pattern) :
    firesModulo relEnv language declaration sources targets ↔
      fires declaration sources targets := by
  constructor
  · rintro ⟨join⟩
    have sourceEq := pointwise_eq_of_equationFree relEnv equationFree join.source_eq
    exact ⟨join.bindings, by simpa only [sourceEq] using join.matched,
      (pointwise_eq_of_equationFree relEnv equationFree join.target_eq).symm⟩
  · exact fires_to_modulo relEnv language

/-! ## Matcher facts used by the canaries

`matchArgsWith` is well-founded, so it does not reduce by `rfl`.  `simp`
still unfolds one equation. -/

theorem apply_bound_fvar (name : String) (value : Pattern) :
    applyBindings [(name, value)] (.fvar name) = value := by
  simp [applyBindings, List.find?, BEq.beq]

theorem matchArgs_two_same_agree (name : String) (term : Pattern) :
    matchSources [.fvar name, .fvar name] [term, term] = [[(name, term)]] := by
  simp [matchSources, matchArgsWith, matchPatternWith, List.flatMap,
    List.filterMap, mergeBindingsWith, List.foldlM, syntacticEq]

theorem matchArgs_two_same_disagree
    (name : String) {left right : Pattern} (hne : left ≠ right) :
    matchSources [.fvar name, .fvar name] [left, right] = [] := by
  simp [matchSources, matchArgsWith, matchPatternWith, List.flatMap,
    List.filterMap, mergeBindingsWith, List.foldlM, syntacticEq]
  split_ifs with h
  · exact (hne h).elim
  · rfl

/-! ## Join declaration: two sources, one name -/

private def exampleLanguage : LanguageDef :=
  LanguageDef.empty "schematic-join-example"

private def joinDecl : MultiRewriteDecl :=
  { name := "joinN"
    sources := [.fvar "n", .fvar "n"]
    targets := [.fvar "n"] }

private def joinLibrary : AdmittedLibrary :=
  ⟨[joinDecl], by decide⟩

private def chA : Pattern := .apply "A" []
private def chB : Pattern := .apply "B" []

private theorem chA_ne_chB : chA ≠ chB := by
  decide

theorem join_fires_literal :
    fires joinDecl [.fvar "n", .fvar "n"] [.fvar "n"] := by
  refine ⟨[("n", .fvar "n")], ?_, ?_⟩
  · simp [joinDecl, matchArgs_two_same_agree]
  · simp [instantiate, joinDecl, apply_bound_fvar]

theorem join_fires_instantiated :
    fires joinDecl [chA, chA] [chA] := by
  refine ⟨[("n", chA)], ?_, ?_⟩
  · simp [joinDecl, matchArgs_two_same_agree]
  · simp [instantiate, joinDecl, apply_bound_fvar]

theorem join_refuses_mismatch :
    ¬ fires joinDecl [chA, chB] [chA] := by
  intro ⟨σ, hmem, _⟩
  simp [joinDecl] at hmem
  rw [matchArgs_two_same_disagree "n" chA_ne_chB] at hmem
  cases hmem

/-- The literal denotation still requires the source list to be the
pattern list itself. Instantiated windows are extra data. -/
theorem literal_misses_instantiation :
    ¬ (denotedTheory exampleLanguage joinLibrary).rewrites [chA, chA] [chA] := by
  intro h
  rcases h with ⟨rule, hrule, hs, _⟩ | ⟨decl, hdecl, hs, _⟩
  · cases hrule
  · have hmem : decl = joinDecl := by
      cases hdecl with
      | head => rfl
      | tail _ h => cases h
    subst hmem
    cases hs

theorem schematic_has_instantiation :
    (schematicTheory exampleLanguage joinLibrary).rewrites [chA, chA] [chA] :=
  Or.inr ⟨joinDecl, List.Mem.head [],
    fires_to_modulo _ _ join_fires_instantiated⟩

theorem schematic_step_instantiated :
    (schematicGSLT exampleLanguage joinLibrary).Step [chA, chA] [chA] :=
  MultiRewriteTheory.step_of_binary
    (schematicTheory exampleLanguage joinLibrary)
    schematic_has_instantiation

theorem schematic_refuses_mismatch :
    ¬ (schematicTheory exampleLanguage joinLibrary).rewrites [chA, chB] [chA] := by
  intro h
  rcases h with unary | ⟨decl, hdecl, hfires⟩
  · have impossible := (ofUnary_only_singletons unary).1
    cases impossible
  · have hmem : decl = joinDecl := by
      cases hdecl with
      | head => rfl
      | tail _ h => cases h
    subst hmem
    exact join_refuses_mismatch
      ((firesModulo_iff_of_equationFree _ (by decide) _ _ _).mp hfires)

/-- Bag search is the commutative join; it is not rho COMM. -/
def schematicBag (declaration : MultiRewriteDecl)
    (sources targets : List Pattern) : Prop :=
  ∃ σ ∈ joinBag declaration.sources sources,
    targets = instantiate σ declaration.targets

/-! ## Canonical unary and atomicity controls -/

private def noLibrary : AdmittedLibrary := ⟨[], by decide⟩

private theorem noLibrary_nonUnary : NoUnaryDeclarations noLibrary := by
  intro declaration member
  cases member

private theorem emptyLanguage_no_step (source target : Pattern) :
    ¬ langSemanticReducesUsing RelationEnv.empty exampleLanguage source target := by
  rw [langSemanticReducesUsing_iff_langReducesUsing_of_equation_free _ (by decide)]
  rintro ⟨fuel, step⟩
  cases step with
  | rule member _ _ _ => cases member

/-- A join cannot consume just one of its required two participants,
including when the document-window machinery is used. -/
theorem join_cannot_partially_consume (targets : List Pattern) :
    ¬ (schematicGSLT exampleLanguage joinLibrary).Step [chA] targets := by
  rintro ⟨window⟩
  rcases window.rule with unary | ⟨declaration, member, ⟨join⟩⟩
  · obtain ⟨source, target, _, _, step⟩ := unary
    exact emptyLanguage_no_step source target step
  · have declEq : declaration = joinDecl := by simpa [joinLibrary] using member
    have arity := join.arities.1
    rw [declEq] at arity
    change window.sources.length = 2 at arity
    have length := window.source_eq.length
    change 1 = (window.pre ++ window.sources ++ window.suf).length at length
    simp only [List.length_append] at length
    omega

private def guardedRule : RewriteRule := {
  name := "unboxWhenPermitted"
  typeContext := [("x", .base "Term")]
  premises := [.relationQuery "permit" []]
  left := .apply "Box" [.fvar "x"]
  right := .fvar "x"
}

private def guardedLanguage : LanguageDef := {
  name := "canonical-unary-controls"
  types := [{ name := "Term" }]
  terms := [
    { label := "Box", category := "Term", params := [.simple "body" (.base "Term")],
      syntaxPattern := [.terminal "Box", .nonTerminal "body"] },
    { label := "A", category := "Term", params := [], syntaxPattern := [.terminal "A"] },
    { label := "B", category := "Term", params := [], syntaxPattern := [.terminal "B"] }]
  equations := []
  rewrites := [guardedRule]
}

private def permitted : RelationEnv where
  tuples := fun relation _ => if relation = "permit" then [[]] else []

private theorem guardedMatch :
    [("x", chA)] ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        guardedLanguage guardedRule (.apply "Box" [chA]) := by
  simp [guardedRule, matchPattern, matchArgs, mergeBindings]

private theorem guardedPrimitive :
    langReducesUsing permitted guardedLanguage (.apply "Box" [chA]) chA := by
  refine ⟨1, .rule (finalBindings := [("x", chA)])
    (by simp [guardedLanguage]) guardedMatch
    (.cons (.relationQuery ?_) (.nil _)) ?_⟩
  · simp [engineBasePremises, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, permitted, matchRelationArgs, mergeBindings,
      List.foldlM]
  · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      guardedRule, applyRuleBindings, apply_bound_fvar]

/-- A real instantiation and a successful external premise flow through the
same singleton semantics as OSLF. -/
theorem instantiated_unary_with_premise :
    (schematicGSLTUsing permitted guardedLanguage noLibrary).Step
      [.apply "Box" [chA]] [chA] :=
  (singleton_step_iff _ _ _ noLibrary_nonUnary _ _).mpr
    (langReducesUsing_to_semantic _ _ guardedPrimitive)

/-- The same authored rule is unavailable when its premise has no evidence. -/
theorem false_premise_blocks_unary :
    ¬ (schematicGSLTUsing RelationEnv.empty guardedLanguage noLibrary).Step
      [.apply "Box" [chA]] [chA] := by
  rw [singleton_step_iff _ _ _ noLibrary_nonUnary,
    langSemanticReducesUsing_iff_langReducesUsing_of_equation_free _ (by decide)]
  rintro ⟨fuel, step⟩
  cases step with
  | @rule fuel source target rule initial final member matched premises result =>
      have ruleEq : rule = guardedRule := by simpa [guardedLanguage] using member
      subst rule
      cases premises with
      | cons premise rest =>
          cases premise with
          | relationQuery impossible =>
              simp [engineBasePremises, premiseStepWithEnv, relationQueryStep,
                builtinRelationTuples, RelationEnv.empty] at impossible

private def equationAB : Equation := {
  name := "AB", typeContext := [], premises := [], left := chA, right := chB
}

private def equationLanguage : LanguageDef :=
  { guardedLanguage with equations := [equationAB] }

private theorem a_equiv_b :
    (langGSLTUsing permitted equationLanguage).Equiv chA chB := by
  apply Relation.EqvGen.rel
  apply EquationContextStep.inContext .hole
  apply Or.inl
  refine ⟨0, EquationInstanceAt.forward (equation := equationAB)
    (initialBindings := []) (finalBindings := [])
    (List.Mem.head []) ?_ (.nil []) ?_⟩
  · simp [equationAB, chA, matchPattern, matchArgs]
  · simp [equationAB, chB, applyBindings]

/-- A target representative licensed by an authored equation is observable
even though the primitive rule produces A, not B. -/
theorem equation_equivalent_target :
    (schematicGSLTUsing permitted equationLanguage noLibrary).Step
      [.apply "Box" [chA]] [chB] := by
  apply (singleton_step_iff _ _ _ noLibrary_nonUnary _ _).mpr
  refine ⟨.apply "Box" [chA], chA, Relation.EqvGen.refl _, ?_, a_equiv_b⟩
  refine ⟨1, .rule (rule := guardedRule)
    (initialBindings := [("x", chA)]) (finalBindings := [("x", chA)])
    (by simp [equationLanguage, guardedLanguage]) ?_
    (.cons (.relationQuery ?_) (.nil _)) ?_⟩
  · exact guardedMatch
  · simp [engineBasePremises, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, permitted, matchRelationArgs, mergeBindings,
      List.foldlM]
  · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      guardedRule, applyRuleBindings, apply_bound_fvar]

/-- The equation may also expose a different source representative beneath
a constructor, without being an extra computational step. -/
theorem equation_equivalent_source :
    (schematicGSLTUsing permitted equationLanguage noLibrary).Step
      [.apply "Box" [chB]] [chB] := by
  have sourceEq : (langGSLTUsing permitted equationLanguage).Equiv
      (.apply "Box" [chA]) (.apply "Box" [chB]) :=
    equationEquiv_fill (.apply "Box" [] .hole []) a_equiv_b
  have step := (singleton_step_iff _ _ _ noLibrary_nonUnary _ _).mp
    equation_equivalent_target
  obtain ⟨result, moved, resultEq⟩ :=
    (langGSLTUsing permitted equationLanguage).rewrites_resp_left sourceEq step
  apply (singleton_step_iff _ _ _ noLibrary_nonUnary _ _).mpr
  exact (langGSLTUsing permitted equationLanguage).rewrites_resp_right moved
    ((langGSLTUsing permitted equationLanguage).equations.symm resultEq)

#print axioms join_fires_instantiated
#print axioms join_refuses_mismatch
#print axioms literal_misses_instantiation
#print axioms schematic_has_instantiation
#print axioms schematic_step_instantiated
#print axioms schematic_refuses_mismatch
#print axioms singleton_step_iff
#print axioms singleton_rewrite_iff_exec
#print axioms singleton_step_iff_exec_representatives
#print axioms join_cannot_partially_consume
#print axioms instantiated_unary_with_premise
#print axioms false_premise_blocks_unary
#print axioms equation_equivalent_target
#print axioms equation_equivalent_source
#print axioms retainedEvent_iff_step
#print axioms join_witnesses_distinct

end Mettapedia.GSLT.LanguageDef.MultiRewriteSchematic
