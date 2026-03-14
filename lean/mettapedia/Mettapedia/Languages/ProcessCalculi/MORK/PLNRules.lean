import Mettapedia.Languages.ProcessCalculi.MORK.CollectionBridge

/-!
# PLN Inference Rules as MORK Source Programs

Instantiates concrete PLN inference rules (transitivity, modus ponens) as
MeTTaIL `RewriteRule`s with `relationQuery` premises, proves they fall within
MORK's translatable fragment, and demonstrates the multi-premise bridge.

## Design

Each PLN rule is expressed as a MeTTaIL `RewriteRule` where:
- The LHS is `.fvar "query"` (matches any query atom)
- The RHS produces the inferred atom (e.g., `Inh(A,C)`)
- Premises are `relationQuery` lookups (e.g., lookup `Inh(A,B)` and `Inh(B,C)`)

The `allPremisesTranslatable` and `morkTranslatable` properties are proven
by `decide`, confirming these rules fall within MORK's executable fragment.

## GSLT routing

The `plnPremiseLanguageDef` packages these rules into a MeTTaIL `LanguageDef`
that MORK can execute via `rewriteRuleToSourceExecRule`. When combined with
the multi-premise bridge (`declReducesWithPremises_multi_implies_mork_fireSourceRule`),
this gives concrete GSLT routing witnesses: PLN inference steps that MORK
can execute as work-queue firings.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.PLNRules

open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## MeTTaIL type aliases (same as MeTTaILBridge.lean) -/

private abbrev ILP     := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILDL    := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
private abbrev ILPremise := Mettapedia.OSLF.MeTTaIL.Syntax.Premise

/-! ## Concrete PLN inference rules -/

/-- PLN Inheritance Transitivity: `(Inh A B), (Inh B C) ⊢ (Inh A C)`

    This is the categorical syllogism: if A inherits from B and B inherits
    from C, then A inherits from C. The shared variable B provides the
    deductive link. -/
def plnTransitivityRule : ILRRule where
  name := "pln_inh_transitivity"
  typeContext := []
  premises := [
    .relationQuery "Inh" [.fvar "A", .fvar "B"],
    .relationQuery "Inh" [.fvar "B", .fvar "C"]
  ]
  left := .fvar "query"
  right := .apply "Inh" [.fvar "A", .fvar "C"]

/-- PLN Modus Ponens: `(Impl P Q), (Eval P) ⊢ (Eval Q)`

    If P implies Q and P holds, then Q holds. Uses `Impl` for implication
    and `Eval` for evaluation/truth assertions. -/
def plnModusPonensRule : ILRRule where
  name := "pln_modus_ponens"
  typeContext := []
  premises := [
    .relationQuery "Impl" [.fvar "P", .fvar "Q"],
    .relationQuery "Eval" [.fvar "P"]
  ]
  left := .fvar "query"
  right := .apply "Eval" [.fvar "Q"]

/-- PLN Inheritance Symmetry: `(Inh A B) ⊢ (Sim A B)`

    Single-premise rule: inheritance implies similarity (with
    appropriate truth-value adjustment, omitted in the structural rule). -/
def plnSimRule : ILRRule where
  name := "pln_inh_to_sim"
  typeContext := []
  premises := [
    .relationQuery "Inh" [.fvar "A", .fvar "B"]
  ]
  left := .fvar "query"
  right := .apply "Sim" [.fvar "A", .fvar "B"]

/-- PLN Guarded Transitivity: `(Inh A B), (Inh B C), A # C ⊢ (Inh A C)`

    Like `plnTransitivityRule` but with a freshness guard: variable A must not
    occur free in C. This prevents trivial self-inheritance derivations where
    A = C. Demonstrates the `SourceGuard` freshness mechanism. -/
def plnGuardedTransitivityRule : ILRRule where
  name := "pln_guarded_inh_transitivity"
  typeContext := []
  premises := [
    .relationQuery "Inh" [.fvar "A", .fvar "B"],
    .relationQuery "Inh" [.fvar "B", .fvar "C"],
    .freshness { varName := "A", term := .fvar "C" }
  ]
  left := .fvar "query"
  right := .apply "Inh" [.fvar "A", .fvar "C"]

/-! ## Translatability proofs -/

/-- Transitivity rule RHS is MORK-translatable. -/
theorem plnTransitivityRule_rhs_translatable :
    morkTranslatable plnTransitivityRule.right = true := by decide

/-- Transitivity rule premises are all translatable to source factors. -/
theorem plnTransitivityRule_premises_translatable :
    allPremisesTranslatable plnTransitivityRule.premises = true := by decide

/-- Modus ponens rule RHS is MORK-translatable. -/
theorem plnModusPonensRule_rhs_translatable :
    morkTranslatable plnModusPonensRule.right = true := by decide

/-- Modus ponens rule premises are all translatable. -/
theorem plnModusPonensRule_premises_translatable :
    allPremisesTranslatable plnModusPonensRule.premises = true := by decide

/-- Similarity rule RHS is MORK-translatable. -/
theorem plnSimRule_rhs_translatable :
    morkTranslatable plnSimRule.right = true := by decide

/-- Similarity rule premises are all translatable. -/
theorem plnSimRule_premises_translatable :
    allPremisesTranslatable plnSimRule.premises = true := by decide

/-- Guarded transitivity rule RHS is MORK-translatable. -/
theorem plnGuardedTransitivityRule_rhs_translatable :
    morkTranslatable plnGuardedTransitivityRule.right = true := by decide

/-- Guarded transitivity rule premises are translatable under the extended
    predicate (accepts both `relationQuery` and `freshness` premises). -/
theorem plnGuardedTransitivityRule_premises_translatable_ext :
    allPremisesTranslatableExt plnGuardedTransitivityRule.premises = true := by decide

/-- The guarded transitivity rule is NOT translatable under the strict
    `allPremisesTranslatable` (which only accepts `relationQuery`), confirming
    the freshness premise is properly classified. -/
theorem plnGuardedTransitivityRule_not_strict_translatable :
    allPremisesTranslatable plnGuardedTransitivityRule.premises = false := by decide

/-! ## PLN Language Definition -/

/-- PLN inference rules as a MeTTaIL language definition.
    All rules use `relationQuery` premises and `fvar` LHS patterns,
    falling within MORK's translatable fragment. -/
def plnPremiseLanguageDef : ILDL where
  name := "PLN_Premise_LanguageDef"
  types := ["Concept"]
  terms := []
  equations := []
  rewrites := [plnTransitivityRule, plnModusPonensRule, plnSimRule]

/-- Every rule in `plnPremiseLanguageDef` has `fvar` LHS. -/
theorem plnPremise_all_fvar_lhs :
    ∀ r ∈ plnPremiseLanguageDef.rewrites,
      ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x := by
  intro r hr
  simp [plnPremiseLanguageDef] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨"query", rfl⟩

/-- Every rule in `plnPremiseLanguageDef` has translatable RHS. -/
theorem plnPremise_all_rhs_translatable :
    ∀ r ∈ plnPremiseLanguageDef.rewrites, morkTranslatable r.right = true := by
  intro r hr
  simp [plnPremiseLanguageDef] at hr
  rcases hr with rfl | rfl | rfl
  · exact plnTransitivityRule_rhs_translatable
  · exact plnModusPonensRule_rhs_translatable
  · exact plnSimRule_rhs_translatable

/-- Every rule in `plnPremiseLanguageDef` has translatable premises. -/
theorem plnPremise_all_premises_translatable :
    ∀ r ∈ plnPremiseLanguageDef.rewrites,
      allPremisesTranslatable r.premises = true := by
  intro r hr
  simp [plnPremiseLanguageDef] at hr
  rcases hr with rfl | rfl | rfl
  · exact plnTransitivityRule_premises_translatable
  · exact plnModusPonensRule_premises_translatable
  · exact plnSimRule_premises_translatable

/-! ## MORK source rules -/

/-- Translated MORK source rules for PLN inference. -/
noncomputable def plnSourceExecRules : List SourceExecRule :=
  languageDefToSourceExecRules plnPremiseLanguageDef

/-- Every PLN rule translates to a source exec rule. -/
theorem plnSourceExecRules_length : plnSourceExecRules.length = 3 := by
  simp only [plnSourceExecRules, languageDefToSourceExecRules, plnPremiseLanguageDef,
    plnTransitivityRule, plnModusPonensRule, plnSimRule,
    allPremisesTranslatable, List.all_cons, List.all_nil, Bool.and_true,
    premiseToSourceFactor, Option.isSome, List.filterMap, ite_true,
    List.length_cons, List.length_nil]

/-! ## Additional PLN rules with varied premise shapes -/

/-- PLN Abduction: `(Inh A B), (Inh C B) ⊢ (Sim A C)`

    Shared variable B appears in different positions across premises.
    A and C are independent; similarity is derived from shared superclass. -/
def plnAbductionRule : ILRRule where
  name := "pln_abduction"
  typeContext := []
  premises := [
    .relationQuery "Inh" [.fvar "A", .fvar "B"],
    .relationQuery "Inh" [.fvar "C", .fvar "B"]
  ]
  left := .fvar "query"
  right := .apply "Sim" [.fvar "A", .fvar "C"]

/-- Abduction RHS is MORK-translatable. -/
theorem plnAbductionRule_rhs_translatable :
    morkTranslatable plnAbductionRule.right = true := by decide

/-- Abduction premises are all translatable. -/
theorem plnAbductionRule_premises_translatable :
    allPremisesTranslatable plnAbductionRule.premises = true := by decide

/-- PLN Double-Guarded Deduction: `(Inh A B), (Inh B C), B # A, B # C ⊢ (Inh A C)`

    Two freshness guards ensure the intermediate concept B is distinct from
    both endpoints. This exercises the multi-guard path. -/
def plnDoubleGuardedDeductionRule : ILRRule where
  name := "pln_double_guarded_deduction"
  typeContext := []
  premises := [
    .relationQuery "Inh" [.fvar "A", .fvar "B"],
    .relationQuery "Inh" [.fvar "B", .fvar "C"],
    .freshness { varName := "B", term := .fvar "A" },
    .freshness { varName := "B", term := .fvar "C" }
  ]
  left := .fvar "query"
  right := .apply "Inh" [.fvar "A", .fvar "C"]

/-- Double-guarded deduction RHS is MORK-translatable. -/
theorem plnDoubleGuardedDeductionRule_rhs_translatable :
    morkTranslatable plnDoubleGuardedDeductionRule.right = true := by decide

/-- Double-guarded deduction is NOT strict-translatable (has freshness premises). -/
theorem plnDoubleGuardedDeductionRule_not_strict :
    allPremisesTranslatable plnDoubleGuardedDeductionRule.premises = false := by decide

/-- Double-guarded deduction IS ext-translatable. -/
theorem plnDoubleGuardedDeductionRule_ext_translatable :
    allPremisesTranslatableExt plnDoubleGuardedDeductionRule.premises = true := by decide

/-! ## Guarded PLN Language Definition -/

/-- PLN rules with freshness guards as a MeTTaIL language definition.
    Includes both guarded and unguarded rules — uses the ext bridge. -/
def plnGuardedPremiseLanguageDef : ILDL where
  name := "PLN_Guarded_Premise_LanguageDef"
  types := ["Concept"]
  terms := []
  equations := []
  rewrites := [plnGuardedTransitivityRule, plnDoubleGuardedDeductionRule, plnAbductionRule]

/-- Every rule in `plnGuardedPremiseLanguageDef` has `fvar` LHS. -/
theorem plnGuardedPremise_all_fvar_lhs :
    ∀ r ∈ plnGuardedPremiseLanguageDef.rewrites,
      ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x := by
  intro r hr
  simp [plnGuardedPremiseLanguageDef] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨"query", rfl⟩

/-- Every rule in `plnGuardedPremiseLanguageDef` has translatable RHS. -/
theorem plnGuardedPremise_all_rhs_translatable :
    ∀ r ∈ plnGuardedPremiseLanguageDef.rewrites, morkTranslatable r.right = true := by
  intro r hr
  simp [plnGuardedPremiseLanguageDef] at hr
  rcases hr with rfl | rfl | rfl
  · exact plnGuardedTransitivityRule_rhs_translatable
  · exact plnDoubleGuardedDeductionRule_rhs_translatable
  · exact plnAbductionRule_rhs_translatable

/-- Every rule in `plnGuardedPremiseLanguageDef` has ext-translatable premises. -/
theorem plnGuardedPremise_all_premises_ext_translatable :
    ∀ r ∈ plnGuardedPremiseLanguageDef.rewrites,
      allPremisesTranslatableExt r.premises = true := by
  intro r hr
  simp [plnGuardedPremiseLanguageDef] at hr
  rcases hr with rfl | rfl | rfl
  · exact plnGuardedTransitivityRule_premises_translatable_ext
  · exact plnDoubleGuardedDeductionRule_ext_translatable
  · -- Abduction has only relationQuery premises → ext-translatable
    decide

/-! ## Concrete bridge instantiation

The multi-premise bridge theorem `declReducesWithPremises_multi_implies_mork_fireSourceRule`
applies to `plnPremiseLanguageDef` when:
1. The reduction uses a rule from `plnPremiseLanguageDef`
2. The result is ground
3. A `PremiseChain` witness exists in the workspace

For `congElem` reductions (collection element replacement), the bridge routes
through `collectionReplaceSourceRule` in the extended rule set. -/

/-- PLN multi-premise bridge: if `DeclReducesWithPremises` fires using a rule
    from `plnPremiseLanguageDef`, and a `PremiseChain` witness exists, then MORK's
    `fireSourceRule` produces the result. Handles both `topRule` and `congElem`
    via `languageDefToSourceExecRulesWithCongr`. -/
theorem pln_reduces_implies_mork_fireSourceRule
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (p q : ILP)
    (h : Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.DeclReducesWithPremises
        relEnv plnPremiseLanguageDef p q)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (hchain : ∀ r ∈ plnPremiseLanguageDef.rewrites,
        ∀ bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p,
        ∀ bs ∈ Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
            relEnv plnPremiseLanguageDef r.premises bs0,
        ∃ witnesses : List Atom,
          PremiseChain relEnv plnPremiseLanguageDef s bs0 r.premises witnesses bs ∧
          witnesses.Nodup ∧
          ∀ a ∈ witnesses, a ≠ morkPatternToAtom p) :
    ∃ r_source ∈ languageDefToSourceExecRulesWithCongr plnPremiseLanguageDef
        [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks s σ r_source.tmpl ∈ fireSourceRule s r_source :=
  declReducesWithPremises_multi_implies_mork_fireSourceRule
    relEnv plnPremiseLanguageDef p q h
    plnPremise_all_fvar_lhs plnPremise_all_rhs_translatable
    plnPremise_all_premises_translatable hground hground_coll s hp_in hchain

/-- PLN guarded ext bridge: if `DeclReducesWithPremises` fires using a rule
    from `plnGuardedPremiseLanguageDef`, and a `PremiseChain` witness exists with
    guard satisfaction, then MORK's `fireSourceRule` produces the result. Handles
    both `topRule` and `congElem` via `languageDefToSourceExecRulesExtWithCongr`. -/
theorem pln_guarded_reduces_implies_mork_fireSourceRule
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (p q : ILP)
    (h : Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.DeclReducesWithPremises
        relEnv plnGuardedPremiseLanguageDef p q)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (hchain : ∀ r ∈ plnGuardedPremiseLanguageDef.rewrites,
        ∀ bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p,
        ∀ bs ∈ Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
            relEnv plnGuardedPremiseLanguageDef r.premises bs0,
        ∃ witnesses : List Atom,
          PremiseChain relEnv plnGuardedPremiseLanguageDef s bs0 r.premises witnesses bs ∧
          witnesses.Nodup ∧
          (∀ a ∈ witnesses, a ≠ morkPatternToAtom p) ∧
          matchSourceGuards (bindingsToSubst bs)
            (premisesToSourceGuards r.premises) = true) :
    ∃ r_source ∈ languageDefToSourceExecRulesExtWithCongr plnGuardedPremiseLanguageDef
        [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks s σ r_source.tmpl ∈ fireSourceRule s r_source :=
  declReducesWithPremises_ext_implies_mork_fireSourceRule
    relEnv plnGuardedPremiseLanguageDef p q h
    plnGuardedPremise_all_fvar_lhs plnGuardedPremise_all_rhs_translatable
    plnGuardedPremise_all_premises_ext_translatable hground hground_coll s hp_in hchain

/-! ## Canary -/

section Canaries
#check @plnTransitivityRule
#check @plnModusPonensRule
#check @plnSimRule
#check @plnGuardedTransitivityRule
#check @plnAbductionRule
#check @plnDoubleGuardedDeductionRule
#check @plnPremiseLanguageDef
#check @plnGuardedPremiseLanguageDef
#check @plnSourceExecRules
#check @plnGuardedTransitivityRule_premises_translatable_ext
#check @plnGuardedTransitivityRule_not_strict_translatable
#check @plnDoubleGuardedDeductionRule_ext_translatable
#check @pln_reduces_implies_mork_fireSourceRule
#check @pln_guarded_reduces_implies_mork_fireSourceRule
end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK.PLNRules
