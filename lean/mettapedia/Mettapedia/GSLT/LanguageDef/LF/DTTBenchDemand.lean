/-
# DTTBench product-rule demand

This module analyzes the frozen Lean-owned DTTBench statements without replaying
any witness.  It models the signature-free lambda-Pi fragment used by those
statements, records every product rule needed during formation, and checks the
result against the source-extracted profiles in `Profiles.lean`.
-/

import Mettapedia.GSLT.LanguageDef.LF.Profiles
import Mettapedia.GSLT.LanguageDef.Pure.BetaEtaConversion
import Mettapedia.GSLT.LanguageDef.Pure.DTTBench31

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureDTTBench31

/-- An inferred object type or a PTS universe result. -/
inductive Inferred where
  | term : Pure.Expr → Inferred
  | universe : Srt → Inferred
  deriving DecidableEq, Repr

def productResult? (profile : Profile) (domain codomain : Srt) : Option Srt :=
  (profile.products.find? fun rule =>
    rule.domain = domain && rule.codomain = codomain).map ProductRule.result

def matchesExpected : Inferred → Pure.Expr → Bool
  | .term actual, expected => PureBetaEta.convBool actual expected
  | .universe _, _ => false

mutual
/-- Executable profile-parametric inference for the closed DTTBench statement fragment. -/
def infer : Nat → Profile → Pure.Ctx → Pure.Expr → Option Inferred
  | 0, _, _, _ => none
  | _fuel + 1, _, _, .sort => some (.universe .kind)
  | _fuel + 1, _, context, .bvar index =>
      (Pure.ctxLookup context index).map .term
  | fuel + 1, profile, context, .pi domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodySort ← inferSort fuel profile (domain :: context) body
      let resultSort ← productResult? profile domainSort bodySort
      pure (.universe resultSort)
  | fuel + 1, profile, context, .lam domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodyType ← infer fuel profile (domain :: context) body
      match bodyType with
      | .universe _ => none
      | .term bodyType =>
          let bodySort ← inferSort fuel profile (domain :: context) bodyType
          let _ ← productResult? profile domainSort bodySort
          pure (.term (.pi domain bodyType))
  | fuel + 1, profile, context, .app fn argument => do
      let fnType ← infer fuel profile context fn
      match fnType with
      | .universe _ => none
      | .term fnType =>
          match PureBetaEta.normalForm fnType with
          | .pi domain body =>
              let argumentType ← infer fuel profile context argument
              if matchesExpected argumentType domain then
                pure (.term (Pure.Expr.subst0 argument body))
              else none
          | _ => none

/-- Sort synthesized for a type/kind expression. -/
def inferSort : Nat → Profile → Pure.Ctx → Pure.Expr → Option Srt
  | 0, _, _, _ => none
  | fuel + 1, profile, context, expression => do
      match ← infer fuel profile context expression with
      | .universe sort => pure sort
      | .term type =>
          if PureBetaEta.convBool type .sort then pure .type else none
end

mutual
/-- Collect every product rule exercised by explicit products and lambda types. -/
def collect : Nat → Profile → Pure.Ctx → Pure.Expr → Option (List ProductRule)
  | 0, _, _, _ => none
  | _fuel + 1, _, _, .sort => some []
  | _fuel + 1, _, _, .bvar _ => some []
  | fuel + 1, profile, context, .pi domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodySort ← inferSort fuel profile (domain :: context) body
      let resultSort ← productResult? profile domainSort bodySort
      let domainRules ← collect fuel profile context domain
      let bodyRules ← collect fuel profile (domain :: context) body
      pure (⟨domainSort, bodySort, resultSort⟩ :: domainRules ++ bodyRules)
  | fuel + 1, profile, context, .lam domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodyInferred ← infer fuel profile (domain :: context) body
      let bodyType ← match bodyInferred with
        | .term type => some type
        | .universe _ => none
      let bodySort ← inferSort fuel profile (domain :: context) bodyType
      let resultSort ← productResult? profile domainSort bodySort
      let domainRules ← collect fuel profile context domain
      let bodyRules ← collect fuel profile (domain :: context) body
      pure (⟨domainSort, bodySort, resultSort⟩ :: domainRules ++ bodyRules)
  | fuel + 1, profile, context, .app fn argument => do
      let fnRules ← collect fuel profile context fn
      let argumentRules ← collect fuel profile context argument
      pure (fnRules ++ argumentRules)
end

def analysisFuel : Nat := 4096

def demand? (profile : Profile) (goal : Pure.Expr) : Option (List ProductRule) := do
  let _ ← inferSort analysisFuel profile [] goal
  collect analysisFuel profile [] goal

def statementWithin (profile : Profile) (statement : Statement) : Bool :=
  (demand? profile statement.goal).isSome

structure DemandRow where
  name : String
  resultSort : Option Srt
  rules : List ProductRule
  deriving DecidableEq, Repr

def demandRow (profile : Profile) (statement : Statement) : DemandRow :=
  { name := statement.name
    resultSort := inferSort analysisFuel profile [] statement.goal
    rules := (demand? profile statement.goal).getD [] }

def indexedRows : List DemandRow := statements.map (demandRow indexed)

def allWithinIndexed : Bool := statements.all (statementWithin indexed)

def allWithinBasic : Bool := statements.all (statementWithin basic)

/-- The two rows selected before the native T1 pilot. -/
def pilotNames : List String := ["Eq_congrFun", "sSup_inter_le"]

def pilotRows : List DemandRow :=
  indexedRows.filter fun row => row.name ∈ pilotNames

def allDemandRules : List ProductRule :=
  (indexedRows.flatMap DemandRow.rules).eraseDups

/-! ## Closed-corpus demand theorems

These propositions reduce in the Lean kernel from the 31 frozen statement values.
They concern statement formation only: no proof witness and no `Pure` acceptance
judgment is replayed here.
-/

/-- The analysis visits exactly the 31 frozen DTTBench statements. -/
theorem indexedRows_length : indexedRows.length = 31 := by
  simp [indexedRows, statements_length]

/-- Every frozen statement is formable at the indexed profile. -/
theorem allWithinIndexed_eq_true : allWithinIndexed = true := by
  rfl

/-- Statement-level form of the indexed coverage result: membership in the
frozen 31-row collection is enough to recover the row's successful formation
check.  Future runtime parity fixtures consume this theorem one row at a time. -/
theorem statementWithin_indexed_of_mem {statement : Statement}
    (hstatement : statement ∈ statements) :
    statementWithin indexed statement = true :=
  (List.all_eq_true.mp allWithinIndexed_eq_true) statement hstatement

/-- The basic profile is too small for the frozen statement collection. -/
theorem allWithinBasic_eq_false : allWithinBasic = false := by
  rfl

/-- The corpus exercises every indexed product rule, including both added rules. -/
theorem allDemandRules_eq_indexed :
    allDemandRules =
      [kindKindKind, typeKindKind, kindTypeKind, typeTypeType] := by
  set_option maxRecDepth 100000 in
    rfl

/-- The `Eq_congrFun` statement requires the Type-parameter product. -/
theorem Eq_congrFun_requires_kindKindKind :
    kindKindKind ∈
      (demand? indexed goal_Eq_Eq_congrFun).getD [] := by
  decide

/-- The basic profile cannot form the `Eq_congrFun` statement. -/
theorem Eq_congrFun_not_within_basic :
    demand? basic goal_Eq_Eq_congrFun = none := by
  rfl

/-- The `sSup_inter_le` statement also requires the Type-parameter product. -/
theorem sSup_inter_le_requires_kindKindKind :
    kindKindKind ∈
      (demand? indexed goal_Leq_sSup_inter_le).getD [] := by
  decide

/-- The basic profile cannot form the `sSup_inter_le` statement. -/
theorem sSup_inter_le_not_within_basic :
    demand? basic goal_Leq_sSup_inter_le = none := by
  rfl

/-- A profile contains the DTTBench point when it contains its sort axiom and
every product rule computed from the frozen statement collection. -/
def ContainsDTTBench (profile : Profile) : Prop :=
  profile.sortAxiom .type = some .kind ∧
    ∀ rule, rule ∈ allDemandRules → rule ∈ profile.products

/-- The source-extracted indexed profile contains the DTTBench statement point. -/
theorem indexed_contains_DTTBench : ContainsDTTBench indexed := by
  constructor
  · rfl
  · intro rule hrule
    rw [allDemandRules_eq_indexed] at hrule
    simp [indexed] at hrule ⊢
    aesop

/-- The source-extracted basic profile does not contain the DTTBench point. -/
theorem basic_does_not_contain_DTTBench : ¬ ContainsDTTBench basic := by
  intro hcontains
  have hdemand : kindKindKind ∈ allDemandRules := by
    rw [allDemandRules_eq_indexed]
    simp
  have hbasic := hcontains.2 kindKindKind hdemand
  simp [basic, kindKindKind, typeTypeType, typeKindKind] at hbasic

/-- T2 minimality crown: every profile containing the frozen DTTBench demand
subsumes the indexed profile. -/
theorem indexed_minimal_for_DTTBench {profile : Profile}
    (hcontains : ContainsDTTBench profile) : indexed ⊑ profile := by
  constructor
  · intro source target haxiom
    cases source <;> simp [indexed, typeAxiom] at haxiom
    · cases haxiom
      exact hcontains.1
  · intro rule hrule
    apply hcontains.2 rule
    rw [allDemandRules_eq_indexed]
    simp [indexed] at hrule ⊢
    aesop

#print axioms allWithinIndexed_eq_true
#print axioms statementWithin_indexed_of_mem
#print axioms Eq_congrFun_requires_kindKindKind
#print axioms sSup_inter_le_requires_kindKindKind
#print axioms indexed_minimal_for_DTTBench

end Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand
