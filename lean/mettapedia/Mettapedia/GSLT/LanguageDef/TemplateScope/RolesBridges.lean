import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesCollection
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.HE.ScopeContract

/-!
# Binding by role: bridges and divergences

## The MeTTa scope contracts

`Languages/MeTTa/{HE,PeTTa}/ScopeContract.lean` classify each binding head by a
`ScopeKind` and list its binder, value and body positions.

* `contract_positions` — **bridge**: for `let`, `chain`, `match`, HE's `unify`
  and PeTTa's `|->`, the contract's binder, value and body positions are the
  pattern, value and body positions of the head's construct in `sigMeTTa`
  (`surface`).
* `contract_kind_role` — **bridge**: the contract's kinds determine the roles of
  `sigMeTTa`: `matchLike` heads are relations, `letLike` and `chainLike` heads
  shadowing arrows, `caseLike` heads testing arrows.
* **Divergence, relations.**  The contract's free-variable analysis
  (`orderedScopedFreeVars`) binds a `matchLike` binder's names in its body:
  `(match &self (p $x) $x)` has no free name, the two `$x` of sibling queries
  are two names, and in `(let $v (match &self (p $x) ok) ($v $x))` the second
  `$x` is free and distinct (values computed with `#eval`; the function is
  defined by well-founded recursion and does not reduce in the kernel).  The
  role model makes them one frame unknown (`sibling_relations_join`).  HE and
  PeTTa answer `((2 2))` and `((ok 1) (ok 2))` on these programs: their
  behaviour follows the role model, not their contract's reading.  The
  principle prefers the role model: the contract's reading is H1's, which needs
  an explicit `new` for every intended join.
* **Divergence, `let`.**  The contract binds only the pattern names not
  already bound (`boundNamesFromPattern`), the testing arrow's rule; so do HE
  and PeTTa (`(let $x 1 (let $x 2 $x))` has no answer).  The query model and the
  CeTTa draft's default make `let` a shadowing arrow (answer 2).  A
  free-variable analysis cannot see the difference (`shadow_test_same_scope`).

## GSLT binding signatures and MeTTaIL

* An OSLF/GSLT binding arity binds positions: each argument binds fresh
  variables of given sorts, which never refer outward.  In the role model that
  is a frame's parameter (`RSrc.par`, resolved lexically by spelling, as
  `parName` in the slot model), or a shadowing arrow when no crossing names are
  in force.  `bindingArityReading` reads every pattern construct that way:
  it is `sigOfRule ruleH0`, the CeTTa draft's default.
* **Divergence.**  A relation position has no binding-arity counterpart: its
  names refer to the frame.  The smallest separating program is the lookup
  probe: read as binders, `(lookup b)` answers `(1 2)`; as a relation, `(2)`
  (`arity_reading_separates`).
* MeTTaIL rewrite rules are frames: a firing instantiates the rule's
  metavariables afresh, and inside one firing a repeated metavariable on the
  left side or in a premise is one unknown — a relation join.
  `BindingAgreement.AgreeOn` (instantiation reads the bindings of the
  metavariables that occur and nothing else) is the rule-level form of
  `ann_congr`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Bridges

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Corpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCorpus
open Mettapedia.Languages.MeTTa.ScopeContract

/-- The surface positions of a construct, as `(binder, value, body)` lists. -/
def surface : MC → List ℕ × List ℕ × List ℕ
  | .letA => ([0], [1], [2])
  | .chainA => ([1], [0], [2])
  | .matchQ => ([1], [0], [2])
  | .unifyR => ([1], [0], [2])
  | _ => ([], [], [])

/-- The positions an entry of a contract declares. -/
def entryPositions (e : ScopeContractEntry) : List ℕ × List ℕ × List ℕ :=
  (e.binderPositions, e.valuePositions, e.bodyPositions)

/-- **Bridge: the contracts' positions are the constructs' positions.** -/
theorem contract_positions :
    entryPositions Mettapedia.Languages.MeTTa.HE.ScopeContract.letScopeEntry = surface .letA ∧
      entryPositions Mettapedia.Languages.MeTTa.HE.ScopeContract.chainScopeEntry = surface .chainA ∧
      entryPositions Mettapedia.Languages.MeTTa.HE.ScopeContract.matchScopeEntry = surface .matchQ ∧
      entryPositions Mettapedia.Languages.MeTTa.HE.ScopeContract.unifyScopeEntry = surface .unifyR ∧
      entryPositions Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.letScopeEntry = surface .letA ∧
      entryPositions Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.chainScopeEntry =
        surface .chainA ∧
      entryPositions Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.matchScopeEntry =
        surface .matchQ ∧
      Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.lambdaArrowScopeEntry.binderPositions = [0] ∧
      Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.lambdaArrowScopeEntry.bodyPositions = [1] := by
  decide

/-- The role a contract kind gives the pattern of its heads. -/
def kindRole : ScopeKind → Option PatRole
  | .matchLike => some .rel
  | .letLike => some (.arrow .shadow)
  | .chainLike => some (.arrow .shadow)
  | .caseLike => some (.arrow .test)
  | _ => none

/-- **Bridge: the contracts' kinds determine `sigMeTTa`'s roles.** -/
theorem contract_kind_role :
    kindRole Mettapedia.Languages.MeTTa.HE.ScopeContract.matchScopeEntry.scopeKind =
        some (sigMeTTa.role .matchQ) ∧
      kindRole Mettapedia.Languages.MeTTa.HE.ScopeContract.unifyScopeEntry.scopeKind =
        some (sigMeTTa.role .unifyR) ∧
      kindRole Mettapedia.Languages.MeTTa.HE.ScopeContract.letScopeEntry.scopeKind =
        some (sigMeTTa.role .letA) ∧
      kindRole Mettapedia.Languages.MeTTa.HE.ScopeContract.chainScopeEntry.scopeKind =
        some (sigMeTTa.role .chainA) ∧
      kindRole Mettapedia.Languages.MeTTa.HE.ScopeContract.caseScopeEntry.scopeKind =
        some (sigMeTTa.role .caseB) ∧
      kindRole Mettapedia.Languages.MeTTa.HE.ScopeContract.switchScopeEntry.scopeKind =
        some (sigMeTTa.role .switchB) ∧
      kindRole Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.matchScopeEntry.scopeKind =
        some (sigMeTTa.role .matchQ) ∧
      kindRole Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.caseScopeEntry.scopeKind =
        some (sigMeTTa.role .caseB) := by
  decide

/-- **A free-variable analysis cannot tell shadowing from testing.**  Both
arrows leave the same names in force for the body: the binders on the path and
the pattern's names. -/
theorem shadow_test_same_scope {C X : Type} [DecidableEq X] (B : List X) (p : RSrc C QSy X)
    (y : X) : y ∈ patB B p none ↔ y ∈ B ∨ y ∈ p.patNames := by
  simp [patB]

/-! ## The binding-arity reading -/

/-- Every pattern read as the binder of a binding arity: a shadowing arrow. -/
def bindingArityReading : Signature MC := sigOfRule ruleH0

theorem bindingArity_patterns_shadow :
    bindingArityReading.role .matchQ = .arrow .shadow ∧
      bindingArityReading.role .caseB = .arrow .shadow ∧
      bindingArityReading.role .letA = .arrow .shadow := by
  decide

/-- **Relations have no binding-arity counterpart**: the lookup probe answers
`(1 2)` when its pattern is read as a binder, `(2)` as a relation. -/
theorem arity_reading_separates :
    ansR bindingArityReading (embedQ lookupB) = some [kT .n1, kT .n2] ∧
      ansR sigMeTTa (embedQ lookupB) = some [kT .n2] := by
  constructor <;> decide +kernel

/-! ## `let` as a testing arrow -/

/-- MeTTa's signature with `let` and `chain` as testing arrows: the reading of
the principle's text, of the contracts' binder rule, and of HE and PeTTa. -/
def sigLetTest : Signature MC :=
  { sigMeTTa with
    role := fun c =>
      match c with
      | .letA => .arrow .test
      | .chainA => .arrow .test
      | c => sigMeTTa.role c }

theorem stable_sigLetTest : Stable sigLetTest := ⟨Or.inr rfl, rfl⟩

/-- **The `let` choice separates on one program**: `(let $x 1 (let $x 2 $x))`
answers 2 when `let` shadows (the query model, the CeTTa draft's default) and
nothing when it tests (HE and PeTTa).  Both signatures are stable, so every law
holds for both (`laws_iff` constrains frames, not roles): the choice is free
of the laws. -/
theorem let_choice_separates :
    ansR sigMeTTa (embedQ letArrow) = some [kT .n2] ∧ ansR sigLetTest (embedQ letArrow) = some [] := by
  constructor <;> decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Bridges
