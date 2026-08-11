import Mettapedia.Languages.ProcessCalculi.MORK.AtomZipper
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# MORK execution of authored contextual steps

This bridge keeps reduction authority and execution representation separate.
One-hole contexts come from authored MeTTaIL congruence rules.  MORK zippers
represent the corresponding focused update, while whole-atom replacement is
an execution detail compiled only from an accepted contextual reduction.

No collection constructor is intrinsically reduction-active here.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ContextualStep

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

private theorem morkPatternToAtomList_eq_map (patterns : List ILPattern) :
    morkPatternToAtom.morkPatternToAtomList patterns =
      patterns.map morkPatternToAtom := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      simp only [morkPatternToAtom.morkPatternToAtomList, List.map_cons, ih]

/-! ## Structural translation -/

/-- Translate a MeTTaIL one-hole context into MORK's Huet zipper context.
The resulting crumbs are ordered from the hole outwards, as required by
`AtomZipper.rebuild`. -/
def morkAtomContext : OneHoleContext → AtomContext
  | .hole => []
  | .apply constructor before inner after =>
      morkAtomContext inner ++
        [{ left := (.symbol constructor :: before.map morkPatternToAtom).reverse
           right := after.map morkPatternToAtom }]
  | .lambda _ inner =>
      morkAtomContext inner ++
        [{ left := [.symbol "λ"], right := [] }]
  | .multiLambda arity _ inner =>
      morkAtomContext inner ++
        [{ left := [.symbol (toString arity), .symbol "λ*"], right := [] }]
  | .substBody inner replacement =>
      morkAtomContext inner ++
        [{ left := [.symbol "subst"], right := [morkPatternToAtom replacement] }]
  | .substReplacement body inner =>
      morkAtomContext inner ++
        [{ left := [morkPatternToAtom body, .symbol "subst"], right := [] }]
  | .collection collectionType before inner after _ =>
      morkAtomContext inner ++
        [{ left :=
             (.symbol (morkCollTypeSymbol collectionType) ::
               before.map morkPatternToAtom).reverse
           right := after.map morkPatternToAtom }]

/-- Translating after plugging a MeTTaIL context agrees exactly with rebuilding
the translated MORK zipper. -/
theorem rebuild_morkAtomContext (context : OneHoleContext) (pattern : ILPattern) :
    rebuild ⟨morkPatternToAtom pattern, morkAtomContext context⟩ =
      morkPatternToAtom (context.fill pattern) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after ih =>
      have innerEq :
          List.foldl plugCrumb (morkPatternToAtom pattern) (morkAtomContext inner) =
            morkPatternToAtom (inner.fill pattern) := by
        simpa only [rebuild] using ih
      simp [morkAtomContext, rebuild, List.foldl_append, plugCrumb,
        OneHoleContext.fill, morkPatternToAtom,
        morkPatternToAtomList_eq_map, innerEq]
  | lambda binderName inner ih =>
      have innerEq :
          List.foldl plugCrumb (morkPatternToAtom pattern) (morkAtomContext inner) =
            morkPatternToAtom (inner.fill pattern) := by
        simpa only [rebuild] using ih
      simp [morkAtomContext, rebuild, List.foldl_append, plugCrumb,
        OneHoleContext.fill, morkPatternToAtom, innerEq]
  | multiLambda arity binderNames inner ih =>
      have innerEq :
          List.foldl plugCrumb (morkPatternToAtom pattern) (morkAtomContext inner) =
            morkPatternToAtom (inner.fill pattern) := by
        simpa only [rebuild] using ih
      simp [morkAtomContext, rebuild, List.foldl_append, plugCrumb,
        OneHoleContext.fill, morkPatternToAtom, innerEq]
  | substBody inner replacement ih =>
      have innerEq :
          List.foldl plugCrumb (morkPatternToAtom pattern) (morkAtomContext inner) =
            morkPatternToAtom (inner.fill pattern) := by
        simpa only [rebuild] using ih
      simp [morkAtomContext, rebuild, List.foldl_append, plugCrumb,
        OneHoleContext.fill, morkPatternToAtom, innerEq]
  | substReplacement body inner ih =>
      have innerEq :
          List.foldl plugCrumb (morkPatternToAtom pattern) (morkAtomContext inner) =
            morkPatternToAtom (inner.fill pattern) := by
        simpa only [rebuild] using ih
      simp [morkAtomContext, rebuild, List.foldl_append, plugCrumb,
        OneHoleContext.fill, morkPatternToAtom, innerEq]
  | collection collectionType before inner after rest ih =>
      have innerEq :
          List.foldl plugCrumb (morkPatternToAtom pattern) (morkAtomContext inner) =
            morkPatternToAtom (inner.fill pattern) := by
        simpa only [rebuild] using ih
      simp [morkAtomContext, rebuild, List.foldl_append, plugCrumb,
        OneHoleContext.fill, morkPatternToAtom,
        morkPatternToAtomList_eq_map, innerEq]

/-- Every MeTTaIL one-hole context translates to a MORK lens update. -/
theorem oneHoleContext_lensRel
    (context : OneHoleContext) (source target : ILPattern) :
    LensRel
      (morkPatternToAtom (context.fill source))
      (morkPatternToAtom source)
      (morkPatternToAtom target)
      (morkPatternToAtom (context.fill target)) := by
  refine ⟨⟨morkPatternToAtom source, morkAtomContext context⟩,
    rebuild_morkAtomContext context source, rfl, ?_⟩
  exact rebuild_morkAtomContext context target

/-- An authored contextual frame therefore has an exact zipper realization;
the language rule supplies authority and the zipper supplies representation. -/
theorem authoredContextFrame_lensRel
    {lang : LanguageDef} {sourceSort targetSort : String}
    {context : OneHoleContext}
    (authored : AuthoredContextFrame lang sourceSort targetSort context)
    (source target : ILPattern) :
    ∃ rule ∈ lang.rewrites,
      RuleAuthorizesContext rule context ∧
      LensRel
        (morkPatternToAtom (context.fill source))
        (morkPatternToAtom source)
        (morkPatternToAtom target)
        (morkPatternToAtom (context.fill target)) := by
  obtain ⟨_, rule, ruleMember, authorization⟩ := authored
  exact ⟨rule, ruleMember, authorization,
    oneHoleContext_lensRel context source target⟩

/-! ## Derived executable rules -/

/-- Whole-atom replacement used by the MORK backend.  This operation carries
no reduction authority on its own; `compiledContextRules` is its only semantic
entry point. -/
def compiledContextRule (source target : Atom) : ExecRule :=
  { priority := 40
    name := "authored-context"
    pat := mkPattern [source]
    tmpl := mkTemplate [mkRemove source, mkAdd target] }

private theorem applySubst_groundAtom (substitution : Subst) (atom : Atom)
    (ground : isGroundAtom atom = true) :
    applySubst substitution atom = atom := by
  match atom with
  | .var name => simp [isGroundAtom] at ground
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression atoms =>
      simp only [applySubst]
      have listGround : isGroundAtom.isGroundList atoms = true := by
        simpa only [isGroundAtom] using ground
      exact congrArg Atom.expression
        (applySubstList_ground substitution atoms listGround)
where
  applySubstList_ground (substitution : Subst) (atoms : List Atom)
      (ground : isGroundAtom.isGroundList atoms = true) :
      applySubst.applySubstList substitution atoms = atoms := by
    match atoms with
    | [] => rfl
    | atom :: atoms =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [applySubst.applySubstList]
        congr 1
        · exact applySubst_groundAtom substitution atom ground.1
        · exact applySubstList_ground substitution atoms ground.2

/-- A ground atom matches itself without changing the incoming substitution. -/
theorem groundAtom_matchAtom_self (substitution : Subst) (atom : Atom)
    (ground : isGroundAtom atom = true) :
    matchAtom substitution atom atom = some substitution := by
  match atom with
  | .var name => simp [isGroundAtom] at ground
  | .symbol _ => simp [matchAtom]
  | .grounded _ => simp [matchAtom]
  | .expression atoms =>
      simp only [matchAtom]
      have listGround : isGroundAtom.isGroundList atoms = true := by
        simpa only [isGroundAtom] using ground
      exact matchAtomList_ground_self substitution atoms listGround
where
  matchAtomList_ground_self (substitution : Subst) (atoms : List Atom)
      (ground : isGroundAtom.isGroundList atoms = true) :
      matchAtom.matchAtomList substitution atoms atoms = some substitution := by
    match atoms with
    | [] => simp [matchAtom.matchAtomList]
    | atom :: atoms =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [matchAtom.matchAtomList]
        rw [groundAtom_matchAtom_self substitution atom ground.1]
        exact matchAtomList_ground_self substitution atoms ground.2

/-- A ground atom present in a workspace is an exact matching candidate. -/
theorem groundAtom_matchOneInSpace
    (substitution : Subst) (atom : Atom)
    (ground : isGroundAtom atom = true) (space : Space) (member : atom ∈ space) :
    (substitution, atom) ∈ matchOneInSpace substitution atom space := by
  simp only [matchOneInSpace, List.mem_filterMap]
  exact ⟨atom, Finset.mem_toList.mpr member,
    by simp [groundAtom_matchAtom_self substitution atom ground]⟩

private theorem compiledContextRule_fires
    (source target : Atom)
    (sourceGround : isGroundAtom source = true)
    (targetGround : isGroundAtom target = true) :
    {target} ∈ fireRule {source} (compiledContextRule source target) := by
  simp only [fireRule, compiledContextRule, List.mem_map]
  refine ⟨([], {source}), ?_, ?_⟩
  · simp only [matchPattern, mkPattern, matchPattern.go,
      List.mem_flatMap, matchOneInSpace, List.mem_filterMap]
    refine ⟨([], source), ?_, by simp⟩
    exact ⟨source, Finset.mem_toList.mpr (by simp),
      by simp [groundAtom_matchAtom_self [] source sourceGround]⟩
  · simp only [applySinks, mkTemplate, List.foldl, applySink,
      mkRemove, mkAdd, applySubst_groundAtom [] source sourceGround,
      applySubst_groundAtom [] target targetGround, targetGround, ite_true]
    simp [Finset.erase_eq]

/-- Compile exactly the bounded authored contextual reducts of `source` into
MORK whole-atom replacement rules. -/
def compiledContextRules
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (source : ILPattern) : List ExecRule :=
  (rewriteAt base lang fuel source).map fun target =>
    compiledContextRule (morkPatternToAtom source) (morkPatternToAtom target)

/-- A bounded authored contextual derivation compiles to a MORK rule in the
generated rule set, and that rule performs the corresponding space update. -/
theorem stepAt_compiles_to_mork_fire
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {source target : ILPattern}
    (step : StepAt base lang fuel source target)
    (sourceGround : isGroundAtom (morkPatternToAtom source) = true)
    (targetGround : isGroundAtom (morkPatternToAtom target) = true) :
    ∃ rule ∈ compiledContextRules base lang fuel source,
      patternToSpace target ∈ fireRule (patternToSpace source) rule := by
  let rule := compiledContextRule
    (morkPatternToAtom source) (morkPatternToAtom target)
  refine ⟨rule, ?_, ?_⟩
  · simp only [compiledContextRules, List.mem_map]
    exact ⟨target, mem_rewriteAt_iff_stepAt.mpr step, rfl⟩
  · exact compiledContextRule_fires _ _ sourceGround targetGround

/-! ## Source-aware derived rules -/

/-- Source-aware form of `compiledContextRule`.  It is generated only from
`rewriteAt`; it is not appended as an independent language rule. -/
def compiledContextSourceRule (source target : Atom) : SourceExecRule :=
  { priority := 40
    name := "authored-context"
    input := .explicit [.btm source]
    guards := []
    tmpl := mkTemplate [mkRemove source, mkAdd target] }

private theorem compiledContextSourceRule_fires
    (workspace : Space) (source target : Atom)
    (sourceMember : source ∈ workspace)
    (sourceGround : isGroundAtom source = true)
    (targetGround : isGroundAtom target = true) :
    workspace.erase source ∪ {target} ∈
      fireSourceRule workspace (compiledContextSourceRule source target) := by
  rw [fireSourceRule_no_guards _ _ rfl]
  rw [List.mem_map]
  refine ⟨([], {source}), ?_, ?_⟩
  · simp only [compiledContextSourceRule, matchInputSpec, matchSourceFactors,
      matchSourceFactors.go, matchSourceFactor,
      List.mem_flatMap]
    exact ⟨([], source),
      groundAtom_matchOneInSpace [] source sourceGround workspace sourceMember,
      by simp⟩
  · simp only [compiledContextSourceRule, applySinks, mkTemplate, List.foldl,
      applySink, mkRemove, mkAdd,
      applySubst_groundAtom [] source sourceGround,
      applySubst_groundAtom [] target targetGround, targetGround, ite_true]

/-- Compile exactly the bounded authored contextual reducts of `source` into
source-aware MORK rules. -/
def compiledContextSourceRules
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (source : ILPattern) : List SourceExecRule :=
  (rewriteAt base lang fuel source).map fun target =>
    compiledContextSourceRule
      (morkPatternToAtom source) (morkPatternToAtom target)

/-- A bounded authored contextual derivation compiles to a source-aware MORK
rule and performs the corresponding update in any workspace containing the
translated source. -/
theorem stepAt_compiles_to_mork_sourceRule
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {source target : ILPattern}
    (step : StepAt base lang fuel source target)
    (workspace : Space)
    (sourceMember : morkPatternToAtom source ∈ workspace)
    (sourceGround : isGroundAtom (morkPatternToAtom source) = true)
    (targetGround : isGroundAtom (morkPatternToAtom target) = true) :
    ∃ rule ∈ compiledContextSourceRules base lang fuel source,
      workspace.erase (morkPatternToAtom source) ∪ {morkPatternToAtom target} ∈
        fireSourceRule workspace rule := by
  let rule := compiledContextSourceRule
    (morkPatternToAtom source) (morkPatternToAtom target)
  refine ⟨rule, ?_, ?_⟩
  · simp only [compiledContextSourceRules, List.mem_map]
    exact ⟨target, mem_rewriteAt_iff_stepAt.mpr step, rfl⟩
  · exact compiledContextSourceRule_fires workspace _ _ sourceMember
      sourceGround targetGround

end Mettapedia.Languages.ProcessCalculi.MORK
