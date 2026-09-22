import Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.Framework.PredFiniteSufficient
import Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
import Mettapedia.GSLT.LanguageDef.BindingSignatureReification

/-!
# Named raw patterns for certified combined WM terms

The intrinsic context uses sorted de Bruijn positions. Authored equation
schemas use named free pattern variables. This module relates the two on the
eight-constructor first-order WM fragment without changing either syntax.
Names are an explicit parameter, so no ambiguous global name allocation is
silently chosen. Generic binding/collection representation forms are outside
this fragment.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

set_option autoImplicit false

/-- Render a certified first-order intrinsic WM term as the authored raw
pattern whose sorted context variables are assigned explicit schema names. -/
def namedErase {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String) :
    {sort : TypeExpr} → {term : Term CombinedSignature Γ sort} →
      FirstOrder term → Pattern
  | _, _, .variable position => .fvar (names _ position)
  | _, _, .revise first second =>
      pRevise (namedErase names first) (namedErase names second)
  | _, _, .extract world query =>
      pExtract (namedErase names world) (namedErase names query)
  | _, _, .combine first second =>
      pCombine (namedErase names first) (namedErase names second)
  | _, _, .zero => pEvidenceZero
  | _, _, .overlapMerge first second =>
      pOverlapMerge (namedErase names first) (namedErase names second)
  | _, _, .overlapFactor first second query =>
      pOverlapFactor (namedErase names first) (namedErase names second)
        (namedErase names query)
  | _, _, .overlapCorrect first second factor =>
      pOverlapCorrect (namedErase names first) (namedErase names second)
        (namedErase names factor)
  | _, _, .forget scope world =>
      pForget (namedErase names scope) (namedErase names world)

private abbrev CombinedLang : LanguageDef :=
  wmExtVertexLanguageDefGuarded combinedVertex

/-- The current authored eight-constructor language has no closed first-order
State, Query, Scope, or Overlap value. The only possible result sort of a
closed, actually typed and compilable raw capture is BinaryEvidence. This
does not assert that every Evidence capture has a model certificate. -/
theorem closed_typed_compiled_only_evidence
    (pattern : Pattern) {sort : TypeExpr}
    (typed : HasType CombinedLang FreeTypeContext.empty [] pattern sort)
    (compiled : compilePattern? pattern ≠ none) :
    sort = .base "BinaryEvidence" := by
  induction pattern using Pattern.inductionOn generalizing sort with
  | hbvar index =>
      cases typed with
      | bvar lookup => simp at lookup
  | hfvar variableName =>
      cases typed with
      | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | happly label arguments ih =>
      cases typed with
      | constructor member ordinary argumentsTyped =>
          have childrenCompiled := compilePatterns?_ne_none_of_apply compiled
          rcases combined_declaration_cases member with h | h | h | h | h | h | h | h
          · cases h
            cases arguments with
            | nil => cases argumentsTyped
            | cons first rest =>
                obtain ⟨firstTyped, _⟩ :=
                  ArgumentsHaveTypes.simple_cons_inv argumentsTyped
                have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
                have firstEvidence := ih _ (List.Mem.head _) firstTyped firstCompiled
                simp at firstEvidence
          · cases h
            rfl
          · cases h
            rfl
          · cases h
            rfl
          · cases h
            cases arguments with
            | nil => cases argumentsTyped
            | cons first rest =>
                obtain ⟨firstTyped, _⟩ :=
                  ArgumentsHaveTypes.simple_cons_inv argumentsTyped
                have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
                have firstEvidence := ih _ (List.Mem.head _) firstTyped firstCompiled
                simp at firstEvidence
          · cases h
            cases arguments with
            | nil => cases argumentsTyped
            | cons first rest =>
                obtain ⟨firstTyped, _⟩ :=
                  ArgumentsHaveTypes.simple_cons_inv argumentsTyped
                have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
                have firstEvidence := ih _ (List.Mem.head _) firstTyped firstCompiled
                simp at firstEvidence
          · cases h
            rfl
          · cases h
            cases arguments with
            | nil => cases argumentsTyped
            | cons first rest =>
                obtain ⟨firstTyped, _⟩ :=
                  ArgumentsHaveTypes.simple_cons_inv argumentsTyped
                have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
                have firstEvidence := ih _ (List.Mem.head _) firstTyped firstCompiled
                simp at firstEvidence
  | hlambda binder body ih => simp [compilePattern?] at compiled
  | hmultiLambda count binders body ih => simp [compilePattern?] at compiled
  | hsubst body replacement bodyIH replacementIH => simp [compilePattern?] at compiled
  | hcollection kind elements rest ih => simp [compilePattern?] at compiled

/-- The executable authored type checker and first-order compiler cannot
jointly accept a closed capture at a non-Evidence sort. This is the exact
surface limitation behind the open-handle path. -/
theorem no_closed_checked_compiled_nonEvidence
    (pattern : Pattern) {sort : TypeExpr}
    (nonEvidence : sort ≠ .base "BinaryEvidence") :
    ¬ (checkHasType CombinedLang FreeTypeContext.empty [] pattern sort = true ∧
       compilePattern? pattern ≠ none) := by
  rintro ⟨typed, compiled⟩
  exact nonEvidence
    (closed_typed_compiled_only_evidence pattern (checkHasType_sound typed) compiled)

/-- The closed-Evidence admission boundary has a real positive witness. -/
theorem closed_evidence_checks_pass :
    checkHasType CombinedLang FreeTypeContext.empty [] pEvidenceZero
      (.base "BinaryEvidence") = true ∧
    (compilePattern? pEvidenceZero).isSome = true := by
  decide +kernel

/-- The named schema has exactly its intrinsic result sort whenever the
chosen free-variable assignment respects every sorted context position.
This is formation of the schema, not a type certificate for future matches. -/
theorem namedErase_typed
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (free : FreeTypeContext)
    (lookup : ∀ sort (position : Var Γ sort), free (names sort position) = some sort)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    HasType CombinedLang free [] (namedErase names fragment) sort := by
  induction fragment with
  | «variable» position =>
      exact HasType.fvar (lookup _ position)
  | revise first second firstIH secondIH =>
      change HasType CombinedLang free []
        (.apply "Revise" [namedErase names first, namedErase names second])
          (.base "State")
      exact HasType.constructor (rule := reviseDecl)
        (by decide +kernel) (by simp [UsesBareCollection, reviseDecl])
        (.cons trivial rfl firstIH (.cons trivial rfl secondIH .nil))
  | extract world query worldIH queryIH =>
      change HasType CombinedLang free []
        (.apply "Extract" [namedErase names world, namedErase names query])
          (.base "BinaryEvidence")
      exact HasType.constructor (rule := extractDecl)
        (by decide +kernel) (by simp [UsesBareCollection, extractDecl])
        (.cons trivial rfl worldIH (.cons trivial rfl queryIH .nil))
  | combine first second firstIH secondIH =>
      change HasType CombinedLang free []
        (.apply "Combine" [namedErase names first, namedErase names second])
          (.base "BinaryEvidence")
      exact HasType.constructor (rule := combineDecl)
        (by decide +kernel) (by simp [UsesBareCollection, combineDecl])
        (.cons trivial rfl firstIH (.cons trivial rfl secondIH .nil))
  | zero =>
      change HasType CombinedLang free []
        (.apply "EvidenceZero" []) (.base "BinaryEvidence")
      exact HasType.constructor (rule := evidenceZeroDecl)
        (by decide +kernel) (by simp [UsesBareCollection, evidenceZeroDecl]) .nil
  | overlapMerge first second firstIH secondIH =>
      change HasType CombinedLang free []
        (.apply "OverlapMerge" [namedErase names first, namedErase names second])
          (.base "State")
      exact HasType.constructor (rule := overlapMergeDecl)
        (by decide +kernel) (by simp [UsesBareCollection, overlapMergeDecl])
        (.cons trivial rfl firstIH (.cons trivial rfl secondIH .nil))
  | overlapFactor first second query firstIH secondIH queryIH =>
      change HasType CombinedLang free []
        (.apply "OverlapFactor"
          [namedErase names first, namedErase names second, namedErase names query])
          (.base "Overlap")
      exact HasType.constructor (rule := overlapFactorDecl)
        (by decide +kernel) (by simp [UsesBareCollection, overlapFactorDecl])
        (.cons trivial rfl firstIH
          (.cons trivial rfl secondIH (.cons trivial rfl queryIH .nil)))
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      change HasType CombinedLang free []
        (.apply "OverlapCorrect"
          [namedErase names first, namedErase names second, namedErase names factor])
          (.base "BinaryEvidence")
      exact HasType.constructor (rule := overlapCorrectDecl)
        (by decide +kernel) (by simp [UsesBareCollection, overlapCorrectDecl])
        (.cons trivial rfl firstIH
          (.cons trivial rfl secondIH (.cons trivial rfl factorIH .nil)))
  | forget scope world scopeIH worldIH =>
      change HasType CombinedLang free []
        (.apply "Forget" [namedErase names scope, namedErase names world])
          (.base "State")
      exact HasType.constructor (rule := forgetDecl)
        (by decide +kernel) (by simp [UsesBareCollection, forgetDecl])
        (.cons trivial rfl scopeIH (.cons trivial rfl worldIH .nil))

/-- Every certified named schema is an object pattern, with no pending
explicit substitution or open collection tail. -/
theorem namedErase_isObjectPattern
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    isObjectPattern (namedErase names fragment) = true := by
  induction fragment with
  | «variable» position =>
      simp [namedErase, isObjectPattern]
  | revise first second firstIH secondIH =>
      simp [namedErase, pRevise, isObjectPattern, isObjectPatternList,
        firstIH, secondIH]
  | extract world query worldIH queryIH =>
      simp [namedErase, pExtract, isObjectPattern, isObjectPatternList,
        worldIH, queryIH]
  | combine first second firstIH secondIH =>
      simp [namedErase, pCombine, isObjectPattern, isObjectPatternList,
        firstIH, secondIH]
  | zero =>
      simp [namedErase, pEvidenceZero, isObjectPattern, isObjectPatternList]
  | overlapMerge first second firstIH secondIH =>
      simp [namedErase, pOverlapMerge, isObjectPattern, isObjectPatternList,
        firstIH, secondIH]
  | overlapFactor first second query firstIH secondIH queryIH =>
      simp [namedErase, pOverlapFactor, isObjectPattern, isObjectPatternList,
        firstIH, secondIH, queryIH]
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simp [namedErase, pOverlapCorrect, isObjectPattern, isObjectPatternList,
        firstIH, secondIH, factorIH]
  | forget scope world scopeIH worldIH =>
      simp [namedErase, pForget, isObjectPattern, isObjectPatternList,
        scopeIH, worldIH]

/-- The existing executable authored type checker accepts every certified
named schema under a sort-respecting free-variable assignment. -/
theorem namedErase_checked
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (free : FreeTypeContext)
    (lookup : ∀ sort (position : Var Γ sort), free (names sort position) = some sort)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    checkHasType CombinedLang free [] (namedErase names fragment) sort = true :=
  (checkHasType_eq_true_iff (namedErase_isObjectPattern names fragment)).2
    (namedErase_typed names free lookup fragment)

/-- Every certified authored WM schema is in the executable matcher's
reconstruction fragment. It has neither binders nor bag matching, which are
the two sources of failure for the generic reconstruction theorem. -/
theorem namedErase_isMatchCorrect
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    Pattern.isMatchCorrect (namedErase names fragment) = true := by
  induction fragment with
  | «variable» position =>
      simp [namedErase, Pattern.isMatchCorrect, isMatchCorrectAux]
  | revise first second firstIH secondIH =>
      simpa [namedErase, pRevise, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using And.intro firstIH secondIH
  | extract world query worldIH queryIH =>
      simpa [namedErase, pExtract, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using And.intro worldIH queryIH
  | combine first second firstIH secondIH =>
      simpa [namedErase, pCombine, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using And.intro firstIH secondIH
  | zero =>
      simp [namedErase, pEvidenceZero, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux]
  | overlapMerge first second firstIH secondIH =>
      simpa [namedErase, pOverlapMerge, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using And.intro firstIH secondIH
  | overlapFactor first second query firstIH secondIH queryIH =>
      simpa [namedErase, pOverlapFactor, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using
        And.intro firstIH (And.intro secondIH queryIH)
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simpa [namedErase, pOverlapCorrect, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using
        And.intro firstIH (And.intro secondIH factorIH)
  | forget scope world scopeIH worldIH =>
      simpa [namedErase, pForget, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux] using And.intro scopeIH worldIH

/-- Every certified named schema is accepted by the existing first-order
pattern compiler. This follows from exact equality of the compiler's syntax
boundary and the matcher's reconstruction fragment; it does not compile the
typed term's semantics. -/
theorem namedErase_compiles
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    (compilePattern? (namedErase names fragment)).isSome = true := by
  rw [compilePattern?_isSome_eq_isMatchCorrectAux]
  simpa only [Pattern.isMatchCorrect] using
    namedErase_isMatchCorrect names fragment

/-- A certified named WM schema has an actual first-order plan whose
execution agrees with the ordinary matcher on every concrete subject. This
is an executable matching bridge, not a typed-value elaborator. -/
theorem namedErase_compiledMatcher
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    ∃ plan : PatternPlan,
      compilePattern? (namedErase names fragment) = some plan ∧
        ∀ concrete : Pattern,
          plan.run concrete = matchPattern (namedErase names fragment) concrete := by
  have accepted := namedErase_compiles names fragment
  cases result : compilePattern? (namedErase names fragment) with
  | none => simp [result] at accepted
  | some plan =>
      exact ⟨plan, rfl, fun concrete =>
        run_compilePattern? (namedErase names fragment) concrete plan result⟩

/-- A successful actual MeTTaIL match reconstructs its target from the
bindings for any certified named WM schema, including repeated names. -/
theorem matchPattern_namedErase_correct
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern) (bindings : Bindings)
    (matched : bindings ∈ matchPattern (namedErase names fragment) concrete) :
    applyBindings bindings (namedErase names fragment) = concrete :=
  matchPattern_correct matched (namedErase_isMatchCorrect names fragment)

/-- Applying actual MeTTaIL bindings to a named authored WM schema agrees
exactly with erasure after intrinsic simultaneous substitution, provided each
named variable is bound to the erasure of its corresponding image. The images
need not themselves be interpreted to establish this syntax-level equality. -/
theorem applyBindings_namedErase_eq_erase_bind
    {Γ Δ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (names sort position)) =
        erase (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    applyBindings bindings (namedErase names fragment) =
      erase (bind sigma term) := by
  induction fragment with
  | «variable» position =>
      change applyBindings bindings (.fvar (names _ position)) =
        erase (sigma _ position)
      exact variableReceipt _ position
  | revise first second firstIH secondIH =>
      simp [namedErase, pRevise, applyBindings, bind_revise, erase_revise,
        firstIH, secondIH]
  | extract world query worldIH queryIH =>
      simp [namedErase, pExtract, applyBindings, bind_extract, erase_extract,
        worldIH, queryIH]
  | combine first second firstIH secondIH =>
      simp [namedErase, pCombine, applyBindings, bind_combine, erase_combine,
        firstIH, secondIH]
  | zero =>
      simp [namedErase, pEvidenceZero, applyBindings, bind_zero, erase_zero]
  | overlapMerge first second firstIH secondIH =>
      simp [namedErase, pOverlapMerge, applyBindings, bind_overlapMerge,
        erase_overlapMerge, firstIH, secondIH]
  | overlapFactor first second query firstIH secondIH queryIH =>
      simp [namedErase, pOverlapFactor, applyBindings, bind_overlapFactor,
        erase_overlapFactor, firstIH, secondIH, queryIH]
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simp [namedErase, pOverlapCorrect, applyBindings, bind_overlapCorrect,
        erase_overlapCorrect, firstIH, secondIH, factorIH]
  | forget scope world scopeIH worldIH =>
      simp [namedErase, pForget, applyBindings, bind_forget, erase_forget,
        scopeIH, worldIH]

/-- Open typed captures use a name assignment at the target context rather
than treating its variables as closed raw patterns. Applying matcher bindings
then agrees with intrinsic supported substitution followed by target naming.
This avoids misreading an intrinsic bound-variable erasure as a free atom. -/
theorem applyBindings_namedErase_eq_namedErase_substitute
    {Γ Δ : Ctx CombinedSignature}
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (sourceNames sort position)) =
        namedErase targetNames (supported sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    applyBindings bindings (namedErase sourceNames fragment) =
      namedErase targetNames (FirstOrder.substitute sigma supported fragment) := by
  induction fragment with
  | «variable» position => exact variableReceipt _ position
  | revise first second firstIH secondIH =>
      have hsub : FirstOrder.substitute sigma supported (FirstOrder.revise first second) =
          FirstOrder.revise (FirstOrder.substitute sigma supported first)
            (FirstOrder.substitute sigma supported second) := rfl
      rw [hsub]
      simp only [namedErase, pRevise, applyBindings, List.map_cons, List.map_nil,
        firstIH, secondIH]
  | extract world query worldIH queryIH =>
      have hsub : FirstOrder.substitute sigma supported (FirstOrder.extract world query) =
          FirstOrder.extract (FirstOrder.substitute sigma supported world)
            (FirstOrder.substitute sigma supported query) := rfl
      rw [hsub]
      simp only [namedErase, pExtract, applyBindings, List.map_cons, List.map_nil,
        worldIH, queryIH]
  | combine first second firstIH secondIH =>
      have hsub : FirstOrder.substitute sigma supported (FirstOrder.combine first second) =
          FirstOrder.combine (FirstOrder.substitute sigma supported first)
            (FirstOrder.substitute sigma supported second) := rfl
      rw [hsub]
      simp only [namedErase, pCombine, applyBindings, List.map_cons, List.map_nil,
        firstIH, secondIH]
  | zero =>
      simp [namedErase, pEvidenceZero, applyBindings, FirstOrder.substitute]
  | overlapMerge first second firstIH secondIH =>
      have hsub : FirstOrder.substitute sigma supported
          (FirstOrder.overlapMerge first second) =
          FirstOrder.overlapMerge (FirstOrder.substitute sigma supported first)
            (FirstOrder.substitute sigma supported second) := rfl
      rw [hsub]
      simp only [namedErase, pOverlapMerge, applyBindings, List.map_cons,
        List.map_nil, firstIH, secondIH]
  | overlapFactor first second query firstIH secondIH queryIH =>
      have hsub : FirstOrder.substitute sigma supported
          (FirstOrder.overlapFactor first second query) =
          FirstOrder.overlapFactor (FirstOrder.substitute sigma supported first)
            (FirstOrder.substitute sigma supported second)
            (FirstOrder.substitute sigma supported query) := rfl
      rw [hsub]
      simp only [namedErase, pOverlapFactor, applyBindings, List.map_cons,
        List.map_nil, firstIH, secondIH, queryIH]
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      have hsub : FirstOrder.substitute sigma supported
          (FirstOrder.overlapCorrect first second factor) =
          FirstOrder.overlapCorrect (FirstOrder.substitute sigma supported first)
            (FirstOrder.substitute sigma supported second)
            (FirstOrder.substitute sigma supported factor) := rfl
      rw [hsub]
      simp only [namedErase, pOverlapCorrect, applyBindings, List.map_cons,
        List.map_nil, firstIH, secondIH, factorIH]
  | forget scope world scopeIH worldIH =>
      have hsub : FirstOrder.substitute sigma supported (FirstOrder.forget scope world) =
          FirstOrder.forget (FirstOrder.substitute sigma supported scope)
            (FirstOrder.substitute sigma supported world) := rfl
      rw [hsub]
      simp only [namedErase, pForget, applyBindings, List.map_cons, List.map_nil,
        scopeIH, worldIH]

/-- A successful match with supported open-context images denotes the source
under the reindexed environment, even when raw handle names change. -/
theorem matchPattern_namedErase_open_denote
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (sourceNames sort position)) =
        namedErase targetNames (supported sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern)
    (matched : bindings ∈ matchPattern (namedErase sourceNames fragment) concrete) :
    ∃ targetCertificate : FirstOrder (bind sigma term),
      namedErase targetNames targetCertificate = concrete ∧
        FirstOrder.denote reading environment targetCertificate =
          FirstOrder.denote reading
            (fun sort position => FirstOrder.denote reading environment
              (supported sort position)) fragment := by
  refine ⟨FirstOrder.substitute sigma supported fragment, ?_, ?_⟩
  · rw [← matchPattern_namedErase_correct sourceNames fragment concrete
      bindings matched]
    exact (applyBindings_namedErase_eq_namedErase_substitute sourceNames
      targetNames bindings sigma supported variableReceipt fragment).symm
  · exact denote_substitute reading sigma supported environment fragment

/-- Every supplied supported open substitution with matching raw binding
receipts is found by the executable matcher. The returned binding set agrees
with the supplied values wherever the source schema uses them. -/
theorem matchPattern_namedErase_open_complete_for_substitution
    {Γ Δ : Ctx CombinedSignature}
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (sourceNames sort position)) =
        namedErase targetNames (supported sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    ∃ returned,
      returned ∈ matchPattern (namedErase sourceNames fragment)
        (namedErase targetNames
          (FirstOrder.substitute sigma supported fragment)) ∧
      BindingsValued returned (lookupOrFvar bindings) := by
  have hmc : isMatchCorrectAux (namedErase sourceNames fragment) = true := by
    simpa only [Pattern.isMatchCorrect] using
      namedErase_isMatchCorrect sourceNames fragment
  obtain ⟨returned, matched, valued⟩ :=
    matchPattern_applyBindings_complete
      (pat := namedErase sourceNames fragment) (bs := bindings) hmc
  refine ⟨returned, ?_, valued⟩
  rw [← applyBindings_namedErase_eq_namedErase_substitute sourceNames
    targetNames bindings sigma supported variableReceipt fragment]
  exact matched

/-- A successful executable match whose bindings have sorted intrinsic image
receipts identifies the matched raw target with intrinsic substitution of the
certified schema. Matching alone does not manufacture those sorted receipts. -/
theorem matchPattern_namedErase_eq_erase_bind
    {Γ Δ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (names sort position)) =
        erase (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern)
    (matched : bindings ∈ matchPattern (namedErase names fragment) concrete) :
    concrete = erase (bind sigma term) := by
  rw [← matchPattern_namedErase_correct names fragment concrete bindings matched]
  exact applyBindings_namedErase_eq_erase_bind names bindings sigma variableReceipt fragment

/-- An actual match with supported, sorted substitution images has the
combined reading's substitution meaning. The returned raw subject is the
erasure of the supported intrinsic target; raw matching alone does not supply
the support hypothesis. -/
theorem matchPattern_namedErase_denote
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (names sort position)) =
        erase (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern)
    (matched : bindings ∈ matchPattern (namedErase names fragment) concrete) :
    ∃ targetCertificate : FirstOrder (bind sigma term),
      erase (bind sigma term) = concrete ∧
        FirstOrder.denote reading environment targetCertificate =
          FirstOrder.denote reading
            (fun sort position => FirstOrder.denote reading environment
              (supported sort position)) fragment := by
  refine ⟨FirstOrder.substitute sigma supported fragment, ?_, ?_⟩
  · exact (matchPattern_namedErase_eq_erase_bind names bindings sigma
      variableReceipt fragment concrete matched).symm
  · exact denote_substitute reading sigma supported environment fragment

/-- Any other supported intrinsic representation of that matched raw subject
has the same value. Thus the semantic result does not depend on selecting the
particular substitution certificate used above. -/
theorem matchPattern_namedErase_denote_any_supported
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (names sort position)) =
        erase (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern)
    (matched : bindings ∈ matchPattern (namedErase names fragment) concrete)
    (other : Term CombinedSignature Δ sort) (otherCertificate : FirstOrder other)
    (otherErases : erase other = concrete) :
    FirstOrder.denote reading environment otherCertificate =
      FirstOrder.denote reading
        (fun sort position => FirstOrder.denote reading environment
          (supported sort position)) fragment := by
  obtain ⟨canonical, canonicalErases, canonicalValue⟩ :=
    matchPattern_namedErase_denote reading environment names bindings sigma
      supported variableReceipt fragment concrete matched
  have sameValue := denote_heq_of_erase_eq reading environment
    otherCertificate canonical (otherErases.trans canonicalErases.symm)
  exact sameValue.eq.trans canonicalValue

/-- A sorted intrinsic substitution, presented through an actual raw binding
list, is found by the executable matcher. The returned bindings agree with
the supplied values wherever they are present. -/
theorem matchPattern_namedErase_complete_for_substitution
    {Γ Δ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (names sort position)) =
        erase (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    ∃ returned,
      returned ∈ matchPattern (namedErase names fragment) (erase (bind sigma term)) ∧
      BindingsValued returned (lookupOrFvar bindings) := by
  have hmc : isMatchCorrectAux (namedErase names fragment) = true := by
    simpa only [Pattern.isMatchCorrect] using namedErase_isMatchCorrect names fragment
  obtain ⟨returned, matched, valued⟩ :=
    matchPattern_applyBindings_complete (pat := namedErase names fragment)
      (bs := bindings) hmc
  refine ⟨returned, ?_, valued⟩
  rw [← applyBindings_namedErase_eq_erase_bind names bindings sigma variableReceipt fragment]
  exact matched

/-- Match results of the instantiated schema recover precisely the original
binding values on every name occurring in that schema. Extra ambient names
are deliberately not constrained by matching. -/
theorem matchPattern_namedErase_recovers_used_bindings
    {Γ Δ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings returned : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (variableReceipt : ∀ sort (position : Var Γ sort),
      applyBindings bindings (.fvar (names sort position)) =
        erase (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term)
    (matched : returned ∈
      matchPattern (namedErase names fragment) (erase (bind sigma term))) :
    ∀ key, key ∈ freeVars (namedErase names fragment) →
      lookupOrFvar returned key = lookupOrFvar bindings key := by
  have hmc : isMatchCorrectAux (namedErase names fragment) = true := by
    simpa only [Pattern.isMatchCorrect] using namedErase_isMatchCorrect names fragment
  have reconstructed := matchPattern_namedErase_correct names fragment
    (erase (bind sigma term)) returned matched
  have sourceReconstructed :=
    applyBindings_namedErase_eq_erase_bind names bindings sigma variableReceipt fragment
  exact applyBindings_injective_isMatchCorrect hmc
    (reconstructed.trans sourceReconstructed.symm)

/-- Accepted closed first-order capture values supply an actual intrinsically
sorted simultaneous substitution. This reuses the declaration-derived closed
reifier; no new constructor search or typed matcher is introduced. Under the
current eight-constructor WM language, the premises can hold only for
Evidence-sorted context variables. -/
theorem checkedClosedBindings_reifySubstitution
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    (typed : ∀ sort (position : Var Γ sort),
      checkHasType CombinedLang FreeTypeContext.empty []
        (applyBindings bindings (.fvar (names sort position))) sort = true)
    (firstOrder : ∀ sort (position : Var Γ sort),
      compilePattern? (applyBindings bindings (.fvar (names sort position))) ≠ none) :
    ∃ sigma : Sub CombinedSignature Γ [],
      ∀ sort (position : Var Γ sort),
        applyBindings bindings (.fvar (names sort position)) =
          erase (sigma sort position) := by
  have each : ∀ sort (position : Var Γ sort),
      ∃ image : Term CombinedSignature [] sort,
        erase image = applyBindings bindings (.fvar (names sort position)) := by
    intro sort position
    obtain ⟨image, _, erases⟩ :=
      exists_reification_of_typed_firstOrder
        (checkHasType_sound (typed sort position)) (firstOrder sort position)
    exact ⟨image, erases⟩
  classical
  choose sigma receipt using each
  exact ⟨sigma, fun sort position => (receipt sort position).symm⟩

/-- The closed-reification premises above cannot hold when the schema context
contains a non-Evidence variable. In particular they cannot instantiate a
State or Query handle: those need an explicitly typed open context. -/
theorem checkedClosedCapture_nonEvidence_impossible
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (bindings : Bindings)
    {sort : TypeExpr} (position : Var Γ sort)
    (nonEvidence : sort ≠ .base "BinaryEvidence")
    (typed : checkHasType CombinedLang FreeTypeContext.empty []
      (applyBindings bindings (.fvar (names sort position))) sort = true)
    (firstOrder :
      compilePattern? (applyBindings bindings (.fvar (names sort position))) ≠ none) :
    False := by
  exact no_closed_checked_compiled_nonEvidence
    (applyBindings bindings (.fvar (names sort position))) nonEvidence
    ⟨typed, firstOrder⟩

/-- Under executable type and first-order checks on every captured value,
any successful raw match of a certified WM schema is an intrinsic closed
substitution instance. The result is syntactic; semantic support of each image
is a separate obligation. The current language has no admissible closed State
or Query capture, so this theorem does not close those WM rule instances. -/
theorem checkedClosedMatch_reifiesIntrinsicInstance
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern) (bindings : Bindings)
    (matched : bindings ∈ matchPattern (namedErase names fragment) concrete)
    (typed : ∀ sort (position : Var Γ sort),
      checkHasType CombinedLang FreeTypeContext.empty []
        (applyBindings bindings (.fvar (names sort position))) sort = true)
    (firstOrder : ∀ sort (position : Var Γ sort),
      compilePattern? (applyBindings bindings (.fvar (names sort position))) ≠ none) :
    ∃ sigma : Sub CombinedSignature Γ [], concrete = erase (bind sigma term) := by
  obtain ⟨sigma, receipt⟩ :=
    checkedClosedBindings_reifySubstitution names bindings typed firstOrder
  exact ⟨sigma, matchPattern_namedErase_eq_erase_bind names bindings sigma
    receipt fragment concrete matched⟩

/-- The reconstructed target is well sorted by the authored language's sole
formation relation. Matcher success alone lacks this consequence; the capture
checks discharge exactly the additional obligation. -/
theorem checkedClosedMatch_target_typed
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (concrete : Pattern) (bindings : Bindings)
    (matched : bindings ∈ matchPattern (namedErase names fragment) concrete)
    (typed : ∀ sort (position : Var Γ sort),
      checkHasType CombinedLang FreeTypeContext.empty []
        (applyBindings bindings (.fvar (names sort position))) sort = true)
    (firstOrder : ∀ sort (position : Var Γ sort),
      compilePattern? (applyBindings bindings (.fvar (names sort position))) ≠ none) :
    HasType CombinedLang FreeTypeContext.empty [] concrete sort := by
  obtain ⟨sigma, equal⟩ :=
    checkedClosedMatch_reifiesIntrinsicInstance names fragment concrete bindings
      matched typed firstOrder
  rw [equal]
  exact erase_typed (bind sigma term)

private def oneEvidenceName :
    (sort : TypeExpr) → Var [(.base "BinaryEvidence")] sort → String :=
  fun _ _ => "e"

private def repeatedEvidenceTerm :
    Term CombinedSignature [(.base "BinaryEvidence")] (.base "BinaryEvidence") :=
  combine (.var .zero) (.var .zero)

private def repeatedEvidenceFragment : FirstOrder repeatedEvidenceTerm :=
  .combine (.variable .zero) (.variable .zero)

/-- An actual repeated-name match with a closed typed capture passes both
executable checks and yields a genuine closed intrinsic substitution. -/
theorem checkedClosed_repeatedEvidence_reifies :
    ∃ sigma : Sub CombinedSignature [(.base "BinaryEvidence")] [],
      pCombine pEvidenceZero pEvidenceZero =
        erase (bind sigma repeatedEvidenceTerm) := by
  apply checkedClosedMatch_reifiesIntrinsicInstance oneEvidenceName
    repeatedEvidenceFragment (pCombine pEvidenceZero pEvidenceZero)
    [("e", pEvidenceZero)]
  · decide +kernel
  · intro sort position
    cases position with
    | zero => decide +kernel
    | succ earlier => cases earlier
  · intro sort position
    cases position with
    | zero => decide +kernel
    | succ earlier => cases earlier

private def repeatedZeroSub :
    Sub CombinedSignature [(.base "BinaryEvidence")] [] :=
  fun _ position => match position with
    | .zero => zero
    | .succ earlier => nomatch earlier

private def repeatedZeroSub_supported :
    ∀ sort (position : Var [(.base "BinaryEvidence")] sort),
      FirstOrder (repeatedZeroSub sort position) := by
  intro sort position
  cases position with
  | zero => exact .zero
  | succ earlier => cases earlier

private def emptyCountEnvironment :
    Environment (State := CountState) (Query := String)
      (Ev := Nat) (Ov := Nat) (Scope := CountScope) [] :=
  fun _ position => nomatch position

/-- A genuinely compiled repeated-name match in the counting reading has
the expected evidence value. The same raw match would not imply this without
the explicit supported substitution images. -/
theorem counting_compiled_repeatedEvidence_denotes :
    ∃ plan : PatternPlan,
      compilePattern? (namedErase oneEvidenceName repeatedEvidenceFragment) =
        some plan ∧
      [("e", pEvidenceZero)] ∈
        plan.run (pCombine pEvidenceZero pEvidenceZero) ∧
      ∃ certificate : FirstOrder (bind repeatedZeroSub repeatedEvidenceTerm),
        erase (bind repeatedZeroSub repeatedEvidenceTerm) =
          pCombine pEvidenceZero pEvidenceZero ∧
        FirstOrder.denote countingCombined emptyCountEnvironment certificate =
          countingCombined.core.zero := by
  obtain ⟨plan, compiled, run⟩ :=
    namedErase_compiledMatcher oneEvidenceName repeatedEvidenceFragment
  have matched : [("e", pEvidenceZero)] ∈
      matchPattern (namedErase oneEvidenceName repeatedEvidenceFragment)
        (pCombine pEvidenceZero pEvidenceZero) := by
    decide +kernel
  have planMatched : [("e", pEvidenceZero)] ∈
      plan.run (pCombine pEvidenceZero pEvidenceZero) := by
    rw [run]
    exact matched
  obtain ⟨certificate, erases, value⟩ :=
    matchPattern_namedErase_denote countingCombined emptyCountEnvironment
      oneEvidenceName [("e", pEvidenceZero)] repeatedZeroSub
      repeatedZeroSub_supported
      (by
        intro sort position
        cases position with
        | zero => decide +kernel
        | succ earlier => cases earlier)
      repeatedEvidenceFragment (pCombine pEvidenceZero pEvidenceZero) matched
  refine ⟨plan, compiled, planMatched, certificate, erases, ?_⟩
  exact value.trans (by rfl)

private abbrev HandleContext : Ctx CombinedSignature :=
  [(.base "State"), (.base "Query")]

private def handleSourceNames :
    (sort : TypeExpr) → Var HandleContext sort → String :=
  fun _ position => match position with
    | .zero => "w"
    | .succ .zero => "q"
    | .succ (.succ earlier) => nomatch earlier

private def handleTargetNames :
    (sort : TypeExpr) → Var HandleContext sort → String :=
  fun _ position => match position with
    | .zero => "w2"
    | .succ .zero => "q2"
    | .succ (.succ earlier) => nomatch earlier

private def handleExtractTerm :
    Term CombinedSignature HandleContext (.base "BinaryEvidence") :=
  extract (.var .zero) (.var (.succ .zero))

private def handleExtractFragment : FirstOrder handleExtractTerm :=
  .extract (.variable .zero) (.variable (.succ .zero))

private def handleIdentitySub : Sub CombinedSignature HandleContext HandleContext :=
  fun _ position => .var position

private def handleIdentitySupported :
    ∀ sort (position : Var HandleContext sort),
      FirstOrder (handleIdentitySub sort position) := by
  intro sort position
  exact .variable position

private def handleBindings : Bindings :=
  [("q", .fvar "q2"), ("w", .fvar "w2")]

private theorem handleVariableReceipt :
    ∀ sort (position : Var HandleContext sort),
      applyBindings handleBindings (.fvar (handleSourceNames sort position)) =
        namedErase handleTargetNames (handleIdentitySupported sort position) := by
  intro sort position
  cases position with
  | zero => decide +kernel
  | succ earlier =>
      cases earlier with
      | zero => decide +kernel
      | succ impossible => cases impossible

/-- Two externally named, sorted handles can be matched by an actual
compiled plan. Their target names change, while supported intrinsic
substitution gives the same model observation under the reindexed context. -/
theorem open_handle_compiled_match_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) HandleContext) :
    ∃ plan : PatternPlan,
      compilePattern? (namedErase handleSourceNames handleExtractFragment) =
        some plan ∧
      handleBindings ∈ plan.run (pExtract (.fvar "w2") (.fvar "q2")) ∧
      ∃ certificate : FirstOrder (bind handleIdentitySub handleExtractTerm),
        namedErase handleTargetNames certificate =
          pExtract (.fvar "w2") (.fvar "q2") ∧
        FirstOrder.denote reading environment certificate =
          FirstOrder.denote reading
            (fun sort position => FirstOrder.denote reading environment
              (handleIdentitySupported sort position)) handleExtractFragment := by
  obtain ⟨plan, compiled, run⟩ :=
    namedErase_compiledMatcher handleSourceNames handleExtractFragment
  have matched : handleBindings ∈
      matchPattern (namedErase handleSourceNames handleExtractFragment)
        (pExtract (.fvar "w2") (.fvar "q2")) := by
    decide +kernel
  have planMatched : handleBindings ∈
      plan.run (pExtract (.fvar "w2") (.fvar "q2")) := by
    rw [run]
    exact matched
  obtain ⟨certificate, named, value⟩ :=
    matchPattern_namedErase_open_denote reading environment handleSourceNames
      handleTargetNames handleBindings handleIdentitySub handleIdentitySupported
      handleVariableReceipt handleExtractFragment
      (pExtract (.fvar "w2") (.fvar "q2")) matched
  exact ⟨plan, compiled, planMatched, certificate, named, value⟩

/-- The renamed raw handle term passes the authored formation checker under
its explicit external type assignment; matching alone is not that receipt. -/
theorem open_handle_target_checked :
    checkHasType CombinedLang
      (FreeTypeContext.ofList
        [("w2", .base "State"), ("q2", .base "Query")]) []
      (pExtract (.fvar "w2") (.fvar "q2"))
      (.base "BinaryEvidence") = true := by
  decide +kernel

/-- The source schema's two externally supplied sorts are checked as well. -/
theorem open_handle_source_checked :
    checkHasType CombinedLang
      (FreeTypeContext.ofList
        [("w", .base "State"), ("q", .base "Query")]) []
      (namedErase handleSourceNames handleExtractFragment)
      (.base "BinaryEvidence") = true := by
  decide +kernel

/-- A raw external handle is a free variable, while intrinsic erasure uses a
bound-context index. Open naming cannot be replaced by closed erasure. -/
theorem open_handle_not_closed_erasure :
    namedErase handleTargetNames handleExtractFragment ≠
      erase handleExtractTerm := by
  decide +kernel

/-- One named variable used twice can match two equal authored evidence
subterms. This exercises the actual canonical pattern matcher. -/
theorem repeatedEvidenceName_matches_consistent :
    matchPattern (pCombine (.fvar "e") (.fvar "e"))
      (pCombine pEvidenceZero pEvidenceZero) ≠ [] := by
  decide +kernel

/-- A conflicting second occurrence cannot be silently assigned a different
image by the same name. This is a matcher-level control, not only a property
of the abstract variable-receipt hypothesis above. -/
theorem repeatedEvidenceName_rejects_conflict :
    matchPattern (pCombine (.fvar "e") (.fvar "e"))
      (pCombine pEvidenceZero (pCombine pEvidenceZero pEvidenceZero)) = [] := by
  decide +kernel

private def wrongSortFree : FreeTypeContext :=
  FreeTypeContext.ofList
    [("w1", .base "State"), ("w2", .base "State")]

private def wrongSortMatcherPattern : Pattern :=
  pCombine (.fvar "e") pEvidenceZero

private def wrongSortMatcherTarget : Pattern :=
  pCombine (pRevise (.fvar "w1") (.fvar "w2")) pEvidenceZero

/-- Structural matching does not type-check captured values. Here the matcher
accepts a State expression in an Evidence slot, while authored formation
rejects the target. Sorted intrinsic image receipts therefore cannot be
inferred from a raw successful match alone. -/
theorem matcher_accepts_cross_sort_capture :
    matchPattern wrongSortMatcherPattern wrongSortMatcherTarget ≠ [] ∧
      ¬ HasType (wmExtVertexLanguageDefGuarded combinedVertex)
        wrongSortFree [] wrongSortMatcherTarget (.base "BinaryEvidence") := by
  constructor
  · decide +kernel
  · intro typed
    have accepted := (checkHasType_eq_true_iff (by decide +kernel)).2 typed
    have rejected :
        checkHasType (wmExtVertexLanguageDefGuarded combinedVertex)
          wrongSortFree [] wrongSortMatcherTarget (.base "BinaryEvidence") = false := by
      decide +kernel
    rw [rejected] at accepted
    cases accepted

#print axioms namedErase_typed
#print axioms closed_typed_compiled_only_evidence
#print axioms no_closed_checked_compiled_nonEvidence
#print axioms closed_evidence_checks_pass
#print axioms namedErase_isObjectPattern
#print axioms namedErase_checked
#print axioms namedErase_isMatchCorrect
#print axioms namedErase_compiles
#print axioms namedErase_compiledMatcher
#print axioms matchPattern_namedErase_correct
#print axioms applyBindings_namedErase_eq_erase_bind
#print axioms matchPattern_namedErase_eq_erase_bind
#print axioms matchPattern_namedErase_denote
#print axioms matchPattern_namedErase_denote_any_supported
#print axioms applyBindings_namedErase_eq_namedErase_substitute
#print axioms matchPattern_namedErase_open_denote
#print axioms matchPattern_namedErase_open_complete_for_substitution
#print axioms matchPattern_namedErase_complete_for_substitution
#print axioms matchPattern_namedErase_recovers_used_bindings
#print axioms checkedClosedBindings_reifySubstitution
#print axioms checkedClosedCapture_nonEvidence_impossible
#print axioms checkedClosedMatch_reifiesIntrinsicInstance
#print axioms checkedClosedMatch_target_typed
#print axioms checkedClosed_repeatedEvidence_reifies
#print axioms counting_compiled_repeatedEvidence_denotes
#print axioms open_handle_compiled_match_denotes
#print axioms open_handle_target_checked
#print axioms open_handle_source_checked
#print axioms open_handle_not_closed_erasure
#print axioms repeatedEvidenceName_matches_consistent
#print axioms repeatedEvidenceName_rejects_conflict
#print axioms matcher_accepts_cross_sort_capture

end Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder
