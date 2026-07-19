import Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
import Mettapedia.Languages.Metamath.InferenceVariableClassification

/-!
# Runtime bridge for Metamath disjoint-variable checks

This module identifies the independent `DVOKSemantics` relation with the live
`DB.dvCheck` computation.  The boundary hypotheses state exactly the facts
that neither side can recover locally: extensional correspondence of the two
substitution representations, canonical orientation of the caller's stored
DV pairs, and agreement between explicit symbol tags and the runtime's active
name classification.

The final classification premise is intentionally explicit.  In a complete
one-step theorem it must be obtained from reachable-stack or generated
`Proves` evidence; bare assertion application and bare `dvCheck` success do
not establish it.
-/

namespace Mettapedia.Languages.Metamath.InferenceDVRuntimeBridge

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceVariableClassification
open Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation

/-! ## Pair and list agreement -/

/-- Strict canonical storage is exactly what turns symmetric generated DV
membership into the runtime's inequality-and-normalized-membership test. -/
theorem dvRelation_iff_runtimePair_of_strictOrderAll
    (pairs : List (String × String))
    (hstrict :
      pairs.all (fun pair => decide (pair.1 < pair.2)) = true)
    (left right : String) :
    DVRelation pairs left right ↔
      left ≠ right ∧
        (if left < right then (left, right) else (right, left)) ∈ pairs := by
  constructor
  · intro relation
    rcases relation with hforward | hreverse
    · have hlt : left < right := by
        simpa using
          (List.all_eq_true.mp hstrict (left, right) hforward)
      exact ⟨ne_of_lt hlt, by simpa [hlt] using hforward⟩
    · have hlt : right < left := by
        simpa using
          (List.all_eq_true.mp hstrict (right, left) hreverse)
      have hnot : ¬ left < right := not_lt_of_ge (le_of_lt hlt)
      exact ⟨(ne_of_lt hlt).symm, by simpa [hnot] using hreverse⟩
  · rintro ⟨_ne, hmember⟩
    by_cases hlt : left < right
    · exact Or.inl (by simpa [hlt] using hmember)
    · exact Or.inr (by simpa [hlt] using hmember)

/-- The generated cross-product relation and the nested Boolean loops used by
`dvCheckBool` agree under the same caller-pair invariant.  Order and duplicate
variable occurrences are retained on both sides. -/
theorem allPairsSemantics_iff_runtimeAll_of_strictOrderAll
    (pairs : List (String × String))
    (hstrict :
      pairs.all (fun pair => decide (pair.1 < pair.2)) = true)
    (lefts rights : List String) :
    AllPairsSemantics pairs lefts rights ↔
      lefts.all (fun left =>
        rights.all (fun right =>
          left != right &&
            decide
              ((if left < right then (left, right) else (right, left)) ∈
                pairs))) = true := by
  constructor
  · intro semantics
    apply List.all_eq_true.mpr
    intro left hleft
    apply List.all_eq_true.mpr
    intro right hright
    have pairSemantics := semantics left hleft right hright
    have runtimePair :=
      (dvRelation_iff_runtimePair_of_strictOrderAll
        pairs hstrict left right).mp pairSemantics
    simp only [Bool.and_eq_true]
    constructor
    · simpa using runtimePair.1
    · simpa using runtimePair.2
  · intro runtimeAll left hleft right hright
    have leftAll := List.all_eq_true.mp runtimeAll left hleft
    have pairCheck := List.all_eq_true.mp leftAll right hright
    simp only [Bool.and_eq_true] at pairCheck
    have hne : left ≠ right := by
      simpa using pairCheck.1
    have hmember :
        (if left < right then (left, right) else (right, left)) ∈ pairs := by
      simpa using pairCheck.2
    exact
      (dvRelation_iff_runtimePair_of_strictOrderAll
        pairs hstrict left right).mpr ⟨hne, hmember⟩

/-- Successful `dvCheck` is exactly truth of its Boolean worker. -/
theorem dvCheck_ok_iff_dvCheckBool_true
    (activeVariables : List String)
    (callerDV calleeDV : Array (String × String))
    (runtimeSubstitution : Std.HashMap String RuntimeFormula) :
    Metamath.Verify.DB.dvCheck activeVariables callerDV calleeDV
        runtimeSubstitution = .ok () ↔
      Metamath.Verify.DB.dvCheckBool activeVariables callerDV calleeDV
        runtimeSubstitution = true := by
  unfold Metamath.Verify.DB.dvCheck
  cases hcheck :
      Metamath.Verify.DB.dvCheckBool activeVariables callerDV calleeDV
        runtimeSubstitution <;>
    simp

/-- A frame-respecting replacement has the same ordered, duplicate-preserving
variable list under explicit-tag and runtime active-name classification. -/
theorem runtimeVarsIn_eq_bodyVariables_of_respectsFrame
    (activeVariables : List String) (replacement : ConstantHeadedFormula)
    (hrespect :
      formulaSymbolsRespectFrame activeVariables replacement = true) :
    replacement.toRuntime.varsIn activeVariables =
      BodyVariables replacement.body := by
  exact
    (varsIn_toRuntime_eq_taggedVariableNames
      activeVariables replacement hrespect).trans
      (bodyVariables_eq_taggedVariableNames replacement.body).symm

/-! ## Exact DV bridge -/

/-- Independent generated DV semantics agrees exactly with the live verifier
under the three explicit representation invariants.  No totality condition is
added beyond the global exact-correspondence premise; the DV computation itself
queries only bindings named by the callee DV list.  Duplicate DV pairs are
harmless on both sides.

The replacement-respect premise is deliberately not inferred here: its live
source is a reachable-stack `StackRespectsFrame` invariant, while its generated
source is a corresponding invariant for the leading `Proves` premise forest. -/
theorem dvOKSemantics_iff_dvCheck_of_correspondence
    {substitution : FiniteSubstitution}
    {callerFrame calleeFrame : RuntimeFrame}
    {callerVariables : List String}
    {runtimeSubstitution : Std.HashMap String RuntimeFormula}
    (hsubstitution :
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution)
    (hcallerDV :
      callerFrame.dj.toList.all
        (fun pair => decide (pair.1 < pair.2)) = true)
    (hreplacement :
      ∀ name replacement,
        LookupSemantics substitution name replacement →
          formulaSymbolsRespectFrame callerVariables replacement = true) :
    DVOKSemantics substitution callerFrame calleeFrame ↔
      Metamath.Verify.DB.dvCheck callerVariables callerFrame.dj calleeFrame.dj
        runtimeSubstitution = .ok () := by
  rw [dvCheck_ok_iff_dvCheckBool_true]
  simp only [DVOKSemantics, DVListsSemantics,
    Metamath.Verify.DB.dvCheckBool, Metamath.Verify.DJ]
  constructor
  · intro semantics
    apply List.all_eq_true.mpr
    rintro ⟨left, right⟩ hpair
    rcases semantics (left, right) hpair with
      ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
        pairSemantics⟩
    have leftRuntime :
        runtimeSubstitution[left]? = some leftReplacement.toRuntime :=
      (hsubstitution left leftReplacement.toRuntime).mpr
        ⟨leftReplacement, leftLookup, rfl⟩
    have rightRuntime :
        runtimeSubstitution[right]? = some rightReplacement.toRuntime :=
      (hsubstitution right rightReplacement.toRuntime).mpr
        ⟨rightReplacement, rightLookup, rfl⟩
    rw [leftRuntime, rightRuntime]
    simp only
    rw [runtimeVarsIn_eq_bodyVariables_of_respectsFrame
      callerVariables leftReplacement
        (hreplacement left leftReplacement leftLookup)]
    rw [runtimeVarsIn_eq_bodyVariables_of_respectsFrame
      callerVariables rightReplacement
        (hreplacement right rightReplacement rightLookup)]
    exact
      (allPairsSemantics_iff_runtimeAll_of_strictOrderAll
        callerFrame.dj.toList hcallerDV
        (BodyVariables leftReplacement.body)
        (BodyVariables rightReplacement.body)).mp pairSemantics
  · intro runtimeAll pair hpair
    have pairCheck := List.all_eq_true.mp runtimeAll pair hpair
    rcases pair with ⟨left, right⟩
    cases leftRuntime : runtimeSubstitution[left]? with
    | none => simp [leftRuntime] at pairCheck
    | some leftRuntimeFormula =>
        cases rightRuntime : runtimeSubstitution[right]? with
        | none => simp [leftRuntime, rightRuntime] at pairCheck
        | some rightRuntimeFormula =>
            obtain ⟨leftReplacement, leftLookup, leftFormula⟩ :=
              (hsubstitution left leftRuntimeFormula).mp leftRuntime
            obtain ⟨rightReplacement, rightLookup, rightFormula⟩ :=
              (hsubstitution right rightRuntimeFormula).mp rightRuntime
            refine
              ⟨leftReplacement, rightReplacement, leftLookup, rightLookup, ?_⟩
            simp only [leftRuntime, rightRuntime] at pairCheck
            rw [leftFormula, rightFormula] at pairCheck
            rw [runtimeVarsIn_eq_bodyVariables_of_respectsFrame
              callerVariables leftReplacement
                (hreplacement left leftReplacement leftLookup)] at pairCheck
            rw [runtimeVarsIn_eq_bodyVariables_of_respectsFrame
              callerVariables rightReplacement
                (hreplacement right rightReplacement rightLookup)] at pairCheck
            exact
              (allPairsSemantics_iff_runtimeAll_of_strictOrderAll
                callerFrame.dj.toList hcallerDV
                (BodyVariables leftReplacement.body)
                (BodyVariables rightReplacement.body)).mpr pairCheck

/-! ## Executable boundaries -/

private def variableFormula (name : String) : ConstantHeadedFormula :=
  ⟨"wff", [.var name]⟩

private def constantFormula (name : String) : ConstantHeadedFormula :=
  ⟨"wff", [.const name]⟩

private def pairSubstitution : FiniteSubstitution :=
  [⟨"x", variableFormula "a"⟩, ⟨"y", variableFormula "b"⟩]

private def pairRuntimeSubstitution : Std.HashMap String RuntimeFormula :=
  InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap pairSubstitution

private def pairCalleeFrame : RuntimeFrame :=
  ⟨#[ ("x", "y") ], #[]⟩

private def canonicalCallerFrame : RuntimeFrame :=
  ⟨#[ ("a", "b") ], #[]⟩

private theorem singletonDVOK
    {substitution : FiniteSubstitution}
    {callerFrame : RuntimeFrame}
    {leftName rightName : String}
    {leftReplacement rightReplacement : ConstantHeadedFormula}
    (leftLookup :
      LookupSemantics substitution leftName leftReplacement)
    (rightLookup :
      LookupSemantics substitution rightName rightReplacement)
    (pairSemantics :
      AllPairsSemantics callerFrame.dj.toList
        (BodyVariables leftReplacement.body)
        (BodyVariables rightReplacement.body)) :
    DVOKSemantics substitution callerFrame
      ⟨#[ (leftName, rightName) ], #[]⟩ := by
  change
    DVListsSemantics substitution callerFrame.dj.toList
      [(leftName, rightName)]
  intro pair hpair
  have hpairEq : pair = (leftName, rightName) := by
    simpa using (List.mem_singleton.mp hpair)
  subst pair
  exact
    ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
      pairSemantics⟩

private theorem pairSemantics_canonical :
    DVOKSemantics pairSubstitution canonicalCallerFrame pairCalleeFrame := by
  apply singletonDVOK
    (leftReplacement := variableFormula "a")
    (rightReplacement := variableFormula "b")
  · simp [LookupSemantics, pairSubstitution]
  · simp [LookupSemantics, pairSubstitution]
  · intro left hleft right hright
    change DVRelation [("a", "b")] left right
    simp [variableFormula, BodyVariables] at hleft hright
    subst left
    subst right
    exact Or.inl (by simp)

/-- Positive boundary: a canonical caller pair and frame-respecting images
pass both semantics. -/
example :
    Metamath.Verify.DB.dvCheck ["a", "b"] canonicalCallerFrame.dj
        pairCalleeFrame.dj pairRuntimeSubstitution = .ok () := by
  apply
    (dvOKSemantics_iff_dvCheck_of_correspondence
      (substitution := pairSubstitution)
      (callerFrame := canonicalCallerFrame)
      (calleeFrame := pairCalleeFrame)
      (callerVariables := ["a", "b"])
      (runtimeSubstitution := pairRuntimeSubstitution) ?_ ?_ ?_).mp
      pairSemantics_canonical
  · apply runtimeSubstitutionMap_correspondence
    simp [InferenceSideConditionsSemantics.SubstitutionKeysUnique,
      pairSubstitution]
  · decide
  · intro name replacement hlookup
    simp [LookupSemantics, pairSubstitution] at hlookup
    rcases hlookup with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private def reversedCallerFrame : RuntimeFrame :=
  ⟨#[ ("b", "a") ], #[]⟩

/-- Reversed caller storage is accepted by symmetric `DVRelation` but rejected
by the runtime's normalized membership test. -/
example :
    DVOKSemantics pairSubstitution reversedCallerFrame pairCalleeFrame ∧
      Metamath.Verify.DB.dvCheck ["a", "b"] reversedCallerFrame.dj
        pairCalleeFrame.dj pairRuntimeSubstitution ≠ .ok () := by
  constructor
  · apply singletonDVOK
      (leftReplacement := variableFormula "a")
      (rightReplacement := variableFormula "b")
    · simp [LookupSemantics, pairSubstitution]
    · simp [LookupSemantics, pairSubstitution]
    · intro left hleft right hright
      change DVRelation [("b", "a")] left right
      simp [variableFormula, BodyVariables] at hleft hright
      subst left
      subst right
      exact Or.inr (by simp)
  · simp [Metamath.Verify.DB.dvCheck,
      Metamath.Verify.DB.dvCheckBool, reversedCallerFrame, pairCalleeFrame,
      pairRuntimeSubstitution, pairSubstitution,
      InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap,
      variableFormula, ConstantHeadedFormula.toRuntime,
      Metamath.Verify.Formula.varsIn, Metamath.Verify.Sym.value,
      Std.HashMap.getElem?_insert, Metamath.Verify.DJ]
    apply String.lt_iff_ltb.mp
    rw [String.lt_iff_toList_lt]
    decide

private def selfSubstitution : FiniteSubstitution :=
  [⟨"x", variableFormula "a"⟩, ⟨"y", variableFormula "a"⟩]

private def selfRuntimeSubstitution : Std.HashMap String RuntimeFormula :=
  InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap selfSubstitution

private def selfCallerFrame : RuntimeFrame :=
  ⟨#[ ("a", "a") ], #[]⟩

/-- A stored self-pair supplies generated membership, while runtime inequality
rejects the same variable against itself. -/
example :
    DVOKSemantics selfSubstitution selfCallerFrame pairCalleeFrame ∧
      Metamath.Verify.DB.dvCheck ["a"] selfCallerFrame.dj pairCalleeFrame.dj
        selfRuntimeSubstitution ≠ .ok () := by
  constructor
  · apply singletonDVOK
      (leftReplacement := variableFormula "a")
      (rightReplacement := variableFormula "a")
    · simp [LookupSemantics, selfSubstitution]
    · simp [LookupSemantics, selfSubstitution]
    · intro left hleft right hright
      change DVRelation [("a", "a")] left right
      simp [variableFormula, BodyVariables] at hleft hright
      subst left
      subst right
      exact Or.inl (by simp)
  · simp [Metamath.Verify.DB.dvCheck,
      Metamath.Verify.DB.dvCheckBool, pairCalleeFrame,
      selfRuntimeSubstitution, selfSubstitution,
      InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap,
      variableFormula, ConstantHeadedFormula.toRuntime,
      Metamath.Verify.Formula.varsIn, Metamath.Verify.Sym.value,
      Std.HashMap.getElem?_insert, Metamath.Verify.DJ]

private def missingSubstitution : FiniteSubstitution :=
  [⟨"x", variableFormula "a"⟩]

private def missingRuntimeSubstitution : Std.HashMap String RuntimeFormula :=
  InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap
    missingSubstitution

/-- A missing callee binding fails on both sides of the bridge. -/
example :
    ¬DVOKSemantics missingSubstitution canonicalCallerFrame pairCalleeFrame ∧
      Metamath.Verify.DB.dvCheck ["a", "b"] canonicalCallerFrame.dj
        pairCalleeFrame.dj missingRuntimeSubstitution ≠ .ok () := by
  constructor
  · intro semantics
    rcases semantics ("x", "y") (by
      change ("x", "y") ∈ [("x", "y")]
      simp) with
      ⟨_leftReplacement, rightReplacement, _leftLookup, rightLookup, _⟩
    simp [LookupSemantics, missingSubstitution] at rightLookup
  · simp [Metamath.Verify.DB.dvCheck,
      Metamath.Verify.DB.dvCheckBool, canonicalCallerFrame, pairCalleeFrame,
      missingRuntimeSubstitution, missingSubstitution,
      InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap,
      variableFormula, ConstantHeadedFormula.toRuntime,
      Metamath.Verify.Formula.varsIn, Metamath.Verify.Sym.value,
      Std.HashMap.getElem?_insert, Metamath.Verify.DJ]

private def classificationMismatchSubstitution : FiniteSubstitution :=
  [⟨"x", constantFormula "a"⟩, ⟨"y", variableFormula "a"⟩]

private def classificationMismatchRuntime :
    Std.HashMap String RuntimeFormula :=
  InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap
    classificationMismatchSubstitution

private def emptyCallerFrame : RuntimeFrame := ⟨#[], #[]⟩

/-- Without frame-respect, an explicitly tagged constant whose name is active
is invisible to `BodyVariables` but visible to runtime `varsIn`. -/
example :
    DVOKSemantics classificationMismatchSubstitution emptyCallerFrame
        pairCalleeFrame ∧
      Metamath.Verify.DB.dvCheck ["a"] emptyCallerFrame.dj pairCalleeFrame.dj
        classificationMismatchRuntime ≠ .ok () := by
  constructor
  · apply singletonDVOK
      (leftReplacement := constantFormula "a")
      (rightReplacement := variableFormula "a")
    · simp [LookupSemantics, classificationMismatchSubstitution]
    · simp [LookupSemantics, classificationMismatchSubstitution]
    · change AllPairsSemantics []
        (BodyVariables (constantFormula "a").body)
        (BodyVariables (variableFormula "a").body)
      intro left hleft
      simp [constantFormula, BodyVariables] at hleft
  · simp [Metamath.Verify.DB.dvCheck,
      Metamath.Verify.DB.dvCheckBool, emptyCallerFrame, pairCalleeFrame,
      classificationMismatchRuntime, classificationMismatchSubstitution,
      InferenceSideConditionsRuntimeBridge.RuntimeSubstitutionMap,
      constantFormula, variableFormula, ConstantHeadedFormula.toRuntime,
      Metamath.Verify.Formula.varsIn, Metamath.Verify.Sym.value,
      Std.HashMap.getElem?_insert, Metamath.Verify.DJ]

end Mettapedia.Languages.Metamath.InferenceDVRuntimeBridge
